// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Mutex services.
//!
//! A [`Mutex<T>`] guards an object of type `T`. When locking succeeds, you're
//! provided a [`MutexGuard`] that wraps the data.
//!
//! [`Mutex`] is recursive. You can acquire the lock multiple times from the
//! same thread. You'll need to unlock it as many times as you've locked it;
//! [`MutexGuard`] will handle that automatically.
//!
//! Since the mutex is recursive, it cannot provide interior mutability. If you
//! need mutation, wrap your data in a [`RefCell`], a [`Cell`], or another
//! type that defends against mutable aliasing. Consider using [`RefCellMutex`]
//! or [`CellMutex`] as common case conveniences.
//!
//! When you allocate a mutex with [`context`](Mutex::context), it's inert. You'll
//! need to [`create`](Mutex::create) the mutex in order to access the data.
//!
//! # Example
//!
//! A mutex protects global data. If another thread cannot be provided with a reference
//! to the already-created mutex, the thread can wait for the mutex to be created.
//!
//! ```no_run
//! use fusible::mutex::{MutexContext, Mutex, MutexGuard};
//! use core::pin::Pin;
//! use core::cell::Cell;
//!
//! static MUTEX: MutexContext<Cell<u32>> = Mutex::with_cell(5);
//!
//! // A thread that creates the mutex...
//! # (|| -> Result<(), fusible::mutex::CreateError> {
//! let mutex = Mutex::create(Pin::static_ref(&MUTEX), &Default::default())?;
//! # (|| -> Result<(), fusible::mutex::LockError> {
//! {
//!     let data = mutex.lock()?;
//!     data.set(data.get() + 7);
//! } // <-- data automatically unlocked.
//! # Ok(()) })().unwrap();
//! # Ok(()) })().unwrap();
//!
//! // A thread that can see MUTEX, but hasn't been provided with
//! // a reference to the already-created mutex...
//! let mutex = loop {
//!     if let Some(mutex) = Pin::static_ref(&MUTEX).try_created() {
//!         break mutex;
//!     }
//!     fusible::thread::sleep(5);
//! };
//! # (|| -> Result<(), fusible::mutex::LockError> {
//! let data = mutex.lock()?;
//! data.set(data.get() + 18);
//! # (|| -> Result<(), fusible::mutex::UnlockError> {
//! MutexGuard::unlock(data)?; // <-- data manually unlocked.
//! # Ok(()) })().unwrap();
//! # Ok(()) })().unwrap();
//! ```
//!
//! A mutex is locally allocated. It can still be shared across threads.
//!
//! ```no_run
//! use fusible::{mutex::Mutex, thread::{Thread, StaticStack, ThreadContext}};
//! use core::pin::{pin, Pin};
//!
//! static STACK_A: StaticStack<256> = StaticStack::new();
//! static THREAD_A: ThreadContext = Thread::context();
//!
//! static STACK_B: StaticStack<256> = StaticStack::new();
//! static THREAD_B: ThreadContext = Thread::context();
//!
//! fn main() {
//!     let mutex = pin!(Mutex::with_cell(0u32));
//!     fusible::kernel_enter(|app_define| {
//!         let mutex = Mutex::create(mutex.into_ref(), &Default::default()).unwrap();
//!
//!         app_define.create_thread(
//!             Pin::static_ref(&THREAD_A),
//!             STACK_A.take().unwrap(),
//!             &Default::default(),
//!             move || loop {
//!             {
//!                 let data = mutex.lock().unwrap();
//!                 data.set(data.get().wrapping_add(4));
//!             }
//!             fusible::thread::sleep(50);
//!         }).unwrap();
//!
//!         
//!         app_define.create_thread(
//!             Pin::static_ref(&THREAD_B),
//!             STACK_B.take().unwrap(),
//!             &Default::default(),
//!             move || loop {
//!             {
//!                 let data = mutex.lock().unwrap();
//!                 data.set(data.get().wrapping_add(7));
//!             }
//!             fusible::thread::sleep(100);
//!         }).unwrap();
//!     });
//! }
//! ```

use core::{
    cell::{Cell, RefCell, UnsafeCell},
    ffi::CStr,
    mem::ManuallyDrop,
    ops::Deref,
    pin::Pin,
};

use crate::{
    marker::{InvariantLifetime, NotSend},
    tx_sys::TX_MUTEX,
    ControlBlock, WaitOption,
};

error_enum! {
    /// An error when creating a mutex.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum CreateError {
        /// The mutex is already created.
        AlreadyCreated = crate::tx_sys::TX_MUTEX_ERROR,

        /// The caller is invalid.
        ///
        /// You can only create a mutex in the initialization or
        /// thread execution contexts.
        Caller = crate::tx_sys::TX_CALLER_ERROR,

        // Not handling TX_INHERIT_ERROR. Enum ensures that values
        // are valid.
    }
}

error_enum! {
    /// An error when locking a mutex.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum LockError {
        // Not handling TX_DELETED. Users cannot delete
        // a mutex while references are live.

        // Not handling TX_NOT_AVAILABLE. That's a success
        // condition.

        /// The call was aborted by another entity.
        ///
        /// This happens when your software chooses to abort a thread's
        /// blocking call.
        WaitAborted = crate::tx_sys::TX_WAIT_ABORTED,

        // Not handling TX_MUTEX_ERROR. A mutex is assumed to be created.

        /// The wait option is invalid for the execution context.
        ///
        /// If you're locking a mutex from a non-thread execution context, then you must
        /// use a `try_*` method, or supply "no wait" as the wait option.
        InvalidWait = crate::tx_sys::TX_WAIT_ERROR,

        /// The caller is invalid.
        ///
        /// You cannot lock a mutex in an interrupt!
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

error_enum! {
    /// An error when unlocking a mutex.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum UnlockError {
        /// The lock isn't owned by the unlocking thread.
        NotOwned = crate::tx_sys::TX_NOT_OWNED,

        // Not handling TX_MUTEX_ERROR. A mutex is assumed to be created.

        /// The caller is invalid.
        ///
        /// You cannot unlock a mutex in an interrupt!
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

/// A mutex's priority inheritance option.
///
/// Set this value in [`MutexOptions`]. The default behavior
/// is "no inherit."
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[repr(u32)]
pub enum PriorityInheritance {
    /// The mutex does not support priority inheritance.
    ///
    /// The primitive `false` converts into this value.
    #[default]
    NoInherit = crate::tx_sys::TX_NO_INHERIT,
    /// The mutex supports priority inheritance.
    ///
    /// The primitive `true` converts into this value.
    Inherit = crate::tx_sys::TX_INHERIT,
}

impl From<bool> for PriorityInheritance {
    #[inline]
    fn from(inherit: bool) -> Self {
        if inherit {
            Self::Inherit
        } else {
            Self::NoInherit
        }
    }
}

impl From<PriorityInheritance> for bool {
    #[inline]
    fn from(inhert: PriorityInheritance) -> Self {
        PriorityInheritance::Inherit == inhert
    }
}

/// Runtime options for a mutex.
///
/// Supply these values to [`create`](Mutex::create).
#[derive(Default)]
#[non_exhaustive]
pub struct MutexOptions<'a> {
    /// An (optional) name for the mutex.
    pub name: Option<&'a CStr>,
    /// The priority inheritance behavior for the mutex.
    pub inheritance: PriorityInheritance,
}

/// Wraps the mutex data, and implements the unsafe traits necessary
/// for a complete mutex. The UnsafeCell is intended to disable
/// layout optimizations while still supporting ?Sized types (not
/// currently supported by MaybeUninit).
#[repr(transparent)]
struct MutexData<T: ?Sized>(UnsafeCell<T>);

// Safety: If we can move the inner data across execution contexts,
// then we can also move the mutex.
unsafe impl<T: ?Sized + Send> Send for MutexData<T> {}
// Safety: The goal of a Mutex is to provide Sync to a type that can
// be moved across execution contexts. We use (non-)blocking locks
// at runtime to ensure mutual exclusion of shared state.
unsafe impl<T: ?Sized + Send> Sync for MutexData<T> {}

/// Manages the control block, data, and borrows.
///
/// Use [`Mutex`] to interact with the context. The methods on
/// the context let you access an already-created mutex.
///
/// # FFI
///
/// The context is transparently a [`Mutex`]. See [`Mutex`]
/// documentation for more information.
#[repr(transparent)]
pub struct MutexContext<'ctx, T>(Mutex<T>, InvariantLifetime<'ctx>);

impl<T> Drop for MutexContext<'_, T> {
    #[inline]
    fn drop(&mut self) {
        // Safety: Resource created and pinned per GSG-002, or not created per
        // GSG-003. Handling lifecycle checks per GSG-003.
        unsafe {
            let result = crate::tx_sys::tx_mutex_delete(self.0 .0.get());
            aborting_assert!(
                result == crate::tx_sys::TX_SUCCESS || result == crate::tx_sys::TX_MUTEX_ERROR,
                "Attempt to drop resource in the initialization context"
            );
        }
    }
}

/// A resource for protecting shared state.
///
/// The priority inheritance behavior is specified in [`MutexOptions`].
///
/// To access the data, use
///
/// - [`lock`](Self::lock) if you're willing to wait forever.
/// - [`try_lock`](Self::try_lock) for a non-blocking lock.
/// - [`lock_with_wait`](Self::lock_with_wait) to wait for the lock.
///
/// The [`MutexGuard`] returned by these methods will automatically unlock
/// the mutex when it's dropped.
///
/// See [the module-level documentation](crate::mutex) for examples.
///
/// # FFI
///
/// Unlike other resources, a `Mutex<T>` *is not* transparently a control
/// block. However, Fusible guarantees that there exists a `TX_MUTEX` at
/// the address of any `Mutex<T>`. For the purposes of FFI, you may think
/// of a `Mutex<T>` as
///
/// ```
/// # struct TX_MUTEX;
/// #[repr(C)]
/// pub struct Mutex<T> {
///     pub control_block: TX_MUTEX,
///     // Private members follow...
/// #   _ignore: core::marker::PhantomData<T>,
/// }
/// ```
#[repr(C)]
pub struct Mutex<T>(ControlBlock<TX_MUTEX>, MutexData<T>);

impl<T> Mutex<T> {
    /// Allocate a mutex with initial state.
    ///
    /// This doesn't register the mutex with the operating system. Use [`create`](Self::create)
    /// for that.
    #[inline]
    pub const fn context<'ctx>(data: T) -> MutexContext<'ctx, T> {
        MutexContext(
            Mutex(ControlBlock::new(), MutexData(UnsafeCell::new(data))),
            InvariantLifetime::mark(),
        )
    }

    /// Create a mutex.
    ///
    /// On success, you're given a handle to the control block. Use this to
    /// interact with the mutex.
    #[inline]
    pub fn create<'ctx, 't>(
        ctx: Pin<&'t MutexContext<'ctx, T>>,
        opts: &MutexOptions<'ctx>,
    ) -> Result<&'t Self, CreateError> {
        // Safety: Context pinned per GSG-001. Tracking lifetime of
        // borrowed name per GSG-000.
        unsafe {
            let ctx = ctx.get_ref();
            let result = crate::tx_sys::tx_mutex_create(
                ctx.0 .0.get(),
                crate::threadx_string(opts.name),
                opts.inheritance as _,
            );
            CreateError::try_from_result(result)?;
            Ok(&ctx.0)
        }
    }
}

impl<T> Mutex<T> {
    /// Try to lock the mutex until the timeout expires.
    ///
    /// If the timeout expires, the result is `Ok(None)`. Otherwise, if
    /// there is no error, you're provided a guard in the `Ok(Some(...))`
    /// result.
    ///
    /// If you're willing to wait forever, use [`lock`](Self::lock). If
    /// you want to return immediately without blocking, use [`try_lock`](Self::try_lock).
    #[inline]
    pub fn lock_with_wait(
        &self,
        wait_option: WaitOption,
    ) -> Result<Option<MutexGuard<'_, T>>, LockError> {
        // Safety: resource pinned and created per GSG-002.
        // We only release the lock guard when we successfully
        // acquire the lock.
        unsafe {
            let result = crate::tx_sys::tx_mutex_get(self.0.get(), wait_option.into());
            if result == crate::tx_sys::TX_NOT_AVAILABLE {
                return Ok(None);
            }

            LockError::try_from_result(result)?;

            Ok(Some(MutexGuard {
                mutex: self,
                _not_send: NotSend::mark(),
            }))
        }
    }

    /// Lock the mutex, waiting forever.
    ///
    /// This method can only be used in a thread execution context.
    #[inline]
    pub fn lock(&self) -> Result<MutexGuard<'_, T>, LockError> {
        // Safety: Since we're waiting forever, we'll never observe TX_NOT_AVAILABLE. Since
        // we never observe TX_NOT_AVAILABLE, we'll never produce a None.
        Ok(unsafe {
            let guard = self.lock_with_wait(WaitOption::wait_forever())?;
            guard.unwrap_unchecked()
        })
    }

    /// Try to lock the mutex.
    ///
    /// Unlike [`lock`](Self::lock), this call will return immediately if the
    /// lock is not available. Since it never blocks, this call can be used from
    /// an initialization context. But although it never blocks, this call cannot
    /// be used from an interrupt context.
    ///
    /// If the lock isn't available, then the return is `Ok(None)`. If there is
    /// no error and the lock is acquired, you're provided a guard in the `Ok(Some(...))`
    /// result.
    #[inline]
    pub fn try_lock(&self) -> Result<Option<MutexGuard<'_, T>>, LockError> {
        // Safety: See inline comments. Exhaustive match checks current / future errors.
        unsafe {
            match self.lock_with_wait(WaitOption::no_wait()) {
                // Happy-path: acquire the lock or timeout.
                Ok(guard) => Ok(guard),
                // Despite the "no wait" option, the calling context can be
                // invalid.
                Err(LockError::Caller) => Err(LockError::Caller),
                // If the calling context is correct then the "no wait" option
                // is always valid.
                Err(LockError::InvalidWait) => fusible_unreachable!(),
                // Since we never wait, there is no wait that can be aborted.
                Err(LockError::WaitAborted) => fusible_unreachable!(),
            }
        }
    }

    /// Manually unlock the mutex.
    ///
    /// # Safety
    ///
    /// If called from a thread that holds a `MutexGuard`, this call can invalidate
    /// that `MutexGuard`'s protection. Once invalidated, another thread can lock
    /// the mutex and access the shared data. As a result, there can be multiple
    /// `!Sync` references to the same data at the same time.
    ///
    /// The caller is responsible for making sure an `unlock` call does not result
    /// in multiple references to the same data.
    #[inline]
    pub unsafe fn unlock(&self) -> Result<(), UnlockError> {
        // Safety: Resource pinned and created per GSG-002. We don't
        // consider the safey of releasing another mutable reference;
        // the caller needs to check that.
        let result = unsafe { crate::tx_sys::tx_mutex_put(self.0.get()) };
        UnlockError::try_from_result(result)?;

        Ok(())
    }

    /// Access the data managed by the mutex.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the lock is held. Otherwise, the returned reference
    /// may be accessed as if it were Sync when it's not actually Sync.
    unsafe fn data(&self) -> &T {
        // Safety: Despite internally using an UnsafeCell, we never
        // produce a mutable reference to the data. We only produce
        // shared references. Even if those shared references aren't
        // Sync, we hold a lock on the data, so no other thread is
        // accessing this state.
        unsafe { &*self.1 .0.get() }
    }
}

impl<T> MutexContext<'_, T> {
    impl_common_context!(Mutex<T>);
}

/// A mutex protecting a `RefCell`.
///
/// This is a convenience for providing interior mutability
/// with a [`Mutex`]. Use [`with_refcell`](RefCellMutex::with_refcell)
/// to easily allocate this type of mutex.
pub type RefCellMutex<T> = Mutex<RefCell<T>>;

impl<T> RefCellMutex<T> {
    /// Allocate a mutex with `RefCell`-managed state.
    #[inline]
    pub const fn with_refcell<'ctx>(data: T) -> MutexContext<'ctx, RefCell<T>> {
        Self::context(RefCell::new(data))
    }
}

/// A mutex protecting a `Cell`.
///
/// This is a convenience for providing interior mutability
/// with a [`Mutex`]. Use [`with_cell`](CellMutex::with_cell)
/// to easily allocate this type of mutex.
pub type CellMutex<T> = Mutex<Cell<T>>;

impl<T> CellMutex<T> {
    /// Allocate a mutex with `Cell`-managed state.
    #[inline]
    pub const fn with_cell<'ctx>(data: T) -> MutexContext<'ctx, Cell<T>> {
        Self::context(Cell::new(data))
    }
}

/// Provides exclusive access to shared data.
///
/// This is acquired by locking a [`Mutex`]. When a thread can access one of these
/// objects, it is the only thread that can access the protected data.
///
/// When this object is dropped, it will unlock the mutex. That may give another
/// thread a chance to access the shared data. If this unlock-during-drop fails,
/// the error is ignored. If you're interested in catching that condition, call
/// [`unlock`](Self::unlock) on the guard.
pub struct MutexGuard<'a, T> {
    mutex: &'a Mutex<T>,
    /// I think we _could_ allow Send on the MutexGuard.
    /// If the guard is sent to another thread and that
    /// other thread drops the guard, it'll observe the
    /// "not owned" error. I expect that would leave the
    /// mutex in the locked state, as if the guard were
    /// forgotten by the original thread. This differs
    /// from std, where the OS requires that the thread
    /// acquiring the lock is the same one that does
    /// the unlock (IIUC).
    ///
    /// Not allowing Send is a hint to the user, a tip
    /// to avoid the above situation. Adding Send would
    /// be a non-breaking change, so we could remove this
    /// marker later.
    _not_send: NotSend,
}

impl<T> Drop for MutexGuard<'_, T> {
    #[inline]
    fn drop(&mut self) {
        // Safety: If we allocated a MutexGuard, then we must
        // hold the lock. There is no (safe) double-unlock, since
        // there is no safe double-drop.
        let _ = unsafe { self.mutex.unlock() };
    }
}

impl<T> Deref for MutexGuard<'_, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &Self::Target {
        // Safety: Since a MutexGuard exists, we must be holding the lock.
        unsafe { self.mutex.data() }
    }
}

impl<T> MutexGuard<'_, T> {
    /// Unlock the mutex.
    ///
    /// This will happen automatically on drop. However, by calling
    /// `unlock`, you can check for any errors.
    #[inline]
    pub fn unlock(guard: Self) -> Result<(), UnlockError> {
        // Safety: If a MutexGuard exists, then we hold the lock on the
        // shared state. It's OK for us to unlock it, but only once!
        unsafe { ManuallyDrop::new(guard).mutex.unlock() }
    }
}
