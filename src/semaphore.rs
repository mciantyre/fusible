// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Semaphore services.
//!
//! A [`Semaphore`] tracks an unsigned 32 bit counter. Every put will increment
//! the counter, and every get will decrement the counter. If the counter is
//! zero, then callers may block until the count increments.
//!
//! # Example
//!
//! A globally-allocated semaphore with an initial count of zero.
//!
//! ```no_run
//! use fusible::semaphore::{Semaphore, SemaphoreContext};
//! use core::pin::Pin;
//!
//! # (|| -> Result<(), fusible::semaphore::CreateError> {
//! static SEMA: SemaphoreContext = Semaphore::context();
//! let sema = Semaphore::create(Pin::static_ref(&SEMA), &Default::default())?;
//!
//! sema.put();
//! assert!(sema.try_get().is_some());
//! # Ok(()) })().unwrap();
//! ```
//!
//! A locally-allocated, named semaphore with a non-zero initial count.
//!
//! ```no_run
//! use fusible::semaphore::{Semaphore, SemaphoreOptions};
//! use core::pin::pin;
//! use core::num::NonZero;
//!
//! # (|| -> Result<(), fusible::semaphore::CreateError> {
//! let sema = pin!(Semaphore::context());
//!
//! let mut opts = SemaphoreOptions::default();
//! opts.initial_count = 5;
//! opts.name = Some(c"counter");
//!
//! let sema = Semaphore::create(sema.into_ref(), &opts)?;
//!
//! const CEILING: NonZero<u32> = // ...
//! # unsafe { NonZero::new_unchecked(1) };
//! let _ = sema.ceiling_put(CEILING);
//! # (|| -> Result<(), fusible::semaphore::GetError> {
//! sema.get()?;
//! # Ok(()) })().unwrap();
//! # Ok(()) })().unwrap();
//! ```

use core::{ffi::CStr, num::NonZeroU32, pin::Pin};

use crate::marker::InvariantLifetime;
use crate::tx_sys::TX_SEMAPHORE;

use crate::{ControlBlock, WaitOption};

error_enum! {
    /// An error when creating a semaphore.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum CreateError {
        /// The semaphore is already created.
        AlreadyCreated = crate::tx_sys::TX_SEMAPHORE_ERROR,

        /// The caller is invalid.
        ///
        /// You can only create semaphores in the initialization
        /// and thread execution contexts.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

error_enum! {
    /// An error when putting with a ceiling.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum CeilingPutError {
        // Not handling TX_INVALID_CEILING. Non-zero types
        // guarantee this isn't possible.

        /// The current count already exceeds the ceiling.
        ///
        /// Your put was ignored.
        Exceeded = crate::tx_sys::TX_CEILING_EXCEEDED,

        // Not handling TX_SEMAPHORE_ERROR. All semaphores are assumed
        // to be created.
    }
}

error_enum! {
    /// An error when getting the semaphore count.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum GetError {
        // Not handling TX_DELETED. A user cannot drop the
        // context block while references are live.

        // Not handling TX_NO_INSTANCE. That's a timeout in
        // the success path.

        /// The call was aborted by another entity.
        ///
        /// This happens when your software chooses to abort a thread's
        /// blocking call.
        WaitAborted = crate::tx_sys::TX_WAIT_ABORTED,

        // Not handling TX_SEMAPHORE_ERROR. All semaphores are assumed
        // to be created.

        /// The wait option is invalid for the calling context.
        ///
        /// If you're getting a semaphore in a non-thread execution context,
        /// then your wait option can only be "no wait."
        InvalidWait = crate::tx_sys::TX_WAIT_ERROR,
    }
}

/// Configure the initial count and other semaphore options.
#[derive(Default)]
#[non_exhaustive]
pub struct SemaphoreOptions<'a> {
    /// A name for this semaphore.
    ///
    /// By default, there is no name.
    pub name: Option<&'a CStr>,
    /// The semaphore's initial count.
    ///
    /// By default, this is zero.
    pub initial_count: u32,
}

/// A counting semaphore for synchronization.
///
/// To decrement the counter, use
///
/// - [`get`](Self::get) if you're willing to wait forever.
/// - [`try_get`](Self::try_get) for a non-blocking decrement.
/// - [`get_with_wait`](Self::get_with_wait) to wait for some time.
///
/// To increment the counter, use [`put`](Self::put) or [`ceiling_put`](Self::ceiling_put).
///
/// See [the module-level documentation](crate::semaphore) for examples.
///
/// # FFI
///
/// `Semaphore` is transparently a `TX_SEMAPHORE`.
#[repr(transparent)]
pub struct Semaphore(ControlBlock<TX_SEMAPHORE>);

/// Manages the semaphore and borrowed data.
///
/// Use [`Semaphore`] to interact with a context. Methods on the context
/// let you access an already-created semaphore.
///
/// # FFI
///
/// The context is transparently a [`Semaphore`].
#[repr(transparent)]
pub struct SemaphoreContext<'ctx>(Semaphore, InvariantLifetime<'ctx>);

impl Drop for SemaphoreContext<'_> {
    #[inline]
    fn drop(&mut self) {
        // Safety: Resource created and pinned per GSG-002, or not created per
        // GSG-003. Handling lifecycle checks per GSG-003.
        unsafe {
            let result = crate::tx_sys::tx_semaphore_delete(self.0.0.get());
            aborting_assert!(
                result == crate::tx_sys::TX_SUCCESS || result == crate::tx_sys::TX_SEMAPHORE_ERROR,
                "Attempt to drop resource in the initialization context",
            );
        }
    }
}

impl Semaphore {
    /// Allocate a semaphore.
    ///
    /// The object is inert; you'll need to pin it and call [`create`](Self::create) before
    /// you can use it.
    #[inline]
    pub const fn context<'ctx>() -> SemaphoreContext<'ctx> {
        SemaphoreContext(Semaphore(ControlBlock::new()), InvariantLifetime::mark())
    }

    /// Create a semaphore.
    ///
    /// Use [`SemaphoreOptions`] to set options, including the initial count
    /// of the semaphore.
    ///
    /// On success, you're given a handle to the created semaphore.
    #[inline]
    pub fn create<'ctx, 's>(
        sema: Pin<&'s SemaphoreContext<'ctx>>,
        opts: &'_ SemaphoreOptions<'ctx>,
    ) -> Result<&'s Self, CreateError> {
        // Safety: Context pinned per GSG-001. Tracking lifetime
        // of borrowed name per GSG-000.
        unsafe {
            let sema = sema.get_ref();
            let result = crate::tx_sys::tx_semaphore_create(
                sema.0.0.get(),
                crate::threadx_string(opts.name),
                opts.initial_count,
            );
            CreateError::try_from_result(result)?;
            Ok(&sema.0)
        }
    }
}

impl Semaphore {
    /// Increment the count by one.
    ///
    /// Internally, the semaphore performs wrapping addition. Therefore, if the
    /// semaphore's internal count is `u32::MAX`, then a `put` will wrap back
    /// around to zero. Consider using [`ceiling_put`](Self::ceiling_put) to
    /// avoid that possibility.
    ///
    /// This can unblock another thread that's waiting on a `get`.
    #[inline]
    pub fn put(&self) {
        // Not handling TX_SEMAPHORE_ERROR. All semaphores are assumed to be created.

        // Safety: Resource created and pinned per GSG-002.
        // Failure would have no bearing on safety.
        let result = unsafe { crate::tx_sys::tx_semaphore_put(self.0.get()) };
        debug_assert_eq!(result, crate::tx_sys::TX_SUCCESS);
    }

    /// Increment the count by one, up to `ceiling`.
    ///
    /// If the incremented count exceeds `ceiling`, then the increment is ignored and
    /// the result is an error. Otherwise, this will increment the counter similar
    /// to [`put`](Self::put).
    ///
    /// This can unblock another thread that's waiting on a `get`.
    #[inline]
    pub fn ceiling_put(&self, ceiling: NonZeroU32) -> Result<(), CeilingPutError> {
        // Safety: Resource created and pinned per GSG-002.
        let result =
            unsafe { crate::tx_sys::tx_semaphore_ceiling_put(self.0.get(), ceiling.get()) };
        CeilingPutError::try_from_result(result)?;
        Ok(())
    }

    /// Try to decrement the count until the timeout expires.
    ///
    /// Blocks while the count is zero. If the timeout expires, then the result is
    /// `Ok(None)`. Otherwise, if the count becomes non-zero, then the count is decremented
    /// and the return is `Ok(Some(()))`.
    ///
    /// If you're willing to wait forever, use [`get`](Self::get). If you
    /// want to return immediately if the count is zero, use [`try_get`](Self::try_get).
    #[inline]
    pub fn get_with_wait(&self, wait_option: WaitOption) -> Result<Option<()>, GetError> {
        // Safety: Resource pinned and created per GSG-002.
        let result = unsafe { crate::tx_sys::tx_semaphore_get(self.0.get(), wait_option.into()) };

        if result == crate::tx_sys::TX_NO_INSTANCE {
            return Ok(None);
        }

        GetError::try_from_result(result)?;
        Ok(Some(()))
    }

    /// Decrement the count, waiting until it's non-zero.
    ///
    /// Blocks while the count is zero, or until there is an error.
    /// This can only be used in a thread execution context.
    #[inline]
    pub fn get(&self) -> Result<(), GetError> {
        // Safety: Since we're waiting forever, we'll never see TX_NO_INSTANCE. If we never
        // see TX_NO_INSTANCE, then we'll never take the branch that returns `None`.
        unsafe {
            self.get_with_wait(WaitOption::wait_forever())?
                .unwrap_unchecked();
        }
        Ok(())
    }

    /// Try to decrement the count.
    ///
    /// If the count is zero, this call will return immediately with `None`.
    /// Otherwise, it will decrement the count by one and return `Some(())`.
    ///
    /// Since this call does not block, it can be used in non-thread execution
    /// contexts, like ISRs.
    #[inline]
    pub fn try_get(&self) -> Option<()> {
        // Safety: see inline comments. We exhaustively match existing / future errors.
        unsafe {
            match self.get_with_wait(WaitOption::no_wait()) {
                // The "no wait" option is valid for all calling contexts.
                // Since it's always valid, we'll never see this error.
                Err(GetError::InvalidWait) => fusible_unreachable!(),
                // The "no wait" option never waits. Since it never waits,
                // it cannot be aborted.
                Err(GetError::WaitAborted) => fusible_unreachable!(),
                Ok(value) => value,
            }
        }
    }
}

impl SemaphoreContext<'_> {
    impl_common_context!(Semaphore);
}
