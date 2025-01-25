// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Thread services
//!
//! A [`Thread`] executes at a given priority. See [`ThreadOptions`] for all of
//! the configurations supported by a thread.
//!
//! Threads execute with a stack allocation that you specify. Typically, those
//! allocations must have static lifetime. Use [`StaticStack`] to easily allocate
//! stacks in global memory.
//!
//! Threads begin executing from an entrypoint. The entrypoint is represented
//! as a `FnOnce() + Send`, which allows you define thread-local state.
//! The Fusible thread implementation moves the entrypoint into the stack
//! you provide. Keep this in mind as you define stack sizes and entrypoints.
//!
//! # Examples
//!
//! A thread context allocated in global memory.
//!
//! ```no_run
//! use fusible::thread::{ThreadContext, Thread, StaticStack};
//! use core::pin::Pin;
//!
//! static THREAD: ThreadContext = Thread::context();
//! static STACK: StaticStack<2048> = StaticStack::new();
//!
//! fn entrypoint() { /* ... */}
//!
//! # (|| -> Result<(), fusible::thread::CreateError> {
//! # let stack = (|| -> Option<&'static mut [u8]> {
//! let stack = STACK.take()?;
//! # Some(stack) })().unwrap();
//! Thread::create(
//!     Pin::static_ref(&THREAD),
//!     stack,
//!     &Default::default(),
//!     entrypoint,
//! )?;
//! # Ok(()) })().unwrap();
//! ```
//!
//! A thread context allocated in local memory. Since it's created through
//! [`AppDefine`], this thread can capture references that are live before
//! entering the kernel.
//!
//! ```
//! use fusible::thread::{Thread, StaticStack};
//! use core::pin::pin;
//!
//! static STACK: StaticStack<2048> = StaticStack::new();
//!
//! fn main() {
//!     let mut data = Vec::new();
//!     let thread = pin!(Thread::context());
//!
//!     fusible::kernel_enter(|app_define| {
//!         app_define.create_thread(
//!             thread.into_ref(),
//!             STACK.take().unwrap(),
//!             &Default::default(),
//!             || {
//!                 data.push(5u32);
//!                 // ...
//! #               std::process::exit(0);
//!             },
//!         ).unwrap();
//!     });
//! }
//! ```

pub use stack::{Stack, StaticStack};

use crate::{marker::InvariantLifetime, ControlBlock, FeatureNotEnabledError};

use super::AppDefine;
use crate::tx_sys::TX_THREAD;
use core::{cell::UnsafeCell, ffi::CStr, num::NonZero, pin::Pin};

error_enum! {
    /// An error when creating a thread.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum CreateError {
        /// The thread is already created.
        AlreadyCreated = crate::tx_sys::TX_THREAD_ERROR,

        // Not handling TX_PTR_ERROR.
        //
        // TX_PTR_ERROR represents an invalid entrypoint address.
        // We ensure the entrypoint address is valid, and users always
        // supply some kind of valid closure.
        //
        // TX_PTR_ERROR says that the stack pointer is NULL. We
        // avoid this by taking a reference to the (static) stack.
        // References can never be NULL.
        //
        // TX_PTR_ERROR can suggest that the stack is assigned to
        // another thread. We handle that through &mut captures.

        /// The stack size is too small.
        ///
        /// The stack cannot accomodate the entry point and the minimum
        /// stack requirements.
        StackTooSmall = crate::tx_sys::TX_SIZE_ERROR,

        // Not handling TX_PRIORITY_ERROR. Checked through strong types.

        /// The preemption threshold is invalid.
        ///
        /// The threshold cannot be less important than the thread's priority.
        InvalidPreemptionThreshold = crate::tx_sys::TX_THRESH_ERROR,

        // Not handling TX_START_ERROR. Checked through strong types.

        /// Invalid caller.
        ///
        /// You can only create threads during initialization or from
        /// another thread.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

error_enum! {
    /// An error when suspending a thread.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum SuspendError {
        // Not handling TX_THREAD_ERROR. Thread handles are tracked
        // by lifetimes, so they're always valid.

        /// The thread has already completed or terminated.
        ///
        /// Since it's completed / terminated, it cannot be suspended.
        AlreadyExited = crate::tx_sys::TX_SUSPEND_ERROR,

        // Not handling TX_CALLER_ERROR. Although documented as a
        // possible error, an inspection of ThreadX shows that this
        // is never returned. Additionally, the documentation says
        // that all execution contexts can suspend threads.
    }
}

error_enum! {
    /// An error when resuming a thread.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum ResumeError {
        // Not handling TX_THREAD_ERROR. Thread handles are tracked
        // by lifetimes, so they're always valid.

        // Not handling TX_SUSPEND_LIFTED. Lifting a delayed suspension
        // is success.

        /// The thread isn't suspended.
        ///
        /// Since it's completed / terminated, it cannot be suspended.
        NotSuspended = crate::tx_sys::TX_RESUME_ERROR,
    }
}

error_enum! {
    /// An error when terminating a thread.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum TerminateError {
        // Not handling TX_THREAD_ERROR. Thread handles are tracked
        // by lifetimes, so they're always valid.

        /// Invalid caller.
        ///
        /// Only another thread (including the timer thread) can
        /// terminate another thread.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

error_enum! {
    /// An error when aborting a thread's wait.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum WaitAbortError {
        // Not handling TX_THREAD_ERROR. Thread handles are tracked
        // by lifetimes, so they're always valid.

        /// The thread isn't waiting on an OS object.
        NotWaiting = crate::tx_sys::TX_WAIT_ABORT_ERROR,
    }
}

error_enum! {
    /// An incomplete or invalid sleep call.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum SleepError {
        /// The sleep was aborted by another entity.
        WaitAborted = crate::tx_sys::TX_WAIT_ABORTED,

        /// Invalid caller.
        ///
        /// Only a thread can sleep.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

/// A thread priority level.
///
/// Use [`new`](Self::new) to specify a priority level between
/// 0 (the highest priority) and
/// [TX_MAX_PRIORITIES](libthreadx_sys::TX_MAX_PRIORITIES) - 1
/// (the lowest priority).
///
/// The associated methods will never panic. If you can tolerate
/// a panic, or if you're defining thread priorities as constants,
/// consider using [`make_priority`].
///
/// A thread priority also describes the preemption threshold for
/// a thread.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct ThreadPriority(u32);

impl ThreadPriority {
    /// Define a new thread priority.
    ///
    /// Returns `None` is the priority isn't valid; see [`is_valid`](Self::is_valid)
    /// for details.
    #[inline]
    pub const fn new(priority: u32) -> Option<Self> {
        // Safety: Checked for validity before forming
        // the priority.
        unsafe {
            if Self::is_valid(priority) {
                Some(Self::new_unchecked(priority))
            } else {
                None
            }
        }
    }

    /// Define a new thread priority without checking validity.
    ///
    /// # Safety
    ///
    /// If `priority` is greater than or equal to the maximum-number of priorities
    /// supported by your ThreadX build, then this can produce undefined behavior
    /// in later `thread` operations. If you're not sure if the priority is
    /// valid, prefer [`new`](Self::new) or [`make_priority`].
    #[inline]
    pub const unsafe fn new_unchecked(priority: u32) -> Self {
        Self(priority)
    }

    /// Returns `true` if `priority` is a valid thread priority.
    ///
    /// This checks the constant `TX_MAX_PRIORITIES` exposed from your
    /// build of your bindings. It's assumed that this constant matches
    /// the constant built into your ThreadX library.
    #[inline]
    pub const fn is_valid(priority: u32) -> bool {
        priority < crate::tx_sys::TX_MAX_PRIORITIES
    }

    /// Returns the least-important priority.
    #[inline]
    pub const fn lowest_priority() -> Self {
        Self(crate::tx_sys::TX_MAX_PRIORITIES - 1)
    }

    /// Returns the most-important priority.
    #[inline]
    pub const fn highest_priority() -> Self {
        Self(0)
    }

    /// Returns `true` if this priority is more important that `other`.
    #[inline]
    pub const fn is_more_important_than(self, other: Self) -> bool {
        self.0 < other.0
    }

    /// Get the raw priority value.
    #[inline]
    pub const fn get(self) -> u32 {
        self.0
    }
}

impl Default for ThreadPriority {
    #[inline]
    fn default() -> Self {
        Self::lowest_priority()
    }
}

/// Make a thread priority.
///
/// This function can execute in constant contexts. Consider using this approach
/// to define statically-known thread priorities. If the panic occurs during
/// constant evaluation, then your program doesn't compile.
///
/// ```
/// use fusible::thread::{ThreadPriority, make_priority};
///
/// const HIGH: ThreadPriority = make_priority(5);
/// const LOW: ThreadPriority = make_priority(24);
/// ```
/// ```compile_fail
/// # use fusible::thread::{ThreadPriority, make_priority};
/// const INVALID: ThreadPriority = make_priority(9999);
/// ```
///
/// # Panics
///
/// Panics if the priority is invalid. To avoid panicking, use the
/// methods on [`ThreadPriority`], or evaluate the function at compile
/// time.
///
/// ```should_panic
/// use fusible::thread::make_priority;
/// make_priority(9999);
/// ```
#[inline]
pub const fn make_priority(priority: u32) -> ThreadPriority {
    // Safety: There's an explicit validity check before forming
    // a possibly-invalid thread priority.
    unsafe {
        assert!(ThreadPriority::is_valid(priority));
        ThreadPriority::new_unchecked(priority)
    }
}

/// The thread's auto-start behavior.
///
/// By default, [`ThreadOptions`] will auto-start the thread.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[repr(u32)]
pub enum AutoStart {
    /// Do not automatically start the thread.
    ///
    /// Call [`resume`](Thread::resume) on the thread
    /// handle to start the thread.
    Disable = crate::tx_sys::TX_DONT_START,
    /// Automatically start the thread.
    ///
    /// This is the default behavior of [`ThreadOptions`]!
    #[default]
    Enable = crate::tx_sys::TX_AUTO_START,
}

impl From<bool> for AutoStart {
    #[inline]
    fn from(enable: bool) -> Self {
        if enable {
            Self::Enable
        } else {
            Self::Disable
        }
    }
}

impl From<AutoStart> for bool {
    #[inline]
    fn from(enable: AutoStart) -> Self {
        AutoStart::Enable == enable
    }
}

/// A thread's time slice configuration.
///
/// If `None`, then the thread does not time slice.
/// Otherwise, the non-zero value represents the maximum
/// number of ticks that a thread can execute before its
/// suspended.
pub type ThreadTimeSlice = Option<NonZero<u32>>;

option_enum! {
    /// A thread's execution state.
    ///
    /// There is no "running" state; a running thread is ready and utilizing
    /// the CPU.
    ///
    /// These represent the standard thread states, or those states documented
    /// in the standard ThreadX distribution's `tx_api.h` header.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum ThreadState {
        /// The thread is ready to run.
        Ready = crate::tx_sys::TX_READY,
        /// The thread exited its entrypoint.
        Completed = crate::tx_sys::TX_COMPLETED,
        /// The thread terminated before completing.
        Terminated = crate::tx_sys::TX_TERMINATED,
        /// The thread is suspended.
        ///
        /// This is a forced suspend; it's not waiting
        /// on an operating system object. When a thread
        /// is waiting on an OS object, it's suspension
        /// reason reflects the object it's waiting for.
        Suspended = crate::tx_sys::TX_SUSPENDED,
        /// The thread is sleeping.
        Sleep = crate::tx_sys::TX_SLEEP,
        /// The thread is suspended on a queue.
        Queue = crate::tx_sys::TX_QUEUE_SUSP,
        /// The thread is suspended on a semaphore.
        Semaphore = crate::tx_sys::TX_SEMAPHORE_SUSP,
        /// The thread is suspended on an event flag.
        EventFlag = crate::tx_sys::TX_EVENT_FLAG,
        /// The thread is suspended on a block pool, waiting for memory.
        BlockMemory = crate::tx_sys::TX_BLOCK_MEMORY,
        /// The thread is suspended on a byte pool, waiting for memory.
        ByteMemory = crate::tx_sys::TX_BYTE_MEMORY,
        /// The thread is suspended on an IO driver.
        IoDriver = crate::tx_sys::TX_IO_DRIVER,
        /// The thread is suspended on a file.
        File = crate::tx_sys::TX_FILE,
        /// The thread is suspended on a TCP/IP network resource.
        TcpIp = crate::tx_sys::TX_TCP_IP,
        /// The thread is suspended on a mutex.
        Mutex = crate::tx_sys::TX_MUTEX_SUSP,
        /// The thread is changing its priority.
        ///
        /// This can be due to an explicit priority change, or a
        /// priority inheritance on a mutex.
        PriorityChange = crate::tx_sys::TX_PRIORITY_CHANGE,
    }
}

/// A handle to an operating system thread.
///
/// See [`ThreadOptions`] to understand all the configurations for a thread.
/// Once created and started, the thread executes its entrypoint once. It
/// uses an exclusively-borrowed, static stack for local storage.
/// See [the module-level documentation](crate::thread) for examples that show
/// thread creation.
///
/// If you're executing on an operating system thread, use [`identify`] and
/// [`try_identify`] to access the executing thread's handle.
///
/// # FFI
///
/// `Thread` is transparently a `TX_THREAD`.
#[repr(transparent)]
pub struct Thread(ControlBlock<TX_THREAD>);

impl Thread {
    /// Suspend the thread.
    ///
    /// Another thread will need to resume the thread with [`resume`](Self::resume).
    /// If the thread is already suspended on an operating system object, then this
    /// suspend takes effect after the existing suspension is lifted.
    ///
    /// To suspend the calling thread, use [`thread::suspend`][suspend].
    #[inline]
    pub fn suspend(&self) -> Result<(), SuspendError> {
        // Safety: resource created and pinned per GSG-002.
        let result = unsafe { crate::tx_sys::tx_thread_suspend(self.0.get()) };
        SuspendError::try_from_result(result)?;
        Ok(())
    }

    /// Resume the thread.
    ///
    /// This will only resume a thread that was suspended with an explicit
    /// [`suspend`](Self::suspend) call. If the thread is suspended on a blocking
    /// service call, then this call will *not* resume the thread. Instead, use
    /// [`wait_abort`](Self::wait_abort) to resume the thread.
    #[inline]
    pub fn resume(&self) -> Result<(), ResumeError> {
        // Safety: resource created and pinned per GSG-002.
        let result = unsafe { crate::tx_sys::tx_thread_resume(self.0.get()) };
        if result != crate::tx_sys::TX_SUSPEND_LIFTED {
            ResumeError::try_from_result(result)?;
        }
        Ok(())
    }

    /// Terminate the thread, preventing further execution.
    ///
    /// If a thread terminates itself, then this call won't return. If you want to terminate
    /// the calling thread, use [`thread::terminate`][terminate].
    #[inline]
    pub fn terminate(&self) -> Result<(), TerminateError> {
        // Safety: resource created and pinned per GSG-002.
        let result = unsafe { crate::tx_sys::tx_thread_terminate(self.0.get()) };
        TerminateError::try_from_result(result)?;
        Ok(())
    }

    /// Abort the thread's wait on a service call.
    ///
    /// The associated thread will observe the service's "wait abort" error if it
    /// was blocked on a service call.
    #[inline]
    pub fn wait_abort(&self) -> Result<(), WaitAbortError> {
        // Safety: resource created and pinned per GSG-002.
        let result = unsafe { crate::tx_sys::tx_thread_wait_abort(self.0.get()) };
        WaitAbortError::try_from_result(result)?;
        Ok(())
    }

    /// Acquire standard thread information.
    pub fn info(&self) -> ThreadInfo<'_> {
        // Safety: resource created and pinned per GSG-002.
        // None of the pointers are held across the call.
        // Inline documentation provides additional information
        // about casts and FFI safety.
        //
        // The thread's name is a nul-terminated C-string. The
        // lifetime is tied to the thread's handle.
        unsafe {
            let mut info = ThreadInfo::default();
            let mut state = 0u32;
            let mut name: *mut core::ffi::c_char = core::ptr::null_mut();

            let result = crate::tx_sys::tx_thread_info_get(
                self.0.get(),
                &mut name,
                &mut state,
                &mut info.run_count,
                // ThreadPriority is transparently a u32. All values
                // are fine; ThreadX is assumed to check for valid ranges.
                core::ptr::from_mut::<ThreadPriority>(&mut info.priority).cast(),
                // See above.
                core::ptr::from_mut::<ThreadPriority>(&mut info.preemption_threshold).cast(),
                // Niche optimization guarantees correct values for the time slice.
                core::ptr::from_mut::<Option<NonZero<u32>>>(&mut info.time_slice).cast(),
                core::ptr::null_mut(),
                core::ptr::null_mut(),
            );

            // The thread is non-null. It must exist if we have a reference.
            debug_assert_eq!(result, crate::tx_sys::TX_SUCCESS);

            info.state = ThreadState::try_from_raw(state);
            info.name = crate::from_threadx_string(name);
            info
        }
    }
}

/// Configuration options for a thread.
///
/// See [`Thread::create`] for more information.
///
/// ```
/// use fusible::thread::{ThreadPriority, ThreadOptions};
///
/// let mut opts = ThreadOptions::default();
/// opts.name = Some(c"foo");
/// opts.preemption_threshold = ThreadPriority::new(28).unwrap();
/// ```
///
/// # Defaults
///
/// The following example shows the default creation options.
///
/// ```
/// use fusible::thread::{ThreadPriority, ThreadOptions};
///
/// let opts = ThreadOptions::default();
///
/// assert!(opts.name.is_none());
///
/// assert_eq!(opts.priority, ThreadPriority::lowest_priority());
/// assert_eq!(opts.preemption_threshold, ThreadPriority::lowest_priority());
///
/// assert!(opts.time_slice.is_none());
/// assert!(bool::from(opts.auto_start));
/// ```
#[derive(Default)]
#[non_exhaustive]
pub struct ThreadOptions<'a> {
    /// An optional name for this thread.
    pub name: Option<&'a CStr>,
    /// The thread's baseline priority.
    ///
    /// By default, this is the lowest possible thread priority.
    pub priority: ThreadPriority,
    /// The preemption threshold for the thread.
    ///
    /// This cannot be less important than [`priority`](Self::priority).
    /// If it is, you'll observe [`CreateError::InvalidPreemptionThreshold`]
    /// when you create the thread.
    ///
    /// By default, this is the lowest possible thread priority.
    pub preemption_threshold: ThreadPriority,
    /// Set the time slicing for the thread.
    ///
    /// Note: if the preemption threshold is more important than
    /// the thread priority, then time slicing is implicitly disabled.
    ///
    /// By default, there is no time slice.
    pub time_slice: ThreadTimeSlice,
    /// The auto-start behavior of the thread.
    ///
    /// By default a created thread will automatically start.
    pub auto_start: AutoStart,
}

impl ThreadOptions<'_> {
    /// Create a thread that runs at a single priority.
    ///
    /// There is no preemption threshold, and there's no
    /// time slicing.
    ///
    /// ```
    /// use fusible::thread::{ThreadPriority, ThreadOptions};
    ///
    /// let opts = ThreadOptions::single_priority(ThreadPriority::new(5).unwrap());
    /// assert_eq!(opts.priority, opts.preemption_threshold);
    /// assert!(opts.time_slice.is_none());
    /// ```
    #[inline]
    pub fn single_priority(priority: ThreadPriority) -> Self {
        Self {
            priority,
            preemption_threshold: priority,
            ..Default::default()
        }
    }
}

/// Implements the thread entrypoint. This is the first thing that executes.
/// when ThreadX starts running a thread.
extern "C" fn entry_trampoline<F: FnOnce() + Send>(entry_start: *mut ()) {
    // Safety: entry_start is clearly an F by studying the usage of entry_trampoline.
    // We moved the entrypoint into the thread's stack without dropping the callable.
    // This read will drop the callable once the callable returns.
    //
    // We do not allow thread resets, so this drop (on successful exit from the thread)
    // will conclude the thread's utility. ThreadX will not implicitly invoke the
    // entry_trampoline multiple times.
    crate::panic::catch_unwind_thread(|| unsafe { core::ptr::read(entry_start.cast::<F>())() });
}

/// Manages a thread and any borrowed data.
///
/// Use [`Thread`] to interact with the context. The context exposes
/// methods to access an already-created thread.
///
/// # FFI
///
/// The context is transparently a [`Thread`].
#[repr(transparent)]
pub struct ThreadContext<'ctx>(Thread, InvariantLifetime<'ctx>);

impl ThreadContext<'_> {
    impl_common_context!(Thread);
}

impl Thread {
    /// Allocate a thread.
    ///
    /// The thread is inert; you'll need to pint it then use [`create`](Self::create)
    /// to define the thread behavior.
    pub const fn context<'ctx>() -> ThreadContext<'ctx> {
        ThreadContext(Thread(ControlBlock::new()), InvariantLifetime::mark())
    }

    /// Create a thread.
    ///
    /// `entrypoint` describes the first function executed by the thread as
    /// well as any initial thread state. See module-level documentation for
    /// more information about the entrypoint and stack utilization.
    #[inline]
    pub fn create<'t, 'ctx, F>(
        context: Pin<&'t ThreadContext<'ctx>>,
        stack: &'static mut [u8],
        options: &'_ ThreadOptions<'ctx>,
        entrypoint: F,
    ) -> Result<&'t Thread, CreateError>
    where
        F: FnOnce() + Send + 'static,
    {
        // Safety: We exclusively borrow the stack. The stack has static lifetime, so it
        // may outlive the thread context (if the thread context is pinned and forgotten).
        unsafe {
            let stack_size = stack.len();
            let stack_start = stack.as_mut_ptr();
            Self::create_unchecked_stack(context, stack_start, stack_size, options, entrypoint)
        }
    }

    /// # Safety
    ///
    /// You must make sure that the stack is exclusively borrowed by the thread. Furthermore,
    /// you must make sure that the stack allocation is valid while the thread is executing.
    #[inline]
    unsafe fn create_unchecked_stack<'t, 'ctx, F>(
        context: Pin<&'t ThreadContext<'ctx>>,
        stack_start: *mut u8,
        stack_size: usize,
        options: &'_ ThreadOptions<'ctx>,
        entrypoint: F,
    ) -> Result<&'t Thread, CreateError>
    where
        F: FnOnce() + Send + 'static,
    {
        // Safety: The entrypoint has static lifetime, as seen in the
        // method signature. Caller swears that the stack allocation
        // is valid for the lifetime of the thread and exclusively
        // borrowed by the thread.
        unsafe { Self::create_unchecked(context, stack_start, stack_size, options, entrypoint) }
    }

    /// # Safety
    ///
    /// The entrypoint may capture lifetimes that are smaller than the lifetime of the thread.
    /// You must make sure that any lifetimes captured by the entrypoint are valid while the
    /// thread is executing.
    ///
    /// You must make sure that the stack is exclusively borrowed by the thread, and that the
    /// stack allocation remains valid while the thread is executing.
    unsafe fn create_unchecked<'your_choice, 't, 'ctx, F>(
        context: Pin<&'t ThreadContext<'ctx>>,
        buffer_start: *mut u8,
        buffer_size: usize,
        options: &'_ ThreadOptions<'ctx>,
        entrypoint: F,
    ) -> Result<&'t Thread, CreateError>
    where
        F: FnOnce() + Send + 'your_choice,
    {
        // Safety: entry_start is a valid pointer to a location in the stack
        // describing the location of the entrypoint. This forms the input for
        // the callback dispatch.
        //
        // The stack is assumed to live for the thread's execution lifetime
        // (which may exceed the thread's context object, if the context is
        // forgotten). Since the stack now holds the entrypoint, the entrypoint
        // has the same lifetime of the stack. The caller swears that any reference
        // captured by the entrypoint is valid while the thread executes.
        //
        // We know that the entrypoint is valid for one call, and ThreadX
        // only invokes the entrypoint once. By API construction, we prevent thread
        // resets that would enable multiple invocations of the entrypoint.
        //
        // The entrypoint will be invoked on another thread. We observe that the
        // entrypoint is Send.
        unsafe {
            let stack::StackLayout {
                stack_start,
                stack_len,
                entry_start,
            } = stack::figure_stack_layout(buffer_start, buffer_size, entrypoint)?;

            let dispatch = crate::callback_dispatch::make(entry_trampoline::<F>, entry_start);

            let result = crate::tx_sys::tx_thread_create(
                context.0 .0.get(),
                crate::threadx_string(options.name),
                Some(dispatch.callback()),
                dispatch.input(),
                stack_start.cast::<core::ffi::c_void>(),
                stack_len
                    .try_into()
                    .map_err(|_| CreateError::StackTooSmall)?,
                options.priority.get(),
                options.preemption_threshold.get(),
                options
                    .time_slice
                    .map_or(crate::tx_sys::TX_NO_TIME_SLICE, NonZero::get),
                options.auto_start as _,
            );

            CreateError::try_from_result(result)?;

            Ok(&context.get_ref().0)
        }
    }
}

impl<'pke> AppDefine<'_, 'pke> {
    /// Create a thread that can borrow local state.
    ///
    /// Unlike [`create`](Thread::create), this method lets you define a thread
    /// entrypoint that captures local state. That state must be allocated before
    /// the call to [`kernel_enter`](crate::kernel_enter).
    #[inline]
    pub fn create_thread<'t, 'ctx, F>(
        &self,
        context: Pin<&'t ThreadContext<'ctx>>,
        stack: &'static mut [u8],
        options: &'_ ThreadOptions<'ctx>,
        entrypoint: F,
    ) -> Result<&'t Thread, CreateError>
    where
        F: FnOnce() + Send + 'pke,
        't: 'pke,
        'ctx: 'pke,
        'ctx: 't,
    {
        // Safety: stack is exclusively borrowed by the caller.
        // Since it's a static reference, we know that it's valid
        // for the lifetime of the thread.
        unsafe {
            let stack_size = stack.len();
            let stack_start = stack.as_mut_ptr();
            Thread::create_unchecked(context, stack_start, stack_size, options, entrypoint)
        }
    }
}

impl Drop for ThreadContext<'_> {
    fn drop(&mut self) {
        // Safety: resource is pinned and created per GSG-002, or never created
        // per GSG-003. Checking lifecycle per GSG-003.
        //
        // We require termination before deletion. It's also required for memory
        // safety, since we need to prevent a program from executing an invalid
        // program. See GSG-002 for details.
        unsafe {
            aborting_assert!(
                self.0.terminate().is_ok(),
                "Attempt to drop resource in the initialization context"
            );

            let result = crate::tx_sys::tx_thread_delete(self.0 .0.get());
            aborting_assert!(
                result == crate::tx_sys::TX_SUCCESS || result == crate::tx_sys::TX_THREAD_ERROR,
                "Attempt to drop resource in the initialization context"
            );
        };
    }
}

/// The result of sleeping.
///
/// Sleeping can be aborted due to another thread, ISR, or a timer.
/// This lets you know if your sleep was stopped short.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SleepResult {
    /// You completed your sleep.
    Completed,
    /// Your sleep was aborted early.
    ///
    /// Another thread aborted the wait with a
    /// [`wait_abort`](Thread::wait_abort) call.
    /// We don't know how long you might have slept.
    Aborted,
}

impl SleepResult {
    /// `true` if the sleep completed.
    pub const fn is_completed(self) -> bool {
        matches!(self, SleepResult::Completed)
    }
    /// `true` if the sleep was aborted.
    pub const fn is_aborted(self) -> bool {
        matches!(self, SleepResult::Aborted)
    }
}

/// Sleep the currently-executing thread for `ticks` of the timer.
///
/// The resolution of `ticks` depends on your system's configuration.
#[inline]
pub fn sleep(ticks: u32) -> Result<(), SleepError> {
    // Safety: This is a valid FFI call with no concern for memory safety.
    // Assume that the bindings library is correct.
    let result = unsafe { crate::tx_sys::tx_thread_sleep(ticks) };
    SleepError::try_from_result(result)?;
    Ok(())
}

/// Relinquish control to other application threads.
///
/// This can only be called from a thread. Effectively, you're yielding
/// to the OS for another scheduling decision.
///
/// `relinquish` is ignored if called from a non-thread execution context.
#[inline]
pub fn relinquish() {
    // Safety: This is a valid FFI call with no concern for memory safety.
    // Assume that the bindings library is correct.
    unsafe { crate::tx_sys::tx_thread_relinquish() }
}

/// Identifies the calling thread.
///
/// If this is called from an ISR, the handle provided to the callback
/// represents the thread that was running prior to the ISR.
///
/// # Panics
///
/// Panics if called before the OS is initialized. To avoid this runtime
/// panic, use [`try_identify`].
pub fn identify<F: FnOnce(&Thread) -> T, T>(f: F) -> T {
    if let Some(value) = try_identify(f) {
        value
    } else {
        panic!()
    }
}

/// Identify the calling thread.
///
/// Unlike [`identify`], this call will not panic if called before
/// the OS is initialized. Instead, it returns `None` to signal that
/// `f` was not invoked.
///
/// If this is called from an ISR, the handle provided to the callback
/// represents the thread that was running prior to the ISR.
pub fn try_identify<F: FnOnce(&Thread) -> T, T>(f: F) -> Option<T> {
    // Safety: The pointer is always valid for the calling thread.
    // If the thread can execute this function, then its thread
    // context (and its thread handle) must be valid.
    //
    // Suppose `f` suspends this calling thread. If another thread
    // were to destroy this calling thread's control block, then this
    // calling thread will never observe that now-invalidated reference.
    // It's been terminated.
    //
    // We guard dereference of a null pointer. It's assumed that the
    // OS will not fabricate an invalid thread control block, so the
    // pointer must be a valid (shared) reference.
    unsafe {
        let thread: *mut TX_THREAD = crate::tx_sys::tx_thread_identify();
        // A Thread is transparently a ControlBlock<TX_THREAD>.
        // A ControlBlock<T> is transparently a T.
        let thread: *mut Thread = thread.cast();
        (!thread.is_null()).then(|| f(&*thread))
    }
}

/// Suspend the calling thread.
///
/// Another thread will need to resume this thread. See [Thread::resume]
/// for details.
///
/// If this is called from an ISR, the call will suspend the thread
/// that was executing prior to the ISR. See [`identify`] for more
/// information.
///
/// # Panics
///
/// Panics if called before the OS is initialized.
#[inline]
pub fn suspend() {
    // Safety: see inline comments. Exhaustively match existing / future errors.
    unsafe {
        // Clippy suggests an 'if let Err' to catch the error. This suggestion
        // would not force us to check errors introduced in the future.
        #[allow(clippy::single_match)]
        match identify(Thread::suspend) {
            // A thread trying to suspend itself cannot have already exited.
            // If it already exited, then it couldn't suspend itself.
            Err(SuspendError::AlreadyExited) => fusible_unreachable!(),
            Ok(()) => (),
        }
    }
}

/// Terminate the calling thread.
///
/// # Panics
///
/// Panics if called from the initialization context or an
/// ISR. Only a thread can terminate itself.
#[inline]
pub fn terminate() -> ! {
    // Safety: The success path never returns, since
    // it's a self-termination. The error path never
    // returns, since a panic never returns.
    unsafe {
        match identify(Thread::terminate) {
            Ok(()) => fusible_unreachable!(),
            Err(TerminateError::Caller) => panic!(),
        }
    }
}

/// Invoked when a thread exceeds its stack allocation.
///
/// See [`register_stack_error_callback`] for more information.
pub type StackErrorCallback = fn(&Thread);

/// Be notified when a thread exceeds its stack allocation.
///
/// If enabled in your operating system, ThreadX will monitor a
/// thread's stack utilization. If the thread exceeds its stack allocation,
/// then it invokes `callback`. Note that it's unspecified which thread
/// executes the callback; in fact, it may be the same thread that has
/// exceeded its stack bounds!
///
/// If your operating system doesn't support this feature, then the result
/// is an error.
pub fn register_stack_error_callback(
    _: &AppDefine<'_, '_>,
    callback: StackErrorCallback,
) -> Result<(), FeatureNotEnabledError> {
    struct StackErrorNotify(UnsafeCell<StackErrorCallback>);
    // Safety: We only access the static while we're in the initialization context.
    // We know we're in the initialization context from the signature of this
    // function. When we're in the initialization context, no threads are executing
    // (which might invoke the callback), and interrupts are disabled. Therefore,
    // there is no race on this memory.
    unsafe impl Sync for StackErrorNotify {}
    static STACK_ERROR_NOTIFY: StackErrorNotify = StackErrorNotify(UnsafeCell::new(|_| {}));

    extern "C" fn on_stack_error_trampoline(thread: *mut TX_THREAD) {
        // repr(C).
        // Safety: TODO(mciantyre)
        unsafe { (*STACK_ERROR_NOTIFY.0.get())(&*thread.cast()) }
    }

    // Safety: Store on the static is observed by the operating system once threads
    // are executing. There is no concern for a race on this static, or in any global
    // memory accessed by the service call.
    //
    // The signature of the callback is assumed valid, thanks to the bindings library.
    let result = unsafe {
        *STACK_ERROR_NOTIFY.0.get() = callback;
        crate::tx_sys::tx_thread_stack_error_notify(Some(on_stack_error_trampoline))
    };

    match result {
        crate::tx_sys::TX_SUCCESS => Ok(()),
        crate::tx_sys::TX_FEATURE_NOT_ENABLED => Err(FeatureNotEnabledError(())),
        _ => unreachable!(),
    }
}

/// Standard thread information.
#[derive(Default)]
pub struct ThreadInfo<'a> {
    /// The thread's name set during creation.
    pub name: crate::ResourceName<'a>,
    /// The thread's state.
    ///
    /// A `None` indicates that the thread state
    /// is unknown.
    pub state: Option<ThreadState>,
    /// How many times the thread has run.
    ///
    /// This is how many times the schedule has assigned this
    /// thread the implicit "running" state. It's not counting
    /// the number of entrances into the entrypoint.
    pub run_count: u32,
    /// The thread's priority.
    pub priority: ThreadPriority,
    /// The thread's preemption threshold.
    pub preemption_threshold: ThreadPriority,
    /// The thread's time slice.
    pub time_slice: ThreadTimeSlice,
}

/// Details for the thread stack.
mod stack {
    /// A thread's stack allocation.
    ///
    /// You should use this to allocate your thread's stack. It's exactly the same
    /// size as a `[u8; N]`, but it's aligned for thread's requirements.
    #[repr(align(4))]
    pub struct Stack<const N: usize>([u8; N]);

    impl<const N: usize> Default for Stack<N> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<const N: usize> Stack<N> {
        /// Allocate a stack.
        pub const fn new() -> Self {
            Self([0; N])
        }

        #[cfg(test)]
        fn start(&mut self) -> *mut u8 {
            self.0.as_mut_ptr()
        }

        /// Access this stack as an exclusively-borrowed slice.
        #[inline]
        pub fn as_mut_slice(&mut self) -> &mut [u8] {
            self.0.as_mut_slice()
        }
    }

    /// A stack that can be statically allocated.
    ///
    /// If you would like your stack to be allocated globally, in a `static`,
    /// use `StaticStack` to reserve the allocation. The object uses a simple
    /// runtime check to ensure you can safely access a `&'static mut [u8]`;
    /// use [`take`](Self::take) to acquire the slice.
    pub struct StaticStack<const N: usize>(crate::StaticCell<Stack<N>>);

    impl<const N: usize> Default for StaticStack<N> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<const N: usize> StaticStack<N> {
        const MEETS_MIN_STACK_SIZE: () = assert!(crate::tx_sys::TX_MINIMUM_STACK as usize <= N);

        /// Allocate a stack of `N` bytes.
        pub const fn new() -> Self {
            #[allow(clippy::let_unit_value)] // Force evaluation to catch compile-time errors.
            {
                let _ = Self::MEETS_MIN_STACK_SIZE;
            }
            Self(crate::StaticCell::new(Stack::new()))
        }

        /// Take the slice if it hasn't already been taken.
        ///
        /// Although the return is a byte slice, the start of the slice is aligned
        /// for the thread.
        pub fn take(&'static self) -> Option<&'static mut [u8]> {
            self.0.take().map(|stack| stack.0.as_mut_slice())
        }
    }

    /// Compute the stack layout, figuring where the entrypoint
    /// will be moved.
    pub(crate) fn figure_stack_layout<F: FnOnce() + Send>(
        buffer_start: *mut u8,
        buffer_size: usize,
        entrypoint: F,
    ) -> Result<StackLayout, super::CreateError> {
        if size_of::<F>() >= buffer_size.saturating_sub(crate::tx_sys::TX_MINIMUM_STACK as usize) {
            return Err(super::CreateError::StackTooSmall);
        }

        // What's the offset we need to apply to the start of the stack
        // in order to utilize an aligned entrypoint?
        let entry_align = align_of::<F>();
        let offset = buffer_start.align_offset(entry_align);

        // Safety: the offset is in bounds of the stack allocation.
        // Cast to unitialized F from an aligned byte pointer.
        let entry_start_ptr: *mut F = unsafe {
            if offset >= buffer_size {
                return Err(super::CreateError::StackTooSmall);
            }
            buffer_start.add(offset).cast()
        };

        // Safety: pointer is valid for writes. We initialize the memory
        // without dropping another object.
        unsafe { entry_start_ptr.write(entrypoint) };

        // Safety: increment of one entry pointer remains in bounds; we showed
        // at the top of the function that there's enouch space.
        let beyond_entry: *mut u8 = unsafe {
            // Increment the pointer by one sizeof(F). We're still aligned...
            let beyond_entry: *mut F = entry_start_ptr.add(1);
            // This is the start of the stack beyond the entrypoint.
            beyond_entry.cast()
        };

        // How much stack space did we use for the entrypoint?
        //
        // Safety: We're in range, since buffer entry and buffer start are
        // both in the bounds of the original stack allocation.
        let stack_loss: usize = unsafe {
            beyond_entry
                .offset_from(buffer_start)
                .try_into()
                .map_err(|_| super::CreateError::StackTooSmall)?
        };

        Ok(StackLayout {
            entry_start: entry_start_ptr.cast(),
            stack_start: beyond_entry,
            stack_len: buffer_size.checked_sub(stack_loss).unwrap(),
        })
    }

    /// The stack layout just before we create a thread.
    pub(crate) struct StackLayout {
        /// Where the entrypoint was placed.
        pub(crate) entry_start: *mut (),
        /// The start of the usable stack for the thread's locals.
        ///
        /// This is somewhere after the entry_start. It may not be
        /// aligned; ThreadX handles that.
        pub(crate) stack_start: *mut u8,
        /// The size of the usable stack for the thread's locals.
        pub(crate) stack_len: usize,
    }

    #[cfg(test)]
    mod tests {
        #![allow(clippy::undocumented_unsafe_blocks)]
        use super::{Stack, StackLayout};

        #[test]
        fn stuff_entrypoint_pure() {
            let fn_ptr: fn() = std::hint::black_box({
                fn pure() {}
                pure
            });

            const STACK_SIZE: usize = 256;
            let fn_size = size_of_val(&fn_ptr);
            let mut stack: Stack<STACK_SIZE> = Stack::new();
            assert_eq!(align_of_val(&fn_ptr), 2 * align_of_val(&stack));

            let layout = super::figure_stack_layout(stack.start(), STACK_SIZE, fn_ptr).unwrap();
            let loss_due_to_alignment = stack.start().align_offset(align_of_val(&fn_ptr));
            assert_eq!(
                layout.stack_len,
                STACK_SIZE - fn_size - loss_due_to_alignment
            );
            assert_eq!(layout.stack_start, unsafe {
                stack.start().add(fn_size).add(loss_due_to_alignment)
            });
        }

        #[test]
        fn stuff_entrypoint_stateful() {
            let memory = [0xDEADBEEFu32; 32];
            let entrypoint = move || {
                std::hint::black_box(memory);
            };

            const STACK_SIZE: usize = 512;
            let entrypoint_size = size_of_val(&entrypoint);
            assert_eq!(entrypoint_size, size_of_val(&memory));
            assert_eq!(align_of_val(&entrypoint), 4);

            let mut stack: Stack<STACK_SIZE> = Stack::new();
            let layout = super::figure_stack_layout(stack.start(), STACK_SIZE, entrypoint).unwrap();

            assert_eq!(layout.stack_len, STACK_SIZE - entrypoint_size);
            assert_eq!(layout.entry_start, stack.start().cast());
            assert_eq!(layout.stack_start, unsafe {
                stack.start().add(size_of_val(&memory))
            });
        }

        #[test]
        fn stuff_entrypoint_too_big() {
            let memory = [0u8; 128];
            let entrypoint = move || {
                std::hint::black_box(memory);
            };

            const STACK_SIZE: usize = 256;
            let mut stack: Stack<STACK_SIZE> = Stack::new();
            assert!(super::figure_stack_layout(stack.start(), STACK_SIZE, entrypoint).is_err());
        }

        #[test]
        fn stuff_entrypoint_considering_alignment() {
            const N: usize = 23;

            #[repr(C, align(32))]
            struct NeedsAlign32([u8; N]);
            impl NeedsAlign32 {
                const fn new() -> Self {
                    Self([0; N])
                }
            }

            const STACK_SIZE: usize = 256;
            #[repr(C)]
            struct ForceBufferOffAlign32 {
                bytes: u8,
                stack: Stack<STACK_SIZE>,
                needs_align_32: NeedsAlign32,
            }

            let mut forcer: ForceBufferOffAlign32 = ForceBufferOffAlign32 {
                bytes: 0,
                stack: Stack::new(),
                needs_align_32: NeedsAlign32::new(),
            };

            // The compiler minimizes the padding inserted after the byte
            // to align the stack. As a result, the stack never takes a
            // 32-byte aligned address.
            assert!(core::ptr::addr_of!(forcer.bytes) as usize % 32 == 0);
            assert!(core::ptr::addr_of!(forcer.stack) as usize % 32 != 0);
            assert!(core::ptr::addr_of!(forcer.needs_align_32) as usize % 32 == 0);

            {
                let hard_align = NeedsAlign32::new();
                // Drop isn't called in this test, since we never invoke the entrypoint
                // after stuffing it into the stack. Should be OK; there's no drop impl.
                // Miri doesn't seem to care.
                let entrypoint = move || {
                    std::hint::black_box(hard_align);
                };
                assert_eq!(size_of_val(&entrypoint), 32, "Round up for alignment");

                let StackLayout {
                    stack_start: ptr,
                    stack_len: size,
                    ..
                } = super::figure_stack_layout(forcer.stack.start(), STACK_SIZE, entrypoint)
                    .unwrap();

                let delta: usize = (ptr as usize) - core::ptr::addr_of!(forcer.stack) as usize;
                assert!(delta > N);
                assert!(ptr as usize % 32 == 0);
                assert_eq!(size, STACK_SIZE - delta);
            }

            {
                let easy_align = [0u8; N];
                // See note above: drop isn't called.
                let entrypoint = move || {
                    std::hint::black_box(easy_align);
                };
                assert_eq!(size_of_val(&entrypoint), N);

                let StackLayout {
                    stack_start: ptr,
                    stack_len: size,
                    ..
                } = super::figure_stack_layout(forcer.stack.start(), STACK_SIZE, entrypoint)
                    .unwrap();

                let delta: usize =
                    unsafe { ptr.offset_from(core::ptr::addr_of!(forcer.stack) as _) }
                        .try_into()
                        .unwrap();
                assert_eq!(delta, N);
                assert_eq!(size, STACK_SIZE - N);
            }
        }
    }
}
