// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Application timer services.
//!
//! A [`Timer`] manages a runnable, generalized by [`TimerRunnable`]. Given a
//! [`TimerSchedule`], `Timer` will execute your runnable on a hidden, high priority
//! system thread. You can control the timer from threads, ISRs, other timers, or
//! within the timer itself.
//!
//! All timers use the operating system's periodic timer interrupt, the same timer
//! that [`thread::sleep`](crate::thread::sleep) uses. Timers use raw ticks as their
//! unit of duration.
//!
//! You can allocate timers in global or local memory. See [`TimerRunnable`] for tips
//! on allocating stateful, static timers. The following examples show how stateless
//! functions and stateful closures can be used as your timer's runnable.
//!
//! # Examples
//!
//! A timer allocated in global memory. This timer increments a global atomic. By
//! default the timer will not activate, so we manually [`activate`](Timer::activate)
//! it.
//!
//! ```no_run
//! use fusible::timer::{Timer, TimerContext, TimerSchedule};
//! use core::pin::Pin;
//! use core::sync::atomic::{AtomicU32, Ordering};
//! use core::num::NonZero;
//!
//! static COUNT: AtomicU32 = AtomicU32::new(0);
//! fn increment() { COUNT.fetch_add(1, Ordering::Relaxed); }
//!
//! static COUNTER: TimerContext<fn()> = Timer::context();
//!
//! # (|| -> Result<(), fusible::timer::CreateError> {
//! const TICKS: NonZero<u32> = // ...
//! # unsafe { NonZero::new_unchecked(5) };
//!
//! let timer = Timer::create(
//!     Pin::static_ref(&COUNTER),
//!     TimerSchedule::periodic(TICKS),
//!     &Default::default(),
//!     increment
//! )?;
//!
//! # (|| -> Result<(), fusible::timer::ActivateError> {
//! timer.activate()?;
//! # Ok(()) })().unwrap();
//! # Ok(()) })().unwrap();
//! ```
//!
//! A timer allocated in local memory. This timer will auto-activate, since we
//! override its default create options.
//!
//! By default, the timer's runnable must have static lifetime and capture static
//! state. However, when we enter the kernel, we can capture state before we entered
//! the kernel.
//!
//! ```no_run
//! use fusible::timer::{Timer, TimerSchedule, TimerOptions};
//! use core::pin::{pin, Pin};
//! use core::num::NonZero;
//!
//! const TICKS: NonZero<u32> = // ...
//! # unsafe { NonZero::new_unchecked(5) };
//!
//! let mut counter = 0;
//! let timer = pin!(Timer::context());
//! let mut runnable = || {
//!     counter += 1;
//!     # fn send(_: i32) {}
//!     send(counter);
//! };
//! fusible::kernel_enter(|app_define| {
//!     app_define.create_timer(
//!         timer.into_ref(),
//!         TimerSchedule::periodic(TICKS),
//!         &{
//!             let mut opts = TimerOptions::default();
//!             opts.activate = true.into();
//!             opts
//!         },
//!         &mut runnable,
//!     ).unwrap();
//! });
//! ```

use core::{cell::UnsafeCell, ffi::CStr, mem::MaybeUninit, num::NonZero, pin::Pin};

use libthreadx_sys::{TX_TIMER, ULONG};

use crate::{
    callback_dispatch::{self, CallbackDispatch},
    interrupt_control,
    marker::InvariantLifetime,
    AppDefine, ControlBlock,
};

error_enum! {
    /// An error when creating a timer.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum CreateError {
        /// The timer is already created.
        AlreadyCreated = crate::tx_sys::TX_TIMER_ERROR,

        // Not handling TX_TICK_ERROR. NonZero types guarantee no invalid values.

        // Not handling TX_ACTIVATE_ERROR. Enum guarantees valid activate values.

        /// The caller is invalid.
        ///
        /// You can only create timers in the initialization
        /// and thread execution contexts.
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

error_enum! {
    /// An error when activating a timer.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum ActivateError {
        // Not handling TX_TIMER_ERROR. We assume all timers are created.

        /// The timer is already active, or it's an expired one-shot timer.
        ///
        /// If this one-shot timer has expired, you'll need to [`change`](Timer::change)
        /// the timer before you can activate it. If this timer is an active periodic
        /// timer, then there's nothing to do.
        AlreadyActiveOrExpired = crate::tx_sys::TX_ACTIVATE_ERROR,
    }
}

error_enum! {
    /// An error when changing a timer schedule.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[cfg_attr(feature = "defmt", derive(defmt::Format))]
    pub enum ChangeError {
        // Not handling TX_TIMER_ERROR. We assume all timers are created.

        // Not handling TX_TICK_ERROR. NonZero types guarantee no invalid values.

        /// Invalid calling context.
        ///
        /// You cannot change a timer's schedule in the initialization context!
        /// Make sure you set the schedule when creating the timer; see [`create`](Timer::create).
        Caller = crate::tx_sys::TX_CALLER_ERROR,
    }
}

/// Describes how the timer runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimerSchedule {
    /// After activation, the timer will invoke its callback once, then expire.
    ///
    /// The timer is stalled after it expires. Use [`change`](Timer::change) to
    /// select an new schedule, then call [`activate`](Timer::activate) to run
    /// the timer again.
    ///
    /// Use [`one_shot`](Self::one_shot) to conveniently define this schedule.
    OneShot {
        /// The delay, in ticks, between activation and expiration.
        ticks: NonZero<u32>,
    },
    /// After activation the timer will repeatedly invoke its callback.
    ///
    /// Use [`deactivate`](Timer::deactivate) to stop this timer. Use
    /// [`periodic`](Self::periodic) to conveniently set these two ticks
    /// to the same value.
    Periodic {
        /// The delay, in ticks, between activation and the first expiration.
        initial_ticks: NonZero<u32>,
        /// The delay, in ticks, between all expirations after the first.
        reschedule_ticks: NonZero<u32>,
    },
}

/// The auto-activate timer option.
///
/// The default option is [`Disable`](AutoActivate::Disable).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[repr(u32)]
pub enum AutoActivate {
    /// The timer will not automatically activate.
    ///
    /// Call [`activate`](Timer::activate) in order start the timer.
    #[default]
    Disable = crate::tx_sys::TX_NO_ACTIVATE,
    /// The timer will automatically start running.
    ///
    /// If [`create`](Timer::create) returns success, then the timer
    /// will automatically start running.
    Enable = crate::tx_sys::TX_AUTO_ACTIVATE,
}

struct RawSchedule {
    initial_ticks: u32,
    reschedule_ticks: u32,
}

impl TimerSchedule {
    /// Create a [`OneShot`](TimerSchedule::OneShot) schedule.
    #[inline]
    pub const fn one_shot(ticks: NonZero<u32>) -> Self {
        Self::OneShot { ticks }
    }
    /// Create a [`Periodic`](TimerSchedule::Periodic) schedule with
    /// consistent ticks.
    #[inline]
    pub const fn periodic(ticks: NonZero<u32>) -> Self {
        Self::Periodic {
            initial_ticks: ticks,
            reschedule_ticks: ticks,
        }
    }

    const fn raw(self) -> RawSchedule {
        let (initial_ticks, reschedule_ticks) = match self {
            TimerSchedule::OneShot { ticks } => (ticks.get(), 0),
            TimerSchedule::Periodic {
                initial_ticks,
                reschedule_ticks,
            } => (initial_ticks.get(), reschedule_ticks.get()),
        };
        RawSchedule {
            initial_ticks,
            reschedule_ticks,
        }
    }
}

impl From<bool> for AutoActivate {
    #[inline]
    fn from(auto: bool) -> Self {
        if auto {
            Self::Enable
        } else {
            Self::Disable
        }
    }
}

impl From<AutoActivate> for bool {
    #[inline]
    fn from(auto: AutoActivate) -> Self {
        auto == AutoActivate::Enable
    }
}

/// Options for a timer.
#[derive(Default)]
#[non_exhaustive]
pub struct TimerOptions<'ctx> {
    /// The timer's (optional) name.
    pub name: Option<&'ctx CStr>,
    /// The timer's auto-activation behavior.
    pub activate: AutoActivate,
}

/// A timer executes a runnable on a high priority thread.
///
/// `Timer` lets you set the runnable during creation, specify
/// the timer schedule, and control the timer's activation.
///
/// # FFI
///
/// `Timer` is transparently a `TX_TIMER`.
#[repr(transparent)]
pub struct Timer(ControlBlock<TX_TIMER>);

impl Timer {
    /// Allocate a new timer.
    ///
    /// This doesn't create or activate the timer! You'll need to pin this
    /// object then use [`create`](Self::create) to use the timer.
    #[inline]
    pub const fn context<'ctx, R>() -> TimerContext<'ctx, R> {
        TimerContext(
            Timer(ControlBlock::new()),
            InvariantLifetime::mark(),
            RunnableFn::new(),
        )
    }

    /// Create the timer.
    ///
    /// Use [`TimerOptions`] to specify the auto-activation behavior of the timer. See
    /// [`AutoActivate`] for more information.
    ///
    /// On success, you're given a handle to the timer for further timer control. The
    /// runnable will be invoked after the initial ticks expires.
    #[inline]
    pub fn create<'ctx, 't, R>(
        ctx: Pin<&'t TimerContext<'ctx, R>>,
        schedule: TimerSchedule,
        opts: &'_ TimerOptions<'ctx>,
        runnable: R,
    ) -> Result<&'t Self, CreateError>
    where
        R: TimerRunnable + 'static,
    {
        // Safety: Runnable has static lifetime, which is always valid.
        unsafe { Self::create_unchecked(ctx, schedule, opts, runnable) }
    }

    /// # Safety
    ///
    /// The runnable may capture a lifetime that may not be valid while the timer
    /// is executing. You must make sure anything captured by the runnable remains
    /// valid while the timer can execute.
    unsafe fn create_unchecked<'your_choice, 'ctx, 't, R>(
        ctx: Pin<&'t TimerContext<'ctx, R>>,
        schedule: TimerSchedule,
        opts: &'_ TimerOptions<'ctx>,
        runnable: R,
    ) -> Result<&'t Timer, CreateError>
    where
        R: TimerRunnable + 'your_choice,
        'ctx: 't,
    {
        // Safety: We realize a critical section with disabled interrupts.
        // tx_timer_create does not preempt the caller, so we won't switch
        // to another caller while we're in this critical section. Nothing
        // else in this critical section will voluntarily yield to the
        // scheduler.
        //
        // The dispatch provides a pointer to the MaybeUninit runnable.
        // If the timer hasn't been created, we haven't initialized that memory
        // until after we check the result code. The critical section prevents
        // the timer from firing until we've initialized the runnable.
        //
        // If the timer is already created, then the timer holds a reference
        // to the runnable. In this case, we do not set the runnable; we bail
        // out with an error, dropping the user's runnable.
        //
        // The context is pinned in memory, so the runnable slot is also pinned
        // in memory. The callback dispatch points to a stable location in
        // memory.
        unsafe {
            let ctx = ctx.get_ref();

            let RawSchedule {
                initial_ticks,
                reschedule_ticks,
            } = schedule.raw();

            let dispatch = ctx.callback_dispatch();

            interrupt_control::with_disabled(|| {
                let result = crate::tx_sys::tx_timer_create(
                    ctx.0 .0.get(),
                    crate::threadx_string(opts.name),
                    Some(dispatch.callback()),
                    dispatch.input(),
                    initial_ticks,
                    reschedule_ticks,
                    opts.activate as _,
                );

                CreateError::try_from_result(result)?;
                ctx.set_runnable(runnable);

                Ok(&ctx.0)
            })
        }
    }
}

impl<'pke> AppDefine<'_, 'pke> {
    /// Create a timer with borrowed state.
    ///
    /// Unlike [`create`](Timer::create), this creation method lets the
    /// timer runnable borrow state that lives before [`kernel_enter`](crate::kernel_enter).
    /// See [`create`](Timer::create) for more information.
    pub fn create_timer<'ctx, 't, R>(
        &self,
        ctx: Pin<&'t TimerContext<'ctx, R>>,
        schedule: TimerSchedule,
        opts: &'_ TimerOptions<'ctx>,
        runnable: R,
    ) -> Result<&'t Timer, CreateError>
    where
        R: TimerRunnable + 'ctx,
        't: 'pke,
        'ctx: 'pke,
        'ctx: 't,
    {
        // Safety: Runnable has the same lifetime as the context.
        // The context outlives the pre-kernel init lifetime. We
        // know we're in the initialization context, since this
        // is a method on AppDefine.
        //
        // Since kernel initialization never returns, and since the
        // context lifetime is at least as long as the pre-kernel
        // init lifetime, the runnable's captures remain live while
        // the timer can execute.
        unsafe { Timer::create_unchecked(ctx, schedule, opts, runnable) }
    }
}

impl Timer {
    /// Activate a deactivated timer.
    ///
    /// If you created your timer with [`AutoActivate::Disable`], then use this to start
    /// your timer. If you ever [`change`](Self::change)d your timer, then use this
    /// to commit the new schedule.
    #[inline]
    pub fn activate(&self) -> Result<(), ActivateError> {
        // Safety: resource pinned and created per GSG-002.
        let result = unsafe { crate::tx_sys::tx_timer_activate(self.0.get()) };
        ActivateError::try_from_result(result)?;
        Ok(())
    }

    /// Stop a timer.
    ///
    /// If the timer isn't running, then this does nothing.
    #[inline]
    pub fn deactivate(&self) {
        // Safety: resource pinned and created per GSG-002.
        let result = unsafe { crate::tx_sys::tx_timer_deactivate(self.0.get()) };
        debug_assert_eq!(result, crate::tx_sys::TX_SUCCESS);
    }

    /// Change a timer's schedule.
    ///
    /// This call is required for all expired one-shot timers; you need to reset
    /// the one-shot timer schedule.
    ///
    /// The timer must be deactivated before the change takes effect. If this
    /// isn't true, then the call returns success but nothing happens.
    ///
    /// After changing the schedule, use [`activate`](Self::activate) to start the timer.
    #[inline]
    pub fn change(&self, schedule: TimerSchedule) -> Result<(), ChangeError> {
        let RawSchedule {
            initial_ticks,
            reschedule_ticks,
        } = schedule.raw();
        // Safety: resource pinned and created per GSG-002.
        let result = unsafe {
            crate::tx_sys::tx_timer_change(self.0.get(), initial_ticks, reschedule_ticks)
        };
        ChangeError::try_from_result(result)?;
        Ok(())
    }

    /// Acquire runtime information for this timer.
    pub fn info(&self) -> TimerInfo<'_> {
        // Safety: GSG-002. No pointers are held beyond the call.
        // The info call returns a c-string for the name. We tie
        // the lifetime of that name to the timer, a lifetime
        // less than the context.
        unsafe {
            let mut info = TimerInfo::default();
            let mut name: *mut core::ffi::c_char = core::ptr::null_mut();
            let mut active = 0;

            let result = crate::tx_sys::tx_timer_info_get(
                self.0.get(),
                &mut name,
                &mut active,
                core::ptr::null_mut(),
                core::ptr::null_mut(),
                core::ptr::null_mut(),
            );
            debug_assert_eq!(result, crate::tx_sys::TX_SUCCESS);

            info.name = crate::from_threadx_string(name);
            info
        }
    }
}

/// Run a function when a timer expires.
///
/// When a [`Timer`] expires, it invokes [`on_timer_expire`](TimerRunnable::on_timer_expire)
/// on a hidden, high-priority thread. This trait lets you define your timer's
/// behavior.
///
/// For convenience, `TimerRunnable` has a blanket implementation for all
/// `FnMut() + Send` types. Consider using a custom implementation
/// when you must name the runnable's type.
///
/// # Examples
///
/// A static, stateful timer.
///
/// ```no_run
/// use fusible::timer::{Timer, TimerContext, TimerRunnable, TimerSchedule};
/// use core::{cell::Cell, pin::Pin};
///
/// #[derive(Default)]
/// struct StatefulRunnable(u32, Cell<u32>);
/// impl TimerRunnable for StatefulRunnable {
///     fn on_timer_expire(&mut self) {
///         self.1.set(self.1.get() + self.0);
///     }
/// }
///
/// static TIMER: TimerContext<StatefulRunnable> = Timer::context();
///
/// # const TICKS: core::num::NonZero<u32> = unsafe { core::num::NonZero::new_unchecked(5) };
/// # (|| -> Result<(), fusible::timer::CreateError> {
/// Timer::create(
///     Pin::static_ref(&TIMER),
///     TimerSchedule::periodic(TICKS),
///     &Default::default(),
///     StatefulRunnable::default(),
/// )?;
/// # Ok(()) })().unwrap();
/// ```
pub trait TimerRunnable: Send {
    /// Invoked when a timer expires.
    ///
    /// Keep in mind that `run` executes on a hidden, high priority system
    /// thread. This is typically the timer thread, which is the highest
    /// priority thread in the system. Any time spent in `run` is time not
    /// spent in other lower priority threads.
    ///
    /// Additionally, this thread is just like any other thread: it can be
    /// suspended. If you suspend the timer thread, other time-dependent
    /// functions may not execute.
    fn on_timer_expire(&mut self);
}

impl<F> TimerRunnable for F
where
    F: FnMut() + Send,
{
    fn on_timer_expire(&mut self) {
        (self)();
    }
}

struct RunnableFn<R>(UnsafeCell<MaybeUninit<R>>);
impl<R> RunnableFn<R> {
    const fn new() -> Self {
        Self(UnsafeCell::new(MaybeUninit::uninit()))
    }
}

impl<R: TimerRunnable> TimerContext<'_, R> {
    /// # Safety
    ///
    /// Caller must make sure the runnable slot isn't already registered
    /// with the timer.
    unsafe fn set_runnable(&self, runnable: R) {
        // Safety: pointer is valid for writes.
        unsafe { self.2 .0.get().write(MaybeUninit::new(runnable)) }
    }

    /// Produce a callback dispatch to the MaybeUninit runnable.
    ///
    /// # Safety
    ///
    /// The runnable slot must be pinned in memory. Caller must guarantee
    /// that the runnable will be initialized before the callback is invoked.
    unsafe fn callback_dispatch(&self) -> CallbackDispatch<ULONG>
    where
        R: TimerRunnable,
    {
        // Safety: Caller swears to the safey guarantee required by `make`.
        unsafe {
            extern "C" fn entry<R: TimerRunnable>(ctx: *mut ()) {
                // Safety: We know that the pointer is of type TimerContext<R>,
                // since we're calling this withing a TimerContext<R>. We do
                // not drop the memory.
                //
                // If the entrypoint is executing, then the runnable must have
                // been initialized. Cast away the MaybeUninit when invoking the
                // runnable.
                //
                // If the timer panics, deactivate timer. We have to keep the
                // timer created; the user may have live references to the timer
                // that suggest it's created. That means we cannot drop the
                // timer's runnable.
                //
                // TODO(mciantyre) prevent re-activation of a timer if it has
                // ever panicked. This only matters for applications that permit
                // unwinding (and at the moment, I only care about suppressing
                // incessant panics).
                unsafe {
                    let TimerContext(timer, _, runnable): &TimerContext<'_, R> = &(*ctx.cast());
                    let run_timer = core::panic::AssertUnwindSafe(|| {
                        (*runnable.0.get().cast::<R>()).on_timer_expire();
                    });
                    crate::panic::catch_unwind_timer(timer, run_timer);
                }
            }
            callback_dispatch::make(entry::<R>, core::ptr::from_ref(self).cast_mut().cast())
        }
    }
}

// Safety: If we can Send the R across execution contexts, then we can
// also send the wrapper RunnableFn across execution contexts. This
// is the same as the auto-impl Send.
unsafe impl<R: Send> Send for RunnableFn<R> {}

// Safety: We never expose the inner R to user code. The R type is only
// made available to ThreadX through a function pointer and input pointer
// pairing. Since no user code can access the state, it is safe to share
// references to this RunnableFn wrapper.
unsafe impl<R: Send> Sync for RunnableFn<R> {}

/// Maintains the context for a timer.
///
/// Use [`Timer`] to control the timer and interact with the
/// context. If your context is globally allocated, you can
/// use these methods to access the [`Timer`] handle across
/// your threads.
///
/// # FFI
///
/// Unlike some contexts, the timer context is not transparently
/// its resource. Instead, for the purposes of FFI, the context
/// guarantees the following layout:
///
/// ```
/// # struct Timer;
/// #[repr(C)]
/// pub struct TimerContext<'ctx, R> {
///     pub timer: Timer,
///     // Private members follow...
/// #   _ignore: core::marker::PhantomData<&'ctx R>,
/// }
/// ```
#[repr(C)]
pub struct TimerContext<'ctx, R>(Timer, InvariantLifetime<'ctx>, RunnableFn<R>);

impl<R> Drop for TimerContext<'_, R> {
    #[inline]
    fn drop(&mut self) {
        // Safety: Resource pinned and created per GSG-002, or never created per GSG-003.
        // Ensure context lifecycle per GSG-003. If the resource was created, then we
        // initialized the runnable, and it's OK to drop the runnable. By deleting the
        // timer before dropping the runnable, we prevent the timer from firing which could
        // observe multiple mutable runnable references.
        //
        // We allow the runnable's panic to propagate. We've already deleted the timer,
        // completing our job of managing OS resources. It's the user's job to handle any
        // panic-on-drop conditions due to their code.
        unsafe {
            let result = crate::tx_sys::tx_timer_delete(self.0 .0.get());
            aborting_assert!(
                result == crate::tx_sys::TX_SUCCESS || result == crate::tx_sys::TX_TIMER_ERROR,
                "Attempt to drop resource in the initialization context"
            );

            if result == crate::tx_sys::TX_SUCCESS {
                self.2 .0.get_mut().assume_init_drop();
            }
        }
    }
}

impl<R> TimerContext<'_, R> {
    impl_common_context!(Timer);
}

/// Information about a timer.
///
/// This is always tracked by a timer. It is not affected by
/// build configurations. Use [`Timer::info`] to query this
/// information.
#[derive(Debug, Default)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub struct TimerInfo<'a> {
    /// What's the timer's name?
    pub name: crate::ResourceName<'a>,
    /// Is the timer active?
    pub active: bool,
}
