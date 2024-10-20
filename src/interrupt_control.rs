// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Interrupt control services.
//!
//! An _interrupt posture_ describes a thread's potential to be preempted by an interrupt.
//! In most systems, the posture affects all maskable interrupts, including the periodic timer.
//! Consult your ThreadX configuration for details on its interrupt control policy.
//!
//! An interrupt posture is associated with an application thread's context.
//! If a thread suspends after it disabled interrupts, interrupts will remain disabled once the thread is resumed.
//! However, this says nothing about the interrupt posture _while_ the thread is suspended.
//! In fact, interrupts may be re-enabled while a thread is suspended.
//! Keep this caveat in mind as you use [`with_disabled`].
//!
//! # Interrupt posture during initialization
//!
//! Interrupts are disabled throughout the [`kernel_enter`](crate::kernel_enter) initialization context.
//! You must not enable interrupts within the initialization context.
//!
//! # Limitations
//!
//! The API does not directly expose `tx_interrupt_control`. Such an implementation
//! would need to consider how to handle BASEPRI- and PRIMASK-based policies on
//! Cortex-M ports. Until this is supported, this module guarantees that [`with_disabled`]
//! provides an interrupt control policy that's at least as conservative as the one used
//! internally by ThreadX.

use core::cell::Cell;

/// A cell that can be manipulated within an interrupt-free critical section.
///
/// Since `T: Copy`, this cell has no drop behavior. Since it
/// has no drop behavior, we're in full control of the code that
/// executes within the critical section.
#[repr(transparent)]
pub(crate) struct InterruptFreeCell<T: Copy>(Cell<T>);

// Safety: as long as we can send the data across execution contexts,
// the interrupt-free critical section will protect access to the
// data.
unsafe impl<T: Copy + Send> Sync for InterruptFreeCell<T> {}

impl<T: Copy> InterruptFreeCell<T> {
    /// Allocate a cell with an initial value.
    pub(crate) const fn new(value: T) -> Self {
        Self(Cell::new(value))
    }
    /// Replace the contents of the cell with a new value.
    ///
    /// No drop / foreign code runs.
    pub(crate) fn replace(&self, val: T) -> T {
        with_disabled(|| self.0.replace(val))
    }
}

/// Execute `f` while interrupts are disabled.
///
/// Keep in mind that the interrupt posture is associated with a thread's execution context.
/// If a thread suspends within `f`, then interrupts may re-enable during thread
/// suspension.
///
/// This behavior is still considered safe, since this interface provides no way of accessing
/// any shared, mutable state. Should you desire that functionality, you'll need to build that
/// yourself with a full understanding of your system's interrupt control implementation.
///
/// The implementation is panic safe. If `f` panics, an unwind will re-commit the previous
/// interrupt posture.
pub fn with_disabled<F: FnOnce() -> R, R>(f: F) -> R {
    use libthreadx_sys::UINT;
    unsafe extern "C" {
        fn _tx_thread_interrupt_disable() -> UINT;
        fn _tx_thread_interrupt_restore(prior: UINT);
    }

    struct PreviousPosture(UINT);
    impl PreviousPosture {
        fn guard() -> Self {
            // Safety: This ThreadX implementation detail will maximally
            // disable interrupts, depending on the port configuration.
            //
            // The ABI is correct for all considered ports; see ThreadX
            // for details. This is safe to call no matter the execution
            // context, since it changes a CPU / scheduler in a reentrant
            // safe manner.
            unsafe { Self(_tx_thread_interrupt_disable()) }
        }
    }

    impl Drop for PreviousPosture {
        fn drop(&mut self) {
            // Safety: This ThreadX implementation detail will restore
            // the interrupt posture before the most-recent disable
            // call.
            //
            // The ABI is correct for all considered ports; see ThreadX
            // for details. This is safe to call no matter the execution
            // context, since it changes a CPU / scheduler in a reentrant
            // safe manner.
            unsafe { _tx_thread_interrupt_restore(self.0) }
        }
    }

    let _previous_posture_guard = PreviousPosture::guard();
    f()
}
