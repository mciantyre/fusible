// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! A critical section implementation for Fusible.
//!
//! This package provides a [`critical-section`](https://docs.rs/critical-section/1/critical_section/)
//! implementation suitable for Fusible *threads*. The critical section acquires a global mutex
//! with priority inheritance.
//!
//! To use this critical section, depend on this package. Then, use the package somewhere in
//! your dependency graph:
//!
//! ```
//! use fusible_critical_section as _;
//! ```
//!
//! # Panics
//!
//! The critical section panics if an interrupt tries to acquire the critical section. It
//! also panics if code tries to acquire the critical section before the kernel starts
//! initializing.
//!
//! ## On panicking in interrupts
//!
//! There's an emphasis on *thread* in the this documentation. The critical section protects
//! shared state between threads. It does not protect state shared between interrupts and
//! threads. In fact, if you try to acquire a critical section in an interrupt, your program
//! panics.
//!
//! Consider the following example, where a thread enters the critical section, sleeps, then
//! accesses the shared state. Although not depicted, assume that the shared state is also
//! accessed by an interrupt.
//!
//! ```no_run
//! use fusible::thread;
//! use critical_section::Mutex;
//!
//!
//! # struct SharedState; impl SharedState { fn access(&self) {} }
//! static SHARED_STATE: Mutex<SharedState> = Mutex::context(SharedState);
//!
//! critical_section::with(|cs| {
//!     let shared_state = SHARED_STATE.borrow(cs);
//!     thread::sleep(10);
//!     shared_state.access();
//! });
//! ```
//!
//! In Fusible, there is no global interrupt posture. Instead, each Fusible thread has an
//! interrupt posture. When a thread suspends, interrupts are re-enabled.
//!
//! In the above example, the calling thread's interrupt posture is disabled when the thread
//! enters the critical section. The critical section locks a mutex, preventing any threads
//! from accessing the shared state. This code is sound for thread-only mutual exclusion, even
//! when the thread sleeps.
//!
//! However, once the thread voluntarily suspends with `thread::sleep`, the thread implicitly
//! re-enables interrupts! Once the thread suspends -- for any reason -- the implicit posture
//! change allows the interrupt to access the shared state, violating the critical section
//! guarantee.
//!
//! This crate hasn't designed around this problem. Instead, the crate panics if an interrupt
//! tries to acquire the critical section.

#![no_std]

use core::pin::Pin;

use critical_section::RawRestoreState;

use fusible::{
    WaitOption,
    mutex::{Mutex, MutexContext, MutexGuard, MutexOptions},
};

fn global_mutex() -> &'static Mutex<()> {
    static GLOBAL_MUTEX: MutexContext<()> = Mutex::context(());

    let mtx = Pin::static_ref(&GLOBAL_MUTEX);
    MutexContext::try_created(mtx).unwrap_or_else(|| {
        let mut options = MutexOptions::default();
        options.name = Some(c"critical-section");
        options.inheritance = true.into();
        Mutex::create(mtx, &options).unwrap()
    })
}

struct FusibleCriticalSection;
critical_section::set_impl!(FusibleCriticalSection);

unsafe impl critical_section::Impl for FusibleCriticalSection {
    unsafe fn acquire() -> RawRestoreState {
        let wait_option = if fusible::is_initializing() {
            WaitOption::no_wait()
        } else {
            WaitOption::wait_forever()
        };

        let guard: MutexGuard<()> = global_mutex().lock_with_wait(wait_option).unwrap().unwrap();
        core::mem::forget(guard);
    }

    unsafe fn release(_: RawRestoreState) {
        unsafe { global_mutex().unlock().unwrap() };
    }
}
