// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Preventing cross-language unwinding panics.

use core::panic::UnwindSafe;

use crate::timer::Timer;

#[cfg(not(any(panic = "abort", panic = "unwind")))]
compile_error!("Unknown panic option!");

// Defeated once there's a no-std-only Rust
// target that supports unwinding. None come
// to mind, but I'm not doing research.
#[cfg(panic = "unwind")]
extern crate std;

/// Force the program to abort.
///
/// This is stronger than a panic, since it never allows unwinding.
/// If the program would normally abort on panic, then this is a
/// normal panic.
macro_rules! abort {
    ($($arg:tt)*) => {{
        #[cfg(panic = "unwind")]
        {
            extern crate std;
            std::eprintln!($($arg)*);
            std::eprintln!("Aborting the Fusible program");
            std::process::abort();
        }
        #[cfg(panic = "abort")]
        {
            panic!($($arg)*);
        }
    }};
}

fn catch_unwind_default<W: FnOnce() + UnwindSafe, P: FnOnce()>(work: W, on_panic: P) {
    #[cfg(panic = "unwind")]
    {
        if std::panic::catch_unwind(work).is_err() {
            on_panic();
        }
    }

    #[cfg(panic = "abort")]
    {
        work();
        drop(on_panic);
    }
}

/// If app initialization unwinds, abort the process.
pub(crate) fn catch_unwind_init<W: FnOnce() + UnwindSafe>(work: W) {
    abort_on_panic(work);
}

/// If a thread unwinds, terminate the thread.
pub(crate) fn catch_unwind_thread<W: FnOnce() + UnwindSafe>(work: W) {
    catch_unwind_default(work, || crate::thread::terminate());
}

/// If a timer unwinds, disable the timer.
pub(crate) fn catch_unwind_timer<W: FnOnce() + UnwindSafe>(timer: &Timer, work: W) {
    catch_unwind_default(work, || timer.deactivate());
}

/// Abort the program if the assert fails.
///
/// See [`abort`] for more information.
macro_rules! aborting_assert {
    ($cond:expr $(,)?) => {
        if !$cond {
            abort!(::core::stringify!($cond));
        }
    };
    ($cond:expr, $($arg:tt)+) => {
        if !$cond {
            abort!($($arg)*);
        }
    }
}

/// Abort the program if `f` panics.
pub(crate) fn abort_on_panic<F: FnOnce() + UnwindSafe>(f: F) {
    catch_unwind_default(f, || abort!());
}
