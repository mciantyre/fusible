// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! If a timer panics and unwinds, Fusible disables the timer.

use std::pin::pin;

use fusible::{
    semaphore::Semaphore,
    thread::{StaticStack, Thread},
    timer::{Timer, TimerOptions, TimerSchedule},
};

static STACK: StaticStack<2048> = StaticStack::new();

#[test]
fn main() {
    let thread = pin!(Thread::context());
    let sema = pin!(Semaphore::context());
    let timer = pin!(Timer::context());

    fusible::kernel_enter(|app_define| {
        let sema = Semaphore::create(sema.into_ref(), &Default::default()).unwrap();
        let timer = app_define
            .create_timer(
                timer.into_ref(),
                TimerSchedule::one_shot(1.try_into().unwrap()),
                &{
                    let mut opts = TimerOptions::default();
                    opts.name = Some(c"The one-shot timer");
                    opts.activate = true.into();
                    opts
                },
                || {
                    sema.put();
                    panic!("Intentional timer panic");
                },
            )
            .unwrap();

        app_define
            .create_thread(
                thread.into_ref(),
                STACK.take().unwrap(),
                &Default::default(),
                || {
                    if sema.get().is_err() {
                        std::process::exit(1);
                    }
                    let info = timer.info();
                    if info.active {
                        std::process::exit(1);
                    }
                    std::process::exit(0);
                },
            )
            .unwrap();
    });
}
