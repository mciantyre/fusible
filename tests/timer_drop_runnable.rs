// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::{
    thread::{StaticStack, Thread},
    timer::{Timer, TimerRunnable, TimerSchedule},
};
use std::{
    pin::{Pin, pin},
    sync::atomic::{AtomicUsize, Ordering},
};

static STACK: StaticStack<2048> = StaticStack::new();

fn entrypoint() {
    static COUNT: AtomicUsize = AtomicUsize::new(0);
    struct IncrementOnDrop;
    impl TimerRunnable for IncrementOnDrop {
        fn on_timer_expire(&mut self) {}
    }
    impl Drop for IncrementOnDrop {
        fn drop(&mut self) {
            COUNT.fetch_add(1, Ordering::Relaxed);
        }
    }

    {
        let _: Pin<&mut fusible::timer::TimerContext<'_, IncrementOnDrop>> = pin!(Timer::context());
    }
    assert_eq!(COUNT.load(Ordering::Relaxed), 0);

    {
        let timer: Pin<&mut fusible::timer::TimerContext<'_, IncrementOnDrop>> =
            pin!(Timer::context());
        Timer::create(
            timer.into_ref(),
            TimerSchedule::one_shot(1.try_into().unwrap()),
            &Default::default(),
            IncrementOnDrop,
        )
        .unwrap();
    }
    assert_eq!(COUNT.load(Ordering::Relaxed), 1);

    std::process::exit(0);
}

#[test]
fn main() {
    let thread = pin!(Thread::context());
    fusible::kernel_enter(|app_define| {
        app_define
            .create_thread(
                thread.into_ref(),
                STACK.take().unwrap(),
                &Default::default(),
                entrypoint,
            )
            .unwrap();
    });
}
