// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Demonstrates simple periodic timers.

use std::{
    num::NonZero,
    pin::{pin, Pin},
    sync::atomic::{AtomicU32, Ordering},
};

use fusible::{
    thread::{StaticStack, Thread, ThreadContext},
    timer::{Timer, TimerContext, TimerOptions, TimerRunnable, TimerSchedule},
};

static STACK: StaticStack<2048> = StaticStack::new();
static THREAD: ThreadContext = Thread::context();

struct OneShotter {
    old_values: Vec<u32>,
}

impl OneShotter {
    fn new() -> Self {
        Self {
            old_values: Vec::new(),
        }
    }
}

impl TimerRunnable for OneShotter {
    fn on_timer_expire(&mut self) {
        let old_value = GLOBAL_STATIC.fetch_add(1, Ordering::Relaxed);
        self.old_values.push(old_value);

        let one_shot = Pin::static_ref(&ONE_SHOT).try_created().unwrap();
        one_shot
            .change(TimerSchedule::one_shot(NonZero::new(3).unwrap()))
            .unwrap();
        one_shot.activate().unwrap();
    }
}

static GLOBAL_STATIC: AtomicU32 = AtomicU32::new(0);
static ONE_SHOT: TimerContext<OneShotter> = Timer::context();

#[test]
fn main() {
    static HIDDEN_STATIC: AtomicU32 = AtomicU32::new(0);

    let mut values = Vec::new();
    let mut local_runnable = move || {
        values.push(1u32);
        HIDDEN_STATIC.fetch_add(values.pop().unwrap(), Ordering::Relaxed);
    };
    let periodic = pin!(Timer::context());

    fusible::kernel_enter(|app_define| {
        Thread::create(
            Pin::static_ref(&THREAD),
            STACK.take().unwrap(),
            &Default::default(),
            || loop {
                let _ = fusible::thread::sleep(20);
                if HIDDEN_STATIC.load(Ordering::Relaxed) > 10
                    && GLOBAL_STATIC.load(Ordering::Relaxed) > 10
                {
                    std::process::exit(0);
                }
            },
        )
        .unwrap();

        app_define
            .create_timer(
                periodic.into_ref(),
                TimerSchedule::periodic(NonZero::new(5).unwrap()),
                &TimerOptions::default(),
                &mut local_runnable,
            )
            .unwrap()
            .activate()
            .unwrap();

        Timer::create(
            Pin::static_ref(&ONE_SHOT),
            TimerSchedule::one_shot(NonZero::new(3).unwrap()),
            &{
                let mut opts = TimerOptions::default();
                opts.activate = true.into();
                opts
            },
            OneShotter::new(),
        )
        .unwrap();
    })
}
