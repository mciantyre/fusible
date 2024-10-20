// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Fusible catches an unwinding panic in the thread execution context.

use std::{
    pin::pin,
    sync::atomic::{AtomicUsize, Ordering},
};

use fusible::thread::{self, StaticStack, Thread, ThreadOptions, ThreadPriority};

static STACK_A: StaticStack<2048> = StaticStack::new();
static STACK_B: StaticStack<2048> = StaticStack::new();
static STACK_C: StaticStack<2048> = StaticStack::new();

const PRIO_HIGH: ThreadPriority = thread::make_priority(5);
const PRIO_MED: ThreadPriority = thread::make_priority(6);
const PRIO_LOW: ThreadPriority = thread::make_priority(7);

#[test]
fn main() {
    let thread_a = pin!(Thread::context());
    let thread_b = pin!(Thread::context());
    let thread_c = pin!(Thread::context());
    let counter = AtomicUsize::new(0);

    fn make_job<'a>(
        counter: &'a AtomicUsize,
        expected: usize,
        fin: impl FnOnce() + 'a,
    ) -> impl FnOnce() + 'a {
        move || {
            if counter.load(Ordering::Relaxed) != expected {
                std::process::exit(expected as i32 + 1);
            }
            counter.fetch_add(1, Ordering::Relaxed);
            fin()
        }
    }

    fusible::kernel_enter(|app_define| {
        app_define
            .create_thread(
                thread_a.into_ref(),
                STACK_A.take().unwrap(),
                &{
                    let mut opts = ThreadOptions::single_priority(PRIO_HIGH);
                    opts.name = Some(c"The thread known as 'A'");
                    opts
                },
                make_job(&counter, 0, || panic!("Thread A intentionally panicked")),
            )
            .unwrap();

        app_define
            .create_thread(
                thread_b.into_ref(),
                STACK_B.take().unwrap(),
                &{
                    let mut opts = ThreadOptions::single_priority(PRIO_MED);
                    opts.name = Some(c"The thread who goes by 'B'");
                    opts
                },
                make_job(&counter, 1, || panic!("Thread B intentionally panicked")),
            )
            .unwrap();

        app_define
            .create_thread(
                thread_c.into_ref(),
                STACK_C.take().unwrap(),
                &ThreadOptions::single_priority(PRIO_LOW),
                make_job(&counter, 2, || std::process::exit(0)),
            )
            .unwrap();
    });
}
