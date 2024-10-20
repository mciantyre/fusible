// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! When a thread returns from its entrypoint, it drops its entrypoint.
//! Since thread A has higher priority than thread B, it will run to
//! completion, dropping its state, before thread B ever executes.

use fusible::thread::{StaticStack, Thread, ThreadOptions, ThreadPriority};
use std::{pin::pin, sync::atomic::AtomicUsize};

static DROP: AtomicUsize = AtomicUsize::new(0);

struct Dropper;
impl Drop for Dropper {
    fn drop(&mut self) {
        DROP.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}

static STACK_A: StaticStack<256> = StaticStack::new();
static STACK_B: StaticStack<256> = StaticStack::new();

#[test]
fn main() {
    let thread_a = pin!(Thread::context());
    let thread_b = pin!(Thread::context());

    let opts_a = ThreadOptions::single_priority(ThreadPriority::new(5).unwrap());
    let opts_b = ThreadOptions::single_priority(ThreadPriority::new(24).unwrap());

    fusible::kernel_enter(|app_define| {
        let moved_drops = vec![Dropper, Dropper, Dropper];

        app_define
            .create_thread(
                thread_a.into_ref(),
                STACK_A.take().unwrap(),
                &opts_a,
                move || {
                    let _local_drops = Dropper;
                    let _moved_drops = moved_drops;
                },
            )
            .unwrap();

        app_define
            .create_thread(
                thread_b.into_ref(),
                STACK_B.take().unwrap(),
                &opts_b,
                || {
                    assert_eq!(DROP.load(std::sync::atomic::Ordering::Relaxed), 4);
                    std::process::exit(0);
                },
            )
            .unwrap();
    });
}
