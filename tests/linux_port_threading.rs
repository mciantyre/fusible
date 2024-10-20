// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Demonstrates that the Linux ThreadX port utilizes OS threads under the hood.
//!
//! This is only representative of how ThreadX works on Linux.

use fusible::{
    kernel_enter,
    mutex::{Mutex, RefCellMutex},
    thread::{Stack, StaticStack, Thread, ThreadContext},
};
use std::{
    collections::HashSet,
    pin::{pin, Pin},
    thread::ThreadId,
};

static STACK: StaticStack<512> = StaticStack::new();
static SUPERVISOR: ThreadContext = Thread::context();

#[test]
fn linux_port_separate_threads() {
    const WORKERS: usize = 32;

    let supervisor = |thread_ids: &RefCellMutex<Vec<ThreadId>>| {
        let start = std::time::Instant::now();

        loop {
            let count = thread_ids.lock().unwrap().borrow().len();
            if count == WORKERS {
                break;
            }

            if start.elapsed() > std::time::Duration::from_secs(1) {
                panic!("Didn't finish in time! We have values from {count} workers");
            }

            fusible::thread::relinquish();
        }

        let guard = thread_ids.lock().unwrap();
        let mut thread_ids = guard.borrow_mut();
        let thread_ids = std::mem::take(&mut *thread_ids);
        let thread_ids: HashSet<ThreadId> = thread_ids.into_iter().collect();
        assert_eq!(thread_ids.len(), WORKERS);
        std::process::exit(0);
    };

    let mut threads_stacks = Vec::with_capacity(WORKERS);
    for _ in 0..WORKERS {
        let thread = Pin::static_ref(Box::leak(Box::new(Thread::context())));
        let stack = Box::leak(Box::new(Stack::<512>::new()));
        threads_stacks.push((thread, stack));
    }

    let thread_ids = pin!(Mutex::with_refcell(Vec::new()));

    kernel_enter(|app_define| {
        let thread_ids = Mutex::create(thread_ids.into_ref(), &Default::default()).unwrap();
        app_define
            .create_thread(
                Pin::static_ref(&SUPERVISOR),
                STACK.take().unwrap(),
                &Default::default(),
                move || supervisor(thread_ids),
            )
            .unwrap();

        for (thread, stack) in threads_stacks.into_iter() {
            app_define
                .create_thread(
                    thread,
                    stack.as_mut_slice(),
                    &Default::default(),
                    move || {
                        let id = std::thread::current().id();
                        thread_ids.lock().unwrap().borrow_mut().push(id);
                    },
                )
                .unwrap();
        }
    });
}
