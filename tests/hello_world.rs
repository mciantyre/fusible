// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! Run a single thread!
//!
//! Note that you need to, somehow, stop the ThreadX OS from running.
//! We'll kill the process to achieve that. This means that all tests
//! need to be defined in their own file.

use std::pin::Pin;

use fusible::{
    kernel_enter,
    thread::{StaticStack, Thread, ThreadContext},
};

static STACK: StaticStack<512> = StaticStack::new();
static THREAD: ThreadContext = Thread::context();

#[test]
fn hello_world() {
    kernel_enter(|_| {
        Thread::create(
            Pin::static_ref(&THREAD),
            STACK.take().unwrap(),
            &Default::default(),
            || {
                let x = 1;
                let y = 2;
                assert_eq!(x + y, 3);
                std::process::exit(0);
            },
        )
        .unwrap();
    })
}
