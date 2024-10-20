// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use core::pin::pin;
use fusible::thread::{StaticStack, Thread};

static STACK: StaticStack<512> = StaticStack::new();

/// By default, a thread's entrypoint cannot capture local state.
fn main() {
    let x = 5;
    let thread = pin!(Thread::context());
    Thread::create(
        thread.into_ref(),
        STACK.take().unwrap(),
        &Default::default(),
        || {
            let _nope = &x;
            let _fine = &STACK;
        },
    )
    .unwrap();
}
