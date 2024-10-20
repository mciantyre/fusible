// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::thread::{StaticStack, Thread, ThreadOptions};
use std::ffi::CString;
use std::pin::pin;

static STACK: StaticStack<512> = StaticStack::new();

/// A thread's context cannot outlive the name it captures.
fn main() {
    let thread = pin!(Thread::context());

    let name = CString::new("name").unwrap();
    let mut opts = ThreadOptions::default();
    opts.name = Some(&name);

    Thread::create(thread.into_ref(), STACK.take().unwrap(), &opts, || ()).unwrap();
}
