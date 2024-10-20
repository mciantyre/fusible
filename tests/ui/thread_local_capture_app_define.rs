// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use core::pin::pin;
use fusible::thread::{StaticStack, Thread};

static STACK: StaticStack<512> = StaticStack::new();

/// If a thread is created when defining the application, it can capture
/// references that exist before we entered the kernel. However, it can't
/// capture references allocated within the application define callback.
fn main() {
    let pre_kernel_init = 5;
    let thread = pin!(Thread::context());
    fusible::kernel_enter(|app_define| {
        let in_app_define = 7;
        app_define.create_thread(
            thread.into_ref(),
            STACK.take().unwrap(),
            &Default::default(),
            || {
                let _ok = &pre_kernel_init;
                let _error = &in_app_define;
            },
        );

        let context_too_small = pin!(Thread::context());
        app_define
            .create_thread(
                context_too_small.into_ref(),
                STACK.take().unwrap(),
                &Default::default(),
                || (),
            )
            .unwrap();
    });
}
