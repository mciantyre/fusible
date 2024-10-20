// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use core::{cell::Cell, pin::pin};
use fusible::thread::{StaticStack, Thread};

static STACK: StaticStack<512> = StaticStack::new();

/// Disallowed: Cell (or any !Sync type) cannot be shared across threads.
fn main() {
    let state = Cell::new(5);
    let thread = pin!(Thread::context());

    fusible::kernel_enter(|app_define| {
        app_define
            .create_thread(
                thread.into_ref(),
                STACK.take().unwrap(),
                &Default::default(),
                || state.set(state.get() + 4),
            )
            .unwrap();
    });
}
