// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::queue::{Queue, QueueSlot};

type MyElem = QueueSlot<[u8; 7]>;

/// The queue outlives the slots. When this happens, the queue holds
/// a dangling reference to the slots. The compiler rejects this
/// ordering.
fn bi() {
    let queue = core::pin::pin!(Queue::context());
    let mut slots = [const { MyElem::new() }; 5];
    Queue::create(queue.as_ref(), &mut slots, &Default::default()).unwrap();
}

/// Multiple create calls would appear to compile (though they'll
/// fail at runtime, which isn't tested here). The compiler rejects
/// call that uses the slots with a smaller lifetime. This checks
/// our understanding of how the compiler infers the queue's inner
/// lifetime.
fn bim() {
    let mut upper = [const { MyElem::new() }; 5];
    let queue = core::pin::pin!(Queue::context());
    let mut lower = [const { MyElem::new() }; 5];

    Queue::create(queue.as_ref(), &mut upper, &Default::default()).unwrap(); // OK: upper lifetime greater than queue.
    Queue::create(queue.as_ref(), &mut lower, &Default::default()).unwrap(); // ERROR: lower lifetime less than queue.
}

/// Multiple create calls would appear to compile (though they'll
/// fail at runtime, which isn't tested here). The compiler rejects
/// call that uses the slots with a smaller lifetime. This checks
/// our understanding of how the compiler infers the queue's inner
/// lifetime.
fn bap() {
    let mut upper = [const { MyElem::new() }; 5];
    let queue = core::pin::pin!(Queue::context());
    let mut lower = [const { MyElem::new() }; 5];

    Queue::create(queue.as_ref(), &mut lower, &Default::default()).unwrap(); // ERROR: lower lifetime less than queue.
    Queue::create(queue.as_ref(), &mut upper, &Default::default()).unwrap(); // OK: upper lifetime greater than queue.
}

fn main() {
    bi();
    bim();
    bap();
}
