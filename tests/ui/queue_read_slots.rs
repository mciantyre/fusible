// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::queue::{Queue, QueueSlot};

/// Once you create a queue with slots, the pool exclusively
/// borrows those slots. You can't read from the slots.
fn main() {
    let mut slots = [const { QueueSlot::<[u32; 4]>::new() }; 1024];
    let queue = core::pin::pin!(Queue::context());
    Queue::create(queue.as_ref(), &mut slots, &Default::default()).unwrap();
    let _ = slots[0];
}
