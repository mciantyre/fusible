// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::queue::{Queue, QueueContext, QueueSlot};

static QUEUE: QueueContext<String> = Queue::context();

/// A static queue cannot be created with local slots.
fn main() {
    let mut slots = [const { QueueSlot::<String>::new() }; 30];
    let queue = core::pin::Pin::static_ref(&QUEUE);
    Queue::create(queue.as_ref(), &mut slots, &Default::default()).unwrap();
}
