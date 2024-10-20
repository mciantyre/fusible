// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::queue::{Queue, QueueSlot};

/// If you pin the queue directly into the create call, it'll compile.
/// However, you can't use the pinned reference produced by create.
fn main() {
    let mut slots = [const { QueueSlot::<[u32; 4]>::new() }; 1024];
    let queue = Queue::create(
        core::pin::pin!(Queue::context()).into_ref(),
        &mut slots,
        &Default::default(),
    )
    .unwrap();
    queue.try_receive().unwrap();
}
