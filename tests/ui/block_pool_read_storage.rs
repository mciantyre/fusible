// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::block_pool::{BlockOf, BlockPool};

/// Once you create a pool with storage, the pool exclusively
/// borrows that storage. You can't read from the storage.
fn main() {
    let mut storage = [const { BlockOf::<[u32; 4]>::new() }; 1024];
    let pool = core::pin::pin!(BlockPool::context());
    BlockPool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();
    let _ = storage[0];
}
