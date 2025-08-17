// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::block_pool::{BlockOf, BlockPool};

type MyBlock = BlockOf<[u32; 4]>;

fn use_block(_: &MyBlock) {}

/// Once you create a pool with storage, the pool exclusively
/// borrows that storage. You can't read from the storage.
fn main() {
    let mut storage = [const { MyBlock::new() }; 1024];
    let pool = core::pin::pin!(BlockPool::context());
    BlockPool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();
    use_block(&storage[0]);
}
