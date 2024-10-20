// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::block_pool::{BlockOf, BlockPool, BlockPoolContext};

static BLOCK_POOL: BlockPoolContext<String> = BlockPool::context();

/// A static block pool cannot be created with local storage.
fn main() {
    let mut storage = [const { BlockOf::<String>::new() }; 1024];
    let pool = core::pin::Pin::static_ref(&BLOCK_POOL);
    BlockPool::create(pool, &mut storage, &Default::default()).unwrap();
}
