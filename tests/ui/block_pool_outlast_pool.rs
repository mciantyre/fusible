// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::block_pool::{Block, BlockOf, BlockPool};

type MyBlock = BlockOf<Vec<f64>>;

/// A smart pointer cannot outlive the pool that derives it.
fn main() {
    let mut storage = [const { MyBlock::new() }; 100];
    let floats: Block<Vec<f64>> = {
        let pool = core::pin::pin!(BlockPool::context());
        let pool = BlockPool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();
        pool.allocate(|| vec![0f64, 1f64, 2f64]).unwrap()
    };
    drop(floats);
}
