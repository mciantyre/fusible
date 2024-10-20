// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::block_pool::{BlockOf, BlockPool};

type MyBlock = BlockOf<[u8; 7]>;

/// The pool outlives the storage. When this happens, the pool holds
/// a dangling reference to the storage. The compiler rejects this
/// ordering.
fn bi() {
    let pool = core::pin::pin!(BlockPool::context());
    let mut storage = [const { MyBlock::new() }; 5];
    BlockPool::create(pool.as_ref(), &mut storage, &Default::default()).unwrap();
}

/// Multiple create calls would appear to compile (though they'll
/// fail at runtime, which isn't tested here). The compiler rejects
/// call that uses the storage with a smaller lifetime. This checks
/// our understanding of how the compiler infers the pool's inner
/// lifetime.
fn bim() {
    let mut upper = [const { MyBlock::new() }; 5];
    let pool = core::pin::pin!(BlockPool::context());
    let mut lower = [const { MyBlock::new() }; 5];

    BlockPool::create(pool.as_ref(), &mut upper, &Default::default()).unwrap(); // OK: upper lifetime greater than pool.
    BlockPool::create(pool.as_ref(), &mut lower, &Default::default()).unwrap(); // ERROR: lower lifetime less than pool.
}

/// Multiple create calls would appear to compile (though they'll
/// fail at runtime, which isn't tested here). The compiler rejects
/// call that uses the storage with a smaller lifetime. This checks
/// our understanding of how the compiler infers the pool's inner
/// lifetime.
fn bap() {
    let mut upper = [const { MyBlock::new() }; 5];
    let pool = core::pin::pin!(BlockPool::context());
    let mut lower = [const { MyBlock::new() }; 5];

    BlockPool::create(pool.as_ref(), &mut lower, &Default::default()).unwrap(); // ERROR: lower lifetime less than pool.
    BlockPool::create(pool.as_ref(), &mut upper, &Default::default()).unwrap(); // OK: upper lifetime greater than pool.
}

fn main() {
    bi();
    bim();
    bap();
}
