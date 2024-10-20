// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::byte_pool::{BytePool, BytePoolOptions};

/// The pool outlives the storage. When this happens, the pool holds
/// a dangling reference to the storage. The compiler rejects this
/// ordering.
fn bi() {
    let pool = core::pin::pin!(BytePool::context());
    let mut storage = [0u8; 1024];
    BytePool::create(pool.as_ref(), &mut storage, &{
        let mut opts = BytePoolOptions::default();
        opts.name = Some(c"name");
        opts
    })
    .unwrap();
}

/// Multiple create calls would appear to compile (though they'll
/// fail at runtime, which isn't tested here). The compiler rejects
/// call that uses the storage with a smaller lifetime. This checks
/// our understanding of how the compiler infers the pool's inner
/// lifetime.
fn bim() {
    let mut upper = [0u8; 512];
    let pool = core::pin::pin!(BytePool::context());
    let mut lower = [0u8; 512];

    BytePool::create(pool.as_ref(), &mut upper, &Default::default()).unwrap(); // OK: upper lifetime greater than pool.
    BytePool::create(pool.as_ref(), &mut lower, &Default::default()).unwrap(); // ERROR: lower lifetime less than pool.
}

/// Multiple create calls would appear to compile (though they'll
/// fail at runtime, which isn't tested here). The compiler rejects
/// call that uses the storage with a smaller lifetime. This checks
/// our understanding of how the compiler infers the pool's inner
/// lifetime.
fn bap() {
    let mut upper = [0u8; 512];
    let pool = core::pin::pin!(BytePool::context());
    let mut lower = [0u8; 512];

    BytePool::create(pool.as_ref(), &mut lower, &Default::default()).unwrap(); // ERROR: lower lifetime less than pool.
    BytePool::create(pool.as_ref(), &mut upper, &Default::default()).unwrap(); // OK: upper lifetime greater than pool.
}

fn main() {
    bi();
    bim();
    bap();
}
