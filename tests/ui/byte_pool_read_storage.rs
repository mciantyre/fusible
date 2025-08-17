// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::byte_pool::BytePool;

fn use_storage(_: &[u8]) {}

/// Once you create a pool with storage, the pool exclusively
/// borrows that storage. You can't read from the storage.
fn main() {
    let mut storage = [0u8; 1024];
    let pool = core::pin::pin!(BytePool::context());
    BytePool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();
    use_storage(&storage);
}
