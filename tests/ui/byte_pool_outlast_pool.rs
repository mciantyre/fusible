// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::byte_pool::{BytePool, Bytes};

/// A smart pointer cannot outlive the pool that derives it.
fn main() {
    let mut storage = [0u8; 1024];
    let floats: Bytes<[f32]> = {
        let pool = core::pin::pin!(BytePool::context());
        let pool = BytePool::create(pool.into_ref(), &mut storage, &Default::default()).unwrap();
        let floats = pool.allocate(|| [0f32, 1f32, 2f32]).unwrap();
        Bytes::into_slice(floats)
    };
    drop(floats);
}
