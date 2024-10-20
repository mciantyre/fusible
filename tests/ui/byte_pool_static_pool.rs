// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::byte_pool::{BytePool, BytePoolContext};

static BYTE_POOL: BytePoolContext = BytePool::context();

/// A static byte pool cannot be created with local storage.
fn main() {
    let mut storage = [0u8; 1024];
    let pool = core::pin::Pin::static_ref(&BYTE_POOL);
    BytePool::create(pool, &mut storage, &Default::default()).unwrap();
}
