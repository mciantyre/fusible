// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::byte_pool::{AlignedBytePoolStorage, BytePool, BytePoolOptions};
use std::ffi::CString;
use std::pin::pin;

fn main() {
    let mut storage = AlignedBytePoolStorage::from_array([0u8; 512]);
    let pool = pin!(BytePool::context());

    let name = CString::new("name").unwrap();
    let mut opts = BytePoolOptions::default();
    opts.name = Some(&name);

    BytePool::create(pool.into_ref(), &mut storage, &opts).unwrap();
}
