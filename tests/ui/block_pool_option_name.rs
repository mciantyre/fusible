// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::block_pool::{BlockOf, BlockPool, BlockPoolOptions};
use std::ffi::CString;
use std::pin::pin;

fn main() {
    let mut storage = [const { BlockOf::<u32>::new() }; 32];
    let pool = pin!(BlockPool::context());

    let name = CString::new("name").unwrap();
    let mut opts = BlockPoolOptions::default();
    opts.name = Some(&name);

    BlockPool::create(pool.into_ref(), &mut storage, &opts).unwrap();
}
