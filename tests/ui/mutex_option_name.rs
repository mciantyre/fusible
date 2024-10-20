// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::mutex::{Mutex, MutexOptions};
use std::ffi::CString;
use std::pin::pin;

/// The mutex name has a shorter life than the mutex control block.
/// Therefore, this fails to compile.
fn main() {
    let mutex = pin!(Mutex::context(5u32));

    let name = CString::new("name").unwrap();
    let mut opts = MutexOptions::default();
    opts.name = Some(&name);

    Mutex::create(mutex.into_ref(), &opts).unwrap();
}
