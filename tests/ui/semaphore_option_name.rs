// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::semaphore::{Semaphore, SemaphoreOptions};
use std::ffi::CString;
use std::pin::pin;

/// The semaphore name has a shorter life than the semaphore control block.
/// Therefore, this fails to compile.
fn main() {
    let semaphore = pin!(Semaphore::context());

    let name = CString::new("name").unwrap();
    let mut opts = SemaphoreOptions::default();
    opts.name = Some(&name);

    Semaphore::create(semaphore.into_ref(), &opts).unwrap();
}
