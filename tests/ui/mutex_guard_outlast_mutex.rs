// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::mutex::Mutex;
use std::pin::pin;

/// The mutex guard cannot outlive the control block.
fn main() {
    let guard = {
        let mutex = pin!(Mutex::context(5u32));
        let mutex = Mutex::create(mutex.into_ref(), &Default::default()).unwrap();
        mutex.lock().unwrap()
    };
    println!("{}", *guard);
}
