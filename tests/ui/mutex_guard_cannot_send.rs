// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use core::pin::pin;
use fusible::mutex::Mutex;

/// You cannot send a mutex guard to another thread.
fn main() {
    let mtx = pin!(Mutex::context(5u32));
    let mtx = Mutex::create(mtx.into_ref(), &Default::default()).unwrap();
    let guard = mtx.lock().unwrap();
    std::thread::spawn(move || {
        std::mem::drop(guard);
    });
}
