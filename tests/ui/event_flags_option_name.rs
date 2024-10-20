// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::event_flags::{EventFlags, EventFlagsOptions};
use std::ffi::CString;
use std::pin::pin;

fn main() {
    let flags = pin!(EventFlags::context());

    let name = CString::new("name").unwrap();
    let mut opts = EventFlagsOptions::default();
    opts.name = Some(&name);

    EventFlags::create(flags.into_ref(), &opts).unwrap();
}
