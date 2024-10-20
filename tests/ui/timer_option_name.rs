// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::timer::{Timer, TimerOptions, TimerSchedule};
use std::ffi::CString;
use std::num::NonZero;
use std::pin::pin;

const TICKS: NonZero<u32> = unsafe { NonZero::new_unchecked(6) };
const SCHEDULE: TimerSchedule = TimerSchedule::one_shot(TICKS);

/// The timer name has a shorter life than the timer control block.
/// Therefore, this fails to compile.
fn main() {
    let timer = pin!(Timer::context());

    let name = CString::new("name").unwrap();
    let mut opts = TimerOptions::default();
    opts.name = Some(&name);

    Timer::create(timer.into_ref(), SCHEDULE, &opts, &|| ()).unwrap();
}
