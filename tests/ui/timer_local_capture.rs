// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use core::{num::NonZero, pin::pin};
use fusible::timer::{Timer, TimerSchedule};

const TICKS: NonZero<u32> = unsafe { NonZero::new_unchecked(6) };
const SCHEDULE: TimerSchedule = TimerSchedule::one_shot(TICKS);

fn main() {
    let msg = &String::new();
    let timer = pin!(Timer::context());
    Timer::create(timer.into_ref(), SCHEDULE, &Default::default(), move || {
        let _msg: &str = &msg;
    })
    .unwrap();
}
