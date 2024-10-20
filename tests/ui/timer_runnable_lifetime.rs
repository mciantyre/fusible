// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use fusible::timer::{Timer, TimerSchedule};
use std::pin::pin;

fn main() {
    let runnable = || println!();
    let timer = pin!(Timer::context());
    Timer::create(
        timer.into_ref(),
        TimerSchedule::one_shot(1.try_into().unwrap()),
        &Default::default(),
        &runnable,
    )
    .unwrap();
}
