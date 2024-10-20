// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use core::{cell::Cell, num::NonZero, pin::pin};
use fusible::timer::{Timer, TimerSchedule};

const TICKS: NonZero<u32> = unsafe { NonZero::new_unchecked(6) };
const SCHEDULE: TimerSchedule = TimerSchedule::one_shot(TICKS);

/// Disallowed: Cell (or any !Sync type) cannot be shared across timers.
fn main() {
    let state = Cell::new(5);
    let timer = pin!(Timer::context());

    fusible::kernel_enter(|app_define| {
        app_define
            .create_timer(timer.into_ref(), SCHEDULE, &Default::default(), || {
                state.set(state.get() + 4)
            })
            .unwrap();
    });
}
