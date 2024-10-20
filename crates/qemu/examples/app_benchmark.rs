// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! This example runs. However, QEMU can't measure cycle counts, so it doesn't
//! serve as a useful benchmark. You should run the benchmark application on
//! real hardware.
//!
//! Although it's useless for benchmarking, it's a helpful example for getting
//! fusible running on QEMU, complete with defmt semihosting support.

#![no_std]
#![no_main]

use fusible_qemu as fusible;
use panic_probe as _;

#[cortex_m_rt::entry]
fn main() -> ! {
    fusible::kernel_enter(|app_define| {
        fusible_app_benchmark::run(app_define);
    })
}
