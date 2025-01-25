// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

//! An extension package for running Fusible in QEMU.
//!
//! It uses defmt semihosting to convey debug messages. You can expect your
//! QEMU instance to write defmt frames to stdout, and you can parse those using
//! `defmt-print`, or your custom decoder.

#![no_std]

use defmt_semihosting as _;

pub use fusible::*;

#[doc(hidden)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _tx_initialize_low_level() {
    use cortex_m::{peripheral::scb::SystemHandler, Peripherals};

    cortex_m::interrupt::disable();

    let Peripherals {
        mut SYST, mut SCB, ..
    } = Peripherals::take().unwrap();

    unsafe {
        SCB.set_priority(SystemHandler::SysTick, 0x40);
        SCB.set_priority(SystemHandler::PendSV, 0xff);
        SCB.set_priority(SystemHandler::SVCall, 0xff);
    }

    SYST.set_reload(80000 - 1);
    SYST.clear_current();
    SYST.enable_interrupt();
    SYST.enable_counter();
}
