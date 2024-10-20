// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: Copyright 2020 The Knurling-rs developers

// This is defmt-semihosting, a development-only package developed by Knurling.
// It's licensed MIT or Apache 2.0. It's available at https://github.com/knurling-rs/defmt.
// See commit 987724b012f0675a700000ea38c7bd1d2325d7f4 for the original source.
//
// Changelog
// ---------
//
// What have we changed w.r.t. the original?
//
// - Remove `#![no_std]` attribute.

//! `defmt` global logger over semihosting
//!
//! NOTE this is meant to only be used with QEMU
//!
//! WARNING using `cortex_m_semihosting`'s `hprintln!` macro or `HStdout` API will corrupt `defmt`
//! log frames so don't use those APIs.

use core::sync::atomic::{AtomicBool, Ordering};

use cortex_m::{interrupt, register};
use cortex_m_semihosting::hio;

#[defmt::global_logger]
struct Logger;

static TAKEN: AtomicBool = AtomicBool::new(false);
static INTERRUPTS_ACTIVE: AtomicBool = AtomicBool::new(false);
static mut ENCODER: defmt::Encoder = defmt::Encoder::new();

unsafe impl defmt::Logger for Logger {
    fn acquire() {
        let primask = register::primask::read();
        interrupt::disable();

        if TAKEN.load(Ordering::Relaxed) {
            panic!("defmt logger taken reentrantly")
        }

        // no need for CAS because interrupts are disabled
        TAKEN.store(true, Ordering::Relaxed);

        INTERRUPTS_ACTIVE.store(primask.is_active(), Ordering::Relaxed);

        // safety: accessing the `static mut` is OK because we have disabled interrupts.
        unsafe { ENCODER.start_frame(do_write) }
    }

    unsafe fn flush() {
        // Do nothing.
        //
        // semihosting is fundamentally blocking, and does not have I/O buffers the target can control.
        // After write returns, the host has the data, so there's nothing left to flush.
    }

    unsafe fn release() {
        // safety: accessing the `static mut` is OK because we have disabled interrupts.
        ENCODER.end_frame(do_write);

        TAKEN.store(false, Ordering::Relaxed);
        if INTERRUPTS_ACTIVE.load(Ordering::Relaxed) {
            // re-enable interrupts
            interrupt::enable()
        }
    }

    unsafe fn write(bytes: &[u8]) {
        // safety: accessing the `static mut` is OK because we have disabled interrupts.
        ENCODER.write(bytes, do_write);
    }
}

fn do_write(bytes: &[u8]) {
    // using QEMU; it shouldn't mind us opening several handles (I hope)
    if let Ok(mut hstdout) = hio::hstdout() {
        hstdout.write_all(bytes).ok();
    }
}
