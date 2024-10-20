// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

#![no_std]
#![no_main]

use fusible_qemu as fusible;
use panic_probe as _;

struct Exit;
impl fusible_hybrid_app::ExitProcess for Exit {
    fn success(self) -> ! {
        use cortex_m_semihosting::debug::*;
        defmt::println!("Success! The hybrid app completed as expected.");
        exit(EXIT_SUCCESS);
        unreachable!()
    }
}

#[cortex_m_rt::entry]
fn main() -> ! {
    fusible::kernel_enter(|ctx| {
        fusible_hybrid_app::setup(ctx, Exit);
    });
}
