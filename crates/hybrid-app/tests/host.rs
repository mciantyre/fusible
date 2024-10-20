// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

struct Exit;

impl fusible_hybrid_app::ExitProcess for Exit {
    fn success(self) -> ! {
        std::process::exit(0);
    }
}

#[test]
fn main() {
    fusible::kernel_enter(|ctx| {
        fusible_hybrid_app::setup(ctx, Exit);
    });
}
