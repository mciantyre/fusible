// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use std::env;

fn main() {
    println!("cargo::rerun-if-changed=src/lib.c");
    let threadx_common_include = env::var("DEP_THREADX_COMMON_INCLUDE").unwrap();
    let threadx_port_include = env::var("DEP_THREADX_PORT_INCLUDE").unwrap();

    cc::Build::new()
        .file("src/lib.c")
        .include(threadx_common_include)
        .include(threadx_port_include)
        .define("TX_SINGLE_MODE_SECURE", None) // For ARMv8-M
        .compile("hybridappc");
}
