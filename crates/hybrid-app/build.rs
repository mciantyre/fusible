// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

use std::{env, path::PathBuf};

fn guess_the_port_include() -> PathBuf {
    let target = env::var("TARGET").unwrap();
    let host = env::var("HOST").unwrap();

    if host == target {
        if cfg!(target_os = "linux") || cfg!(target_os = "macos") {
            return "linux/gnu/inc".into();
        } else if cfg!(target_os = "windows") {
            return "win32/vs_2019/inc".into();
        }
    } else if target.starts_with("thumbv7m") || target.starts_with("thumbv7em") {
        return "cortex_m4/gnu/inc".into();
    } else if target.starts_with("thumbv6m") {
        return "cortex_m0/gnu/inc".into();
    } else if target.starts_with("thumbv8m.base") {
        return "cortex_m23/gnu/inc".into();
    } else if target.starts_with("thumbv8m.main") {
        return "cortex_m33/gnu/inc".into();
    }

    panic!("Can't guess the port! To fix this issue, update this build script.");
}

fn main() {
    println!("cargo::rerun-if-env-changed=THREADX_INSTALL");

    let install = PathBuf::from(
        env::var("THREADX_INSTALL")
            .expect("Set the THREADX_INSTALL env var to your ThreadX source installation"),
    );

    assert!(install.exists(), "{} doesn't exist", install.display());

    let common_include = install.join("common").join("inc");
    assert!(common_include.exists());

    let port_include = install.join("ports").join(guess_the_port_include());
    assert!(
        port_include.exists(),
        "{} doesn't exist",
        port_include.display()
    );

    println!("cargo::rerun-if-changed=src/lib.c");
    cc::Build::new()
        .file("src/lib.c")
        .includes([common_include, port_include])
        .define("TX_SINGLE_MODE_SECURE", None) // For ARMv8-M
        .compile("hybridappc");
}
