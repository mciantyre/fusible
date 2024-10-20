// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("cargo::rerun-if-changed=memory.x");

    let out_dir = std::path::PathBuf::from(std::env::var("OUT_DIR")?);
    std::fs::copy("memory.x", out_dir.join("memory.x"))?;
    println!("cargo::rustc-link-search={}", out_dir.display());

    Ok(())
}
