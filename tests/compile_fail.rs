// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: Copyright 2024 Ian McIntyre

#[test]
fn compile_fail() {
    trybuild::TestCases::new().compile_fail("tests/ui/*.rs");
}
