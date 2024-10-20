#!/usr/bin/env bash

set -euf -o pipefail

emph=$(tput bold)$(tput setaf 4)
noemph=$(tput sgr0)
toolchain=${TOOLCHAIN:-+stable}

ci_check() {
    printf "\n${emph}=== $@ ===${noemph}\n\n"
}

ci_check Are all packages properly formatted?
cargo ${toolchain} fmt --all --check

ci_check Does Fusible pass all of its tests?
cargo ${toolchain} test

ci_check Are all links in Fusible documentation valid?
cargo ${toolchain} rustdoc -- -D warnings

ci_check Is clippy happy with Fusible?
cargo ${toolchain} clippy                                -- -D warnings
cargo ${toolchain} clippy --target=thumbv7em-none-eabihf -- -D warnings

ci_check Is Miri happy with Fusible unit tests?
cargo +nightly miri test --lib

pushd crates/hybrid-app > /dev/null

ci_check Can we build and test the hybrid-app locally?
cargo test

popd > /dev/null

pushd crates/qemu > /dev/null

ci_check Can we build and run the hybrid-app for all suppored QEMU targets?
QEMU_TARGETS=(
    "thumbv6m-none-eabi"
    "thumbv7m-none-eabi"
    "thumbv7em-none-eabi"
    "thumbv7em-none-eabihf"
    "thumbv8m.base-none-eabi"
    "thumbv8m.main-none-eabi"
    "thumbv8m.main-none-eabihf"
)
for target in ${QEMU_TARGETS[@]}; do
    printf "${emph}--- hybrid_app target $target ---${noemph}\n"
    cargo run --release --example=hybrid_app --target=$target
done

popd > /dev/null
