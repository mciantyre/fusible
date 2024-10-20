#!/usr/bin/env sh

# The cargo runner used for running Fusible applications in QEMU.
# You'll need to install defmt-print in order to see debug output.

set -euf -o pipefail
qemu-system-arm \
    -cpu $1 \
    -machine lm3s6965evb \
    -nographic -semihosting-config enable=on,target=native \
    -kernel $2 | defmt-print -e $2 stdin
