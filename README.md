# Fusible

Fusible provides convenient Rust bindings for the ThreadX RTOS. Fusible thread
is also used to bind textiles.

To learn how to use Fusible, see the API documentation.

## Building

Fusible isn't available on crates.io. Until it's published, use a git dependency
or vendor the package.

Fusible depends on [libthreadx-sys] and its build process. If you can run the
libthreadx-sys examples and tests, you should be able to run Fusible programs.

[libthreadx-sys]: https://github.com/mciantyre/libthreadx-sys

## Repository organization

`./src` contains the `no_std` Fusible library, called `fusible`. The library
provides a slim Rust interface for ThreadX. If you're targeting a MCU, you'll
need more support; see the `fusible` API documentation for details.

`./tests` contains programs that should run on a *nix-like host and programs
that should fail to compile. Use `cargo test` to execute these tests and the
examples in the API documentation.

`./crates` contains extra packages that enhance Fusible. These include

- `./crates/allocator` implements a global allocator.
- `./crates/app-benchmark` contains a small benchmarking application intended
  for physical hardware.
- `./crates/critical-section` provides a critical section implementation for
  threads.
- `./crates/hybrid-app` is an abomination that evaluates FFI support and ability
  to integrate with C programs.
- `./crates/qemu` helps you run Fusible applications in a QEMU emulator.

## License

All packages in this repository are licensed MPL-2.0. See [LICENSE](./LICENSE)
for more information. Individual files may carry their own licenses; see file
comments for details.
