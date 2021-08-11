llvm-bitcursor.rs
=================

[![Build Status](https://img.shields.io/github/workflow/status/woodruffw/llvm-bitcursor.rs/CI/main)](https://github.com/woodruffw/llvm-bitcursor.rs/actions?query=workflow%3ACI)
[![Crates.io](https://img.shields.io/crates/v/llvm-bitcursor)](https://crates.io/crates/llvm-bitcursor)

A no-frills cursor library that supports reading unaligned fields from
a bitstream.

This library primarily exists to provide low-level support for the task
of parsing LLVM's [bitstream format](https://llvm.org/docs/BitCodeFormat.html).
If you're looking for a general purpose bitvector handling library, try
[bitvec](https://crates.io/crates/bitvec) or [bit-vec](https://crates.io/crates/bit-vec).

Features:

* No-copy, all cursor state is internal
* Support for LLVM's [VBR](https://llvm.org/docs/BitCodeFormat.html#variable-width-value) encoding
  (requires the `vbr` feature)
* 100% safe Rust, with `#![forbid(unsafe_code)]`
* No use of `unwrap`, `expect`, or `panic`

Anti-features:

* Not a general purpose bitvector/bitstring handling library
* Probably not very fast
* Doesn't care about bit order (always LSB-first)
