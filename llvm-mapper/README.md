llvm-mapper
===========

[![Crates.io](https://img.shields.io/crates/v/llvm-mapper)](https://crates.io/crates/llvm-mapper)
[![Documentation](https://docs.rs/llvm-mapper/badge.svg)](https://docs.rs/llvm-bitstream)

A library for mapping the contents of bitstreams into LLVM IR models.

This library produces a "full-featured" view of a particular LLVM IR program by mapping
blocks and records in the underlying bitstream into their appropriate LLVM models.

This library uses [`llvm-bitstream`](https://crates.io/crates/llvm-bitstream) under the hood.
