mollusc
=======

[![Build Status](https://img.shields.io/github/workflow/status/woodruffw/mollusc/CI/main)](https://github.com/woodruffw/mollusc/actions?query=workflow%3ACI)

⚠️This is a work in progress! Many parts are incomplete or only partially functional!⚠️

*mollusc* is a collection of pure-Rust libraries for parsing, interpreting, and analyzing LLVM.

| Crate   | Version | Description |
| ------- | ------- | ----------- |
| [`llvm-bitcursor`](./llvm-bitcursor) | [![Crates.io](https://img.shields.io/crates/v/llvm-bitcursor)](https://crates.io/crates/llvm-bitcursor) | A no-frills cursor library for reading fields from a bitstream. |
| [`llvm-bitstream`](./llvm-bitstream) | [![Crates.io](https://img.shields.io/crates/v/llvm-bitstream)](https://crates.io/crates/llvm-bitstream) | A content-agnostic parser for LLVM's bitstream container format. |
| [`llvm-constants`](./llvm-constants) | [![Crates.io](https://img.shields.io/crates/v/llvm-constants)](https://crates.io/crates/llvm-constants) | A collection of numeric and enum constants useful across multiple crates in the *mollusc* ecosystem. |
| [`llvm-support`](./llvm-support) | [![Crates.io](https://img.shields.io/crates/v/llvm-support)](https://crates.io/crates/llvm-support) | Support types and routines for parsing LLVM's bitcode. |
| [`llvm-mapper`](./llvm-mapper) | [![Crates.io](https://img.shields.io/crates/v/llvm-mapper)](https://crates.io/crates/llvm-mapper) | A library for mapping the contents of bitstreams into LLVM IR models. |
| **Not implemented.** | N/A | A high level interface for interacting with LLVM IR. |
