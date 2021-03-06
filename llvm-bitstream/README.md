llvm-bitstream
==============

[![Crates.io](https://img.shields.io/crates/v/llvm-bitstream)](https://crates.io/crates/llvm-bitstream)
[![Documentation](https://docs.rs/llvm-bitstream/badge.svg)](https://docs.rs/llvm-bitstream)

A content-agnostic parser for LLVM's [bitstream container format](https://llvm.org/docs/BitCodeFormat.html).

Conceptually, this library is one step below a full LLVM bitcode parser:
it can interpret the entries in a bitstream, but isn't aware of their semantics
and isn't responsible for composing them into an LLVM IR
program (or any other concrete structure that's been serialized as a bitstream).

This library uses [`llvm-bitcursor`](https://crates.io/crates/llvm-bitcursor) under the hood.
