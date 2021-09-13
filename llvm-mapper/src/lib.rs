//! `llvm-mapper` is a library for mapping entities in LLVM's bitstream
//! format into higher-level IR and bitcode metadata models.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

pub mod block;
pub mod error;
pub mod map;
pub mod record;
pub mod unroll;
