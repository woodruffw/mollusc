//! `llvm-constants` contains numeric and enum constants for interacting with LLVM
//! bitstreams and IR.

#![deny(broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

mod constants;
mod enums;

pub use crate::constants::*;
pub use crate::enums::*;
