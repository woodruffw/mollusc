//! Functionality for mapping `VALUE_SYMTAB_BLOCK_ID` blocks.
//!
//! These blocks contain "value symbol tables," which are effectively
//! mappings between strings and value models (in LLVM, `llvm::Value`s).

use std::convert::TryFrom;

use thiserror::Error;

use crate::unroll::Block;

/// Errors that can occur when mapping or accessing a VST.
#[derive(Debug, Error)]
pub enum VstError {}

/// Represents a single value symbol table ("VST") in a bitcode module.
pub struct Vst {}

impl TryFrom<&'_ Block> for Vst {
    type Error = VstError;

    fn try_from(_block: &'_ Block) -> Result<Self, Self::Error> {
        unimplemented!();
    }
}
