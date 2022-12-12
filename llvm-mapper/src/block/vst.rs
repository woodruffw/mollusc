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

/// A ZST representing a "module-style" VST.
///
/// This is a ZST instead of an enum variant to make dispatch on the "style" of VST
/// being parsed slightly more static and readable.
pub struct ModuleStyleVst;

/// A ZST reprsenting a "function-style" VST.
///
/// See [`ModuleStyleVst`] for the design justification here.
pub struct FunctionStyleVst;

/// Represents a single value symbol table ("VST") in a bitcode module.
pub struct Vst {}

impl TryFrom<(&'_ Block, ModuleStyleVst)> for Vst {
    type Error = VstError;

    fn try_from((_block, _): (&'_ Block, ModuleStyleVst)) -> Result<Self, Self::Error> {
        Ok(Vst {})
        // unimplemented!();
    }
}

impl TryFrom<(&'_ Block, FunctionStyleVst)> for Vst {
    type Error = VstError;

    fn try_from((_block, _): (&'_ Block, FunctionStyleVst)) -> Result<Self, Self::Error> {
        Ok(Vst {})
        // unimplemented!();
    }
}
