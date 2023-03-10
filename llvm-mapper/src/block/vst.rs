//! Functionality for mapping `VALUE_SYMTAB_BLOCK_ID` blocks.
//!
//! These blocks contain "value symbol tables," which are effectively
//! mappings between strings and value models (in LLVM, `llvm::Value`s).

use std::convert::TryFrom;

use llvm_support::bitcodes::ValueSymtabCode;
use thiserror::Error;

use crate::unroll::Block;

/// Errors that can occur when mapping or accessing a VST.
#[derive(Debug, Error)]
pub enum VstError {
    /// An invalid `VST_CODE_FNENTRY` record was encountered.
    #[error("invalid VST_CODE_FNENTRY: {0}")]
    BadFnEntry(&'static str),
}

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
#[derive(Debug)]
pub struct Vst {
    /// The value IDs in this VST.
    pub value_ids: Vec<u64>,
}

impl TryFrom<(&'_ Block, ModuleStyleVst)> for Vst {
    type Error = VstError;

    fn try_from((block, _): (&'_ Block, ModuleStyleVst)) -> Result<Self, Self::Error> {
        let mut value_ids = vec![];
        // The only records we expect in a global ("module-style") VST are
        // function entry records.
        for fn_entry in block.records.by_code(ValueSymtabCode::FnEntry) {
            // These should be [valueid, offset, namechar x N].
            // Experimentally, module-style VSTs don't have that last field,
            // and, since we're parsing eagerly, we don't care about the
            // function's offset (we'll get to it anyways).
            value_ids.push(
                *fn_entry
                    .fields()
                    .first()
                    .ok_or(VstError::BadFnEntry("expected valueid field"))?,
            );
        }

        Ok(Vst { value_ids })
    }
}

impl TryFrom<(&'_ Block, FunctionStyleVst)> for Vst {
    type Error = VstError;

    fn try_from((_block, _): (&'_ Block, FunctionStyleVst)) -> Result<Self, Self::Error> {
        Ok(Vst { value_ids: vec![] })
        // unimplemented!();
    }
}
