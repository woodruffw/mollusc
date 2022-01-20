//! Functionality for mapping the `SYMTAB_BLOCK` block.

use llvm_constants::{IrBlockId, SymtabCode};
use thiserror::Error;

use crate::block::{BlockMapError, IrBlock};
use crate::map::PartialMapCtx;
use crate::record::RecordBlobError;
use crate::unroll::UnrolledBlock;

/// Errors that can occur when accessing a symbol table.
#[derive(Debug, Error)]
pub enum SymtabError {
    /// The blob containing the symbol table is invalid.
    #[error("invalid string table: {0}")]
    BadBlob(#[from] RecordBlobError),
}

/// Models the `SYMTAB_BLOCK` block.
///
/// For now, this is an opaque block: it's really only used to accelerate LTO,
/// so we don't attempt to expand its fields here.
#[derive(Debug)]
pub struct Symtab(Vec<u8>);

impl AsRef<[u8]> for Symtab {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl IrBlock for Symtab {
    const BLOCK_ID: IrBlockId = IrBlockId::Symtab;

    fn try_map_inner(
        block: &UnrolledBlock,
        _ctx: &mut PartialMapCtx,
    ) -> Result<Self, BlockMapError> {
        let symtab = {
            let symtab = block.one_record(SymtabCode::Blob as u64)?;

            symtab.try_blob(0).map_err(SymtabError::from)?
        };

        Ok(Self(symtab))
    }
}
