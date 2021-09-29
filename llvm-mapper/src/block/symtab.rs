//! Functionality for mapping the `SYMTAB_BLOCK` block.

use llvm_constants::{IrBlockId, SymtabCode};

use crate::block::{BlockMapError, IrBlock};
use crate::map::MapCtx;
use crate::unroll::UnrolledBlock;

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

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        let symtab = {
            let symtab = block.one_record(SymtabCode::Blob as u64)?;

            symtab.try_blob(0)?
        };

        Ok(Self(symtab))
    }
}
