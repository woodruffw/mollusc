//! Functionality for mapping individual blocks.

pub mod attributes;
pub mod identification;
pub mod module;
pub mod strtab;
pub mod symtab;
pub mod type_table;

use std::convert::TryFrom;

use llvm_constants::{IrBlockId, ReservedBlockId};
use thiserror::Error;

pub use self::attributes::*;
pub use self::identification::*;
pub use self::module::*;
pub use self::strtab::*;
pub use self::symtab::*;
pub use self::type_table::*;
use crate::map::{MapCtxError, PartialCtxMappable, PartialMapCtx};
use crate::record::RecordMapError;
use crate::unroll::UnrolledBlock;

/// Potential errors when mapping a single bitstream block.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum BlockMapError {
    /// Parsing a record failed, for some internal reason.
    #[error("error while mapping record")]
    BadRecord(#[from] RecordMapError),

    /// Our mapping context was invalid for our operation.
    #[error("invalid mapping context")]
    BadContext(#[from] MapCtxError),

    /// We couldn't map a block, for any number of reasons.
    #[error("error while mapping block: {0}")]
    BadBlockMap(String),

    /// We expected exactly one record with this code in this block.
    #[error("expected exactly one record of code {0} in block {1:?}")]
    BlockRecordMismatch(u64, BlockId),

    /// We expected exactly one sub-block with this ID in this block.
    #[error("expected exactly one block of ID {0:?} in block {1:?}")]
    BlockBlockMismatch(BlockId, BlockId),

    /// We couldn't map the type table.
    #[error("error while mapping type table")]
    BadTypeTable(#[from] TypeTableError),

    /// We couldn't map one of the attribute blocks.
    #[error("error while mapping attributes")]
    BadAttributes(#[from] AttributeError),

    /// We encountered an unsupported feature or layout.
    #[error("unsupported: {0}")]
    Unsupported(String),
}

/// A holistic model of all possible block IDs, spanning reserved, IR, and unknown IDs.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum BlockId {
    /// A block ID that's been reserved by LLVM. Reserved IDs are internal, and cannot be mapped here.
    Reserved(ReservedBlockId),
    /// A block ID used by LLVM IR.
    Ir(IrBlockId),
    /// An unknown block ID. Unknown IDs cannot be mapped.
    Unknown(u64),
}

impl From<u64> for BlockId {
    fn from(value: u64) -> Self {
        // Try to turn `value` into each of our known kinds of block IDs, in order
        // of precedence.
        ReservedBlockId::try_from(value).map_or_else(
            |_| IrBlockId::try_from(value).map_or_else(|_| BlockId::Unknown(value), BlockId::Ir),
            BlockId::Reserved,
        )
    }
}

/// A trait implemented by all blocks that correspond to IR models, allowing them
/// to be mapped into their corresponding model.
pub(crate) trait IrBlock: Sized {
    /// The `IrBlockId` that corresponds to this IR model.
    const BLOCK_ID: IrBlockId;

    /// Attempt to map the given block to the implementing type, returning an error if mapping fails.
    ///
    /// This is an interior trait that shouldn't be used directly.
    fn try_map_inner(block: &UnrolledBlock, ctx: &mut PartialMapCtx)
        -> Result<Self, BlockMapError>;
}

impl<T: IrBlock> PartialCtxMappable<UnrolledBlock> for T {
    type Error = BlockMapError;

    fn try_map(block: &UnrolledBlock, ctx: &mut PartialMapCtx) -> Result<Self, Self::Error> {
        if block.id != BlockId::Ir(T::BLOCK_ID) {
            return Err(BlockMapError::BadBlockMap(format!(
                "can't map {:?} into {:?}",
                block.id,
                Identification::BLOCK_ID
            )));
        }

        IrBlock::try_map_inner(block, ctx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_blockid_from_u64() {
        assert_eq!(
            BlockId::from(0),
            BlockId::Reserved(ReservedBlockId::BlockInfo)
        );
        assert_eq!(
            BlockId::from(7),
            BlockId::Reserved(ReservedBlockId::Reserved7)
        );
        assert_eq!(BlockId::from(8), BlockId::Ir(IrBlockId::Module));
        assert_eq!(BlockId::from(2384629342), BlockId::Unknown(2384629342));
    }
}
