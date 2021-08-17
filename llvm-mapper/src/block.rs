//! Structures for mapping from bitstream blocks to LLVM models.

use std::convert::TryFrom;

use llvm_constants::{IrBlockId, ReservedBlockId};

use crate::error::Error;
use crate::unroll::UnrolledBlock;

/// A holistic model of all possible block IDs, spanning reserved, IR, and unknown IDs.
#[derive(Debug, PartialEq)]
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

trait IrBlock {
    const BLOCK_ID: IrBlockId;

    fn try_map_inner(block: UnrolledBlock) -> Result<Self, Error>
    where
        Self: Sized;
}

trait MappableBlock {
    fn try_map(block: UnrolledBlock) -> Result<Self, Error>
    where
        Self: Sized;
}

impl<T: IrBlock> MappableBlock for T {
    fn try_map(block: UnrolledBlock) -> Result<Self, Error> {
        if block.id != BlockId::Ir(T::BLOCK_ID) {
            return Err(Error::BadBlockMap(format!(
                "can't map {:?} into {:?}",
                block.id,
                Identification::BLOCK_ID
            )));
        }

        IrBlock::try_map_inner(block)
    }
}

/// Models the `IDENTIFICATION_BLOCK` block.
#[non_exhaustive]
pub struct Identification {
    /// The name of the "producer" for this bitcode.
    pub code: String,
    /// The compatibility epoch.
    pub epoch: u64,
}

impl IrBlock for Identification {
    const BLOCK_ID: IrBlockId = IrBlockId::Identification;

    fn try_map_inner(block: UnrolledBlock) -> Result<Self, Error> {
        // Scan our records, looking for ones we know.
        // We don't expect any sub-blocks in the IDENTIFICATION_BLOCK, so we don't scanning them.
        for _record in block.records {}

        unimplemented!();
    }
}
