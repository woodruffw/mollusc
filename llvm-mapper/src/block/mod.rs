//! Functionality for mapping individual blocks.

pub mod attributes;
pub mod function;
pub mod identification;
pub mod module;
pub mod strtab;
pub mod symtab;
pub mod type_table;
pub mod vst;

use std::convert::TryFrom;

use llvm_support::bitcodes::{IrBlockId, ReservedBlockId};
use thiserror::Error;

pub use self::attributes::*;
pub use self::identification::*;
pub use self::module::*;
pub use self::strtab::*;
pub use self::symtab::*;
pub use self::type_table::*;

/// Potential errors when mapping a single bitstream block.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum BlockMapError {
    /// We couldn't map the identification block.
    #[error("error while mapping identification block")]
    Identification(#[from] IdentificationError),

    /// We couldn't map the module block.
    #[error("error while mapping module")]
    Module(#[from] ModuleError),

    /// We couldn't map the string table.
    #[error("error while mapping string table")]
    Strtab(#[from] StrtabError),

    /// We couldn't map the symbol table.
    #[error("error while mapping symbol table")]
    Symtab(#[from] SymtabError),
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

impl From<ReservedBlockId> for BlockId {
    fn from(v: ReservedBlockId) -> Self {
        Self::Reserved(v)
    }
}

impl From<IrBlockId> for BlockId {
    fn from(v: IrBlockId) -> Self {
        Self::Ir(v)
    }
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
