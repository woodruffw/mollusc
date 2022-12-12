//! Functionality for mapping the `SYMTAB_BLOCK` block.

use std::convert::TryFrom;

use llvm_support::bitcodes::SymtabCode;
use thiserror::Error;

use crate::map::MapError;
use crate::record::RecordBlobError;
use crate::unroll::Block;

/// Errors that can occur when accessing a symbol table.
#[derive(Debug, Error)]
pub enum SymtabError {
    /// The symbol table is missing its blob.
    #[error("malformed symbol table: missing blob")]
    MissingBlob,

    /// The blob containing the symbol table is invalid.
    #[error("invalid string table: {0}")]
    InvalidBlob(#[from] RecordBlobError),

    /// A generic mapping error occured.
    #[error("mapping error in string table")]
    Map(#[from] MapError),
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

impl TryFrom<&'_ Block> for Symtab {
    type Error = SymtabError;

    fn try_from(block: &'_ Block) -> Result<Self, Self::Error> {
        let symtab = block
            .records
            .one(SymtabCode::Blob as u64)
            .ok_or(SymtabError::MissingBlob)
            .and_then(|r| r.try_blob(0).map_err(SymtabError::from))?;

        Ok(Self(symtab))
    }
}
