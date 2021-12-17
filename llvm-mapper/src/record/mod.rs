//! Structures for mapping from bitstream records to LLVM models.
//!
//! Depending on their importance or complexity, not every record is given a dedicated
//! structure or mapping implementation. Simpler records are mapped inline within their
//! blocks.

pub mod datalayout;

use std::convert::TryInto;

use llvm_support::StrtabRef;
use num_enum::TryFromPrimitive;
use thiserror::Error;

pub use self::datalayout::*;
use crate::block::StrtabError;
use crate::map::{MapCtx, MapCtxError, Mappable};
use crate::unroll::UnrolledRecord;

/// Potential errors when mapping a single bitstream record.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum RecordMapError {
    /// Parsing the datalayout specification failed.
    #[error("error while parsing datalayout: {0}")]
    DataLayout(#[from] DataLayoutParseError),

    /// We couldn't interpret a record field, for any number of reasons.
    #[error("error while decoding record field: {0}")]
    BadField(String),

    /// We encountered a record layout we didn't understand.
    #[error("error while mapping record: {0}")]
    BadRecordLayout(String),

    /// Our mapping context was invalid for our operation.
    #[error("invalid mapping context: {0}")]
    BadContext(#[from] MapCtxError),

    /// Retrieving a string from a string table failed.
    #[error("error while accessing string table: {0}")]
    BadStrtab(#[from] StrtabError),

    /// We encountered an unsupported feature or layout.
    #[error("unsupported: {0}")]
    Unsupported(String),
}

/// The different kinds of COMDAT selections.
///
/// This is a nearly direct copy of LLVM's `SelectionKind`; see `IR/Comdat.h`.
#[non_exhaustive]
#[derive(Debug, TryFromPrimitive)]
#[repr(u64)]
pub enum ComdatSelectionKind {
    /// The linker may choose any COMDAT.
    Any,
    /// The data referenced by the COMDAT must be the same.
    ExactMatch,
    /// The linker will choose the largest COMDAT.
    Largest,
    /// No deduplication is performed.
    NoDeduplicate,
    /// The data referenced by the COMDAT must be the same size.
    SameSize,
}

/// Models the `MODULE_CODE_COMDAT` record.
#[non_exhaustive]
#[derive(Debug)]
pub struct Comdat {
    /// The selection kind for this COMDAT.
    pub selection_kind: ComdatSelectionKind,
    /// The COMDAT key.
    pub name: String,
}

impl Mappable<UnrolledRecord> for Comdat {
    type Error = RecordMapError;

    fn try_map(record: &UnrolledRecord, ctx: &mut MapCtx) -> Result<Self, Self::Error> {
        if !ctx.use_strtab()? {
            return Err(RecordMapError::Unsupported(
                "v1 COMDAT records are not supported".into(),
            ));
        }

        // v2: [strtab offset, strtab size, selection kind]
        if record.fields().len() != 3 {
            return Err(RecordMapError::BadRecordLayout(format!(
                "expected exactly 3 fields in COMDAT record, got {}",
                record.fields().len()
            )));
        }

        // Index safety: we check for at least 3 fields above.
        let name = {
            let sref: StrtabRef = (record.fields()[0], record.fields()[1]).into();
            ctx.strtab()?.try_get(&sref)?
        };
        let selection_kind: ComdatSelectionKind = record.fields()[2].try_into().map_err(|e| {
            RecordMapError::BadRecordLayout(format!("invalid COMDAT selection kind: {:?}", e))
        })?;

        Ok(Self {
            selection_kind,
            name: name.into(),
        })
    }
}
