//! Functionality for mapping the `MODULE_CODE_COMDAT` record.

use std::convert::TryInto;

use llvm_support::StrtabRef;
use num_enum::{TryFromPrimitive, TryFromPrimitiveError};
use thiserror::Error;

use crate::block::strtab::StrtabError;
use crate::map::{CtxMappable, MapCtx};
use crate::unroll::UnrolledRecord;

/// Errors that can occur when mapping a COMDAT record.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum ComdatError {
    /// The COMDAT record is in an old unsupported format.
    #[error("unsupported COMDAT record format (v1)")]
    V1Unsupported,

    /// The COMDAT record is too short.
    #[error("COMDAT record doesn't have enough fields ({0} < 3)")]
    TooShort(usize),

    /// We couldn't get the COMDAT's name from the string table.
    #[error("error while accessing COMDAT name: {0}")]
    Name(#[from] StrtabError),

    /// The COMDAT's selection kind is invalid or unknown.
    #[error("unknown or invalid COMDAT selection kind: {0}")]
    SelectionKind(#[from] TryFromPrimitiveError<SelectionKind>),
}

/// The different kinds of COMDAT selections.
///
/// This is a nearly direct copy of LLVM's `SelectionKind`; see `IR/Comdat.h`.
#[non_exhaustive]
#[derive(Debug, TryFromPrimitive)]
#[repr(u64)]
pub enum SelectionKind {
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
pub struct Comdat<'ctx> {
    /// The selection kind for this COMDAT.
    pub selection_kind: SelectionKind,
    /// The COMDAT key.
    pub name: &'ctx str,
}

impl<'ctx> CtxMappable<'ctx, UnrolledRecord> for Comdat<'ctx> {
    type Error = ComdatError;

    fn try_map(record: &UnrolledRecord, ctx: &'ctx MapCtx) -> Result<Self, Self::Error> {
        if !ctx.use_strtab() {
            return Err(ComdatError::V1Unsupported);
        }

        // v2: [strtab offset, strtab size, selection kind]
        if record.fields().len() != 3 {
            return Err(ComdatError::TooShort(record.fields().len()));
        }

        // Index safety: we check for at least 3 fields above.
        let name = {
            let sref: StrtabRef = (record.fields()[0], record.fields()[1]).into();
            ctx.strtab.try_get(&sref)?
        };
        let selection_kind: SelectionKind = record.fields()[2].try_into()?;

        Ok(Self {
            selection_kind,
            name: name,
        })
    }
}
