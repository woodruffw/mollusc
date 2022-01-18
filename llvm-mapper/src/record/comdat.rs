//! Functionality for mapping the `MODULE_CODE_COMDAT` record.

use std::convert::TryInto;

use llvm_support::StrtabRef;
use num_enum::TryFromPrimitive;

use crate::map::{CtxMappable, MapCtx};
use crate::record::RecordMapError;
use crate::unroll::UnrolledRecord;

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
pub struct Comdat<'ctx> {
    /// The selection kind for this COMDAT.
    pub selection_kind: ComdatSelectionKind,
    /// The COMDAT key.
    pub name: &'ctx str,
}

impl<'ctx> CtxMappable<'ctx, UnrolledRecord> for Comdat<'ctx> {
    type Error = RecordMapError;

    fn try_map(record: &UnrolledRecord, ctx: &'ctx MapCtx) -> Result<Self, Self::Error> {
        if !ctx.use_strtab() {
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
            ctx.strtab.try_get(&sref)?
        };
        let selection_kind: ComdatSelectionKind = record.fields()[2].try_into().map_err(|e| {
            RecordMapError::BadRecordLayout(format!("invalid COMDAT selection kind: {:?}", e))
        })?;

        Ok(Self {
            selection_kind,
            name: name,
        })
    }
}
