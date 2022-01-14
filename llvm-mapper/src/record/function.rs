//! Functionality for mapping the `MODULE_CODE_FUNCTION` record.

use std::convert::TryFrom;

use llvm_constants::CallingConvention;
use llvm_support::Linkage;
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::block::type_table::TypeRef;
use crate::map::{MapCtx, MapCtxError, Mappable};
use crate::record::StrtabError;
use crate::unroll::UnrolledRecord;

/// Errors that can occur when mapping a function record.
#[derive(Debug, Error)]
pub enum FunctionError {
    /// The function record is too short to be well-formed.
    #[error("function record too short: {0} < 10 fields")]
    TooShort(usize),

    /// The function record is in an old unsupported format.
    #[error("unsupported function record format (v1)")]
    V1Unsupported,

    /// Our mapping context was invalid for our operation.
    #[error("invalid mapping context: {0}")]
    BadContext(#[from] MapCtxError),

    /// Retrieving a string from a string table failed.
    #[error("error while accessing string table: {0}")]
    BadStrtab(#[from] StrtabError),

    /// This function has an unknown calling convention.
    #[error("unknown calling convention")]
    CallingConvention(#[from] TryFromPrimitiveError<CallingConvention>),
}

/// Models the `MODULE_CODE_FUNCTION` record.
#[non_exhaustive]
#[derive(Debug)]
pub struct Function {
    name: String,
    typ_ref: TypeRef,
    calling_convention: CallingConvention,
    is_declaration: bool,
    linkage: Linkage,
}

impl Mappable<UnrolledRecord> for Function {
    type Error = FunctionError;

    fn try_map(record: &UnrolledRecord, ctx: &mut MapCtx) -> Result<Self, Self::Error> {
        let fields = record.fields();

        if !ctx.use_strtab()? {
            return Err(FunctionError::V1Unsupported);
        }

        // Every function record has at least 10 records, corresponding to
        // [strtab_offset, strtab_size, *v1], where v1 has 8 mandatory records:
        // [type, callingconv, isproto, linkage, paramattr, alignment, section, visibility, ...]
        if fields.len() < 10 {
            return Err(FunctionError::TooShort(fields.len()));
        }

        let name = ctx.strtab()?.read_name(&record)?.to_owned();

        let typ_ref = TypeRef(fields[2] as usize);
        let calling_convention = CallingConvention::try_from(fields[3])?;
        let is_declaration = fields[3] != 0;
        let linkage = Linkage::from(fields[4]);

        Ok(Self { name, typ_ref, calling_convention, is_declaration, linkage })
    }
}
