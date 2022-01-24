//! Functionality for mapping the `MODULE_CODE_ALIAS` record.

use llvm_support::{Linkage, Type};
use thiserror::Error;

use crate::map::{CtxMappable, MapCtx};
use crate::record::StrtabError;
use crate::unroll::UnrolledRecord;

/// Errors that can occur while mapping an alias record.
#[derive(Debug, Error)]
pub enum AliasError {
    /// The alias record is too short to be well-formed.
    #[error("alias record too short: {0} < 5 fields")]
    TooShort(usize),

    /// The alias record is in an old unsupported format.
    #[error("unsupported alias record format (v1)")]
    V1Unsupported,

    /// Retrieving a string from a string table failed.
    #[error("error while accessing string table")]
    Strtab(#[from] StrtabError),

    /// The function has a bad or unknown type.
    #[error("invalid type table index: {0}")]
    Type(u64),
}

/// Models the `MODULE_CODE_ALIAS` record.
#[derive(Debug)]
pub struct Alias<'ctx> {
    /// The alias's name.
    pub name: &'ctx str,

    /// The alias's type.
    pub ty: &'ctx Type,

    /// The aliasee value index.
    pub value_index: u64,

    /// The alias's linkage.
    pub linkage: Linkage,
}

impl<'ctx> CtxMappable<'ctx, UnrolledRecord> for Alias<'ctx> {
    type Error = AliasError;

    fn try_map(record: &UnrolledRecord, ctx: &'ctx MapCtx) -> Result<Self, Self::Error> {
        let fields = record.fields();

        if !ctx.use_strtab() {
            return Err(AliasError::V1Unsupported);
        }

        // Every alias record has at least 5 fields, corresponding to
        // [strtab_offset, strtab_size, *v1], where v1 has 3 mandatory fields:
        // [alias type, aliasee value#, linkage, ...]
        if fields.len() < 5 {
            return Err(AliasError::TooShort(fields.len()));
        }

        let name = ctx.strtab.read_name(record)?;
        let ty = ctx
            .type_table
            .get(fields[2])
            .ok_or(AliasError::Type(fields[2]))?;
        let value_index = fields[3];
        let linkage = Linkage::from(fields[4]);

        Ok(Alias {
            name,
            ty,
            value_index,
            linkage,
        })
    }
}
