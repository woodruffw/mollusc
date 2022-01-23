//! Functionality for mapping the `MODULE_CODE_FUNCTION` record.

use std::convert::TryFrom;

use llvm_constants::CallingConvention;
use llvm_support::{AlignError, Linkage, MaybeAlign, Type, Visibility};
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::block::attributes::AttributeEntry;
use crate::block::type_table::{TypeRef, TypeTableError};
use crate::map::{CtxMappable, MapCtx};
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

    /// Retrieving a string from a string table failed.
    #[error("error while accessing string table")]
    BadStrtab(#[from] StrtabError),

    /// This function has an unknown calling convention.
    #[error("unknown calling convention")]
    CallingConvention(#[from] TryFromPrimitiveError<CallingConvention>),

    /// The function has a bad or unknown type.
    #[error("invalid type")]
    Type(#[from] TypeTableError),

    /// The function has an invalid attribute entry ID.
    #[error("invalid attribute entry ID: {0}")]
    Attribute(u64),

    /// The function has an invalid alignment.
    #[error("invalid alignment")]
    Alignment(#[from] AlignError),

    /// The function has an invalid section table index.
    #[error("invalid section table index: {0}")]
    Section(usize),

    /// The function has an invalid visibility.
    #[error("invalid visibility")]
    Visibility(#[from] TryFromPrimitiveError<Visibility>),

    /// The function has an invalid GC table index.
    #[error("invalid GC table index: {0}")]
    Gc(usize),
}

/// Models the `MODULE_CODE_FUNCTION` record.
#[non_exhaustive]
#[derive(Debug)]
pub struct Function<'ctx> {
    /// The function's name.
    pub name: &'ctx str,

    /// A reference to the function's type in the type table.
    pub ty: &'ctx Type,

    /// The function's calling convention.
    pub calling_convention: CallingConvention,

    /// Whether the function is a declaration, or a full definition (with body).
    pub is_declaration: bool,

    /// The function's linkage.
    pub linkage: Linkage,

    /// The function's attributes, if it has any.
    pub attributes: Option<&'ctx AttributeEntry>,

    /// The function's alignment.
    pub alignment: MaybeAlign,

    /// The function's custom section, if it has one.
    pub section: Option<&'ctx str>,

    /// The function's visibility.
    pub visibility: Visibility,

    /// The function's garbage collector, if it has one.
    pub gc_name: Option<&'ctx str>,
}

impl<'ctx> CtxMappable<'ctx, UnrolledRecord> for Function<'ctx> {
    type Error = FunctionError;

    fn try_map(record: &UnrolledRecord, ctx: &'ctx MapCtx) -> Result<Self, Self::Error> {
        let fields = record.fields();

        if !ctx.use_strtab() {
            return Err(FunctionError::V1Unsupported);
        }

        // Every function record has at least 10 records, corresponding to
        // [strtab_offset, strtab_size, *v1], where v1 has 8 mandatory records:
        // [type, callingconv, isproto, linkage, paramattr, alignment, section, visibility, ...]
        if fields.len() < 10 {
            return Err(FunctionError::TooShort(fields.len()));
        }

        let name = ctx.strtab.read_name(record)?;

        let ty = {
            let typ_ref = TypeRef(fields[2] as usize);
            ctx.type_table.get(&typ_ref)?
        };

        let calling_convention = CallingConvention::try_from(fields[3])?;
        let is_declaration = fields[4] != 0;
        let linkage = Linkage::from(fields[5]);

        let attributes = {
            let paramattr = fields[6];
            // An ID of 0 is a special sentinel for no attributes,
            // so any nonzero ID is a 1-based index.
            if paramattr == 0 {
                None
            } else {
                // NOTE(ww): This is more conservative than LLVM: LLVM treats an
                // unknown attribute ID as an empty set of attributes,
                // rather than a hard failure.
                Some(
                    ctx.attributes
                        .get(paramattr - 1)
                        .ok_or(FunctionError::Attribute(paramattr))?,
                )
            }
        };

        // TODO: Upgrade attributes here? It's what LLVM does.

        let alignment = MaybeAlign::try_from(fields[7] as u8)?;

        let section = match fields[8] as usize {
            0 => None,
            idx => Some(
                ctx.section_table
                    .get(idx - 1)
                    .map(AsRef::as_ref)
                    .ok_or(FunctionError::Section(idx - 1))?,
            ),
        };

        let visibility = Visibility::try_from(fields[9])?;

        // From here, all fields are optional and need to be guarded as such.

        let gc_name = fields
            .get(10)
            .and_then(|idx| match *idx as usize {
                0 => None,
                idx => Some(
                    ctx.gc_table
                        .get(idx - 1)
                        .map(AsRef::as_ref)
                        .ok_or(FunctionError::Gc(idx - 1)),
                ),
            })
            .transpose()?;

        Ok(Self {
            name,
            ty,
            calling_convention,
            is_declaration,
            linkage,
            attributes,
            alignment,
            section,
            visibility,
            gc_name,
        })
    }
}
