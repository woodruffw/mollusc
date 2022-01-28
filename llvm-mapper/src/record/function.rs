//! Functionality for mapping the `MODULE_CODE_FUNCTION` record.

use std::convert::TryFrom;

use llvm_support::{
    AlignError, CallingConvention, DllStorageClass, Linkage, MaybeAlign, Type, UnnamedAddr,
    Visibility,
};
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::block::attributes::AttributeEntry;
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
    Strtab(#[from] StrtabError),

    /// This function has an unknown calling convention.
    #[error("unknown calling convention")]
    CallingConvention(#[from] TryFromPrimitiveError<CallingConvention>),

    /// The function has a bad or unknown type.
    #[error("invalid type table index: {0}")]
    Type(u64),

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

    /// The function has an invalid DLL storage class.
    #[error("invalid storage class")]
    DllStorageClass(#[from] TryFromPrimitiveError<DllStorageClass>),
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

    /// The function's `unnamed_addr` specifier.
    pub unnamed_addr: UnnamedAddr,

    /// The function's DLL storage class.
    pub storage_class: DllStorageClass,
}

impl<'ctx> CtxMappable<'ctx, UnrolledRecord> for Function<'ctx> {
    type Error = FunctionError;

    fn try_map(record: &UnrolledRecord, ctx: &'ctx MapCtx) -> Result<Self, Self::Error> {
        let fields = record.fields();

        if !ctx.use_strtab() {
            return Err(FunctionError::V1Unsupported);
        }

        // Every function record has at least 10 fields, corresponding to
        // [strtab_offset, strtab_size, *v1], where v1 has 8 mandatory fields:
        // [type, callingconv, isproto, linkage, paramattr, alignment, section, visibility, ...]
        if fields.len() < 10 {
            return Err(FunctionError::TooShort(fields.len()));
        }

        let name = ctx.strtab.read_name(record)?;
        let ty = ctx
            .type_table
            .get(fields[2])
            .ok_or(FunctionError::Type(fields[2]))?;
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

        let unnamed_addr = fields
            .get(11)
            .copied()
            .map(UnnamedAddr::from)
            .unwrap_or(UnnamedAddr::None);

        // fields[12]: prologuedata

        let storage_class = fields.get(13).map_or_else(
            || Ok(DllStorageClass::Default),
            |v| DllStorageClass::try_from(*v),
        )?;

        // fields[14]: comdat
        // fields[15]: prefixdata
        // fields[16]: personalityfn
        // fields[16]: preemptionspecifier

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
            unnamed_addr,
            storage_class,
        })
    }
}
