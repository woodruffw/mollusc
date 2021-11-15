//! Functionality for mapping the `PARAMATTR_BLOCK` and `PARAMATTR_GROUP_BLOCK` blocks.

use std::convert::TryFrom;

use llvm_constants::{AttributeCode, IrBlockId};
use llvm_support::{Align, AttributeId, AttributeKind};
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::block::{BlockMapError, IrBlock};
use crate::map::MapCtx;
use crate::record::RecordMapError;
use crate::unroll::{UnrolledBlock, UnrolledRecord};

/// Errors that can occur when mapping attribute blocks.
#[derive(Debug, Error)]
pub enum AttributeError {
    /// An unknown record code was seen.
    #[error("unknown attribute code")]
    UnknownAttributeCode(#[from] TryFromPrimitiveError<AttributeCode>),
    /// An unknown attribute kind (format) was seen.
    #[error("unknown attribute kind")]
    UnknownAttributeKind(#[from] TryFromPrimitiveError<AttributeKind>),
    /// The given code was seen in an unexpected block.
    #[error("wrong block for code: {0:?}")]
    WrongBlock(AttributeCode),
    /// The attribute couldn't be constructed because of missing fields.
    #[error("attribute structure too short")]
    TooShort,
    /// The attribute has an invalid string key or string balue.
    #[error("bad attribute string")]
    BadString,
    /// The attribute has an unknown (integral) ID.
    #[error("unknown attribute ID")]
    UnknownAttributeId(#[from] TryFromPrimitiveError<AttributeId>),
}

/// Represents a single, concrete LLVM attribute.
#[non_exhaustive]
#[derive(Debug, PartialEq)]
pub enum Attribute {
    /// `align(<n>)`
    Alignment(Align),
    /// `alwaysinline`
    AlwaysInline,
    /// `byval`
    ByVal,
    /// `inlinehint`
    InlineHint,
    /// `inreg`
    InReg,
    /// `minsize`
    MinSize,
    /// `naked`
    Naked,
    /// `nest`
    Nest,
    /// `noalias`
    NoAlias,
    /// `nobuiltin`
    NoBuiltin,
    /// `nocapture`
    NoCapture,
    /// `noduplicate`
    NoDuplicate,
    /// `noimplicitfloat`
    NoImplicitFloat,
    /// `noinline`
    NoInline,
    /// `nonlazybind`
    NonLazyBind,
    /// `noredzone`
    NoRedZone,
    /// `noreturn`
    NoReturn,
    /// `nounwind`
    NoUnwind,
    /// `optsize`
    OptimizeForSize,
    /// `readnone`
    ReadNone,
    /// `readonly`
    ReadOnly,
    /// `returned`
    Returned,
    /// `returns_twice`
    ReturnsTwice,
    /// `signext`
    SExt,
    /// `alignstack(<n>)`
    StackAlignment(Align),
    /// `ssp`
    StackProtect,
    /// `sspreq`
    StackProtectReq,
    /// `sspstrong`
    StackProtectStrong,
    /// `sret`
    StructRet,
    /// `sanitize_address`
    SanitizeAddress,
    /// `sanitize_thread`
    SanitizeThread,
    /// `sanitize_memory`
    SanitizeMemory,
    /// `uwtable`
    UwTable,
    /// `zeroext`
    ZExt,
    /// `builtin`
    Builtin,
    /// `cold`
    Cold,
    /// `optnone`
    OptimizeNone,
    /// `inalloca`
    InAlloca,
    /// `nonnull`
    NonNull,
    /// `jumptable`
    JumpTable,
    /// `dereferenceable(<n>)`
    Dereferenceable(u64),
    /// `dereferenceable_or_null(<n>)`
    DereferenceableOrNull(u64),
    /// `convergent`
    Convergent,
    /// `safestack`
    SafeStack,
    /// `argmemonly`
    ArgMemOnly,
    /// `swiftself`
    SwiftSelf,
    /// `swifterror`
    SwiftError,
    /// `norecurse`
    NoRecurse,
    /// `inaccessiblememonly`
    InaccessiblememOnly,
    /// `inaccessiblememonly_or_argmemonly`
    InaccessiblememOrArgmemonly,
    /// `allocsize(<EltSizeParam>[, <NumEltsParam>])`
    AllocSize(u32, u32),
    /// `writeonly`
    WriteOnly,
    /// `speculatable`
    Speculatable,
    /// `strictfp`
    StrictFp,
    /// `sanitize_hwaddress`
    SanitizeHwAddress,
    /// `nocf_check`
    NoCfCheck,
    /// `optforfuzzing`
    OptForFuzzing,
    /// `shadowcallstack`
    Shadowcallstack,
    /// `speculative_load_hardening`
    SpeculativeLoadHardening,
    /// `immarg`
    ImmArg,
    /// `willreturn`
    WillReturn,
    /// `nofree`
    NoFree,
    /// `nosync`
    NoSync,
    /// `sanitize_memtag`
    SanitizeMemtag,
    /// `preallocated`
    Preallocated,
    /// `no_merge`
    NoMerge,
    /// `null_pointer_is_valid`
    NullPointerIsValid,
    /// `noundef`
    NoUndef,
    /// `byref`
    ByRef,
    /// `mustprogress`
    MustProgress,
    /// `no_callback`
    NoCallback,
    /// `hot`
    Hot,
    /// `no_profile`
    NoProfile,
    /// `vscale_range(<Min>[, <Max>])`
    VScaleRange(u32, u32),
    /// `swift_async`
    SwiftAsync,
    /// `nosanitize_coverage`
    NoSanitizeCoverage,
    /// `elementtype`
    ElementType,
    /// `disable_sanitizer_instrumentation`
    DisableSanitizerInstrumentation,
    /// An arbitrary string attribute.
    Str(String),
    /// An arbitrary string attribute with a string value.
    StrKeyValue(String, String),
}

impl Attribute {
    /// Parse a new `Attribute` from the given record at the given start index, returning
    /// a tuple of the number of fields consumed and the parsed result.
    fn from_record(start: usize, record: &UnrolledRecord) -> Result<(usize, Self), AttributeError> {
        let mut fields = record.fields().iter().skip(start);
        let mut fieldcount = 0;

        macro_rules! next {
            () => {
                if let Some(field) = fields.next() {
                    fieldcount += 1;
                    Ok(*field)
                } else {
                    Err(AttributeError::TooShort)
                }
            };
        }

        macro_rules! take_string {
            // NOTE(ww): Weird double-brace to make sure the macro expands as a full expression.
            () => {{
                let str_bytes = fields
                    .take_while(|f| **f != 0)
                    .map(|f| u8::try_from(*f))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|_| AttributeError::BadString)?;

                if str_bytes.is_empty() {
                    Err(AttributeError::BadString)
                } else {
                    let result =
                        String::from_utf8(str_bytes).map_err(|_| AttributeError::BadString)?;
                    fieldcount += result.as_bytes().len();

                    Ok(result)
                }
            }};
        }

        // Each attribute's fields look like this:
        //  [kind, key[...], [value[...]]]
        // ...where `kind` indicates the general attribute structure
        // (integral or string, single-value or key-value).
        let kind = AttributeKind::try_from(next!()?)?;
        match kind {
            AttributeKind::Int => {
                // Integer attributes: one key field, nothing else.
                let _key = AttributeId::try_from(next!()?)?;
                unimplemented!()
            }
            AttributeKind::IntKeyValue => {
                // Integer key-value attributes: one key, one integer value.
                let _key = AttributeId::try_from(next!()?)?;
                let _value = next!()?;

                unimplemented!()
            }
            AttributeKind::StrKey => {
                // String attributes: one string key field, nothing else.
                let _key = take_string!()?;

                unimplemented!()
            }
            AttributeKind::StrKeyValue => {
                // String key-value attributes: one string key field, one string value field.
                let _key = take_string!()?;
                // let _value = take_string!()?;

                unimplemented!()
            }
        }
    }
}

/// Maps all attributes in an IR module.
///
/// This is a zero-sized type that, when mapped, updates the associated
/// [`MapCtx`](MapCtx) as appropriate.
pub struct Attributes;

impl IrBlock for Attributes {
    const BLOCK_ID: IrBlockId = IrBlockId::ParamAttr;

    fn try_map_inner(_block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        unimplemented!();
    }
}

/// Maps all attribute groups in an IR module.
///
/// This is a zero-sized type that, when mapped, updates the associated
/// [`MapCtx`](MapCtx) as appropriate.
pub struct AttributeGroups;

impl IrBlock for AttributeGroups {
    const BLOCK_ID: IrBlockId = IrBlockId::ParamAttrGroup;

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        for record in block.all_records() {
            let code = AttributeCode::try_from(record.code()).map_err(AttributeError::from)?;

            if code != AttributeCode::GroupCodeEntry {
                return Err(AttributeError::WrongBlock(code).into());
            }

            // Structure: [grpid, paramidx, <attr0>, <attr1>, ...]
            // Every group record must have at least one attribute.
            if record.fields().len() < 3 {
                return Err(RecordMapError::BadRecordLayout(format!(
                    "too few fields in {:?}, expected {} >= 3",
                    code,
                    record.fields().len()
                ))
                .into());
            }

            // Panic safety: We check for at least three fields above.
            let _grpid = record.fields()[0];
            let _paramidx = record.fields()[1];

            // Each attribute in the group can potentially span multiple fields
            // in the record. Keep track of our field index to ensure that we
            // fully consume the records into a list of attributes.
            let mut fieldidx = 2;
            let mut attrs = vec![];
            while fieldidx < record.fields().len() {
                let (count, attr) = Attribute::from_record(fieldidx, &record)?;

                attrs.push(attr);
                fieldidx += count;
            }

            // Sanity check: we should have consumed every single record.
            if fieldidx != record.fields().len() {
                return Err(RecordMapError::BadRecordLayout(format!(
                    "under/overconsumed fields in attribute group record ({} fields, {} consumed)",
                    fieldidx,
                    record.fields().len(),
                ))
                .into());
            }
        }

        Ok(AttributeGroups)
    }
}
