//! Functionality for mapping the `PARAMATTR_BLOCK` and `PARAMATTR_GROUP_BLOCK` blocks.

use std::convert::{TryFrom, TryInto};

use llvm_constants::{AttributeCode, IrBlockId};
use llvm_support::{Align, AttributeId, AttributeKind};
use num_enum::{TryFromPrimitive, TryFromPrimitiveError};
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
    /// The attribute's ID doesn't match the format supplied.
    #[error("malformed attribute (format doesn't match ID): {0}: {1:?}")]
    AttributeMalformed(&'static str, AttributeId),
}

/// Represents the "enum" attributes, i.e. those with a single integer identifier.
#[non_exhaustive]
#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum EnumAttribute {
    /// `alwaysinline`
    AlwaysInline = AttributeId::AlwaysInline as u64,
    /// `byval`
    ByVal = AttributeId::ByVal as u64,
    /// `inlinehint`
    InlineHint = AttributeId::InlineHint as u64,
    /// `inreg`
    InReg = AttributeId::InReg as u64,
    /// `minsize`
    MinSize = AttributeId::MinSize as u64,
    /// `naked`
    Naked = AttributeId::Naked as u64,
    /// `nest`
    Nest = AttributeId::Nest as u64,
    /// `noalias`
    NoAlias = AttributeId::NoAlias as u64,
    /// `nobuiltin`
    NoBuiltin = AttributeId::NoBuiltin as u64,
    /// `nocapture`
    NoCapture = AttributeId::NoCapture as u64,
    /// `noduplicate`
    NoDuplicate = AttributeId::NoDuplicate as u64,
    /// `noimplicitfloat`
    NoImplicitFloat = AttributeId::NoImplicitFloat as u64,
    /// `noinline`
    NoInline = AttributeId::NoInline as u64,
    /// `nonlazybind`
    NonLazyBind = AttributeId::NonLazyBind as u64,
    /// `noredzone`
    NoRedZone = AttributeId::NoRedZone as u64,
    /// `noreturn`
    NoReturn = AttributeId::NoReturn as u64,
    /// `nounwind`
    NoUnwind = AttributeId::NoUnwind as u64,
    /// `optsize`
    OptimizeForSize = AttributeId::OptimizeForSize as u64,
    /// `readnone`
    ReadNone = AttributeId::ReadNone as u64,
    /// `readonly`
    ReadOnly = AttributeId::ReadOnly as u64,
    /// `returned`
    Returned = AttributeId::Returned as u64,
    /// `returns_twice`
    ReturnsTwice = AttributeId::ReturnsTwice as u64,
    /// `signext`
    SExt = AttributeId::SExt as u64,
    /// `ssp`
    StackProtect = AttributeId::StackProtect as u64,
    /// `sspreq`
    StackProtectReq = AttributeId::StackProtectReq as u64,
    /// `sspstrong`
    StackProtectStrong = AttributeId::StackProtectStrong as u64,
    /// `sret`
    StructRet = AttributeId::StructRet as u64,
    /// `sanitize_address`
    SanitizeAddress = AttributeId::SanitizeAddress as u64,
    /// `sanitize_thread`
    SanitizeThread = AttributeId::SanitizeThread as u64,
    /// `sanitize_memory`
    SanitizeMemory = AttributeId::SanitizeMemory as u64,
    /// `uwtable`
    UwTable = AttributeId::UwTable as u64,
    /// `zeroext`
    ZExt = AttributeId::ZExt as u64,
    /// `builtin`
    Builtin = AttributeId::Builtin as u64,
    /// `cold`
    Cold = AttributeId::Cold as u64,
    /// `optnone`
    OptimizeNone = AttributeId::OptimizeNone as u64,
    /// `inalloca`
    InAlloca = AttributeId::InAlloca as u64,
    /// `nonnull`
    NonNull = AttributeId::NonNull as u64,
    /// `jumptable`
    JumpTable = AttributeId::JumpTable as u64,
    /// `convergent`
    Convergent = AttributeId::Convergent as u64,
    /// `safestack`
    SafeStack = AttributeId::SafeStack as u64,
    /// `argmemonly`
    ArgMemOnly = AttributeId::ArgMemOnly as u64,
    /// `swiftself`
    SwiftSelf = AttributeId::SwiftSelf as u64,
    /// `swifterror`
    SwiftError = AttributeId::SwiftError as u64,
    /// `norecurse`
    NoRecurse = AttributeId::NoRecurse as u64,
    /// `inaccessiblememonly`
    InaccessiblememOnly = AttributeId::InaccessiblememOnly as u64,
    /// `inaccessiblememonly_or_argmemonly`
    InaccessiblememOrArgmemonly = AttributeId::InaccessiblememOrArgmemonly as u64,
    /// `writeonly`
    WriteOnly = AttributeId::WriteOnly as u64,
    /// `speculatable`
    Speculatable = AttributeId::Speculatable as u64,
    /// `strictfp`
    StrictFp = AttributeId::StrictFp as u64,
    /// `sanitize_hwaddress`
    SanitizeHwAddress = AttributeId::SanitizeHwAddress as u64,
    /// `nocf_check`
    NoCfCheck = AttributeId::NoCfCheck as u64,
    /// `optforfuzzing`
    OptForFuzzing = AttributeId::OptForFuzzing as u64,
    /// `shadowcallstack`
    Shadowcallstack = AttributeId::Shadowcallstack as u64,
    /// `speculative_load_hardening`
    SpeculativeLoadHardening = AttributeId::SpeculativeLoadHardening as u64,
    /// `immarg`
    ImmArg = AttributeId::ImmArg as u64,
    /// `willreturn`
    WillReturn = AttributeId::WillReturn as u64,
    /// `nofree`
    NoFree = AttributeId::NoFree as u64,
    /// `nosync`
    NoSync = AttributeId::NoSync as u64,
    /// `sanitize_memtag`
    SanitizeMemtag = AttributeId::SanitizeMemtag as u64,
    /// `preallocated`
    Preallocated = AttributeId::Preallocated as u64,
    /// `no_merge`
    NoMerge = AttributeId::NoMerge as u64,
    /// `null_pointer_is_valid`
    NullPointerIsValid = AttributeId::NullPointerIsValid as u64,
    /// `noundef`
    NoUndef = AttributeId::NoUndef as u64,
    /// `byref`
    ByRef = AttributeId::ByRef as u64,
    /// `mustprogress`
    MustProgress = AttributeId::MustProgress as u64,
    /// `no_callback`
    NoCallback = AttributeId::NoCallback as u64,
    /// `hot`
    Hot = AttributeId::Hot as u64,
    /// `no_profile`
    NoProfile = AttributeId::NoProfile as u64,
    /// `swift_async`
    SwiftAsync = AttributeId::SwiftAsync as u64,
    /// `nosanitize_coverage`
    NoSanitizeCoverage = AttributeId::NoSanitizeCoverage as u64,
    /// `elementtype`
    ElementType = AttributeId::ElementType as u64,
    /// `disable_sanitizer_instrumentation`
    DisableSanitizerInstrumentation = AttributeId::DisableSanitizerInstrumentation as u64,
}

impl TryFrom<AttributeId> for EnumAttribute {
    type Error = AttributeError;

    fn try_from(value: AttributeId) -> Result<Self, Self::Error> {
        value
            .try_into()
            .map_err(|_| AttributeError::AttributeMalformed("non-enum attribute ID given", value))
    }
}

/// Represents an integral attribute, i.e. an attribute that carries (at least) one integer value with it.
#[non_exhaustive]
#[derive(Debug, PartialEq)]
pub enum IntAttribute {
    /// `align(<n>)`
    Alignment(Align),
    /// `alignstack(<n>)`
    StackAlignment(Align),
    /// `dereferenceable(<n>)`
    Dereferenceable(u64),
    /// `dereferenceable_or_null(<n>)`
    DereferenceableOrNull(u64),
    /// `allocsize(<EltSizeParam>[, <NumEltsParam>])`
    AllocSize(u32, u32),
    /// `vscale_range(<Min>[, <Max>])`
    VScaleRange(u32, u32),
}

impl TryFrom<(AttributeId, u64)> for IntAttribute {
    type Error = AttributeError;

    fn try_from((key, value): (AttributeId, u64)) -> Result<Self, Self::Error> {
        // Test if it's an enum attribute. If it is, we know it can't be an integer attribute
        // and any fallthrough in our match below is unsupported rather than malformed.
        if EnumAttribute::try_from(key).is_err() {
            return Err(AttributeError::AttributeMalformed(
                "expected int attribute, but given enum ID",
                key,
            ));
        }

        Ok(match key {
            AttributeId::Alignment => {
                let value = u8::try_from(value).map_err(|_| {
                    AttributeError::AttributeMalformed(
                        "attribute value too large (invalid alignment)",
                        key,
                    )
                })?;

                IntAttribute::Alignment(
                    Align::from_shift(value).map_err(|_| {
                        AttributeError::AttributeMalformed("invalid alignment", key)
                    })?,
                )
            }
            AttributeId::StackAlignment => {
                let value = u8::try_from(value).map_err(|_| {
                    AttributeError::AttributeMalformed(
                        "attribute value too large (invalid alignment)",
                        key,
                    )
                })?;

                IntAttribute::StackAlignment(
                    Align::from_shift(value).map_err(|_| {
                        AttributeError::AttributeMalformed("invalid alignment", key)
                    })?,
                )
            }
            AttributeId::Dereferenceable => IntAttribute::Dereferenceable(value),
            AttributeId::DereferenceableOrNull => IntAttribute::DereferenceableOrNull(value),
            AttributeId::AllocSize => {
                unimplemented!()
            }
            AttributeId::VScaleRange => {
                unimplemented!()
            }
            o => unimplemented!(),
        })
    }
}

/// Represents a single, concrete LLVM attribute.
#[non_exhaustive]
#[derive(Debug, PartialEq)]
pub enum Attribute {
    /// An enumerated attribute.
    Enum(EnumAttribute),
    /// An integer attribute.
    Int(IntAttribute),
    /// An arbitrary string attribute.
    Str(String),
    /// An arbitrary string attribute with a string value.
    StrKeyValue(String, String),
}

impl Attribute {
    /// Parse a new `Attribute` from the given record at the given start index, returning
    /// a tuple of the number of fields consumed and the parsed result.
    fn from_record(start: usize, record: &UnrolledRecord) -> Result<(usize, Self), AttributeError> {
        let mut fieldcount = 0;

        macro_rules! next {
            () => {
                if let Some(field) = record.fields().get(start + fieldcount) {
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
                let str_bytes = record.fields()[start + fieldcount..]
                    .iter()
                    .take_while(|f| **f != 0)
                    .map(|f| u8::try_from(*f))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|_| AttributeError::BadString)?;

                if str_bytes.is_empty() {
                    Err(AttributeError::BadString)
                } else {
                    let result =
                        String::from_utf8(str_bytes).map_err(|_| AttributeError::BadString)?;

                    // NOTE(ww): plus one to include the NULL byte that we consumed above.
                    fieldcount += result.as_bytes().len() + 1;

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
            AttributeKind::Enum => {
                // Enum attributes: one key field, nothing else.
                let key = AttributeId::try_from(next!()?)?;
                Ok((fieldcount, Attribute::Enum(key.try_into()?)))
            }
            AttributeKind::IntKeyValue => {
                // Integer key-value attributes: one key, one integer value.
                let key = AttributeId::try_from(next!()?)?;
                let value = next!()?;

                Ok((fieldcount, Attribute::Int(TryInto::try_into((key, value))?)))
            }
            AttributeKind::StrKey => {
                // String attributes: one string key field, nothing else.
                let _key = take_string!()?;

                unimplemented!()
            }
            AttributeKind::StrKeyValue => {
                // String key-value attributes: one string key field, one string value field.
                let _key = take_string!()?;
                let _value = take_string!()?;

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
