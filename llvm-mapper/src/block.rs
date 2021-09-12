//! Structures for mapping from bitstream blocks to LLVM models.

use std::convert::TryFrom;
use std::str::Utf8Error;

use llvm_constants::{
    IdentificationCode, IrBlockId, ModuleCode, ReservedBlockId, StrtabCode, SymtabCode, TypeCode,
};
use llvm_support::{AddressSpace, IntegerTypeError, PointerTypeError, StrtabRef, Type};
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::error::Error;
use crate::map::{MapCtx, Mappable};
use crate::record::{Comdat, DataLayout};
use crate::unroll::UnrolledBlock;

/// A holistic model of all possible block IDs, spanning reserved, IR, and unknown IDs.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum BlockId {
    /// A block ID that's been reserved by LLVM. Reserved IDs are internal, and cannot be mapped here.
    Reserved(ReservedBlockId),
    /// A block ID used by LLVM IR.
    Ir(IrBlockId),
    /// An unknown block ID. Unknown IDs cannot be mapped.
    Unknown(u64),
}

impl From<u64> for BlockId {
    fn from(value: u64) -> Self {
        // Try to turn `value` into each of our known kinds of block IDs, in order
        // of precedence.
        ReservedBlockId::try_from(value).map_or_else(
            |_| IrBlockId::try_from(value).map_or_else(|_| BlockId::Unknown(value), BlockId::Ir),
            BlockId::Reserved,
        )
    }
}

/// A trait implemented by all blocks that correspond to IR models, allowing them
/// to be mapped into their corresponding model.
pub(crate) trait IrBlock: Sized {
    /// The `IrBlockId` that corresponds to this IR model.
    const BLOCK_ID: IrBlockId;

    /// Attempt to map the given block to the implementing type, returning an error if mapping fails.
    ///
    /// This is an interior trait that shouldn't be used directly.
    fn try_map_inner(block: &UnrolledBlock, ctx: &mut MapCtx) -> Result<Self, Error>;
}

impl<T: IrBlock> Mappable<UnrolledBlock> for T {
    fn try_map(block: &UnrolledBlock, ctx: &mut MapCtx) -> Result<Self, Error> {
        if block.id != BlockId::Ir(T::BLOCK_ID) {
            return Err(Error::BadBlockMap(format!(
                "can't map {:?} into {:?}",
                block.id,
                Identification::BLOCK_ID
            )));
        }

        IrBlock::try_map_inner(block, ctx)
    }
}

/// Models the `IDENTIFICATION_BLOCK` block.
#[non_exhaustive]
#[derive(Debug)]
pub struct Identification {
    /// The name of the "producer" for this bitcode.
    pub producer: String,
    /// The compatibility epoch.
    pub epoch: u64,
}

impl IrBlock for Identification {
    const BLOCK_ID: IrBlockId = IrBlockId::Identification;

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, Error> {
        let producer = {
            let producer = block.one_record(IdentificationCode::ProducerString as u64)?;

            producer.try_string(0)?
        };

        let epoch = {
            let epoch = block.one_record(IdentificationCode::Epoch as u64)?;

            epoch.get_field(0)?
        };

        Ok(Self { producer, epoch })
    }
}

/// Models the `MODULE_BLOCK` block.
#[non_exhaustive]
#[derive(Debug)]
pub struct Module {
    /// The format version.
    version: u64,
    /// The target triple specification.
    pub triple: String,
    /// The data layout specification.
    pub datalayout: DataLayout,
    /// Any assembly block lines in the module.
    pub asm: Vec<String>,
    /// Any dependent libraries listed in the module.
    pub deplibs: Vec<String>,
}

impl IrBlock for Module {
    const BLOCK_ID: IrBlockId = IrBlockId::Module;

    fn try_map_inner(block: &UnrolledBlock, ctx: &mut MapCtx) -> Result<Self, Error> {
        let version = {
            let version = block.one_record(ModuleCode::Version as u64)?;

            version.as_ref().fields[0]
        };

        ctx.version = Some(version);

        let triple = block.one_record(ModuleCode::Triple as u64)?.try_string(0)?;

        let datalayout = {
            let datalayout = block
                .one_record(ModuleCode::DataLayout as u64)?
                .try_string(0)?;

            log::debug!("raw datalayout: {}", datalayout);

            datalayout.parse::<DataLayout>()?
        };

        // Each module has zero or exactly one MODULE_CODE_ASM records.
        let asm = match block.one_record_or_none(ModuleCode::Asm as u64)? {
            Some(rec) => rec
                .try_string(0)?
                .split('\n')
                .map(String::from)
                .collect::<Vec<_>>(),
            None => Vec::new(),
        };

        // Deplib records are deprecated, but we might be parsing an older bitstream.
        let deplibs = block
            .records(ModuleCode::DepLib as u64)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()?;

        // Build the section table. We'll reference this later.
        let _section_table = block
            .records(ModuleCode::SectionName as u64)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()?;

        // Build the GC table. We'll reference this later.
        let _gc_table = block
            .records(ModuleCode::GcName as u64)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()?;

        // Build the Comdat list. We'll reference this later.
        let _comdats = block
            .records(ModuleCode::Comdat as u64)
            .map(|rec| Comdat::try_map(rec, ctx))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self {
            version,
            triple,
            datalayout,
            asm,
            deplibs,
        })
    }
}

/// Errors that can occur when mapping the type table.
#[derive(Debug, Error)]
pub enum TypeTableError {
    /// An unknown record code was seen.
    #[error("unknown type code: {0}")]
    UnknownTypeCode(#[from] TryFromPrimitiveError<TypeCode>),
    /// An invalid integer type was seen.
    #[error("invalid integer type: {0}")]
    InvalidIntegerType(#[from] IntegerTypeError),
    /// An invalid pointer type was seen.
    #[error("invalid pointer type: {0}")]
    InvalidPointerType(#[from] PointerTypeError),
}

/// Models the `TYPE_BLOCK_ID_NEW` block.
///
/// This model has no state of its own; its responsibility during mapping is to update
/// the [MapCtx](MapCtx) with information about the types used in the module.
#[derive(Clone, Debug)]
pub struct TypeTable {}

impl IrBlock for TypeTable {
    const BLOCK_ID: IrBlockId = IrBlockId::Type;

    fn try_map_inner(block: &UnrolledBlock, ctx: &mut MapCtx) -> Result<Self, Error> {
        // Figure out how many type entries we have, and reserve the space for them up-front.
        let numentries = {
            let numentries = block.one_record(TypeCode::NumEntry as u64)?;

            numentries.get_field(0)?
        };
        ctx.types.reserve(numentries as usize);

        // Bits of type mapping state:
        // * Keep track of how many types we've seen; we'll reconcile this count
        //   with our expected type count (numentries) once all types are mapped.
        // * Keep track of the last `TYPE_CODE_STRUCT_NAME` we've seen; we'll use
        //   this to name the next named struct or opaque type we see.
        let mut count = 0;
        let mut last_type_name = String::new();
        for record in block.all_records() {
            let code = TypeCode::try_from(record.as_ref().code).map_err(TypeTableError::from)?;

            match code {
                // Already visited; nothing to do.
                TypeCode::NumEntry => continue,
                TypeCode::Void => ctx.types.push(Type::Void),
                TypeCode::Half => ctx.types.push(Type::Half),
                TypeCode::BFloat => ctx.types.push(Type::BFloat),
                TypeCode::Float => ctx.types.push(Type::Float),
                TypeCode::Double => ctx.types.push(Type::Double),
                TypeCode::Label => ctx.types.push(Type::Label),
                TypeCode::Opaque => {
                    // NOTE(ww): LLVM's BitcodeReader checks that the
                    // TYPE_CODE_OPAQUE record has exactly one field, but
                    // doesn't seem to use that field for anything.
                    // Not sure what's up with that.

                    if last_type_name.is_empty() {
                        return Err(Error::BadRecordMap(
                            "opaque type but no preceding type name".into(),
                        ));
                    }

                    // Our opaque type might be forward-referenced. If so, we
                    // fill in the previous type's name. Otherwise, we create
                    // a new structure type with no body.
                    if let Some(Type::Struct(s)) = ctx.types.last_mut() {
                        if s.name.is_some() {
                            return Err(Error::BadBlockMap(
                                "forward-declared opaque type already has name".into(),
                            ));
                        }

                        s.name = Some(last_type_name.clone());
                    } else {
                        ctx.types
                            .push(Type::new_named_struct(last_type_name.clone(), vec![]));
                    }

                    last_type_name.clear();
                }
                TypeCode::Integer => {
                    // Integer type codes carry their width.
                    let bit_width = record.get_field(0)?;
                    ctx.types
                        .push(Type::new_integer(bit_width as u32).map_err(TypeTableError::from)?);
                }
                TypeCode::Pointer => {
                    // Pointer types refer to their pointee type by index,
                    // and optionally include an address space record.
                    let pointee_type = {
                        let idx = record.get_field(0)? as usize;

                        ctx.types
                            .get(idx)
                            .ok_or_else(|| {
                                Error::BadField(format!(
                                    "invalid pointee type index: no type at {}",
                                    idx
                                ))
                            })?
                            .clone()
                    };

                    let address_space = record.get_field(1).and_then(|f| {
                        AddressSpace::try_from(f).map_err(|e| {
                            Error::BadField(format!("bad address space for pointer type: {:?}", e))
                        })
                    })?;

                    // Not all types are actually valid pointee types, hence
                    // the fallible type construction here.
                    ctx.types.push(
                        Type::new_pointer(pointee_type, address_space)
                            .map_err(TypeTableError::from)?,
                    );
                }
                TypeCode::FunctionOld => unimplemented!(),
                TypeCode::Array => unimplemented!(),
                TypeCode::Vector => unimplemented!(),
                TypeCode::X86Fp80 => unimplemented!(),
                TypeCode::Fp128 => ctx.types.push(Type::Fp128),
                TypeCode::PpcFp128 => ctx.types.push(Type::PpcFp128),
                TypeCode::Metadata => ctx.types.push(Type::Metadata),
                TypeCode::X86Mmx => ctx.types.push(Type::X86Mmx),
                TypeCode::StructAnon => unimplemented!(),
                TypeCode::StructName => {
                    // A `TYPE_CODE_STRUCT_NAME` is not a type in its own right; it merely
                    // supplies the name for a future type record.
                    last_type_name.push_str(&record.try_string(0)?);
                }
                TypeCode::StructNamed => unimplemented!(),
                TypeCode::Function => unimplemented!(),
                TypeCode::X86Amx => ctx.types.push(Type::X86Amx),
                TypeCode::OpaquePointer => {
                    let address_space = record.get_field(0).and_then(|f| {
                        AddressSpace::try_from(f).map_err(|e| {
                            Error::BadField(format!("bad address space in type: {:?}", e))
                        })
                    })?;

                    ctx.types.push(Type::OpaquePointer(address_space))
                }
                o => {
                    return Err(Error::Unsupported(format!(
                        "unsupported type code: {:?}",
                        o
                    )))
                }
            }

            count += 1;
        }

        if count != numentries {
            unimplemented!();
        }

        Ok(Self {})
    }
}

/// Errors that can occur when accessing a string table.
#[derive(Debug, Error)]
pub enum StrtabError {
    /// The requested range is invalid.
    #[error("requested range in string table is invalid")]
    BadRange,
    /// The requested string is not UTF-8.
    #[error("could not decode range into a UTF-8 string: {0}")]
    BadString(#[from] Utf8Error),
}

/// Models the `STRTAB_BLOCK` block.
#[derive(Clone, Debug)]
pub struct Strtab(Vec<u8>);

impl AsRef<[u8]> for Strtab {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl IrBlock for Strtab {
    const BLOCK_ID: IrBlockId = IrBlockId::Strtab;

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, Error> {
        // TODO(ww): The docs also claim that there's only one STRTAB_BLOB per STRTAB_BLOCK,
        // but at least one person has reported otherwise here:
        // https://lists.llvm.org/pipermail/llvm-dev/2020-August/144327.html
        // Needs investigation.
        let strtab = {
            let strtab = block.one_record(StrtabCode::Blob as u64)?;

            strtab.try_blob(0)?
        };

        Ok(Self(strtab))
    }
}

impl Strtab {
    /// Get a string in the string table by its index and length.
    ///
    /// Returns `None` on all of the error conditions associated with
    /// [`try_get`](Strtab::try_get).
    pub fn get(&self, sref: &StrtabRef) -> Option<&str> {
        self.try_get(sref).ok()
    }

    /// Get a string in the string table by its index and length.
    ///
    /// Returns an error if the requested span is invalid, or if the extracted
    /// slice isn't a valid string.
    pub fn try_get(&self, sref: &StrtabRef) -> Result<&str, StrtabError> {
        let inner = self.as_ref();

        if sref.size == 0 || sref.offset >= inner.len() || sref.offset + sref.size > inner.len() {
            return Err(StrtabError::BadRange);
        }

        Ok(std::str::from_utf8(
            &inner[sref.offset..sref.offset + sref.size],
        )?)
    }
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

impl IrBlock for Symtab {
    const BLOCK_ID: IrBlockId = IrBlockId::Symtab;

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, Error> {
        let symtab = {
            let symtab = block.one_record(SymtabCode::Blob as u64)?;

            symtab.try_blob(0)?
        };

        Ok(Self(symtab))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sref(tup: (usize, usize)) -> StrtabRef {
        tup.into()
    }

    #[test]
    fn test_blockid_from_u64() {
        assert_eq!(
            BlockId::from(0),
            BlockId::Reserved(ReservedBlockId::BlockInfo)
        );
        assert_eq!(
            BlockId::from(7),
            BlockId::Reserved(ReservedBlockId::Reserved7)
        );
        assert_eq!(BlockId::from(8), BlockId::Ir(IrBlockId::Module));
        assert_eq!(BlockId::from(2384629342), BlockId::Unknown(2384629342));
    }

    #[test]
    fn test_strtab() {
        let inner = "this is a string table";
        let strtab = Strtab(inner.into());
        assert_eq!(strtab.get(&sref((0, 4))).unwrap(), "this");
        assert_eq!(strtab.get(&sref((0, 7))).unwrap(), "this is");
        assert_eq!(strtab.get(&sref((8, 14))).unwrap(), "a string table");
        assert_eq!(
            strtab.get(&sref((0, inner.len()))).unwrap(),
            "this is a string table"
        );

        assert!(strtab.get(&sref((inner.len(), 0))).is_none());
        assert!(strtab.get(&sref((0, inner.len() + 1))).is_none());
        assert!(strtab.get(&sref((0, 0))).is_none());
    }
}
