//! Structures for mapping from bitstream blocks to LLVM models.

use std::convert::TryFrom;
use std::str::Utf8Error;

use llvm_constants::{
    IdentificationCode, IrBlockId, ModuleCode, ReservedBlockId, StrtabCode, SymtabCode, TypeCode,
    TARGET_TRIPLE,
};
use llvm_support::{
    AddressSpace, ArrayTypeError, FunctionTypeError, IntegerTypeError, PointerTypeError, StrtabRef,
    StructTypeError, Type, VectorTypeError,
};
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::map::{MapCtx, MapCtxError, Mappable};
use crate::record::{Comdat, DataLayout, RecordMapError};
use crate::unroll::UnrolledBlock;

/// Potential errors when mapping a single bitstream block.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum BlockMapError {
    /// Parsing a record failed, for some internal reason.
    #[error("error while mapping record: {0}")]
    BadRecord(#[from] RecordMapError),

    /// Our mapping context was invalid for our operation.
    #[error("invalid mapping context: {0}")]
    BadContext(#[from] MapCtxError),

    /// We couldn't map a block, for any number of reasons.
    #[error("error while mapping block: {0}")]
    BadBlockMap(String),

    /// We expected exactly one record with this code in this block.
    #[error("expected exactly one record of code {0} in block {1:?}")]
    BlockRecordMismatch(u64, BlockId),

    /// We expected exactly one sub-block with this ID in this block.
    #[error("expected exactly one block of ID {0:?} in block {1:?}")]
    BlockBlockMismatch(BlockId, BlockId),

    /// We couldn't map the type table.
    #[error("error while mapping type table: {0}")]
    BadTypeTable(#[from] TypeTableError),

    /// We encountered an unsupported feature or layout.
    #[error("unsupported: {0}")]
    Unsupported(String),
}

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
    fn try_map_inner(block: &UnrolledBlock, ctx: &mut MapCtx) -> Result<Self, BlockMapError>;
}

impl<T: IrBlock> Mappable<UnrolledBlock> for T {
    type Error = BlockMapError;

    fn try_map(block: &UnrolledBlock, ctx: &mut MapCtx) -> Result<Self, Self::Error> {
        if block.id != BlockId::Ir(T::BLOCK_ID) {
            return Err(BlockMapError::BadBlockMap(format!(
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

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
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
    /// The module's type table.
    pub type_table: TypeTable,
}

impl IrBlock for Module {
    const BLOCK_ID: IrBlockId = IrBlockId::Module;

    fn try_map_inner(block: &UnrolledBlock, ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        let version = {
            let version = block.one_record(ModuleCode::Version as u64)?;

            version.get_field(0)?
        };

        ctx.version = Some(version);

        // Each module *should* have a target triple, but doesn't necessarily.
        let triple = if let Some(record) = block.one_record_or_none(ModuleCode::Triple as u64)? {
            record.try_string(0)?
        } else {
            TARGET_TRIPLE.into()
        };

        // Each module *should* have a datalayout record, but doesn't necessarily.
        let datalayout =
            if let Some(record) = block.one_record_or_none(ModuleCode::DataLayout as u64)? {
                DataLayout::try_map(record, ctx)?
            } else {
                DataLayout::default()
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

        // Build the type table.
        let type_table = TypeTable::try_map(block.one_block(BlockId::Ir(IrBlockId::Type))?, ctx)?;

        Ok(Self {
            version,
            triple,
            datalayout,
            asm,
            deplibs,
            type_table,
        })
    }
}

/// Errors that can occur when mapping the type table.
#[derive(Debug, Error)]
pub enum TypeTableError {
    /// An invalid type index was requested.
    #[error("invalid type table index: {0}")]
    BadIndex(usize),
    /// An unknown record code was seen.
    #[error("unknown type code: {0}")]
    UnknownTypeCode(#[from] TryFromPrimitiveError<TypeCode>),
    /// An invalid integer type was seen.
    #[error("invalid integer type: {0}")]
    InvalidIntegerType(#[from] IntegerTypeError),
    /// An invalid pointer type was seen.
    #[error("invalid pointer type: {0}")]
    InvalidPointerType(#[from] PointerTypeError),
    /// An invalid array type was seen.
    #[error("invalid array type: {0}")]
    InvalidArrayType(#[from] ArrayTypeError),
    /// An invalid vector type was seen.
    #[error("invalid vector type: {0}")]
    InvalidVectorType(#[from] VectorTypeError),
    /// An invalid structure type was seen.
    #[error("invalid structure type: {0}")]
    InvalidStructType(#[from] StructTypeError),
    /// An invalid function type was seen.
    #[error("invalid function type: {0}")]
    InvalidFunctionType(#[from] FunctionTypeError),
}

/// Models the `TYPE_BLOCK_ID_NEW` block.
#[derive(Clone, Debug)]
pub struct TypeTable(Vec<Type>);

impl TypeTable {
    /// Create a new type table with `numentries` slots reserved up-front.
    pub(self) fn new(numentries: usize) -> Self {
        Self(Vec::with_capacity(numentries))
    }

    /// Return a mutable reference to the most recently added type in the table.
    pub(self) fn last_mut(&mut self) -> Option<&mut Type> {
        self.0.last_mut()
    }

    /// Get a copy of a type from the type table by index.
    pub(self) fn get_owned(&self, idx: usize) -> Result<Type, TypeTableError> {
        self.0
            .get(idx)
            .cloned()
            .ok_or(TypeTableError::BadIndex(idx))
    }

    /// Add a type to the type table.
    pub(self) fn add(&mut self, ty: Type) {
        self.0.push(ty)
    }
}

impl IrBlock for TypeTable {
    const BLOCK_ID: IrBlockId = IrBlockId::Type;

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        // Figure out how many type entries we have, and reserve the space for them up-front.
        let numentries = {
            let numentries = block.one_record(TypeCode::NumEntry as u64)?;

            numentries.get_field(0)?
        };

        let mut types = Self::new(numentries as usize);

        // Bits of type mapping state:
        // * Keep track of how many types we've seen; we'll reconcile this count
        //   with our expected type count (numentries) once all types are mapped.
        // * Keep track of the last `TYPE_CODE_STRUCT_NAME` we've seen; we'll use
        //   this to name the next named struct or opaque type we see.
        let mut count = 0;
        let mut last_type_name = String::new();
        for record in block.all_records() {
            let code = TypeCode::try_from(record.code()).map_err(TypeTableError::from)?;
            log::debug!("visiting type code: {:?}", code);

            match code {
                // Already visited; nothing to do.
                TypeCode::NumEntry => continue,
                TypeCode::Void => types.add(Type::Void),
                TypeCode::Half => types.add(Type::Half),
                TypeCode::BFloat => types.add(Type::BFloat),
                TypeCode::Float => types.add(Type::Float),
                TypeCode::Double => types.add(Type::Double),
                TypeCode::Label => types.add(Type::Label),
                TypeCode::Opaque => {
                    // NOTE(ww): LLVM's BitcodeReader checks that the
                    // TYPE_CODE_OPAQUE record has exactly one field, but
                    // doesn't seem to use that field for anything.
                    // Not sure what's up with that.

                    if last_type_name.is_empty() {
                        return Err(BlockMapError::BadBlockMap(
                            "opaque type but no preceding type name".into(),
                        ));
                    }

                    // Our opaque type might be forward-referenced. If so, we
                    // fill in the previous type's name. Otherwise, we create
                    // a new structure type with no body.
                    if let Some(Type::Struct(s)) = types.last_mut() {
                        if s.name.is_some() {
                            return Err(BlockMapError::BadBlockMap(
                                "forward-declared opaque type already has name".into(),
                            ));
                        }

                        s.name = Some(last_type_name.clone());
                    } else {
                        types.add(
                            Type::new_struct(Some(last_type_name.clone()), vec![], false)
                                .map_err(TypeTableError::from)?,
                        );
                    }

                    last_type_name.clear();
                }
                TypeCode::Integer => {
                    // Integer type codes carry their width.
                    let bit_width = record.get_field(0)?;
                    types.add(Type::new_integer(bit_width as u32).map_err(TypeTableError::from)?);
                }
                TypeCode::Pointer => {
                    // Pointer types refer to their pointee type by index,
                    // and optionally include an address space record.
                    let pointee_type = {
                        let idx = record.get_field(0)? as usize;

                        types.get_owned(idx)?
                    };

                    let address_space =
                        AddressSpace::try_from(record.get_field(1)?).map_err(|e| {
                            BlockMapError::BadBlockMap(format!(
                                "bad address space for pointer type: {:?}",
                                e
                            ))
                        })?;

                    // Not all types are actually valid pointee types, hence
                    // the fallible type construction here.
                    types.add(
                        Type::new_pointer(pointee_type, address_space)
                            .map_err(TypeTableError::from)?,
                    );
                }
                TypeCode::FunctionOld => {
                    // TODO(ww): These only show up in older bitcode, so don't bother with them for now.
                    return Err(BlockMapError::Unsupported(
                        "unsupported: old function type codes; please implement!".into(),
                    ));
                }
                TypeCode::Array => {
                    let num_elements = record.get_field(0)?;

                    let element_type = {
                        let idx = record.get_field(1)? as usize;

                        types.get_owned(idx)?
                    };

                    types.add(
                        Type::new_array(num_elements, element_type)
                            .map_err(TypeTableError::from)?,
                    );
                }
                TypeCode::Vector => {
                    let num_elements = record.get_field(0)?;

                    let element_type = {
                        let idx = record.get_field(1)? as usize;

                        types.get_owned(idx)?
                    };

                    // A vector type is either fixed or scalable, depending on the
                    // third field (which can also be absent, indicating fixed).
                    let scalable = record.get_field(2).map_or_else(|_| false, |f| f > 0);
                    let new_type = match scalable {
                        true => Type::new_scalable_vector(num_elements, element_type),
                        false => Type::new_vector(num_elements, element_type),
                    }
                    .map_err(TypeTableError::from)?;

                    types.add(new_type);
                }
                TypeCode::X86Fp80 => types.add(Type::X86Fp80),
                TypeCode::Fp128 => types.add(Type::Fp128),
                TypeCode::PpcFp128 => types.add(Type::PpcFp128),
                TypeCode::Metadata => types.add(Type::Metadata),
                TypeCode::X86Mmx => types.add(Type::X86Mmx),
                TypeCode::StructAnon => {
                    let is_packed = record.get_field(0).map(|f| f > 0)?;

                    let element_types = record.fields()[1..]
                        .iter()
                        .map(|idx| types.get_owned(*idx as usize))
                        .collect::<Result<Vec<_>, _>>()?;

                    types.add(
                        Type::new_struct(None, element_types, is_packed)
                            .map_err(TypeTableError::from)?,
                    );
                }
                TypeCode::StructName => {
                    // A `TYPE_CODE_STRUCT_NAME` is not a type in its own right; it merely
                    // supplies the name for a future type record.
                    last_type_name.push_str(&record.try_string(0)?);
                }
                TypeCode::StructNamed => {
                    // TODO(ww): Should probably be deduped with StructAnon above,
                    // since they're 90% identical.

                    let is_packed = record.get_field(0).map(|f| f > 0)?;

                    let element_types = record.fields()[1..]
                        .iter()
                        .map(|idx| types.get_owned(*idx as usize))
                        .collect::<Result<Vec<_>, _>>()?;

                    // Like with opaque types, we might be forward-referenced here.
                    // If so, we update our pre-existing structure type with its
                    // correct name and fields.
                    if let Some(Type::Struct(s)) = types.last_mut() {
                        if s.name.is_some() || !s.fields.is_empty() {
                            return Err(BlockMapError::BadBlockMap(
                                "forward-declared struct type already has name and/or type fields"
                                    .into(),
                            ));
                        }

                        s.name = Some(last_type_name.clone());
                        s.fields = element_types;
                    } else {
                        types.add(
                            Type::new_struct(
                                Some(last_type_name.clone()),
                                element_types,
                                is_packed,
                            )
                            .map_err(TypeTableError::from)?,
                        );
                    }

                    last_type_name.clear();
                }
                TypeCode::Function => {
                    let is_vararg = record.get_field(0).map(|f| f > 0)?;
                    let return_type = {
                        let idx = record.get_field(1)?;
                        types.get_owned(idx as usize)?
                    };

                    let param_types = record.fields()[2..]
                        .iter()
                        .map(|idx| types.get_owned(*idx as usize))
                        .collect::<Result<Vec<_>, _>>()?;

                    types.add(
                        Type::new_function(return_type, param_types, is_vararg)
                            .map_err(TypeTableError::from)?,
                    );
                }
                TypeCode::X86Amx => types.add(Type::X86Amx),
                TypeCode::OpaquePointer => {
                    let address_space =
                        AddressSpace::try_from(record.get_field(0)?).map_err(|e| {
                            BlockMapError::BadBlockMap(format!(
                                "bad address space in type: {:?}",
                                e
                            ))
                        })?;

                    types.add(Type::OpaquePointer(address_space))
                }
                o => {
                    return Err(BlockMapError::Unsupported(format!(
                        "unsupported type code: {:?}",
                        o
                    )))
                }
            }

            count += 1;
        }

        if count != numentries {
            return Err(BlockMapError::BadBlockMap(format!(
                "bad type table: expected {} entries, but got {}",
                numentries, count
            )));
        }

        Ok(types)
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

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
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

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
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
