//! Functionality for mapping the `TYPE_BLOCK_ID_NEW` block.

use std::convert::TryFrom;

use llvm_constants::{IrBlockId, TypeCode};
use llvm_support::{
    AddressSpace, ArrayTypeError, FunctionTypeError, IntegerTypeError, PointerTypeError,
    StructTypeError, Type, VectorTypeError,
};
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::block::{BlockMapError, IrBlock};
use crate::map::MapCtx;
use crate::unroll::UnrolledBlock;

/// Errors that can occur when mapping the type table.
#[derive(Debug, Error)]
pub enum TypeTableError {
    /// The size of the type table is invalid.
    #[error("invalid type table size (expected {0} elements, got {1})")]
    BadSize(usize, usize),
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

/// A symbolic type reference, which is really just an index into some
/// unspecified type table.
#[derive(Debug)]
struct TypeRef(usize);

/// Represents a "partial type," i.e. a type whose subtypes may be symbolic
/// and not fully resolved against a type table.
#[derive(Debug)]
enum PartialType {
    Half,
    BFloat,
    Float,
    Double,
    Metadata,
    X86Fp80,
    Fp128,
    PpcFp128,
    Void,
    Label,
    X86Mmx,
    X86Amx,
    Token,
    Integer(PartialIntegerType),
    Function(PartialFunctionType),
    Pointer(PartialPointerType),
    OpaquePointer(AddressSpace),
    Struct(PartialStructType),
    Array(PartialArrayType),
    FixedVector(PartialVectorType),
    ScalableVector(PartialVectorType),
}

impl PartialType {
    /// Fallibly convert this `PartialType` into a `Type`, using the given
    /// `PartialTypeTable` as a reference.
    fn resolve(&self, partials: &PartialTypeTable) -> Result<Type, TypeTableError> {
        match self {
            PartialType::Half => Ok(Type::Half),
            PartialType::BFloat => Ok(Type::BFloat),
            PartialType::Float => Ok(Type::Float),
            PartialType::Double => Ok(Type::Double),
            PartialType::Metadata => Ok(Type::Metadata),
            PartialType::X86Fp80 => Ok(Type::X86Fp80),
            PartialType::Fp128 => Ok(Type::Fp128),
            PartialType::PpcFp128 => Ok(Type::PpcFp128),
            PartialType::Void => Ok(Type::Void),
            PartialType::Label => Ok(Type::Label),
            PartialType::X86Mmx => Ok(Type::X86Mmx),
            PartialType::X86Amx => Ok(Type::X86Amx),
            PartialType::Token => Ok(Type::Token),
            PartialType::Integer(ity) => Ok(Type::new_integer(ity.bit_width)?),
            PartialType::Function(fty) => {
                let return_type = partials.resolve(&fty.return_type)?;
                let param_types = fty
                    .param_types
                    .iter()
                    .map(|ty_ref| partials.resolve(ty_ref))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Type::new_function(return_type, param_types, fty.is_vararg)?)
            }
            PartialType::Pointer(pty) => {
                let pointee = partials.resolve(&pty.pointee)?;

                Ok(Type::new_pointer(pointee, pty.address_space)?)
            }
            PartialType::OpaquePointer(oty) => Ok(Type::OpaquePointer(*oty)),
            PartialType::Struct(sty) => {
                let field_types = sty
                    .field_types
                    .iter()
                    .map(|fty| partials.resolve(fty))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Type::new_struct(
                    sty.name.clone(),
                    field_types,
                    sty.is_packed,
                )?)
            }
            PartialType::Array(aty) => {
                let element_type = partials.resolve(&aty.element_type)?;

                Ok(Type::new_array(aty.num_elements, element_type)?)
            }
            PartialType::FixedVector(vty) => {
                let element_type = partials.resolve(&vty.element_type)?;

                Ok(Type::new_vector(vty.num_elements, element_type)?)
            }
            PartialType::ScalableVector(vty) => {
                let element_type = partials.resolve(&vty.element_type)?;

                Ok(Type::new_scalable_vector(vty.num_elements, element_type)?)
            }
        }
    }
}

#[derive(Debug)]
struct PartialIntegerType {
    bit_width: u32,
}

/// Represents an (unresolved) function type.
#[derive(Debug)]
struct PartialFunctionType {
    return_type: TypeRef,
    param_types: Vec<TypeRef>,
    is_vararg: bool,
}

/// Represents an (unresolved) pointer type.
#[derive(Debug)]
struct PartialPointerType {
    pointee: TypeRef,
    address_space: AddressSpace,
}

#[derive(Debug)]
struct PartialStructType {
    name: Option<String>,
    field_types: Vec<TypeRef>,
    is_packed: bool,
}

#[derive(Debug)]
struct PartialArrayType {
    num_elements: u64,
    element_type: TypeRef,
}

#[derive(Debug)]
struct PartialVectorType {
    num_elements: u64,
    element_type: TypeRef,
}

/// Represents a partial type table.
///
/// Every partial type table starts out empty (but with an expected ultimate size),
/// and is incrementally updated as records within the type block are visited.
#[derive(Debug)]
struct PartialTypeTable {
    numentries: usize,
    inner: Vec<PartialType>,
}

impl PartialTypeTable {
    fn new(numentries: usize) -> Self {
        Self {
            numentries: numentries,
            inner: Vec::with_capacity(numentries),
        }
    }

    fn add(&mut self, ty: PartialType) {
        self.inner.push(ty)
    }

    fn last_mut(&mut self) -> Option<&mut PartialType> {
        self.inner.last_mut()
    }

    /// Fallibly convert a `TypeRef` into its `PartialType` in this partial type table.
    fn get(&self, ty_ref: &TypeRef) -> Result<&PartialType, TypeTableError> {
        self.inner
            .get(ty_ref.0)
            .ok_or(TypeTableError::BadIndex(ty_ref.0))
    }

    /// Fallibly converts the given `TypeRef` into a fully owned `Type`.
    fn resolve(&self, ty_ref: &TypeRef) -> Result<Type, TypeTableError> {
        // `TypeRef` resolution happens in two steps: we grab the corresponding
        // `PartialType`, and then resolve its subtypes.
        let pty = self.get(ty_ref)?;

        pty.resolve(self)
    }

    /// Fallibly converts this `PartialTypeTable` into a `TypeTable`.
    fn reify(self) -> Result<TypeTable, TypeTableError> {
        if self.inner.len() != self.numentries {
            return Err(TypeTableError::BadSize(self.numentries, self.inner.len()));
        }

        // Walk the partial type table, resolving each partial type
        // into a fully owned `Type`.
        let types = self
            .inner
            .iter()
            .map(|pty| pty.resolve(&self))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(TypeTable(types))
    }
}

/// Models the `TYPE_BLOCK_ID_NEW` block.
#[derive(Clone, Debug)]
pub struct TypeTable(Vec<Type>);

impl IrBlock for TypeTable {
    const BLOCK_ID: IrBlockId = IrBlockId::Type;

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        // Figure out how many type entries we have, and reserve the space for them up-front.
        let numentries = {
            let numentries = block.one_record(TypeCode::NumEntry as u64)?;

            numentries.get_field(0)? as usize
        };

        // To map the type table, we perform two passes:
        // 1. We iterate over all type records, building an initial table of "partial"
        //    types that contain only symbolic references to other types.
        //    This pass allows us to fully resolve e.g. forward-declared types
        //    without having to perform a more expensive visiting pass later.
        // 2. We iterate over all of the partial types, resolving them into
        //    fully owned and expanded `Type`s.

        let mut partial_types = PartialTypeTable::new(numentries);

        // Bits of type mapping state:
        // * Keep track of how many types we've seen; we'll reconcile this count
        //   with our expected type count (numentries) once all types are mapped.
        // * Keep track of the last `TYPE_CODE_STRUCT_NAME` we've seen; we'll use
        //   this to name the next named struct or opaque type we see.
        let mut ty_idx = 0;
        let mut last_type_name = String::new();
        for record in block.all_records() {
            let code = TypeCode::try_from(record.code()).map_err(TypeTableError::from)?;
            log::debug!("visiting type code: {:?}", code);

            match code {
                // Already visited; nothing to do.
                TypeCode::NumEntry => continue,
                TypeCode::Void => partial_types.add(PartialType::Void),
                TypeCode::Half => partial_types.add(PartialType::Half),
                TypeCode::BFloat => partial_types.add(PartialType::BFloat),
                TypeCode::Float => partial_types.add(PartialType::Float),
                TypeCode::Double => partial_types.add(PartialType::Double),
                TypeCode::Label => partial_types.add(PartialType::Label),
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
                    if let Some(PartialType::Struct(s)) = partial_types.last_mut() {
                        if s.name.is_some() {
                            return Err(BlockMapError::BadBlockMap(
                                "forward-declared opaque type already has name".into(),
                            ));
                        }

                        s.name = Some(last_type_name.clone());
                    } else {
                        partial_types.add(PartialType::Struct(PartialStructType {
                            name: Some(last_type_name.clone()),
                            field_types: vec![],
                            is_packed: false,
                        }));
                    }

                    last_type_name.clear();
                }
                TypeCode::Integer => {
                    let bit_width = record.get_field(0)? as u32;
                    partial_types.add(PartialType::Integer(PartialIntegerType { bit_width }));
                }
                TypeCode::Pointer => {
                    let pointee = TypeRef(record.get_field(0)? as usize);

                    let address_space =
                        AddressSpace::try_from(record.get_field(1)?).map_err(|e| {
                            BlockMapError::BadBlockMap(format!(
                                "bad address space for pointer type: {:?}",
                                e
                            ))
                        })?;

                    partial_types.add(PartialType::Pointer(PartialPointerType {
                        pointee,
                        address_space,
                    }));
                }
                TypeCode::FunctionOld => {
                    // TODO(ww): These only show up in older bitcode, so don't bother with them for now.
                    return Err(BlockMapError::Unsupported(
                        "unsupported: old function type codes; please implement!".into(),
                    ));
                }
                TypeCode::Array => {
                    let num_elements = record.get_field(0)?;

                    let element_type = TypeRef(record.get_field(1)? as usize);

                    partial_types.add(PartialType::Array(PartialArrayType {
                        num_elements,
                        element_type,
                    }));
                }
                TypeCode::Vector => {
                    let num_elements = record.get_field(0)?;

                    let element_type = TypeRef(record.get_field(1)? as usize);

                    // A vector type is either fixed or scalable, depending on the
                    // third field (which can also be absent, indicating fixed).
                    let scalable = record.get_field(2).map_or_else(|_| false, |f| f > 0);
                    let new_type = match scalable {
                        true => PartialType::ScalableVector(PartialVectorType {
                            num_elements,
                            element_type,
                        }),
                        false => PartialType::FixedVector(PartialVectorType {
                            num_elements,
                            element_type,
                        }),
                    };

                    partial_types.add(new_type);
                }
                TypeCode::X86Fp80 => partial_types.add(PartialType::X86Fp80),
                TypeCode::Fp128 => partial_types.add(PartialType::Fp128),
                TypeCode::PpcFp128 => partial_types.add(PartialType::PpcFp128),
                TypeCode::Metadata => partial_types.add(PartialType::Metadata),
                TypeCode::X86Mmx => partial_types.add(PartialType::X86Mmx),
                TypeCode::StructAnon => {
                    let is_packed = record.get_field(0).map(|f| f > 0)?;

                    let field_types = record.fields()[1..]
                        .iter()
                        .map(|f| TypeRef(*f as usize))
                        .collect::<Vec<_>>();

                    partial_types.add(PartialType::Struct(PartialStructType {
                        name: None,
                        field_types,
                        is_packed,
                    }));
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

                    let field_types = record.fields()[1..]
                        .iter()
                        .map(|f| TypeRef(*f as usize))
                        .collect::<Vec<_>>();

                    // Like with opaque types, we might be forward-referenced here.
                    // If so, we update our pre-existing structure type with its
                    // correct name and fields.
                    if let Some(PartialType::Struct(s)) = partial_types.last_mut() {
                        if s.name.is_some() || !s.field_types.is_empty() {
                            return Err(BlockMapError::BadBlockMap(
                                "forward-declared struct type already has name and/or type fields"
                                    .into(),
                            ));
                        }

                        s.name = Some(last_type_name.clone());
                        s.field_types = field_types;
                    } else {
                        partial_types.add(PartialType::Struct(PartialStructType {
                            name: Some(last_type_name.clone()),
                            field_types,
                            is_packed,
                        }));
                    }

                    last_type_name.clear();
                }
                TypeCode::Function => {
                    let is_vararg = record.get_field(0).map(|f| f > 0)?;
                    let return_type = TypeRef(record.get_field(1)? as usize);

                    let param_types = record.fields()[2..]
                        .iter()
                        .map(|f| TypeRef(*f as usize))
                        .collect::<Vec<_>>();

                    partial_types.add(PartialType::Function(PartialFunctionType {
                        return_type,
                        param_types,
                        is_vararg,
                    }));
                }
                TypeCode::Token => partial_types.add(PartialType::Token),
                TypeCode::X86Amx => partial_types.add(PartialType::X86Amx),
                TypeCode::OpaquePointer => {
                    let address_space =
                        AddressSpace::try_from(record.get_field(0)?).map_err(|e| {
                            BlockMapError::BadBlockMap(format!(
                                "bad address space in type: {:?}",
                                e
                            ))
                        })?;

                    partial_types.add(PartialType::OpaquePointer(address_space))
                }
                o => {
                    return Err(BlockMapError::Unsupported(format!(
                        "unsupported type code: {:?}",
                        o
                    )))
                }
            }

            ty_idx += 1;
        }

        if ty_idx != numentries {
            return Err(BlockMapError::BadBlockMap(format!(
                "bad type table: expected {} entries, but got {}",
                numentries, ty_idx
            )));
        }

        log::debug!("partial_types: {:?}", partial_types);

        Ok(partial_types.reify()?)
    }
}
