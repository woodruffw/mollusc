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
