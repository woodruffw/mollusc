//! Structures for managing LLVM types.

use std::convert::TryFrom;

use thiserror::Error;

use crate::AddressSpace;

/// The IDs of types known to LLVM.
///
/// These are not fully unique: all integer types share the `Integer` type ID,
/// and similarly for pointers, arrays, etc.
// TODO(ww): Perhaps use arbitrary enum discriminants here when they're stabilized.
// See: https://github.com/rust-lang/rfcs/pull/2363
#[repr(u64)]
pub enum TypeId {
    /// 16-bit floating-points.
    Half = 0,
    /// 16-bit floating-points (7-bit significand).
    BFloat,
    /// 32-bit floating-points.
    Float,
    /// 64-bit floating-points.
    Double,
    /// 80-bit floating-points (x87).
    X86Fp80,
    /// 128-bit floating-points (112-bit significand).
    Fp128,
    /// 128-bit floating-points (two 64-bits, PowerPC).
    PpcFp128,
    /// The void type (a type with no size).
    Void,
    /// Labels.
    Label,
    /// Metadata.
    Metadata,
    /// MMX vectors (64 bits, x86).
    X86Mmx,
    /// AMX vectors (8192 bits, x86).
    X86Amx,
    /// Tokens.
    Token,
    /// Arbitrary bit-width integers.
    Integer,
    /// Functions.
    Function,
    /// Pointers.
    Pointer,
    /// Structures.
    Struct,
    /// Arrays.
    Array,
    /// Fixed-width SIMD vectors.
    FixedVector,
    /// Scalable SIMD vectors.
    ScalableVector,
}

/// A representation of LLVM's types.
///
/// See [`TypeId`](TypeId) for documentation of each variant.
#[allow(missing_docs)]
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
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
    Integer(IntegerType),
    Function(Box<Type>, Vec<Type>),
    Pointer(PointerType),
    OpaquePointer(AddressSpace),
    Struct(StructType),
    Array(u32, Box<Type>),
    FixedVector(u32, Box<Type>),
    ScalableVector(u32, Box<Type>),
}

impl Type {
    /// Returns whether this type is a valid "pointee" type, i.e. suitable as the inner type
    /// for a pointer type.
    pub fn is_pointee(&self) -> bool {
        !matches!(
            self,
            Type::Void | Type::Label | Type::Metadata | Type::Token | Type::X86Amx
        )
    }

    /// Create a new named (non-anonymous) struct type with the given fields.
    pub fn new_named_struct(name: String, fields: Vec<Type>) -> Self {
        Type::Struct(StructType {
            name: Some(name),
            fields: fields,
        })
    }

    /// Create a new integral type from the given bit width.
    pub fn new_integer(bit_width: u32) -> Result<Self, IntegerTypeError> {
        let inner = IntegerType::try_from(bit_width)?;

        Ok(Type::Integer(inner))
    }

    /// Create a new pointer type from the given pointee type and address space.
    pub fn new_pointer(
        pointee: Type,
        address_space: AddressSpace,
    ) -> Result<Self, PointerTypeError> {
        let inner = PointerType::new(pointee, address_space)?;

        Ok(Type::Pointer(inner))
    }
}

/// Represents a "struct" type.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub struct StructType {
    /// This structure's name, if is has one.
    pub name: Option<String>,
    /// The individual fields of this structure.
    pub fields: Vec<Type>,
}

/// Errors that can occur when constructing an [`IntegerType`](IntegerType).
#[derive(Debug, Error)]
pub enum IntegerTypeError {
    /// The requested bit width for this integer type is invalid.
    #[error(
        "specified bit width is invalid (not in [{}, {}])",
        IntegerType::MIN_INT_BITS,
        IntegerType::MAX_INT_BITS
    )]
    BadWidth,
}

/// Represents a fixed-width integral type.
///
/// The validity of the internal width is correct by construction.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub struct IntegerType {
    /// The width of this integral type, in bits.
    bit_width: u32,
}

impl IntegerType {
    /// The minimum number of bits in a valid integer type.
    pub const MIN_INT_BITS: u32 = 1;
    /// The maximum number of bits in a valid integer type.
    pub const MAX_INT_BITS: u32 = (1 << 24) - 1;

    /// Returns the width of this integral type in bits.
    pub fn bit_width(&self) -> u32 {
        self.bit_width
    }

    /// Returns the width of this integral type in bytes.
    ///
    /// The byte width of this type may be larger than the number of bits needed.
    pub fn byte_width(&self) -> u32 {
        (self.bit_width + 7) / 8
    }
}

impl TryFrom<u32> for IntegerType {
    type Error = IntegerTypeError;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if (IntegerType::MIN_INT_BITS..=IntegerType::MAX_INT_BITS).contains(&value) {
            Ok(Self { bit_width: value })
        } else {
            Err(Self::Error::BadWidth)
        }
    }
}

/// Errors that can occur when constructing an [`PointerType`](PointerType).
#[derive(Debug, Error)]
pub enum PointerTypeError {
    /// The requested pointee type is invalid.
    #[error("invalid pointee type")]
    BadPointee,
}

/// Represents a pointer type in some address space.
///
/// The validity of the internal pointee type is correct by construction.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub struct PointerType {
    pointee: Box<Type>,
    address_space: AddressSpace,
}

impl PointerType {
    /// Create a new `PointerType`.
    pub fn new(pointee: Type, address_space: AddressSpace) -> Result<Self, PointerTypeError> {
        pointee
            .is_pointee()
            .then(|| Self {
                pointee: Box::new(pointee),
                address_space,
            })
            .ok_or(PointerTypeError::BadPointee)
    }

    /// Return a reference to the pointed-to type.
    pub fn pointee(&self) -> &Type {
        self.pointee.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_integer_type() {
        {
            // Error cases.
            assert!(IntegerType::try_from(0).is_err());
            assert!(IntegerType::try_from(IntegerType::MAX_INT_BITS + 1).is_err());
        }

        {
            // Normal cases.
            let ty = IntegerType::try_from(IntegerType::MIN_INT_BITS).unwrap();
            assert_eq!(ty.bit_width(), 1);
            assert_eq!(ty.byte_width(), 1);

            let ty = IntegerType::try_from(IntegerType::MAX_INT_BITS).unwrap();
            assert_eq!(ty.bit_width(), IntegerType::MAX_INT_BITS);
            assert_eq!(ty.byte_width(), 2097152);

            let ty = IntegerType::try_from(31).unwrap();
            assert_eq!(ty.bit_width(), 31);
            assert_eq!(ty.byte_width(), 4);

            let ty = IntegerType::try_from(32).unwrap();
            assert_eq!(ty.bit_width(), 32);
            assert_eq!(ty.byte_width(), 4);

            for i in 1..=8 {
                let ty = IntegerType::try_from(i).unwrap();
                assert_eq!(ty.bit_width(), i);
                assert_eq!(ty.byte_width(), 1);
            }
        }
    }

    #[test]
    fn test_pointer_type() {
        {
            // Error cases.
            assert!(PointerType::new(Type::Void, AddressSpace::default()).is_err());
            assert!(PointerType::new(Type::Label, AddressSpace::default()).is_err());
            assert!(PointerType::new(Type::Metadata, AddressSpace::default()).is_err());
            assert!(PointerType::new(Type::Token, AddressSpace::default()).is_err());
            assert!(PointerType::new(Type::X86Amx, AddressSpace::default()).is_err());
        }

        {
            // Normal cases.
            let ty = PointerType::new(Type::Double, AddressSpace::default()).unwrap();
            assert_eq!(ty.pointee(), &Type::Double);

            let ty =
                PointerType::new(Type::new_integer(32).unwrap(), AddressSpace::default()).unwrap();
            assert_eq!(ty.pointee(), &Type::new_integer(32).unwrap());
        }
    }
}
