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
    Function(FunctionType),
    Pointer(PointerType),
    OpaquePointer(AddressSpace),
    Struct(StructType),
    Array(ArrayType),
    FixedVector(VectorType),
    ScalableVector(VectorType),
}

impl Type {
    /// Returns whether this type is one of the floating point types.
    ///
    /// ```rust
    /// use llvm_support::Type;
    ///
    /// assert!(Type::BFloat.is_floating());
    /// assert!(Type::Float.is_floating());
    /// assert!(Type::Double.is_floating());
    /// assert!(Type::X86Fp80.is_floating());
    /// assert!(Type::Fp128.is_floating());
    /// assert!(Type::PpcFp128.is_floating());
    /// assert!(!Type::Metadata.is_floating());
    /// ```
    pub fn is_floating(&self) -> bool {
        matches!(
            self,
            Type::Half
                | Type::BFloat
                | Type::Float
                | Type::Double
                | Type::X86Fp80
                | Type::Fp128
                | Type::PpcFp128
        )
    }

    /// Returns whether this type is an integer type.
    pub fn is_integer(&self) -> bool {
        matches!(self, Type::Integer(_))
    }

    /// Returns whether this type is a valid "pointee" type, i.e. suitable as the inner type
    /// for a pointer type.
    pub fn is_pointee(&self) -> bool {
        !matches!(
            self,
            Type::Void | Type::Label | Type::Metadata | Type::Token | Type::X86Amx
        )
    }

    /// Returns whether this type is a valid array element type, i.e. is suitable as the inner type
    /// for an array type.
    pub fn is_array_element(&self) -> bool {
        !matches!(
            self,
            Type::Void
                | Type::Label
                | Type::Metadata
                | Type::Function(_)
                | Type::Token
                | Type::X86Amx
                | Type::ScalableVector(_)
        )
    }

    /// Returns whether this type is a valid structure element type, i.e. is suitable as a field
    /// type within a structure type.
    pub fn is_struct_element(&self) -> bool {
        !matches!(
            self,
            Type::Void | Type::Label | Type::Metadata | Type::Function(_) | Type::Token
        )
    }

    /// Returns whether this type is a valid vector element type, i.e. is suitable as the inner
    /// type for a vector type.
    ///
    /// ```rust
    /// use llvm_support::{AddressSpace, Type};
    ///
    /// assert!(Type::Float.is_vector_element());
    /// assert!(Type::new_integer(32).unwrap().is_vector_element());
    /// assert!(
    ///     Type::new_pointer(Type::new_integer(8).unwrap(), AddressSpace::default())
    ///     .unwrap()
    ///     .is_vector_element()
    /// );
    /// assert!(!Type::Metadata.is_vector_element());
    /// ```
    pub fn is_vector_element(&self) -> bool {
        self.is_floating() || matches!(self, Type::Integer(_) | Type::Pointer(_))
    }

    /// Returns whether this type is "first class", i.e. is a valid type for an LLVM value.
    fn is_first_class(&self) -> bool {
        !matches!(self, Type::Function(_) | Type::Void)
    }

    /// Returns whether this type is a valid argument type, i.e. is suitable as an argument
    /// within a function type.
    ///
    /// ```rust
    /// use llvm_support::Type;
    ///
    /// assert!(Type::Float.is_argument());
    /// assert!(!Type::Void.is_argument());
    /// ```
    pub fn is_argument(&self) -> bool {
        self.is_first_class()
    }

    /// Returns whether this type is a valid return type, i.e. is suitable as the return type
    /// within a function type.
    pub fn is_return(&self) -> bool {
        !matches!(self, Type::Function(_) | Type::Label | Type::Metadata)
    }

    /// Return the scalar type for this type.
    ///
    /// This is always the identity type for non-vector types, and the element type for vector types.
    pub fn scalar_type(&self) -> &Self {
        match &self {
            Type::ScalableVector(VectorType {
                num_elements: _,
                element_type,
                ..
            }) => element_type,
            Type::FixedVector(VectorType {
                num_elements: _,
                element_type,
                ..
            }) => element_type,
            _ => self,
        }
    }

    /// Returns whether this type is a floating-point type or a vector type
    /// of floating points.
    pub fn is_floating_or_floating_vector(&self) -> bool {
        self.scalar_type().is_floating()
    }

    /// Returns whether this type is a integer type or a vector type
    /// of integers.
    pub fn is_integer_or_integer_vector(&self) -> bool {
        self.scalar_type().is_integer()
    }

    /// Create a new struct type with the given fields.
    pub fn new_struct(
        name: Option<String>,
        fields: Vec<Type>,
        is_packed: bool,
    ) -> Result<Self, StructTypeError> {
        let inner = StructType::new(name, fields, is_packed)?;

        Ok(Type::Struct(inner))
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

    /// Create a new array type of the given size and element type.
    pub fn new_array(num_elements: u64, element_type: Type) -> Result<Self, ArrayTypeError> {
        let inner = ArrayType::new(num_elements, element_type)?;

        Ok(Type::Array(inner))
    }

    /// Create a new scalable vector type of the given size and element type.
    pub fn new_scalable_vector(
        num_elements: u64,
        element_type: Type,
    ) -> Result<Self, VectorTypeError> {
        let inner = VectorType::new(num_elements, element_type)?;

        Ok(Type::ScalableVector(inner))
    }

    /// Create a new (fixed) vector type of the given size and element type.
    pub fn new_vector(num_elements: u64, element_type: Type) -> Result<Self, VectorTypeError> {
        let inner = VectorType::new(num_elements, element_type)?;

        Ok(Type::FixedVector(inner))
    }

    /// Create a new function type of the given return type, parameter types, and variadic disposition.
    pub fn new_function(
        return_type: Type,
        param_types: Vec<Type>,
        is_vararg: bool,
    ) -> Result<Self, FunctionTypeError> {
        let inner = FunctionType::new(return_type, param_types, is_vararg)?;

        Ok(Type::Function(inner))
    }
}

/// Errors that can occur when constructing an [`StructType`](StructType).
#[derive(Debug, Error)]
pub enum StructTypeError {
    /// The requested element type is invalid.
    #[error("invalid structure element type: {0:?}")]
    BadElement(Type),
}

/// Represents a "struct" type.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub struct StructType {
    /// This structure's name, if is has one.
    pub name: Option<String>,
    /// The individual fields of this structure.
    pub fields: Vec<Type>,
    /// Whether the fields of this structure are packed.
    is_packed: bool,
}

impl StructType {
    /// Create a new `StructType`.
    pub fn new(
        name: Option<String>,
        fields: Vec<Type>,
        is_packed: bool,
    ) -> Result<Self, StructTypeError> {
        if let Some(bad) = fields.iter().find(|t| !t.is_struct_element()) {
            Err(StructTypeError::BadElement(bad.clone()))
        } else {
            Ok(Self {
                name,
                fields,
                is_packed,
            })
        }
    }
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    #[error("invalid pointee type: {0:?}")]
    BadPointee(Type),
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
        if pointee.is_pointee() {
            Ok(Self {
                pointee: Box::new(pointee),
                address_space,
            })
        } else {
            Err(PointerTypeError::BadPointee(pointee))
        }
    }

    /// Return a reference to the pointed-to type.
    pub fn pointee(&self) -> &Type {
        self.pointee.as_ref()
    }
}

/// Errors that can occur when constructing an [`ArrayType`](ArrayType).
#[derive(Debug, Error)]
pub enum ArrayTypeError {
    /// The requested element type is invalid.
    #[error("invalid array element type: {0:?}")]
    BadElement(Type),
}

/// Represents an array type.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub struct ArrayType {
    num_elements: u64,
    element_type: Box<Type>,
}

impl ArrayType {
    /// Create a new `ArrayType`.
    pub fn new(num_elements: u64, element_type: Type) -> Result<Self, ArrayTypeError> {
        if element_type.is_array_element() {
            Ok(Self {
                num_elements,
                element_type: Box::new(element_type),
            })
        } else {
            Err(ArrayTypeError::BadElement(element_type))
        }
    }

    /// Return a reference to the inner element type.
    pub fn element(&self) -> &Type {
        self.element_type.as_ref()
    }
}

/// Errors that can occur when constructing a [`VectorType`](VectorType).
#[derive(Debug, Error)]
pub enum VectorTypeError {
    /// The requested element type is invalid.
    #[error("invalid vector element type: {0:?}")]
    BadElement(Type),
}

/// Represents an vector type.
///
/// This vector may be fixed or scaled; which one is determined by its surrounding
/// [`Type`](Type) variant.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub struct VectorType {
    num_elements: u64,
    element_type: Box<Type>,
}

impl VectorType {
    /// Create a new `VectorType`.
    pub fn new(num_elements: u64, element_type: Type) -> Result<Self, VectorTypeError> {
        if element_type.is_vector_element() {
            Ok(Self {
                num_elements,
                element_type: Box::new(element_type),
            })
        } else {
            Err(VectorTypeError::BadElement(element_type))
        }
    }

    /// Return a reference to the inner element type.
    pub fn element(&self) -> &Type {
        self.element_type.as_ref()
    }
}

/// Errors that can occur when constructing a [`FunctionType`](FunctionType).
#[derive(Debug, Error)]
pub enum FunctionTypeError {
    /// The requested return type is invalid.
    #[error("invalid function return type: {0:?}")]
    BadReturn(Type),
    /// The requested parameter type is invalid.
    #[error("invalid function parameter type: {0:?}")]
    BadParameter(Type),
}

/// Represents an function type.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub struct FunctionType {
    return_type: Box<Type>,
    param_types: Vec<Type>,
    is_vararg: bool,
}

impl FunctionType {
    /// Create a new `FunctionType`.
    pub fn new(
        return_type: Type,
        param_types: Vec<Type>,
        is_vararg: bool,
    ) -> Result<Self, FunctionTypeError> {
        if !return_type.is_return() {
            Err(FunctionTypeError::BadReturn(return_type))
        } else if let Some(bad) = param_types.iter().find(|ty| !ty.is_argument()) {
            Err(FunctionTypeError::BadParameter(bad.clone()))
        } else {
            Ok(FunctionType {
                return_type: Box::new(return_type),
                param_types,
                is_vararg,
            })
        }
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
