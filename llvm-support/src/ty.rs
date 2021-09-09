//! Structures for managing LLVM types.

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
/// Like in the official C++ API, instances of `Type` are uniqued within their module's context.
/// The APIs provided here make it hard, albeit not impossible, to construct duplicate instances
/// of the same type.
///
/// See [`TypeId`](TypeId) for documentation of each variant.
#[allow(missing_docs)]
pub enum Type {
    Half,
    BFloat,
    Float,
    Double,
    Metadata,
    X86Fp80,
    Fp128,
    PpcFp128,
    X86Mmx,
    X86Amx,
    Token,
    Integer(u32),
    Function(Box<Type>, Vec<Type>),
    Pointer(Box<Type>),
    Struct(Vec<Type>),
    Array(u32, Box<Type>),
    FixedVector(u32, Box<Type>),
    ScalableVector(u32, Box<Type>),
}
