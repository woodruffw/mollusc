//! A typesafe representation of alignment states and operations that
//! preserves LLVM's alignment invariants.

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::{Debug, Display, Error as FmtError, Formatter, Result as FmtResult};

use paste::paste;
use thiserror::Error;

/// Errors that can occur when constructing an [`Align`](Align)
#[derive(Debug, Error)]
pub enum AlignError {
    /// The shift would exceed our maximum shift value.
    #[error("supplied shift is too large ({0} > {})", Align::MAX_SHIFT)]
    ShiftTooBig(u8),
    /// The input used to compute the shift is not a power of two.
    #[error("supplied value is not a power of two: {0}")]
    NotPowerOfTwo(u64),
    /// The input used to compute the shift is not a byte multiple.
    #[error("supplied value is not a multiple of 8: {0}")]
    NotByteMultiple(u64),
}

/// A size efficient, opaque representation of bytewise alignment.
///
/// See `Alignment.h` for LLVM's corresponding structures.
#[derive(Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct Align(u8);

impl Debug for Align {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        f.debug_struct("Align")
            .field("byte_align", &self.byte_align())
            .finish()
    }
}

impl Display for Align {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.byte_align())
    }
}

macro_rules! make_const_align {
    ($align:literal, $shift:literal) => {
        paste! {
            /// A convenience handle for types of exactly $width bits.
            pub const [< ALIGN $align >]: Align = Align($shift);
        }
    };
}

impl Align {
    /// The maximum alignment shift representable with this type.
    pub const MAX_SHIFT: u8 = 63;

    make_const_align!(8, 0);
    make_const_align!(16, 1);
    make_const_align!(32, 2);
    make_const_align!(64, 3);
    make_const_align!(128, 4);

    /// Returns whether `value` is a power of two, for `value > 0`.
    #[inline(always)]
    fn is_pow2(value: u64) -> bool {
        (value > 0) && ((value & (value - 1)) == 0)
    }

    /// Returns the log2 of `value`, for `value > 0`. The result is floored.
    #[inline(always)]
    fn log2(value: u64) -> u8 {
        // NOTE(ww): u8 truncation is sound here, since log2(u64::MAX) == 64.
        ((u64::from(u64::BITS) - 1) - u64::from(value.leading_zeros())) as u8
    }

    /// Create an `Align` from the given shift value, returning an error if the requested
    /// shift is invalid.
    pub fn from_shift(shift: u8) -> Result<Align, AlignError> {
        match shift > Align::MAX_SHIFT {
            false => Ok(Align(shift)),
            true => Err(AlignError::ShiftTooBig(shift)),
        }
    }

    /// Create an `Align` from the given byte alignment value, returning an error if the requested
    /// shift is invalid.
    pub fn from_byte_align(byte_align: u64) -> Result<Align, AlignError> {
        match Align::is_pow2(byte_align) {
            true => Align::from_shift(Align::log2(byte_align)),
            false => Err(AlignError::NotPowerOfTwo(byte_align)),
        }
    }

    /// Create an `Align` from the given bit alignment value, returning an error if the requested
    /// shift is invalid.
    pub fn from_bit_align(bit_align: u64) -> Result<Align, AlignError> {
        match bit_align % 8 == 0 {
            true => Align::from_byte_align(bit_align / 8),
            false => Err(AlignError::NotByteMultiple(bit_align)),
        }
    }

    /// Return this alignment's shift value, i.e. the power of two for the alignment.
    pub fn shift(&self) -> u8 {
        self.0
    }

    /// Return this alignment as a byte-granular alignment.
    pub fn byte_align(&self) -> u64 {
        1 << self.0
    }

    /// Return this alignment as a bit-granular alignment.
    pub fn bit_align(&self) -> u64 {
        self.byte_align() * 8
    }
}

/// Errors that can occur when constructing an [`AlignedTypeWidth`](AlignedTypeWidth)
#[derive(Debug, Error)]
pub enum AlignedTypeWidthError {
    /// The requested bit width is zero, which is nonsense (every non-aggregate type
    /// carries a nonzero width).
    #[error("bit width for type cannot be zero")]
    Zero,
    /// The requested bit width exceeds our support.
    #[error(
        "bit width for type is too large ({0} > {} bits)",
        AlignedTypeWidth::MAX
    )]
    TooBig(u32),
}

/// An invariant-preserving newtype for representing the bitwidth of an
/// alignable type.
#[derive(Debug, Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct AlignedTypeWidth(u32);

macro_rules! make_const_width {
    ($width:literal) => {
        paste! {
            /// A convenience handle for types of exactly $width bits.
            pub const [< WIDTH $width >]: AlignedTypeWidth = AlignedTypeWidth($width);
        }
    };
}

impl AlignedTypeWidth {
    /// The maximum type width, in bits, representable in this structure.
    pub const MAX: u32 = (1 << 23) - 1;

    // Common infallible widths, for convenience.
    make_const_width!(1);
    make_const_width!(8);
    make_const_width!(16);
    make_const_width!(32);
    make_const_width!(64);
    make_const_width!(128);
}

impl TryFrom<u32> for AlignedTypeWidth {
    type Error = AlignedTypeWidthError;
    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value > 0 && value <= AlignedTypeWidth::MAX {
            true => Ok(AlignedTypeWidth(value)),
            false => Err(AlignedTypeWidthError::TooBig(value)),
        }
    }
}

/// An enumeration of alignable non-pointer types.
#[derive(Debug, Eq, PartialEq)]
pub enum AlignedType {
    /// Aggregate types.
    Aggregate,
    /// Floating point types.
    Float(AlignedTypeWidth),
    /// Integer types.
    Integer(AlignedTypeWidth),
    /// Vector types.
    Vector(AlignedTypeWidth),
}

impl PartialOrd for AlignedType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AlignedType {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            // AlignedTypes are ordered first by their type, and then by their bitwidth.
            // Per LLVM, the type ordering is: aggregate < float < integer < vector.

            // Aggregate types are ordered lowest. They don't have a width, so two
            // aggregate types are always equal.
            (AlignedType::Aggregate, AlignedType::Aggregate) => Ordering::Equal,
            (AlignedType::Aggregate, _) => Ordering::Less,

            // Float types are ordered second lowest.
            (AlignedType::Float(_), AlignedType::Aggregate) => Ordering::Greater,
            (AlignedType::Float(lhs), AlignedType::Float(rhs)) => lhs.cmp(rhs),
            (AlignedType::Float(_), AlignedType::Integer(_) | AlignedType::Vector(_)) => {
                Ordering::Less
            }

            // Integer types are ordered third lowest.
            (AlignedType::Integer(_), AlignedType::Aggregate | AlignedType::Float(_)) => {
                Ordering::Greater
            }
            (AlignedType::Integer(lhs), AlignedType::Integer(rhs)) => lhs.cmp(rhs),
            (AlignedType::Integer(_), AlignedType::Vector(_)) => Ordering::Less,

            // Vector types are ordered highest.
            (
                AlignedType::Vector(_),
                AlignedType::Aggregate | AlignedType::Float(_) | AlignedType::Integer(_),
            ) => Ordering::Greater,
            (AlignedType::Vector(lhs), AlignedType::Vector(rhs)) => lhs.cmp(rhs),
        }
    }
}

macro_rules! make_const_aligned {
    ($name:ident, $width:literal) => {
        paste! {
            /// A $width bit $name:lower, subject to some alignment rules.
            pub const [< $name:upper $width >]: AlignedType = AlignedType::$name(AlignedTypeWidth::[< WIDTH $width >]);
        }
    }
}

impl AlignedType {
    // Common infallible aligned types, for convenience.
    make_const_aligned!(Float, 16);
    make_const_aligned!(Float, 32);
    make_const_aligned!(Float, 64);
    make_const_aligned!(Float, 128);
    make_const_aligned!(Integer, 1);
    make_const_aligned!(Integer, 8);
    make_const_aligned!(Integer, 16);
    make_const_aligned!(Integer, 32);
    make_const_aligned!(Integer, 64);
}

/// Errors that can occur when constructing a [`TypeAlignElem`](TypeAlignElem).
#[derive(Debug, Error)]
pub enum TypeAlignElemError {
    /// The underlying type being specified has a bad width.
    #[error("impossible bit width for underlying aligned type")]
    BadTypeWidth(#[from] AlignedTypeWidthError),
    /// The supplied preferred alignment isn't greater than or equal to the ABI minimum
    #[error("impossible preferred alignment: {0} must be >= {1}")]
    AlignPref(Align, Align),
    /// The supplied ABI alignment is too large.
    #[error(
        "impossible ABI alignment for type: {0} > {}",
        TypeAlignElem::MAX_ALIGN
    )]
    AbiAlignTooLarge(Align),
}

/// Represents an alignable type, along with its ABI-mandated and
/// preferred alignments (which may differ).
#[non_exhaustive]
#[derive(Debug, Eq, PartialEq)]
pub struct TypeAlignElem {
    /// The type being aligned.
    pub aligned_type: AlignedType,
    /// The ABI-enforced alignment for the type.
    pub abi_alignment: Align,
    /// The preferred alignment for the type.
    ///
    /// NOTE: This **must** be greater than or equal to the ABI alignment.
    /// This invariant is preserved during construction.
    pub preferred_alignment: Align,
}

impl PartialOrd for TypeAlignElem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.aligned_type.cmp(&other.aligned_type))
    }
}

impl Ord for TypeAlignElem {
    fn cmp(&self, other: &Self) -> Ordering {
        self.aligned_type.cmp(&other.aligned_type)
    }
}

impl TypeAlignElem {
    /// The maximum type width, in bits, representable in this structure.
    pub const MAX_TYPE_BIT_WIDTH: u32 = (1 << 23) - 1;

    /// The maximum alignment supported by instances of `TypeAlignElem`.
    // NOTE(ww): On top of the normal alignment invariants, `TypeAlignElem`
    // requires its alignments to be less than 2^16 bits. This is
    // to prevent unforeseen compatibility issues.
    // See: https://reviews.llvm.org/D67400
    pub const MAX_ALIGN: Align = Align(15);

    /// Create a new `TypeAlignElem` for the given `AlignedType` and alignment
    /// constraints.
    pub fn new(
        aligned_type: AlignedType,
        abi: Align,
        pref: Align,
    ) -> Result<Self, TypeAlignElemError> {
        if pref < abi {
            return Err(TypeAlignElemError::AlignPref(pref, abi));
        }

        match ((abi <= Self::MAX_ALIGN), (pref <= Self::MAX_ALIGN)) {
            (true, true) => Ok(Self {
                aligned_type: aligned_type,
                abi_alignment: abi,
                preferred_alignment: pref,
            }),
            // NOTE(ww): We don't need a special case for the preferred alignment
            // being too large here, since it's precluded by our `pref > abi` check
            // above: `pref > MAX_ALIGN && pref >= abi` implies `abi >= MAX_ALIGN`,
            // so our ABI value is always erroneous.
            (_, _) => Err(TypeAlignElemError::AbiAlignTooLarge(abi)),
        }
    }
}

/// Represents a sorted collection of [`TypeAlignElem`](TypeAlignElem)s.
#[derive(Debug)]
pub struct TypeAlignElems(Vec<TypeAlignElem>);

impl Default for TypeAlignElems {
    fn default() -> Self {
        // NOTE: The default sequence here is sorted.
        // Unwrap safety: each of these constructions is infallible.
        // TODO(ww): Use macro_rules! here to make each of these `TypeAlignElem`s
        // into an infallible constant.
        #[allow(clippy::unwrap_used)]
        Self(vec![
            TypeAlignElem::new(AlignedType::Aggregate, Align::ALIGN64, Align::ALIGN64).unwrap(),
            TypeAlignElem::new(AlignedType::FLOAT16, Align::ALIGN16, Align::ALIGN16).unwrap(),
            TypeAlignElem::new(AlignedType::FLOAT32, Align::ALIGN32, Align::ALIGN32).unwrap(),
            TypeAlignElem::new(AlignedType::FLOAT64, Align::ALIGN64, Align::ALIGN64).unwrap(),
            TypeAlignElem::new(AlignedType::FLOAT128, Align::ALIGN128, Align::ALIGN128).unwrap(),
            TypeAlignElem::new(AlignedType::INTEGER1, Align::ALIGN8, Align::ALIGN8).unwrap(),
            TypeAlignElem::new(AlignedType::INTEGER8, Align::ALIGN8, Align::ALIGN8).unwrap(),
            TypeAlignElem::new(AlignedType::INTEGER16, Align::ALIGN16, Align::ALIGN16).unwrap(),
            TypeAlignElem::new(AlignedType::INTEGER32, Align::ALIGN32, Align::ALIGN32).unwrap(),
            TypeAlignElem::new(AlignedType::INTEGER64, Align::ALIGN64, Align::ALIGN64).unwrap(),
        ])
    }
}

/// Represents a pointer width (in bits), along with its ABI-mandated and
/// preferred alignments (which may differ).
#[derive(Debug)]
pub struct PointerAlignElem {}

/// Represents a sorted collection of [`PointerAlignElem`](PointerAlignElem)s.
#[derive(Debug)]
pub struct PointerAlignElems(Vec<PointerAlignElem>);

impl Default for PointerAlignElems {
    fn default() -> Self {
        Self(vec![])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_align_constants() {
        assert_eq!(Align::ALIGN8.byte_align(), 1);
        assert_eq!(Align::ALIGN16.byte_align(), 2);
        assert_eq!(Align::ALIGN32.byte_align(), 4);
        assert_eq!(Align::ALIGN64.byte_align(), 8);
        assert_eq!(Align::ALIGN128.byte_align(), 16);
    }

    #[test]
    fn test_align_is_pow2() {
        assert!(Align::is_pow2(1));
        assert!(Align::is_pow2(2));
        assert!(Align::is_pow2(4));
        assert!(Align::is_pow2(8));
        assert!(Align::is_pow2(16));
        assert!(Align::is_pow2(32));
        assert!(Align::is_pow2(64));

        assert!(!Align::is_pow2(3));
        assert!(!Align::is_pow2(6));
        assert!(!Align::is_pow2(12));
        assert!(!Align::is_pow2(65));
    }

    #[test]
    fn test_align_compares() {
        assert_eq!(Align::from_shift(1).unwrap(), Align::from_shift(1).unwrap());
        assert!(Align::from_shift(1).unwrap() < Align::from_shift(2).unwrap());
        assert!(Align::from_shift(1).unwrap() <= Align::from_shift(2).unwrap());
        assert!(Align::from_shift(2).unwrap() > Align::from_shift(1).unwrap());
        assert!(Align::from_shift(2).unwrap() >= Align::from_shift(1).unwrap());
    }

    #[test]
    fn test_align_log2() {
        assert_eq!(Align::log2(1), 0);
        assert_eq!(Align::log2(2), 1);
        assert_eq!(Align::log2(4), 2);
        assert_eq!(Align::log2(8), 3);
        assert_eq!(Align::log2(16), 4);
        assert_eq!(Align::log2(32), 5);
        assert_eq!(Align::log2(64), 6);

        // Our internal log2 is a flooring log2.
        assert_eq!(Align::log2(65), 6);
    }

    #[test]
    fn test_align_basic() {
        for (s, ba) in &[(0, 1), (1, 2), (2, 4), (3, 8), (4, 16), (5, 32), (6, 64)] {
            let align = Align(*s);

            assert_eq!(align.shift(), *s);
            assert_eq!(align.byte_align(), *ba);
            assert_eq!(align.bit_align(), (*ba) * 8);
        }
    }

    #[test]
    fn test_align_from_byte_align() {
        assert_eq!(Align::from_byte_align(1).unwrap().shift(), 0);
        assert_eq!(Align::from_byte_align(2).unwrap().shift(), 1);
        assert_eq!(Align::from_byte_align(4).unwrap().shift(), 2);
        assert_eq!(Align::from_byte_align(8).unwrap().shift(), 3);
        assert_eq!(Align::from_byte_align(16).unwrap().shift(), 4);
        assert_eq!(Align::from_byte_align(32).unwrap().shift(), 5);
        assert_eq!(Align::from_byte_align(64).unwrap().shift(), 6);
        assert_eq!(Align::from_byte_align(128).unwrap().shift(), 7);

        assert!(Align::from_byte_align(0).is_err());
        assert!(Align::from_byte_align(3).is_err());
        assert!(Align::from_byte_align(7).is_err());
        assert!(Align::from_byte_align(22).is_err());
        assert!(Align::from_byte_align(24).is_err());
    }

    #[test]
    fn test_align_from_bit_align() {
        assert_eq!(Align::from_bit_align(8).unwrap().shift(), 0);
        assert_eq!(Align::from_bit_align(16).unwrap().shift(), 1);
        assert_eq!(Align::from_bit_align(32).unwrap().shift(), 2);
        assert_eq!(Align::from_bit_align(64).unwrap().shift(), 3);
        assert_eq!(Align::from_bit_align(128).unwrap().shift(), 4);
        assert_eq!(Align::from_bit_align(256).unwrap().shift(), 5);
        assert_eq!(Align::from_bit_align(512).unwrap().shift(), 6);
        assert_eq!(Align::from_bit_align(1024).unwrap().shift(), 7);

        assert!(Align::from_bit_align(0).is_err());
        assert!(Align::from_bit_align(1).is_err());
        assert!(Align::from_bit_align(7).is_err());
        assert!(Align::from_bit_align(9).is_err());
        assert!(Align::from_bit_align(24).is_err());
        assert!(Align::from_bit_align(33).is_err());
    }

    #[test]
    fn test_aligned_type_width() {
        for i in 1..(1 << 15) {
            assert!(AlignedTypeWidth::try_from(i).is_ok());
        }

        assert!(AlignedTypeWidth::try_from(0).is_err());
        assert!(AlignedTypeWidth::try_from(u32::MAX).is_err());
    }

    #[test]
    fn test_aligned_type_ordering() {
        assert!(
            AlignedType::Integer(AlignedTypeWidth(1)) == AlignedType::Integer(AlignedTypeWidth(1))
        );
        assert!(
            AlignedType::Vector(AlignedTypeWidth(1)) == AlignedType::Vector(AlignedTypeWidth(1))
        );
        assert!(AlignedType::Float(AlignedTypeWidth(1)) == AlignedType::Float(AlignedTypeWidth(1)));

        for i in 2..(1 << 15) {
            assert!(
                AlignedType::Integer(AlignedTypeWidth(i))
                    < AlignedType::Vector(AlignedTypeWidth(i))
            );
            assert!(
                AlignedType::Integer(AlignedTypeWidth(i))
                    <= AlignedType::Vector(AlignedTypeWidth(i))
            );

            assert!(
                AlignedType::Integer(AlignedTypeWidth(i + 1))
                    < AlignedType::Vector(AlignedTypeWidth(i - 1))
            );
            assert!(
                AlignedType::Integer(AlignedTypeWidth(i + 1))
                    <= AlignedType::Vector(AlignedTypeWidth(i - 1))
            );

            assert!(
                AlignedType::Integer(AlignedTypeWidth(i)) > AlignedType::Float(AlignedTypeWidth(i))
            );
            assert!(
                AlignedType::Integer(AlignedTypeWidth(i))
                    >= AlignedType::Float(AlignedTypeWidth(i))
            );

            assert!(
                AlignedType::Integer(AlignedTypeWidth(i + 1))
                    > AlignedType::Float(AlignedTypeWidth(i - 1))
            );
            assert!(
                AlignedType::Integer(AlignedTypeWidth(i + 1))
                    >= AlignedType::Float(AlignedTypeWidth(i - 1))
            );

            assert!(AlignedType::Integer(AlignedTypeWidth(i)) > AlignedType::Aggregate);
            assert!(AlignedType::Integer(AlignedTypeWidth(i)) >= AlignedType::Aggregate);
        }

        assert!(AlignedType::Aggregate == AlignedType::Aggregate);
    }

    #[test]
    fn test_type_align_elem() {
        // Normal cases.
        assert!(TypeAlignElem::new(
            AlignedType::Integer(AlignedTypeWidth(64)),
            Align::ALIGN64,
            Align::ALIGN64
        )
        .is_ok());
        assert!(TypeAlignElem::new(
            AlignedType::Integer(AlignedTypeWidth(64)),
            Align::ALIGN64,
            Align::ALIGN128
        )
        .is_ok());
        assert!(TypeAlignElem::new(
            AlignedType::Float(AlignedTypeWidth(32)),
            Align::ALIGN32,
            Align::ALIGN32
        )
        .is_ok());
        assert!(TypeAlignElem::new(
            AlignedType::Float(AlignedTypeWidth(32)),
            Align::ALIGN32,
            Align::ALIGN64
        )
        .is_ok());

        // Can't create with an undersized preferred alignment.
        assert_eq!(
            TypeAlignElem::new(
                AlignedType::Integer(AlignedTypeWidth(8)),
                Align(2),
                Align(1)
            )
            .unwrap_err()
            .to_string(),
            "impossible preferred alignment: 2 must be >= 4"
        );

        // Can't create with an oversized ABI alignment.
        assert_eq!(
            TypeAlignElem::new(
                AlignedType::Integer(AlignedTypeWidth(8)),
                Align(16),
                Align(16)
            )
            .unwrap_err()
            .to_string(),
            "impossible ABI alignment for type: 65536 > 32768"
        );
    }
}
