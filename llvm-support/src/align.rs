//! A typesafe representation of alignment states and operations that
//! preserves LLVM's alignment invariants.

use std::fmt::{Debug, Error as FmtError, Formatter};

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
pub struct Align(u8);

impl Debug for Align {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        f.debug_struct("Align")
            .field("byte_align", &self.byte_align())
            .finish()
    }
}

impl Align {
    /// The maximum alignment shift representable with this type.
    pub const MAX_SHIFT: u8 = 63;

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

#[cfg(test)]
mod tests {
    use super::*;

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
}
