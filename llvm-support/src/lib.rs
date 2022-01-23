//! `llvm-support` provides support types to the other *mollusc* crates,
//! in furtherance of the general task of parsing LLVM's bitcode.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

pub mod align;
pub mod attribute;
pub mod ty;

use num_enum::{IntoPrimitive, TryFromPrimitive};

pub use self::align::*;
pub use self::attribute::*;
pub use self::ty::*;

/// An exact endianness.
///
/// For an inexact endianness model (i.e., one that supports a notion of "system" endianness),
/// see [`InexactEndian`](InexactEndian)
#[derive(Debug, PartialEq)]
pub enum Endian {
    /// Little-endian.
    Little,
    /// Big-endian.
    Big,
}

/// An "inexact" endianness, i.e. one supports an unspecified system endianness.
#[derive(Debug)]
pub enum InexactEndian {
    /// Either big-endian or little-endian.
    Exact(Endian),
    /// The host system's endianness, which may not be known immediately.
    System,
}

/// Symbol mangling styles supported by LLVM.
#[derive(Debug, PartialEq)]
pub enum Mangling {
    /// ELF-style mangling.
    Elf,
    /// MIPS-style mangling.
    Mips,
    /// Mach-O-style mangling.
    Macho,
    /// COFF on x86 Windows-style mangling.
    WindowsX86Coff,
    /// COFF on Windows-style mangling.
    WindowsCoff,
    /// XCOFF-style mangling.
    XCoff,
}

/// Global value linkage types.
///
/// See: <https://llvm.org/docs/LangRef.html#linkage-types>
#[non_exhaustive]
#[derive(Debug, PartialEq)]
#[repr(u64)]
#[allow(missing_docs)]
pub enum Linkage {
    External,
    AvailableExternally,
    LinkOnceAny,
    LinkOnceOdr,
    WeakAny,
    WeakOdr,
    Appending,
    Internal,
    Private,
    ExternalWeak,
    Common,
}

impl From<u64> for Linkage {
    fn from(value: u64) -> Self {
        // See getDecodedLinkage in BitcodeReader.cpp.
        match value {
            0 | 5 | 6 | 15 => Linkage::External,
            1 | 16 => Linkage::WeakAny,
            2 => Linkage::Appending,
            3 => Linkage::Internal,
            4 | 18 => Linkage::LinkOnceAny,
            7 => Linkage::ExternalWeak,
            8 => Linkage::Common,
            9 | 13 | 14 => Linkage::Private,
            10 | 17 => Linkage::WeakOdr,
            11 | 19 => Linkage::LinkOnceOdr,
            12 => Linkage::AvailableExternally,
            _ => Linkage::External,
        }
    }
}

/// An `(offset, size)` reference to a string within some string table.
pub struct StrtabRef {
    /// The string's offset within its string table.
    pub offset: usize,
    /// The string's size, in bytes.
    pub size: usize,
}

impl From<(usize, usize)> for StrtabRef {
    fn from(value: (usize, usize)) -> Self {
        Self {
            offset: value.0,
            size: value.1,
        }
    }
}

impl From<(u64, u64)> for StrtabRef {
    fn from(value: (u64, u64)) -> Self {
        Self::from((value.0 as usize, value.1 as usize))
    }
}

/// Valid visibility styles.
///
/// See: <https://llvm.org/docs/LangRef.html#visibility-styles>
#[derive(Debug, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u64)]
pub enum Visibility {
    /// Default visibility.
    Default = 0,

    /// Hidden visibility.
    Hidden,

    /// Protected visibility.
    Protected,
}
