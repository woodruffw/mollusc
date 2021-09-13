//! `llvm-support` provides support types to the other *mollusc* crates,
//! in furtherance of the general task of parsing LLVM's bitcode.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

pub mod align;
pub mod ty;

pub use align::*;
pub use ty::*;

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
