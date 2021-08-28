//! `llvm-support` provides support types to the other *mollusc* crates,
//! in furtherance of the general task of parsing LLVM's bitcode.

#![deny(broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

mod align;

pub use align::*;

/// An exact endianness.
///
/// For an inexact endianness model (i.e., one that supports a notion of "system" endianness),
/// see [`InexactEndian`](InexactEndian)
#[derive(Debug)]
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
#[derive(Debug)]
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

/// A newtype for address space values.
#[derive(Debug)]
pub struct AddressSpace(u32);

impl Default for AddressSpace {
    fn default() -> Self {
        Self(0)
    }
}
