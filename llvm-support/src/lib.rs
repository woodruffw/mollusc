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

/// DLL storage classes.
///
/// See: <https://llvm.org/docs/LangRef.html#dllstorageclass>
#[derive(Debug, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u64)]
pub enum DllStorageClass {
    /// The default storage class.
    Default = 0,

    /// The `dllimport` storage class.
    Import,

    /// The `dllexport` storage class.
    Export,
}

/// Thread local storage modes.
///
/// See: <https://llvm.org/docs/LangRef.html#thread-local-storage-models>
/// See also: <https://www.akkadia.org/drepper/tls.pdf>
#[derive(Debug, PartialEq, IntoPrimitive)]
#[repr(u64)]
pub enum ThreadLocalMode {
    /// Not thread local.
    NotThreadLocal = 0,

    /// The general dynamic TLS model.
    GeneralDynamicTls,

    /// The local dynamic TLS model.
    LocalDynamicTls,

    /// The initial exec TLS model.
    InitialExecTls,

    /// The local exec TLS model.
    LocalExecTls,
}

impl From<u64> for ThreadLocalMode {
    fn from(value: u64) -> ThreadLocalMode {
        match value {
            0 => ThreadLocalMode::NotThreadLocal,
            1 => ThreadLocalMode::GeneralDynamicTls,
            2 => ThreadLocalMode::LocalDynamicTls,
            3 => ThreadLocalMode::InitialExecTls,
            4 => ThreadLocalMode::LocalExecTls,
            // Unknown values are treated as general dynamic.
            _ => ThreadLocalMode::GeneralDynamicTls,
        }
    }
}

/// The `unnamed_addr` specifier.
#[derive(Debug, PartialEq, IntoPrimitive)]
#[repr(u64)]
pub enum UnnamedAddr {
    /// No `unnamed_addr`.
    None = 0,

    /// The address of this variable is not significant.
    Global,

    /// The address of this variable is not significant, but only within the module.
    Local,
}

impl From<u64> for UnnamedAddr {
    fn from(value: u64) -> UnnamedAddr {
        match value {
            0 => UnnamedAddr::None,
            1 => UnnamedAddr::Global,
            2 => UnnamedAddr::Local,
            // Unknown values are treated as having no `unnamed_addr` specifier.
            _ => UnnamedAddr::None,
        }
    }
}

/// The runtime preemption specifier.
///
/// See: <https://llvm.org/docs/LangRef.html#runtime-preemption-model>
#[derive(Debug, PartialEq, IntoPrimitive)]
#[repr(u64)]
pub enum RuntimePreemption {
    /// The function or variable may be replaced by a symbol from outside the linkage
    /// unit at runtime.
    DsoPreemptable,

    /// The compiler may assume that the function or variable will resolve to a symbol within
    /// the same linkage unit.
    DsoLocal,
}

impl From<u64> for RuntimePreemption {
    fn from(value: u64) -> RuntimePreemption {
        match value {
            0 => RuntimePreemption::DsoPreemptable,
            1 => RuntimePreemption::DsoLocal,
            // Unknown values are treated as `dso_preemptable`.
            _ => RuntimePreemption::DsoPreemptable,
        }
    }
}
