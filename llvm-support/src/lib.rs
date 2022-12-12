//! `llvm-support` provides support types to the other *mollusc* crates,
//! in furtherance of the general task of parsing LLVM's bitcode.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

pub mod align;
pub mod attribute;
pub mod bitcodes;
pub mod opcode;
pub mod ty;

use num_enum::{IntoPrimitive, TryFromPrimitive};

pub use self::align::*;
pub use self::attribute::*;
pub use self::opcode::*;
pub use self::ty::*;

/// The 32-bit magic that indicates a raw LLVM IR bitcode stream.
pub const LLVM_IR_MAGIC: u32 = 0xdec04342;

/// The 32-bit magic that indicates a bitcode wrapper, which in
/// turn points to the start of the actual bitcode stream.
pub const BITCODE_WRAPPER_MAGIC: u32 = 0x0b17c0de;

/// The initial abbreviation ID width in a bitstream.
pub const INITIAL_ABBREV_ID_WIDTH: u64 = 2;

/// All abbreviation IDs before this are defined by the bitstream format,
/// rather than the stream itself.
pub const FIRST_APPLICATION_ABBREV_ID: usize = 4;

/// All block IDs before this have their semantics defined by the bitstream
/// format, rather than the stream itself.
pub const FIRST_APPLICATION_BLOCK_ID: u64 = 8;

/// The lookup alphabet for the Char6 operand encoding.
pub const CHAR6_ALPHABET: &[u8] =
    b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._";

/// The current toolchain's target triple.
pub const TARGET_TRIPLE: &str = env!("TARGET_TRIPLE");

/// An exact endianness.
///
/// For an inexact endianness model (i.e., one that supports a notion of "system" endianness),
/// see [`InexactEndian`](InexactEndian)
#[derive(Debug, PartialEq, Eq)]
pub enum Endian {
    /// Little-endian.
    Little,
    /// Big-endian.
    Big,
}

/// An "inexact" endianness, i.e. one that supports an unspecified system endianness.
#[derive(Debug)]
pub enum InexactEndian {
    /// Either big-endian or little-endian.
    Exact(Endian),
    /// The host system's endianness, which may not be known immediately.
    System,
}

/// Symbol mangling styles supported by LLVM.
#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
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
#[derive(Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
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
#[derive(Debug, PartialEq, Eq, IntoPrimitive)]
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
#[derive(Debug, PartialEq, Eq, IntoPrimitive)]
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
#[derive(Debug, PartialEq, Eq, IntoPrimitive)]
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

/// Calling conventions supported by LLVM.
#[non_exhaustive]
#[derive(Debug, PartialEq, Eq, TryFromPrimitive)]
#[repr(u64)]
#[allow(missing_docs)]
pub enum CallingConvention {
    C = 0,
    Fast = 8,
    Cold = 9,
    GHC = 10,
    HiPE = 11,
    WebKitJS = 12,
    AnyReg = 13,
    PreserveMost = 14,
    PreserveAll = 15,
    Swift = 16,
    CXXFASTTLS = 17,
    X86Stdcall = 64,
    X86Fastcall = 65,
    ARMAPCS = 66,
    ARMAAPCS = 67,
    ARMAAPCSVFP = 68,
    MSP430INTR = 69,
    X86ThisCall = 70,
    PTXKernel = 71,
    PTXDevice = 72,
    SPIRFUNC = 75,
    SPIRKERNEL = 76,
    IntelOCLBI = 77,
    X8664SysV = 78,
    Win64 = 79,
    X86VectorCall = 80,
    HHVM = 81,
    HHVMC = 82,
    X86INTR = 83,
    AVRINTR = 84,
    AVRSIGNAL = 85,
    AVRBUILTIN = 86,
    AMDGPUVS = 87,
    AMDGPUGS = 88,
    AMDGPUPS = 89,
    AMDGPUCS = 90,
    AMDGPUKERNEL = 91,
    X86RegCall = 92,
    AMDGPUHS = 93,
    MSP430BUILTIN = 94,
    AMDGPULS = 95,
    AMDGPUES = 96,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_target_triple() {
        assert!(!TARGET_TRIPLE.is_empty());
    }
}
