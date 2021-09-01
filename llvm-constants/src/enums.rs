//! Enum constants for `llvm-constants`.

use num_enum::TryFromPrimitive;

use crate::constants::FIRST_APPLICATION_BLOCK_ID;

/// Block IDs that are reserved by LLVM.
// NOTE(ww): Block IDs 0 through 7 are reserved, but only 0 (BLOCKINFO)
// is actually currently used.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum ReservedBlockId {
    /// The `BLOCKINFO` block ID.
    BlockInfo = 0,
    /// Reserved; no semantics.
    Reserved1 = 1,
    /// Reserved; no semantics.
    Reserved2 = 2,
    /// Reserved; no semantics.
    Reserved3 = 3,
    /// Reserved; no semantics.
    Reserved4 = 4,
    /// Reserved; no semantics.
    Reserved5 = 5,
    /// Reserved; no semantics.
    Reserved6 = 6,
    /// Reserved; no semantics.
    Reserved7 = 7,
}

/// Block IDs that are used by LLVM for bitcode (i.e., IR bitstreams).
/// See: `enum BlockIDs` in `Bitcode/LLVMBitCodes.h`,
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum IrBlockId {
    /// `MODULE_BLOCK_ID`
    Module = FIRST_APPLICATION_BLOCK_ID,
    /// `PARAM_ATTR_BLOCK_ID`
    ParamAttr,
    /// `PARAM_ATTR_GROUP_BLOCK_ID`
    ParamAttrGroup,
    /// `CONSTANTS_BLOCK_ID`
    Constants,
    /// `FUNCTION_BLOCK_ID`
    Function,
    /// `IDENTIFICATION_BLOCK_ID`.
    Identification,
    /// `VALUE_SYMTAB_BLOCK_ID`.
    ValueSymtab,
    /// `METADATA_BLOCK_ID`.
    Metadata,
    /// `METADATA_ATTACHMENT_BLOCK_ID`.
    MetadataAttachment,
    /// `TYPE_BLOCK_ID_NEW`.
    Type,
    /// `USELIST_BLOCK_ID`.
    Uselist,
    /// `MODULE_STRTAB_BLOCK_ID`.
    ModuleStrtab,
    /// `GLOBAL_VAL_SUMMARY_BLOCK_ID`.
    GlobalValSummary,
    /// `OPERAND_BUNDLE_TAGS_BLOCK_ID`.
    OperandBundleTags,
    /// `METADATA_KIND_BLOCK_ID`.
    MetadataKind,
    /// `STRTAB_BLOCK_ID`.
    Strtab,
    /// `FULL_LTO_GLOBAL_VAL_SUMMARY_BLOCK_ID`.
    FullLtoGlobalValSummary,
    /// `SYMTAB_BLOCK_ID`.
    Symtab,
    /// `SYNC_SCOPE_NAMES_BLOCK_ID`.
    SyncScopeNames,
}

/// Abbreviation IDs that are reserved by LLVM.
#[derive(Clone, Copy, Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum ReservedAbbrevId {
    /// Identifies an `END_BLOCK` record.
    EndBlock = 0,
    /// Identifies an `ENTER_SUBBLOCK` record.
    EnterSubBlock,
    /// Identifies a `DEFINE_ABBREV` record.
    DefineAbbrev,
    /// Identifies an `UNABBREV_RECORD` record.
    UnabbrevRecord,
}

/// Codes for each operand encoding type supported by `DEFINE_ABBREV`.
#[derive(Clone, Copy, Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum AbbrevOpEnc {
    /// A fixed-length, unsigned operand.
    Fixed = 1,
    /// A variable-length, unsigned operand.
    Vbr,
    /// An array of values.
    Array,
    /// A single 6-bit-encoded character.
    Char6,
    /// A blob of bytes.
    Blob,
}

/// Calling conventions supported by LLVM.
#[derive(Debug, PartialEq, TryFromPrimitive)]
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

/// Codes for each `UNABBREV_RECORD` in `BLOCKINFO`.
#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum BlockInfoCode {
    /// SETBID: `[SETBID, blockid]`
    SetBid = 1,
    /// BLOCKNAME: `[BLOCKNAME, ...name...]`
    BlockName,
    /// SETRECORDNAME: `[SETRECORDNAME, recordid, ...name...]`
    SetRecordName,
}

/// Codes for each record in `IDENTIFICATION_BLOCK`.
#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum IdentificationCode {
    /// IDENTIFICATION_CODE_STRING: `[STRING, ...string...]`
    ProducerString = 1,
    /// IDENTIFICATION_CODE_EPOCH: `[EPOCH, epoch]`
    Epoch,
}

/// Codes for each record in `MODULE_BLOCK`.
#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum ModuleCode {
    /// MODULE_CODE_VERSION: `[VERSION, version#]`
    Version = 1,
    /// MODULE_CODE_TRIPLE: `[TRIPLE, ...string...]`
    Triple,
    /// MODULE_CODE_DATALAYOUT: `[DATALAYOUT, ...string...]`
    DataLayout,
    /// MODULE_CODE_ASM: `[ASM, ...string...]`
    Asm,
    /// MODULE_CODE_SECTIONNAME: `[SECTIONNAME, ...string...]`
    SectionName,
    /// MODULE_CODE_DEPLIB: `[DEPLIB, ...string...]`
    DepLib,
    /// MODULE_CODE_GLOBALVAR: `[GLOBALVAR, ...fields...]`
    /// See: <https://llvm.org/docs/BitCodeFormat.html#module-code-globalvar-record>
    GlobalVar,
    /// MODULE_CODE_FUNCTION: `[FUNCTION, ...fields...]`
    /// See: <https://llvm.org/docs/BitCodeFormat.html#module-code-function-record>
    Function,
    /// MODULE_CODE_ALIAS: `[ALIAS, ...fields...]`
    /// See: <https://llvm.org/docs/BitCodeFormat.html#module-code-alias-record>
    AliasOld,
    /// MODULE_CODE_GCNAME: `[GCNAME, ...string...]`
    GcName,
    /// MODULE_CODE_COMDAT
    /// v1: `[selection_kind, name]`
    /// v2: `[strtab_offset, strtab_size, selection_kind]`
    /// Only `v2` is currently supported.
    Comdat,
    /// MODULE_CODE_VSTOFFSET: `[VSTOFFSET, offset]`
    VstOffset,
    /// MODULE_CODE_ALIAS: `[ALIAS, ...fields...]`
    /// Not well documented; see `ModuleCodes` in `Bitcode/LLVMBitCodes.h`.
    Alias,
    /// MODULE_CODE_METADATA_VALUES_UNUSED
    /// Not documented at all; see `ModuleCodes` in `Bitcode/LLVMBitCodes.h`.
    MetadataValuesUnused,
    /// MODULE_CODE_SOURCE_FILENAME: `[SOURCE_FILENAME, ...string...]`
    SourceFilename,
    /// MODULE_CODE_HASH: `[HASH, 5*i32]`
    Hash,
    /// MODULE_CODE_IFUNC: `[IFUNC, ...fields...]`
    /// Not well documented; see `ModuleCodes` in `Bitcode/LLVMBitCodes.h`.
    IFunc,
}

/// Codes for each record in `STRTAB_BLOCK`.
#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum StrtabCode {
    /// STRTAB_BLOB: `[BLOB, ...string...]`
    Blob = 1,
}

/// Codes for each record in `SYMTAB_BLOCK`.
#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum SymtabCode {
    /// SYMTAB_BLOB: `[BLOB, ...string...]`
    Blob = 1,
}
