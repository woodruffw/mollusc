//! Enum constants for `llvm-constants`.

use num_enum::{IntoPrimitive, TryFromPrimitive};

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
#[non_exhaustive]
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
#[non_exhaustive]
#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum BlockInfoCode {
    /// SETBID: `[blockid]`
    SetBid = 1,
    /// BLOCKNAME: `[...name...]`
    BlockName,
    /// SETRECORDNAME: `[recordid, ...name...]`
    SetRecordName,
}

/// Codes for each record in `IDENTIFICATION_BLOCK`.
#[non_exhaustive]
#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum IdentificationCode {
    /// IDENTIFICATION_CODE_STRING: `[...string...]`
    ProducerString = 1,
    /// IDENTIFICATION_CODE_EPOCH: `[epoch]`
    Epoch,
}

/// Codes for each record in `MODULE_BLOCK`.
#[non_exhaustive]
#[derive(Debug, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u64)]
pub enum ModuleCode {
    /// MODULE_CODE_VERSION: `[version#]`
    Version = 1,
    /// MODULE_CODE_TRIPLE: `[...string...]`
    Triple,
    /// MODULE_CODE_DATALAYOUT: `[...string...]`
    DataLayout,
    /// MODULE_CODE_ASM: `[...string...]`
    Asm,
    /// MODULE_CODE_SECTIONNAME: `[...string...]`
    SectionName,
    /// MODULE_CODE_DEPLIB: `[...string...]`
    DepLib,
    /// MODULE_CODE_GLOBALVAR: `[...fields...]`
    /// See: <https://llvm.org/docs/BitCodeFormat.html#module-code-globalvar-record>
    GlobalVar,
    /// MODULE_CODE_FUNCTION: `[...fields...]`
    /// See: <https://llvm.org/docs/BitCodeFormat.html#module-code-function-record>
    Function,
    /// MODULE_CODE_ALIAS_OLD: `[...fields...]`
    /// See: <https://llvm.org/docs/BitCodeFormat.html#module-code-alias-record>
    AliasOld,
    /// MODULE_CODE_GCNAME: `[...string...]`
    GcName,
    /// MODULE_CODE_COMDAT
    /// v1: `[selection_kind, name]`
    /// v2: `[strtab_offset, strtab_size, selection_kind]`
    /// Only `v2` is currently supported.
    Comdat,
    /// MODULE_CODE_VSTOFFSET: `[offset]`
    VstOffset,
    /// MODULE_CODE_ALIAS: `[...fields...]`
    /// Not well documented; see `ModuleCodes` in `Bitcode/LLVMBitCodes.h`.
    Alias,
    /// MODULE_CODE_METADATA_VALUES_UNUSED
    /// Not documented at all; see `ModuleCodes` in `Bitcode/LLVMBitCodes.h`.
    MetadataValuesUnused,
    /// MODULE_CODE_SOURCE_FILENAME: `[...string...]`
    SourceFilename,
    /// MODULE_CODE_HASH: `[5*i32]`
    Hash,
    /// MODULE_CODE_IFUNC: `[...fields...]`
    /// Not well documented; see `ModuleCodes` in `Bitcode/LLVMBitCodes.h`.
    IFunc,
}

/// Codes for each record in `TYPE_BLOCK` (i.e., `TYPE_BLOCK_ID_NEW`).
#[derive(Debug, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u64)]
pub enum TypeCode {
    /// TYPE_CODE_NUMENTRY: `[numentries]`
    NumEntry = 1,
    /// TYPE_CODE_VOID
    Void,
    /// TYPE_CODE_FLOAT
    Float,
    /// TYPE_CODE_DOUBLE
    Double,
    /// TYPE_CODE_LABEL
    Label,
    /// TYPE_CODE_OPAQUE
    Opaque,
    /// TYPE_CODE_INTEGER: `[width]`
    Integer,
    /// TYPE_CODE_POINTER: `[pointee type]`
    Pointer,
    /// TYPE_CODE_FUNCTION_OLD: `[vararg, attrid, retty, paramty x N]`
    FunctionOld,
    /// TYPE_CODE_HALF
    Half,
    /// TYPE_CODE_ARRAY: `[numelts, eltty]`
    Array,
    /// TYPE_CODE_VECTOR: `[numelts, eltty]`
    Vector,
    /// TYPE_CODE_X86_FP80
    X86Fp80,
    /// TYPE_CODE_FP128
    Fp128,
    /// TYPE_CODE_PPC_FP128
    PpcFp128,
    /// TYPE_CODE_METADATA,
    Metadata,
    /// TYPE_CODE_X86_MMX
    X86Mmx,
    /// TYPE_CODE_STRUCT_ANON: `[ispacked, eltty x N]`
    StructAnon,
    /// TYPE_CODE_STRUCT_NAME: `[strchr x N]`
    StructName,
    /// TYPE_CODE_STRUCT_NAMED: `[ispacked, eltty x N]`
    StructNamed,
    /// TYPE_CODE_FUNCTION: `[vararg, retty, paramty x N]`
    Function,
    /// TYPE_CODE_TOKEN
    Token,
    /// TYPE_CODE_BFLOAT
    BFloat,
    /// TYPE_CODE_X86_AMX
    X86Amx,
    /// TYPE_CODE_OPAQUE_POINTER: `[addrspace]`
    OpaquePointer,
}

/// Codes for each record in `STRTAB_BLOCK`.
#[non_exhaustive]
#[derive(Debug, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u64)]
pub enum StrtabCode {
    /// STRTAB_BLOB: `[...string...]`
    Blob = 1,
}

/// Codes for each record in `SYMTAB_BLOCK`.
#[non_exhaustive]
#[derive(Debug, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u64)]
pub enum SymtabCode {
    /// SYMTAB_BLOB: `[...data...]`
    Blob = 1,
}

/// Codes for each record in `PARAMATTR_BLOCK` or `PARAMATTR_GROUP_BLOCK`.
// NOTE(ww): For whatever reason, these two blocks share the same enum for
/// record codes.
#[derive(Debug, PartialEq, IntoPrimitive, TryFromPrimitive)]
#[repr(u64)]
pub enum AttributeCode {
    /// PARAMATTR_CODE_ENTRY_OLD: `[paramidx0, attr0, paramidx1, attr1...]`
    EntryOld = 1,
    /// PARAMATTR_CODE_ENTRY: `[attrgrp0, attrgrp1, ...]`
    Entry,
    /// PARAMATTR_GRP_CODE_ENTRY: `[grpid, idx, attr0, attr1, ...]`
    GroupCodeEntry,
}
