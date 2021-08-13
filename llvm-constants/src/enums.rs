//! Enum constants for `llvm-constants`.

use num_enum::TryFromPrimitive;

/// Block IDs that are reserved by LLVM.
// NOTE(ww): Block IDs 0 through 7 are reserved, but only 0 (BLOCKINFO)
// is actually currently used.
#[derive(Debug)]
#[repr(u64)]
pub enum ReservedBlockId {
    /// The `BLOCKINFO` block ID.
    BlockInfo = 0,
}

/// Abbreviation IDs that are reserved by LLVM.
#[derive(Clone, Copy, Debug, TryFromPrimitive)]
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

/// Codes for each `UNABBREV_RECORD` in `BLOCKINFO`.
#[derive(Debug, TryFromPrimitive)]
#[repr(u64)]
pub enum BlockInfoCode {
    /// SETBID: `[SETBID, blockid]`
    SetBid = 1,
    /// BLOCKNAME: `[BLOCKNAME, ...name...]`
    BlockName,
    /// SETRECORDNAME: `[SETRECORDNAME, recordid, ...name...]`
    SetRecordName,
}

/// Codes for each record in `MODULE_BLOCK`.
#[derive(Debug, TryFromPrimitive)]
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
    /// See: https://llvm.org/docs/BitCodeFormat.html#module-code-globalvar-record
    GlobalVar,
    /// MODULE_CODE_FUNCTION: `[FUNCTION, ...fields...]`
    /// See: https://llvm.org/docs/BitCodeFormat.html#module-code-function-record
    Function,
    /// MODULE_CODE_ALIAS: `[ALIAS, ...fields...]`
    /// See: https://llvm.org/docs/BitCodeFormat.html#module-code-alias-record
    Alias,
    /// MODULE_CODE_GCNAME: `[GCNAME, ...string...]`
    GcName,
}
