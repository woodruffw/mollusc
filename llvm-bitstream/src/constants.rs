//! Constants for `llvm-bitstream`.

use num_enum::TryFromPrimitive;

/// The 32-bit magic that indicates a raw LLVM IR bitcode stream.
pub const LLVM_IR_MAGIC: u32 = 0xdec04342;

/// The 32-bit magic that indicates a bitcode wrapper, which in
/// turn points to the start of the actual bitcode stream.
pub const BITCODE_WRAPPER_MAGIC: u32 = 0x0b17c0de;

/// Block IDs that are reserved by LLVM.
// NOTE(ww): Block IDs 0 through 7 are reserved, but only 0 (BLOCKINFO)
// is actually currently used.
#[derive(Debug)]
#[repr(u64)]
pub enum BlockId {
    /// The `BLOCKINFO` block ID.
    BlockInfo = 0,
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
