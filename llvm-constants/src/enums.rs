//! Enum constants for `llvm-constants`.

use num_enum::TryFromPrimitive;

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
