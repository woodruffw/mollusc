//! Record parsing and handling functionality for `llvm-bitstream`.

/// A convenience alias for the fields of a record.
pub type Fields = Vec<u64>;

/// Represents a single bitstream record.
#[derive(Clone, Debug)]
pub struct Record {
    /// The abbreviation ID that was used to parse this record, or `None` if
    /// this record was parsed from an `UNABBREV_RECORD` encoding.
    pub abbrev_id: Option<u64>,

    /// The code that identifies the record's kind.
    pub code: u64,

    /// The fields of this record.
    pub fields: Fields,
}

impl Record {
    /// Creates a new `Record` from the given code and fields.
    pub fn from_unabbrev(code: u64, fields: Fields) -> Self {
        Self {
            abbrev_id: None,
            code: code,
            fields: fields,
        }
    }

    /// Creates a new `Record` from the given abbreviation ID, code, and fields.
    pub fn from_abbrev(abbrev_id: u64, code: u64, fields: Fields) -> Self {
        Self {
            abbrev_id: Some(abbrev_id),
            code: code,
            fields: fields,
        }
    }
}

/// Represents a single block scope in the bitstream.
#[derive(Debug)]
pub struct Block {
    /// The ID of the block.
    pub block_id: u64,
    /// The length of the block, in bytes. Blocks are always 32-bit-word-aligned.
    pub len: u64,
}
