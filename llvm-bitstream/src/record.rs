//! Record parsing and handling functionality for `llvm-bitstream`.

use std::convert::TryFrom;

use crate::error::Error;

/// A higher-level representation of the individual values potentially found
/// in a `Record`. The members here correspond roughly to
/// [`AbbrevOpEnc`](crate::abbrev::AbbrevOpEnc).
#[derive(Clone, Debug)]
pub enum Value {
    /// An unsigned value, which may have come from a fixed field or a VBR.
    Unsigned(u64),
    /// An array of values.
    Array(Vec<Value>),
    /// A single Char6-encoded character.
    Char6(u8),
    /// An array of 8-bit objects.
    Blob(Vec<u8>),
}

impl TryFrom<Value> for u64 {
    type Error = Error;

    fn try_from(value: Value) -> Result<u64, Self::Error> {
        if let Value::Unsigned(val) = value {
            return Ok(val);
        }

        Err(Error::BadValue(format!(
            "expected Unsigned, but was {:?}",
            value
        )))
    }
}

/// Represents a single bitstream record.
#[derive(Debug)]
pub struct Record {
    /// The abbreviation ID that was used to parse this record, or `None` if
    /// this record was parsed from an `UNABBREV_RECORD` encoding.
    pub abbrev_id: Option<u64>,

    /// The code that identifies the record's kind.
    pub code: u64,

    /// The fields of this record.
    pub values: Vec<Value>,
}

impl Record {
    /// Creates a new `Record` from the given code and values.
    pub fn from_unabbrev(code: u64, values: Vec<Value>) -> Self {
        Self {
            abbrev_id: None,
            code: code,
            values: values,
        }
    }

    /// Creates a new `Record` from the given abbreviation ID, code, and values.
    pub fn from_abbrev(abbrev_id: u64, code: u64, values: Vec<Value>) -> Self {
        Self {
            abbrev_id: Some(abbrev_id),
            code: code,
            values: values,
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
