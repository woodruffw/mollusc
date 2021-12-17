//! Structures for mapping from bitstream records to LLVM models.
//!
//! Depending on their importance or complexity, not every record is given a dedicated
//! structure or mapping implementation. Simpler records are mapped inline within their
//! blocks.

pub mod comdat;
pub mod datalayout;

use std::num::TryFromIntError;
use std::string::FromUtf8Error;

use thiserror::Error;

pub use self::comdat::*;
pub use self::datalayout::*;
use crate::block::StrtabError;
use crate::map::{MapCtxError, Mappable};

/// Potential errors when trying to extract a string from a record.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum RecordStringError {
    /// The start index for the string is invalid.
    #[error("impossible string index: {0} >= {1} (field count)")]
    BadIndex(usize, usize),
    /// A field in the record is too large to fit in a byte.
    #[error("impossible character value in string: {0}")]
    BadCharacter(#[from] TryFromIntError),
    /// The string doesn't look like valid UTF-8.
    #[error("invalid string encoding: {0}")]
    BadEncoding(#[from] FromUtf8Error),
}

/// Potential errors when mapping a single bitstream record.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum RecordMapError {
    /// Parsing the datalayout specification failed.
    #[error("error while parsing datalayout: {0}")]
    DataLayout(#[from] DataLayoutParseError),

    /// We couldn't interpret a record field, for any number of reasons.
    #[error("error while decoding record field: {0}")]
    BadField(String),

    /// We encountered a record layout we didn't understand.
    #[error("error while mapping record: {0}")]
    BadRecordLayout(String),

    /// We encountered a string we couldn't parse.
    #[error("error while parsing string: {0}")]
    BadRecordString(#[from] RecordStringError),

    /// Our mapping context was invalid for our operation.
    #[error("invalid mapping context: {0}")]
    BadContext(#[from] MapCtxError),

    /// Retrieving a string from a string table failed.
    #[error("error while accessing string table: {0}")]
    BadStrtab(#[from] StrtabError),

    /// We encountered an unsupported feature or layout.
    #[error("unsupported: {0}")]
    Unsupported(String),
}
