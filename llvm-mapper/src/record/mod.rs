//! Structures for mapping from bitstream records to LLVM models.
//!
//! Depending on their importance or complexity, not every record is given a dedicated
//! structure or mapping implementation. Simpler records are mapped inline within their
//! blocks.

pub mod comdat;
pub mod datalayout;
pub mod function;

use std::num::TryFromIntError;
use std::string::FromUtf8Error;

use thiserror::Error;

pub use self::comdat::*;
pub use self::datalayout::*;
pub use self::function::*;
use crate::block::StrtabError;

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

/// Potential errors when trying to extract a blob from a record.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum RecordBlobError {
    /// The start index for the blob is invalid.
    #[error("impossible blob index: {0} >= {1} (field count)")]
    BadIndex(usize, usize),
    /// A field in the record is too large to fit in a byte.
    #[error("impossible byte value in blob: {0}")]
    BadByte(#[from] TryFromIntError),
}

/// Potential errors when mapping a single bitstream record.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum RecordMapError {
    /// Mapping a COMDAT record failed.
    #[error("error while mapping COMDAT record: {0}")]
    Comdat(#[from] ComdatError),

    /// Parsing the datalayout specification failed.
    #[error("error while parsing datalayout: {0}")]
    DataLayout(#[from] DataLayoutError),

    /// Mapping a function record failed.
    #[error("error while mapping function record: {0}")]
    Function(#[from] FunctionError),

    /// We encountered a string we couldn't extract.
    #[error("error while extracting string: {0}")]
    BadRecordString(#[from] RecordStringError),
}
