//! Errors for `llvm-mapper`.

use llvm_bitstream::error::Error as BitstreamError;
use thiserror::Error as ThisError;

/// All possible errors that can occur while mapping a bitstream.
#[derive(Debug, ThisError)]
pub enum Error {
    /// We encountered an error while performing the underlying bitstream parse.
    #[error("error while parsing the bitstream")]
    Parse(#[from] BitstreamError),
    /// We couldn't unroll the stream because of a structural error.
    #[error("error while unrolling the bitstream: {0}")]
    BadUnroll(String),
    /// We couldn't map a record, for any number of reasons.
    #[error("error while mapping record: {0}")]
    BadRecordMap(String),
    /// We couldn't map a block, for any number of reasons.
    #[error("error while mapping block: {0}")]
    BadBlockMap(String),
}