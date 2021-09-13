//! Errors for `llvm-mapper`.

use llvm_bitstream::error::Error as BitstreamError;
use thiserror::Error as ThisError;

use crate::block::BlockMapError;

/// All possible errors that can occur while mapping a bitstream.
///
/// The error variants here are deeply nested.
#[non_exhaustive]
#[derive(Debug, ThisError)]
pub enum Error {
    /// We encountered an error while performing the underlying bitstream parse.
    #[error("error while parsing the bitstream: {0}")]
    Parse(#[from] BitstreamError),

    /// We couldn't unroll the stream because of a structural error.
    #[error("error while unrolling the bitstream: {0}")]
    BadUnroll(String),

    /// We couldn't map a block, for some internal reason.
    #[error("error while mapping block: {0}")]
    BadBlock(#[from] BlockMapError),
}
