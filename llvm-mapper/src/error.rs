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
    #[error("error while parsing the bitstream")]
    Parse(#[from] BitstreamError),

    /// We couldn't unroll the stream because of a structural error.
    #[error("error while unrolling the bitstream: {0}")]
    Unroll(String),

    /// We couldn't perform the bitstream map.
    #[error("error while mapping the bitsteam")]
    Map(#[from] BlockMapError),
}
