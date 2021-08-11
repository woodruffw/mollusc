//! Errors for `llvm-bitstream`.

use llvm_bitcursor::error::Error as CursorError;
use llvm_constants::BlockInfoCode;
use num_enum::TryFromPrimitiveError;
use thiserror::Error as ThisError;

/// All possible errors that can occur while parsing a bitstream.
#[derive(Debug, ThisError)]
pub enum Error {
    /// The underlying bitstream has no more data to parse.
    #[error("bitstream has been exhausted")]
    Exhausted,
    /// The underlying [`BitCursor`](llvm_bitcursor::BitCursor) returned an error
    /// that we couldn't specialize.
    #[error("underlying bitcursor error")]
    Cursor(#[from] CursorError),
    /// We couldn't parse the wrapper structure or other data that precedes the actual bitstream.
    #[error("couldn't parse bitstream container: {0}")]
    BadContainer(String),
    /// A record in the `BLOCKINFO` block has a code that we don't know.
    /// `BLOCKINFO` must be fully interpreted in order to correctly parse the remainder of
    /// the bitstream, so this is a hard error.
    #[error("bad record code for BLOCKINFO block")]
    BadBlockInfoCode(#[from] TryFromPrimitiveError<BlockInfoCode>),
    /// An operand in a `DEFINE_ABBREV` definition has a code that we don't know.
    /// This indicates either a malformed bitstream or a new operand format that
    /// we don't yet support, so it's a hard error.
    #[error("bad operand code for DEFINE_ABBREV operand")]
    BadAbbrevOpEnc(#[from] TryFromPrimitiveError<crate::abbrev::AbbrevOpEnc>),
    /// A field value is either invalid or the incorrect type for a particular context.
    #[error("bad value for context: {0}")]
    BadValue(String),
    /// A generic error occurred while parsing the bitstream.
    #[error("error while parsing stream: {0}")]
    StreamParse(String),
    /// An error occurred while interpreting a `DEFINE_ABBREV` record.
    #[error("error while parsing abbrev record: {0}")]
    AbbrevParse(String),
    /// An error occurred while mapping an abbreviated record back to its abbreviation definition.
    #[error("unknown abbreviation for ID: {0}")]
    BadAbbrev(u64),
    /// An error occurred during block scope entrance or exit.
    #[error("error while parsing block scope: {0}")]
    BadScope(String),
}
