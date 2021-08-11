//! Error management for `llvm-bitcursor`.

use thiserror::Error as ThisError;

/// All errors potentially produced by `llvm-bitcursor` APIs.
/// Consumers should *not* attempt to match specific variants of this error type.
#[non_exhaustive]
#[derive(Debug, ThisError)]
pub enum Error {
    /// A read or other I/O operation encountered the end of the inner buffer.
    #[error("EOF while reading")]
    Eof,
    /// A user attempted to call [`BitCursor::new_with_len`](crate::BitCursor::new_with_len) with
    /// an impossible length (larger that the supplied buffer).
    #[error("invalid length for buffer supplied to cursor")]
    InvalidLength,
    /// A generic API (e.g. [`BitCursor::read_as`](crate::BitCursor::read_as)) was asked to
    /// read a value larger than the requested type could represent.
    #[error("loss of data with cast")]
    BadCast,
    /// A read API was called with an invalid bitsize (too small or large).
    #[error("invalid read size (zero or too large)")]
    InvalidReadSize,
    /// A VBR read API was called with an invalid VBR width.
    #[cfg(any(feature = "vbr", doc))]
    #[error("invalid VBR width (must be > 1 but <= system word width)")]
    InvalidVbrWidth,
    /// An I/O operation completed partially, but the inner buffer ended before it full completion.
    #[error("too little data to service request")]
    Short,
}
