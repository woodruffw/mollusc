//! `llvm-bitstream` is a library for interpreting files in LLVM's
//! [bitstream format](https://llvm.org/docs/BitCodeFormat.html).

#![deny(broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

pub mod abbrev;
pub mod constants;
pub mod error;
pub mod parser;
pub mod record;

use std::io::{Seek, SeekFrom};

use llvm_bitcursor::BitCursor;

use crate::constants::BITCODE_WRAPPER_MAGIC;
use crate::error::Error;
use crate::parser::StreamEntry;

/// A representation of the wrapper structure for a bitstream.
#[derive(Debug)]
pub struct BitcodeWrapper {
    /// The magic for this wrapper.
    pub magic: u32,
    /// The version for this wrapper.
    pub version: u32,
    /// The offset to the actual bitstream.
    pub offset: u32,
    /// The size of the wrapped bitstream.
    pub size: u32,
    /// A target-specific value that encodes the CPU type.
    pub cpu_type: u32,
}

/// Represents an overarching bitstream container.
///
/// This struct is responsible for managing two pieces of state:
/// 1. The application-specific magic that identifies the input
/// 2. An underlying [`StreamParser`](crate::parser::StreamParser) that can
///    be advanced to produce individual blocks and records within the bitstream.
#[derive(Debug)]
pub struct Bitstream<T: AsRef<[u8]>> {
    /// The application-specific magic associated with this bitstream.
    pub magic: u32,
    parser: parser::StreamParser<T>,
}

impl<T: AsRef<[u8]>> Bitstream<T> {
    fn from_cursor(mut cur: BitCursor<T>) -> Result<Self, Error> {
        // This isn't documented anywhere, but LLVM's BitcodeReader requires
        // all inputs to be 4-byte aligned.
        // See: `llvm::initStream` in `Bitcode/Reader/BitcodeReader.cpp`.
        if cur.byte_len() % 4 != 0 {
            return Err(Error::BadContainer("input is not 4-byte aligned".into()));
        }

        // Every bitstream starts with an aligned, 32-bit magic field.
        // There's absolutely no point in continuing the parse if we fail here.
        Ok(Self {
            magic: cur.read_exact::<u32>().map_err(|e| {
                Error::BadContainer(format!(
                    "bitstream should have begun with magic, but errored: {:?}",
                    e
                ))
            })?,
            parser: parser::StreamParser::new(cur),
        })
    }

    /// Intelligently create a new `Bitstream` from the given source, parsing
    /// the bitcode wrapper if necessary.
    pub fn from(inner: T) -> Result<(Option<BitcodeWrapper>, Self), Error> {
        log::debug!("beginning intelligent parse");
        let mut cur = BitCursor::new(&inner);

        // Read the magic to determine which parse strategy to use.
        let magic = cur.read_exact::<u32>()?;

        // The only wrapper we currently know is the bitcode wrapper.
        // If our magic doesn't match that, then we try the raw parser.
        if magic == BITCODE_WRAPPER_MAGIC {
            log::debug!("input looks like a bitcode wrapper!");
            let (wrapper, parser) = Self::from_wrapped(inner)?;
            Ok((Some(wrapper), parser))
        } else {
            log::debug!("input is probably a raw bitstream!");
            Ok((None, Self::from_raw(inner)?))
        }
    }

    /// Create a new `Bitstream` from the given source.
    ///
    /// **NOTE**: This function assumes that it's being given a "raw" bitstream,
    /// i.e. not one that's been wrapped with another container (such as the
    /// bitcode wrapper format). To parse a wrapped bitstream, use the
    /// [`from_wrapped`](Bitstream::from_wrapped) API.
    pub fn from_raw(inner: T) -> Result<Self, Error> {
        let cur = BitCursor::new(inner);
        Self::from_cursor(cur)
    }

    /// Create a new `Bitstream` from the given wrapped source.
    ///
    /// The source is parsed as if it begins with a
    /// [bitcode wrapper](https://llvm.org/docs/BitCodeFormat.html#bitcode-wrapper-format).
    /// "Raw" inputs should be parsed with [`from_raw`](Bitstream::from_raw) instead.
    pub fn from_wrapped(inner: T) -> Result<(BitcodeWrapper, Self), Error> {
        let mut cur = BitCursor::new(&inner);

        let wrapper = BitcodeWrapper {
            magic: cur.read_exact::<u32>()?,
            version: cur.read_exact::<u32>()?,
            offset: cur.read_exact::<u32>()?,
            size: cur.read_exact::<u32>()?,
            cpu_type: cur.read_exact::<u32>()?,
        };

        // NOTE(ww): The `new_with_len` API is a little bit silly -- ideally we'd just
        // take a slice of `inner` and create a new `BitCursor` with it, but we can't do
        // that while preserving the generic `T` bound.
        // The manual fixup (+ 20) is another artifact of this -- we keep the wrapper header
        // in the new cursor to make the offsets more intelligible, which means that we
        // also need to extend the end of our cursor's buffer.
        let actual_length = (wrapper.size as usize) + 20;
        let mut cur = BitCursor::new_with_len(inner, actual_length)?;

        cur.seek(SeekFrom::Start(wrapper.offset.into()))
            .map_err(|e| {
                Error::StreamParse(format!("couldn't seek past bitcode wrapper: {:?}", e))
            })?;
        Ok((wrapper, Self::from_cursor(cur)?))
    }

    /// Advance the underlying bitstream parser by one entry.
    ///
    /// NOTE: Most users should prefer the iterator implementation.
    pub fn advance(&mut self) -> Result<StreamEntry, Error> {
        self.parser.advance()
    }
}

impl<T: AsRef<[u8]>> Iterator for Bitstream<T> {
    type Item = Result<StreamEntry, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.advance() {
            Ok(entry) => Some(Ok(entry)),
            Err(Error::Exhausted) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

#[cfg(test)]
mod tests {}
