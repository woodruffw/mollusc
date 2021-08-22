//! Routines and structures for "unrolling" a [`Bitstream`](llvm_bitstream::Bitstream)
//! into a block-and-record hierarchy.

use std::collections::HashMap;
use std::convert::TryFrom;

use llvm_bitstream::parser::StreamEntry;
use llvm_bitstream::record::{Block, Record};
use llvm_bitstream::Bitstream;

use crate::block::BlockId;
use crate::error::Error;

/// An "unrolled" record. This is internally indistinguishable from a raw bitstream
/// [`Record`](llvm_bitstream::record::Record), but is newtyped to enforce proper
/// isolation of concerns.
#[derive(Debug)]
pub struct UnrolledRecord(Record);

impl AsRef<Record> for UnrolledRecord {
    fn as_ref(&self) -> &Record {
        &self.0
    }
}

impl UnrolledRecord {
    /// Attempt to pull a UTF-8 string from this record's fields.
    ///
    /// Strings are always the last fields in a record, so only the start
    /// index is required.
    pub fn try_string(&self, idx: usize) -> Result<String, Error> {
        // If our start index lies beyond the record fields or would produce
        // an empty string, it's invalid.
        if idx >= self.0.fields.len() - 1 {
            return Err(Error::BadField(format!(
                "impossible string index: {} exceeds record fields",
                idx
            )));
        }

        // Each individual field in our string must fit into a byte.
        let raw = self.0.fields[idx..]
            .iter()
            .map(|f| u8::try_from(*f))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| Error::BadField("impossible character value in string".into()))?;

        // Finally, the buffer itself must decode correctly.
        String::from_utf8(raw).map_err(|_| Error::BadField("invalid string encoding".into()))
    }
}

/// A fully unrolled block within the bitstream, with potential records
/// and sub-blocks.
#[derive(Debug)]
pub struct UnrolledBlock {
    /// This block's ID.
    pub id: BlockId,
    /// The [`UnrolledRecord`](UnrolledRecord)s directly contained by this block,
    /// mapped by their codes. Blocks can have multiple records of the same code, hence
    /// the multiple values.
    // TODO(ww): Evaluate HashMap's performance. We might be better off with a specialized int map.
    pub records: HashMap<u64, Vec<UnrolledRecord>>,
    /// The blocks directly contained by this block, mapped by their IDs. Like with records,
    /// a block can contain multiple sub-blocks of the same ID.
    pub blocks: HashMap<BlockId, Vec<UnrolledBlock>>,
}

impl UnrolledBlock {
    pub(self) fn new(id: u64) -> Self {
        Self {
            id: id.into(),
            // TODO(ww): Figure out a default capacity here.
            records: HashMap::new(),
            blocks: HashMap::new(),
        }
    }

    /// Get a single record from this block by its record code.
    ///
    /// Returns an error if the block either lacks an appropriate record or has more than one.
    pub fn one_record(&self, code: u64) -> Result<&UnrolledRecord, Error> {
        let records_for_code = self
            .records
            .get(&code)
            .ok_or(Error::BlockRecordMismatch(code, self.id))?;

        // The empty case here would indicate API misuse, since we should only
        // create the vector upon inserting at least one record for a given code.
        // But it doesn't hurt (much) to be cautious.
        if records_for_code.is_empty() || records_for_code.len() > 1 {
            return Err(Error::BlockRecordMismatch(code, self.id));
        }

        // Panic safety: we check for exactly one member directly above.
        Ok(&records_for_code[0])
    }
}

// TODO(ww): UnrolledRecord here, where UnrolledRecord is basically Record
// with a reified code (instead of just a u64).

/// A fully unrolled bitstream.
///
/// Every bitstream has a collection of top-level blocks, each with a sub-block hierarchy.
#[derive(Debug)]
pub struct UnrolledBitstream {
    tops: HashMap<BlockId, Vec<UnrolledBlock>>,
}

impl Default for UnrolledBitstream {
    fn default() -> Self {
        Self {
            tops: HashMap::new(),
        }
    }
}

impl<T: AsRef<[u8]>> TryFrom<Bitstream<T>> for UnrolledBitstream {
    type Error = Error;

    fn try_from(mut bitstream: Bitstream<T>) -> Result<UnrolledBitstream, Self::Error> {
        let mut unrolled = UnrolledBitstream::default();

        fn enter_block<T: AsRef<[u8]>>(
            bitstream: &mut Bitstream<T>,
            block: Block,
        ) -> Result<UnrolledBlock, Error> {
            let mut unrolled_block = UnrolledBlock::new(block.block_id);

            // Once we're in a block, we do the following:
            // 1. Take records, and add them to the current unrolled block;
            // 2. Take sub-blocks, and enter them, adding them to our sub-block map;
            // 3. Visit the end of our own block and return so that the caller
            //    (which is either the bitstream context or another parent block)
            //    can add us to its block map.
            loop {
                let entry = bitstream.next().ok_or_else(|| {
                    Error::BadUnroll("unexpected stream end during unroll".into())
                })?;

                match entry? {
                    StreamEntry::Record(record) => unrolled_block
                        .records
                        .entry(record.code)
                        .or_insert_with(Vec::new)
                        .push(UnrolledRecord(record)),
                    StreamEntry::SubBlock(block) => {
                        let unrolled_child = enter_block(bitstream, block)?;
                        unrolled_block
                            .blocks
                            .entry(unrolled_child.id)
                            .or_insert_with(Vec::new)
                            .push(unrolled_child);
                    }
                    StreamEntry::EndBlock => {
                        // End our current block scope.
                        break;
                    }
                }
            }

            Ok(unrolled_block)
        }

        // A bitstream can have more than one top-level block, so we loop
        // here to collect and fully unroll each top-level block.
        // Any entry that isn't a block entrance in this context indicates
        // a malformed bitstream, so fail fast if we see anything unusual.
        loop {
            // `None` means that we've exhausted the bitstream; we're done.
            let entry = bitstream.next();
            if entry.is_none() {
                break;
            }

            // Unwrap safety: we explicitly check the `None` case above.
            #[allow(clippy::unwrap_used)]
            let entry = entry.unwrap();

            if let StreamEntry::SubBlock(block) = entry? {
                unrolled
                    .tops
                    .entry(block.block_id.into())
                    .or_insert_with(Vec::new)
                    .push(enter_block(&mut bitstream, block)?);
            } else {
                // NOTE(ww): Other parts of the parser should be defensive against this,
                // but it's difficult to represent that fact at the type level here.
                return Err(Error::BadUnroll(
                    "bitstream has non-blocks at the top-level scope".into(),
                ));
            }
        }

        Ok(unrolled)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unrolled_record_try_string() {
        let record = UnrolledRecord(Record {
            abbrev_id: None,
            code: 0,
            fields: b"\xff\xffvalid string!".iter().map(|b| *b as u64).collect(),
        });

        assert_eq!(record.try_string(2).unwrap(), "valid string!");
        assert_eq!(record.try_string(8).unwrap(), "string!");

        assert!(record.try_string(0).is_err());
        assert!(record.try_string(record.0.fields.len()).is_err());
        assert!(record.try_string(record.0.fields.len() - 1).is_err());
    }
}
