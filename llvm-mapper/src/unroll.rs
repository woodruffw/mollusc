//! Routines and structures for "unrolling" a [`Bitstream`](llvm_bitstream::Bitstream)
//! into a block-and-record hierarchy.

use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};

use llvm_bitstream::parser::StreamEntry;
use llvm_bitstream::record::{Block, Record};
use llvm_bitstream::Bitstream;

use crate::block::{BlockId, Identification, Module, Strtab, Symtab};
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

    /// Get a single sub-block from this block by its block ID.
    ///
    /// Returns an error if the block either lacks an appropriate block or has more than one.
    pub fn one_block(&self, id: BlockId) -> Result<&UnrolledBlock, Error> {
        let blocks_for_id = self
            .blocks
            .get(&id)
            .ok_or(Error::BlockBlockMismatch(id, self.id))?;

        // The empty case here would indicate API misuse, since we should only
        // create the vector upon inserting at least one block for a given ID.
        // But it doesn't hurt (much) to be cautious.
        if blocks_for_id.is_empty() || blocks_for_id.len() > 1 {
            return Err(Error::BlockBlockMismatch(id, self.id));
        }

        // Panic safety: we check for exactly one member directly above.
        Ok(&blocks_for_id[0])
    }
}

/// A fully unrolled bitcode structure, taken from a bitstream.
///
/// Every `UnrolledBitcode` has a list of `BitstreamModule`s that it contains, each of
/// which corresponds to a single LLVM IR module. In the simplest case, there will only be one.
#[derive(Debug)]
pub struct UnrolledBitcode {
    pub(crate) tops: HashMap<BlockId, Vec<UnrolledBlock>>,
}

impl Default for UnrolledBitcode {
    fn default() -> Self {
        Self {
            tops: HashMap::new(),
        }
    }
}

impl TryFrom<&[u8]> for UnrolledBitcode {
    type Error = Error;

    fn try_from(buf: &[u8]) -> Result<UnrolledBitcode, Self::Error> {
        let (_, bitstream) = Bitstream::from(buf)?;

        bitstream.try_into()
    }
}

impl<T: AsRef<[u8]>> TryFrom<Bitstream<T>> for UnrolledBitcode {
    type Error = Error;

    fn try_from(mut bitstream: Bitstream<T>) -> Result<UnrolledBitcode, Self::Error> {
        let mut unrolled = UnrolledBitcode::default();

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

/// A `BitcodeModule` encapsulates the top-level pieces of bitstream state needed for
/// a single LLVM bitcode module: the `IDENTIFICATION_BLOCK`, the `MODULE_BLOCK` itself,
/// a `STRTAB_BLOCK`, and a `SYMTAB_BLOCK` (if the last is present). A bitstream can
/// contain multiple LLVM modules (e.g. if produced by `llvm-cat -b`), so parsing a bitstream
/// can result in multiple `BitcodeModule`s.
#[derive(Debug)]
pub struct BitcodeModule {
    /// The identification block associated with this module.
    pub identification: Identification,

    /// The module block associated with this module.
    pub module: Module,

    /// The string table associated with this module.
    pub strtab: Strtab,

    /// The symbol table associated with this module, if it has one.
    pub symtab: Option<Symtab>,
}

// impl BitcodeModule {
//     /// Parse a `BitcodeModule` from the given `UnrolledBitstream` by index.
//     ///
//     /// The index here is an index into the list of `MODULE_BLOCK`s, which are treated
//     /// as the "definitive"
//     fn parse_index(unrolled: &UnrolledBitstream, idx: usize) -> Result<Self, Error> {
//         unimplemented!();
//     }

//     /// Parse exactly one `BitcodeModule` from the input.
//     ///
//     /// Ignores any blocks that would form a subsequent `BitcodeModule`, if present.
//     pub fn parse_one(buf: impl AsRef<[u8]>) -> Result<Self, Error> {
//         let unrolled = UnrolledBitstream::try_from(buf.as_ref())?;

//         Self::parse_index(&unrolled, 0)
//     }

//     /// Parse all `BitcodeModule`s from the input.
//     pub fn parse_all(buf: impl AsRef<[u8]>) -> Result<Vec<Self>, Error> {
//         let unrolled = UnrolledBitstream::try_from(buf.as_ref())?;

//         unimplemented!();
//     }
// }

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
