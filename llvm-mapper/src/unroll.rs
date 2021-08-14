//! Routines and structures for "unrolling" a [`Bitstream`](llvm_bitstream::Bitstream)
//! into a block-and-record hierarchy.

use std::convert::TryFrom;

use llvm_bitstream::parser::StreamEntry;
use llvm_bitstream::record::{Block, Record};
use llvm_bitstream::Bitstream;

use crate::error::Error;

/// A fully unrolled block within the bitstream, with potential records
/// and sub-blocks.
#[derive(Debug)]
pub struct UnrolledBlock {
    /// This block's ID.
    pub id: u64,
    /// The [`Record`](llvm_bitstream::record::Record)s directly contained by this block.
    pub records: Vec<Record>,
    /// The blocks directly contained by this block.
    pub blocks: Vec<UnrolledBlock>,
}

impl UnrolledBlock {
    pub(self) fn new(id: u64) -> Self {
        Self {
            id: id,
            records: vec![],
            blocks: vec![],
        }
    }
}

/// A fully unrolled bitstream, with a hierarchy of sub-blocks.
#[derive(Debug)]
pub struct UnrolledBitstream {
    blocks: Vec<UnrolledBlock>,
}

impl Default for UnrolledBitstream {
    fn default() -> Self {
        Self { blocks: vec![] }
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
            // 2. Take sub-blocks, and enter them, adding them to our sub-block list;
            // 3. Visit the end of our own block and return so that the caller
            //    (which is either the bitstream context or another parent block)
            //    can add us to its block list.
            loop {
                let entry = bitstream.next().ok_or_else(|| {
                    Error::BadUnroll("unexpected stream end during unroll".into())
                })?;

                match entry? {
                    StreamEntry::Record(record) => unrolled_block.records.push(record),
                    StreamEntry::SubBlock(block) => {
                        let unrolled_child = enter_block(bitstream, block)?;
                        unrolled_block.blocks.push(unrolled_child);
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
                unrolled.blocks.push(enter_block(&mut bitstream, block)?);
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
