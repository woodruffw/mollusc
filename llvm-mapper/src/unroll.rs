//! Routines and structures for "unrolling" a [`Bitstream`](llvm_bitstream::Bitstream)
//! into a block-and-record hierarchy.

use std::convert::{TryFrom, TryInto};

use indexmap::IndexMap;
use llvm_bitstream::parser::StreamEntry;
use llvm_bitstream::record::{Block as BsBlock, Record as BsRecord};
use llvm_bitstream::Bitstream;
use llvm_support::bitcodes::IrBlockId;
use thiserror::Error;

use crate::block::{BlockId, BlockMapError, Identification, Module, Strtab, Symtab};
use crate::error::Error;
use crate::map::{PartialCtxMappable, PartialMapCtx};
use crate::record::{RecordBlobError, RecordStringError};

/// An "unrolled" record. This is internally indistinguishable from a raw bitstream
/// [`Record`](llvm_bitstream::record::Record), but is newtyped to enforce proper
/// isolation of concerns.
#[derive(Clone, Debug)]
pub struct Record(BsRecord);

impl Record {
    /// Returns this record's code.
    pub fn code(&self) -> u64 {
        self.0.code
    }

    /// Attempt to pull a UTF-8 string from this record's fields.
    ///
    /// Strings are always the last fields in a record, so only the start
    /// index is required.
    pub fn try_string(&self, idx: usize) -> Result<String, RecordStringError> {
        // If our start index lies beyond the record fields or would produce
        // an empty string, it's invalid.
        if idx >= self.0.fields.len() - 1 {
            return Err(RecordStringError::BadIndex(idx, self.0.fields.len()));
        }

        // Each individual field in our string must fit into a byte.
        let raw = self.0.fields[idx..]
            .iter()
            .map(|f| u8::try_from(*f))
            .collect::<Result<Vec<_>, _>>()?;

        // Finally, the buffer itself must decode correctly.
        String::from_utf8(raw).map_err(RecordStringError::from)
    }

    /// Attempt to pull a blob of bytes from this record's fields.
    ///
    /// Blobs are always the last fields in a record, so only the start index is required.
    pub fn try_blob(&self, idx: usize) -> Result<Vec<u8>, RecordBlobError> {
        // If our start index lies beyond the record fields or would produce
        // an empty string, it's invalid.
        if idx >= self.0.fields.len() - 1 {
            return Err(RecordBlobError::BadIndex(idx, self.0.fields.len()));
        }

        // Each individual field in our blob must fit into a byte.
        Ok(self.0.fields[idx..]
            .iter()
            .map(|f| u8::try_from(*f))
            .collect::<Result<Vec<_>, _>>()?)
    }

    /// Returns a reference to this record's fields.
    pub fn fields(&self) -> &[u64] {
        &self.0.fields
    }
}

/// Errors that can occur when attempting to search for blocks and records within
/// an unrolled bitstream.
#[derive(Debug, Error)]
pub enum ConsistencyError {
    /// We expected a (sub-)block of the given ID, but couldn't find one.
    #[error("expected a block with {0:?} but not present")]
    MissingBlock(BlockId),

    /// We expected exactly one (sub-)block of the given ID, but found more than one.
    #[error("expected exactly one block with {0:?} but got more than one")]
    TooManyBlocks(BlockId),

    /// We expected a record of the given code, but couldn't find one.
    #[error("expected a record of code {0} but not present")]
    MissingRecord(u64),

    /// We expected exactly one record of the given code, but found more than one.
    #[error("expected exactly one record of code {0} but got more than one")]
    TooManyRecords(u64),
}

/// Represents a collection of unrolled records.
#[derive(Clone, Debug, Default)]
pub struct Records(Vec<Record>);

impl Records {
    /// Return an iterator for all records that share the given code. Records
    /// are iterated in the order of insertion.
    ///
    /// The returned iterator is empty if the block doesn't have any matching records.
    pub(crate) fn by_code<'a>(
        &'a self,
        code: impl Into<u64> + 'a,
    ) -> impl Iterator<Item = &Record> + 'a {
        let code = code.into();
        self.0.iter().filter(move |r| r.code() == code)
    }

    /// Returns the first record matching the given code, or `None` if there are
    /// no matches.
    ///
    /// Ignores any subsequent matches.
    pub(crate) fn one<'a>(&'a self, code: impl Into<u64> + 'a) -> Option<&Record> {
        self.by_code(code).next()
    }

    /// Returns exactly one record matching the given code, or a variant indicating
    /// the error condition (no matching records, or too many records).
    pub(crate) fn exactly_one<'a>(
        &'a self,
        code: impl Into<u64> + 'a,
    ) -> Result<&Record, ConsistencyError> {
        let code = code.into();
        let mut records = self.by_code(code);

        match records.next() {
            None => Err(ConsistencyError::MissingRecord(code)),
            Some(r) => match records.next() {
                None => Ok(r),
                Some(_) => Err(ConsistencyError::TooManyRecords(code)),
            },
        }
    }

    /// Return an option of one record matching the given code or `None`, or an
    /// `Err` variant if more than one matching record is present.
    pub(crate) fn one_or_none<'a>(
        &'a self,
        code: impl Into<u64> + 'a,
    ) -> Result<Option<&Record>, ConsistencyError> {
        let code = code.into();
        let mut records = self.by_code(code);

        match records.next() {
            None => Ok(None),
            Some(r) => match records.next() {
                None => Ok(Some(r)),
                Some(_) => Err(ConsistencyError::TooManyRecords(code)),
            },
        }
    }
}

impl<'a> IntoIterator for &'a Records {
    type Item = &'a Record;
    type IntoIter = std::slice::Iter<'a, Record>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// Represents a collection of unrolled blocks.
#[derive(Clone, Debug, Default)]
pub struct Blocks(IndexMap<BlockId, Vec<Block>>);

impl Blocks {
    /// Return an iterator over all sub-blocks within this block that share the given ID.
    ///
    /// The returned iterator is empty if the block doesn't have any matching sub-blocks.
    pub(crate) fn by_id(&self, id: BlockId) -> impl Iterator<Item = &Block> + '_ {
        self.0.get(&id).into_iter().flatten()
    }

    pub(crate) fn exactly_one(&self, id: BlockId) -> Result<&Block, ConsistencyError> {
        let mut blocks = self.by_id(id);

        match blocks.next() {
            None => Err(ConsistencyError::MissingBlock(id)),
            Some(b) => match blocks.next() {
                None => Ok(b),
                Some(_) => Err(ConsistencyError::TooManyBlocks(id)),
            },
        }
    }

    /// Return an option of one block matching the given code or `None`, or an
    /// `Err` variant if more than one matching block is present.
    pub(crate) fn one_or_none(&self, id: BlockId) -> Result<Option<&Block>, ConsistencyError> {
        let mut blocks = self.by_id(id);

        match blocks.next() {
            None => Ok(None),
            Some(b) => match blocks.next() {
                None => Ok(Some(b)),
                Some(_) => Err(ConsistencyError::TooManyBlocks(id)),
            },
        }
    }
}

/// A fully unrolled block within the bitstream, with potential records
/// and sub-blocks.
#[derive(Clone, Debug)]
pub struct Block {
    /// This block's ID.
    pub id: BlockId,
    /// The [`UnrolledRecord`](UnrolledRecord)s directly contained by this block.
    // NOTE(ww): It would be nice if we could map this list of records by their codes,
    // since that would save us some time when scanning blocks for particular
    // kinds of records. Doing so correctly is tricky: even with an order-preserving
    // structure like IndexMap, we'd lose the correct order as we insert each record
    // into its bucket.
    pub(crate) records: Records,
    /// The blocks directly contained by this block, mapped by their IDs. Like with records,
    /// a block can contain multiple sub-blocks of the same ID.
    pub(crate) blocks: Blocks,
}

impl Block {
    pub(self) fn new(id: u64) -> Self {
        Self {
            id: id.into(),
            records: Records::default(),
            // TODO(ww): Figure out a default capacity here.
            blocks: Blocks::default(),
        }
    }
}

/// A fully unrolled bitcode structure, taken from a bitstream.
///
/// Every `UnrolledBitcode` has a list of `BitstreamModule`s that it contains, each of
/// which corresponds to a single LLVM IR module. In the simplest case, there will only be one.
#[derive(Debug)]
pub struct UnrolledBitcode {
    /// The modules present in this bitcode stream.
    pub modules: Vec<BitcodeModule>,
}

impl TryFrom<&[u8]> for UnrolledBitcode {
    type Error = Error;

    /// Attempt to map the given buffer into an `UnrolledBitcode`.
    fn try_from(buf: &[u8]) -> Result<UnrolledBitcode, Self::Error> {
        let (_, bitstream) = Bitstream::from(buf)?;

        bitstream.try_into()
    }
}

impl<T: AsRef<[u8]>> TryFrom<Bitstream<T>> for UnrolledBitcode {
    type Error = Error;

    /// Attempt to map the given bitstream into an `UnrolledBitcode`.
    fn try_from(mut bitstream: Bitstream<T>) -> Result<UnrolledBitcode, Self::Error> {
        fn enter_block<T: AsRef<[u8]>>(
            bitstream: &mut Bitstream<T>,
            block: BsBlock,
        ) -> Result<Block, Error> {
            let mut unrolled_block = Block::new(block.block_id);

            // Once we're in a block, we do the following:
            // 1. Take records, and add them to the current unrolled block;
            // 2. Take sub-blocks, and enter them, adding them to our sub-block map;
            // 3. Visit the end of our own block and return so that the caller
            //    (which is either the bitstream context or another parent block)
            //    can add us to its block map.
            loop {
                let entry = bitstream
                    .next()
                    .ok_or_else(|| Error::Unroll("unexpected stream end during unroll".into()))?;

                match entry? {
                    StreamEntry::Record(record) => unrolled_block.records.0.push(Record(record)),
                    StreamEntry::SubBlock(block) => {
                        let unrolled_child = enter_block(bitstream, block)?;
                        unrolled_block
                            .blocks
                            .0
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

        let mut partial_modules = Vec::new();

        // Unrolling a bitstream into an `UnrolledBitcode` is a little involved:
        //
        // 1. There are multiple top-level blocks, each of which needs to be consumed.
        // 2. Certain top-level blocks need to be grouped together to form a single BitcodeModule.
        // 3. There can be multiple BitcodeModules-worth of top-level blocks in the stream.
        loop {
            // `None` means that we've exhausted the bitstream; we're done.
            let entry = bitstream.next();
            if entry.is_none() {
                break;
            }

            // Take a top-level block from the stream.
            let top_block = {
                // Unwrap safety: we explicitly check the `None` case above.
                // NOTE(ww): Other parts of the parser should be defensive against a malformed
                // bitstream here, but it's difficult to represent that at the type level during unrolling.
                #[allow(clippy::unwrap_used)]
                let block = entry.unwrap()?.as_block().ok_or_else(|| {
                    Error::Unroll("bitstream has non-blocks at the top-level scope".into())
                })?;

                enter_block(&mut bitstream, block)?
            };

            // Our top-level block can be one of four cases, if it's valid.
            //
            // Handle each accordingly.
            match top_block.id {
                BlockId::Ir(IrBlockId::Identification) => {
                    // We've unrolled an IDENTIFICATION_BLOCK; this indicates the start of a new
                    // bitcode module. Create a fresh PartialBitcodeModule to fill in, as more
                    // top-level blocks become available.
                    partial_modules.push(PartialBitcodeModule::new(top_block));
                }
                BlockId::Ir(IrBlockId::Module) => {
                    // We've unrolled a MODULE_BLOCK; this contains the vast majority of the
                    // state associated with an LLVM IR module. Grab the most recent
                    // PartialBitcodeModule and fill it in, erroring appropriately if it already
                    // has a module.
                    //
                    // NOTE(ww): We could encounter a top-level sequence that looks like this:
                    //   [IDENTIFICATION_BLOCK, IDENTIFICATION_BLOCK, MODULE_BLOCK]
                    // This would be malformed and in principle we should catch it here by searching
                    // for the first PartialBitcodeModule lacking a module instead of taking
                    // the most recent one, but the PartialBitcodeModule -> BitcodeModule reification
                    // step will take care of that for us.
                    let last_partial = partial_modules.last_mut().ok_or_else(|| {
                        Error::Unroll("malformed bitstream: MODULE_BLOCK with no preceding IDENTIFICATION_BLOCK".into())
                    })?;

                    match &last_partial.module {
                        Some(_) => {
                            return Err(Error::Unroll(
                                "malformed bitstream: adjacent MODULE_BLOCKs".into(),
                            ))
                        }
                        None => last_partial.module = Some(top_block),
                    }
                }
                BlockId::Ir(IrBlockId::Strtab) => {
                    // We've unrolled a STRTAB_BLOCK; this contains the string table for one or
                    // more preceding modules. Any modules that don't already have their own string
                    // table are given their own copy of this one.
                    //
                    // NOTE(ww): Again, we could encounter a sequence that looks like this:
                    //   [..., STRTAB_BLOCK, STRTAB_BLOCK]
                    // This actually wouldn't be malformed, but is *is* nonsense: the second
                    // STRTAB_BLOCK would have no effect on any BitcodeModule, since the first one
                    // in sequence would already have been used for every prior module.
                    // We don't bother catching this at the moment since LLVM's own reader doesn't
                    // and it isn't erroneous per se (just pointless).
                    for prev_partial in partial_modules
                        .iter_mut()
                        .rev()
                        .take_while(|p| p.strtab.is_none())
                    {
                        prev_partial.strtab = Some(top_block.clone());
                    }
                }
                BlockId::Ir(IrBlockId::Symtab) => {
                    // We've unrolled a SYMTAB_BLOCK; this contains the symbol table (which, in
                    // turn, references the string table) for one or more preceding modules. Any
                    // modules that don't already have their own symbol table are given their own
                    // copy of this one.
                    //
                    // NOTE(ww): The same nonsense layout with STRTAB_BLOCK applies here.
                    for prev_partial in partial_modules
                        .iter_mut()
                        .rev()
                        .take_while(|p| p.symtab.is_none())
                    {
                        prev_partial.symtab = Some(top_block.clone());
                    }
                }
                _ => {
                    return Err(Error::Unroll(format!(
                        "unexpected top-level block: {:?}",
                        top_block.id
                    )))
                }
            }
        }

        let modules = partial_modules
            .into_iter()
            .map(|p| p.reify())
            .collect::<Result<Vec<_>, _>>()?;
        let unrolled = UnrolledBitcode { modules };

        Ok(unrolled)
    }
}

/// An internal, partial representation of a bitcode module, used when parsing each bitcode module
/// to avoid polluting the `BitcodeModule` structure with optional types.
#[derive(Debug)]
struct PartialBitcodeModule {
    identification: Block,
    module: Option<Block>,
    strtab: Option<Block>,
    symtab: Option<Block>,
}

impl PartialBitcodeModule {
    /// Create a new `PartialBitcodeModule`.
    pub(self) fn new(identification: Block) -> Self {
        Self {
            identification: identification,
            module: None,
            strtab: None,
            symtab: None,
        }
    }

    /// Reify this `PartialBitcodeModule into a concrete `BitcodeModule`, mapping
    /// each block along the way.
    ///
    /// Returns an error if the `PartialBitcodeModule` is lacking necessary state, or if
    /// block and record mapping fails for any reason.
    pub(self) fn reify(self) -> Result<BitcodeModule, Error> {
        let mut ctx = PartialMapCtx::default();

        // Grab the string table early, so that we can move it into our mapping context and
        // use it for the remainder of the mapping phase.
        let strtab = Strtab::try_map(
            &self
                .strtab
                .ok_or_else(|| Error::Unroll("missing STRTAB_BLOCK for bitcode module".into()))?,
            &mut ctx,
        )
        .map_err(BlockMapError::Strtab)?;

        ctx.strtab = strtab;

        let identification = Identification::try_map(&self.identification, &mut ctx)
            .map_err(BlockMapError::Identification)?;

        let module = Module::try_map(
            &self
                .module
                .ok_or_else(|| Error::Unroll("missing MODULE_BLOCK for bitcode module".into()))?,
            &mut ctx,
        )
        .map_err(BlockMapError::Module)?;

        let symtab = self
            .symtab
            .map(|s| Symtab::try_map(&s, &mut ctx))
            .transpose()
            .map_err(BlockMapError::Symtab)?;

        #[allow(clippy::unwrap_used)]
        Ok(BitcodeModule {
            identification: identification,
            module: module,
            strtab: ctx.strtab,
            symtab: symtab,
        })
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unrolled_record_try_string() {
        let record = Record(BsRecord {
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

    #[test]
    fn test_unrolled_record_try_blob() {
        let record = Record(BsRecord {
            abbrev_id: None,
            code: 0,
            fields: b"\xff\xffvalid string!".iter().map(|b| *b as u64).collect(),
        });

        assert_eq!(record.try_blob(0).unwrap(), b"\xff\xffvalid string!");
        assert_eq!(record.try_blob(8).unwrap(), b"string!");

        assert!(record.try_blob(record.0.fields.len()).is_err());
        assert!(record.try_blob(record.0.fields.len() - 1).is_err());
    }
}
