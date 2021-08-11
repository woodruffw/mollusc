//! Core parsing functionality for `llvm-bitstream`.

use std::collections::HashMap;
use std::convert::TryInto;
use std::iter;

use llvm_bitcursor::BitCursor;

use crate::abbrev::{self, AbbrevId, ReservedAbbrevId};
use crate::constants::{BlockId, BlockInfoCode};
use crate::error::Error;
use crate::record::{Block, Record, Value};

/// All abbreviation IDs before this are defined by the bitstream format,
/// rather than the stream itself.
const FIRST_APPLICATION_ABBREV_ID: usize = 4;

/// The kinds of entries we can see while advancing through the bitstream.
/// Abbreviations are handled transparently by the parser, and thus are
/// never surfaced as `StreamEntry` values.
#[derive(Debug)]
pub enum StreamEntry {
    /// The end of a block scope.
    EndBlock,
    /// The beginning of a new block scope, for a block with the given ID.
    SubBlock(Block),
    /// The beginning of a new record within the current scope, with the given
    /// abbreviation ID.
    Record(Record),
}

/// Represents the necessary parse state for a particular scope in the bitstream.
///
/// Note that a scope does not *necessarily* correspond to a block: every
/// parser begins with an initial non-block scope before the first block is encountered.
#[derive(Debug)]
enum Scope {
    Initial,
    Block {
        abbrev_id_width: u64,
        block_id: u64,
        blockinfo_block_id: Option<u64>,
        abbrevs: Vec<abbrev::Abbrev>,
    },
}

impl Default for Scope {
    fn default() -> Self {
        Self::Initial
    }
}

impl Scope {
    /// Returns a new (block) scope.
    pub(self) fn new(abbrev_id_width: u64, block_id: u64) -> Self {
        Self::Block {
            abbrev_id_width: abbrev_id_width,
            block_id: block_id,
            blockinfo_block_id: None,
            abbrevs: vec![],
        }
    }

    /// Returns the current width used for abbreviation IDs.
    pub(self) fn abbrev_id_width(&self) -> u64 {
        match self {
            // The initial abbreviation ID width is always 2.
            Scope::Initial => 2,
            Scope::Block {
                abbrev_id_width, ..
            } => *abbrev_id_width,
        }
    }

    /// Extend the current (block) scope's abbreviation definition list with the given
    /// iterator.
    ///
    /// Returns an error if used on a non-block scope.
    pub(self) fn extend_abbrevs(
        &mut self,
        new_abbrevs: impl iter::IntoIterator<Item = abbrev::Abbrev>,
    ) -> Result<(), Error> {
        match self {
            Scope::Initial => Err(Error::BadScope(
                "non-block scope cannot reference abbreviations".into(),
            )),
            Scope::Block { abbrevs, .. } => {
                abbrevs.extend(new_abbrevs);
                Ok(())
            }
        }
    }

    /// Return a reference to the abbreviation definition with the given `abbrev_id`.
    ///
    /// Returns an error if the scope cannot contain abbreviation definitions or does
    /// not have one for the given ID.
    pub(self) fn get_abbrev(&self, abbrev_id: u64) -> Result<&abbrev::Abbrev, Error> {
        match self {
            Scope::Initial => Err(Error::BadScope(
                "non-block scope cannot contain records".into(),
            )),
            Scope::Block { abbrevs, .. } => {
                let idx = (abbrev_id as usize) - FIRST_APPLICATION_ABBREV_ID;
                abbrevs.get(idx).ok_or(Error::BadAbbrev(abbrev_id))
            }
        }
    }

    /// Returns `true` if this scope corresponds to a `BLOCKINFO` block.
    ///
    /// This keeps the [`StreamParser`](StreamParser) honest when determining
    /// which blocks and/or records to emit entries for.
    pub(self) fn is_blockinfo(&self) -> bool {
        match self {
            Scope::Initial => false,
            Scope::Block { block_id, .. } => *block_id == BlockId::BlockInfo as u64,
        }
    }

    /// Returns the last block ID recorded with `SETBID` in the `BLOCKINFO` block.
    ///
    /// This function's return is only sensible in the context of a scope corresponding
    /// to `BLOCKINFO`. Use on any other scope constitutes API misuse.
    pub(self) fn blockinfo_block_id(&self) -> Option<u64> {
        match self {
            Scope::Initial => None,
            Scope::Block {
                blockinfo_block_id, ..
            } => *blockinfo_block_id,
        }
    }

    /// Sets the current block ID for the `BLOCKINFO` block's state machine.
    ///
    /// Returns an error if requested in a nonsense context, such as on any
    /// non-`BLOCKINFO` scope.
    pub(self) fn set_blockinfo_block_id(&mut self, new_bid: u64) -> Result<(), Error> {
        if let Scope::Block {
            blockinfo_block_id, ..
        } = self
        {
            *blockinfo_block_id = Some(new_bid);
            return Ok(());
        }

        Err(Error::BadScope(
            "can't set BLOCKINFO block ID for non-BLOCKINFO scope".into(),
        ))
    }
}

/// A parser for individual bitstream entries.
///
/// This structure is **not** a general-purpose parser for bitstream inputs:
/// it expects to be given a prepared [`BitCursor`](BitCursor) whose internal
/// state is correct (i.e., has been advanced past the initial input magic).
///
/// For a general-purpose parser with the correct state management, see
/// [`Bitstream`](crate::Bitstream).
#[derive(Debug)]
pub struct StreamParser<T: AsRef<[u8]>> {
    cursor: BitCursor<T>,
    scopes: Vec<Scope>,
    blockinfo: HashMap<u64, Vec<abbrev::Abbrev>>,
}

impl<T: AsRef<[u8]>> StreamParser<T> {
    /// Create a new `StreamParser` from the given `BitCursor`.
    ///
    /// See the struct-level documentation for caveats.
    pub(crate) fn new(cur: BitCursor<T>) -> Self {
        Self {
            cursor: cur,
            scopes: vec![Scope::default()],
            blockinfo: Default::default(),
        }
    }

    /// Returns the current scope.
    fn scope(&self) -> &Scope {
        // Unwrap safety: `scopes` is always created with at least one scope, so
        // `last()` cannot fail.
        #[allow(clippy::unwrap_used)]
        self.scopes.last().unwrap()
    }

    /// Returns the current scope as a mutable reference.
    fn scope_mut(&mut self) -> &mut Scope {
        // Unwrap safety: `scopes` is always created with at least one scope, so
        // `last()` cannot fail.
        #[allow(clippy::unwrap_used)]
        self.scopes.last_mut().unwrap()
    }

    /// Enter a block, creating the appropriate scope state for interpreting
    /// records within the block.
    ///
    /// If this block is a "metadata" one (e.g., `BLOCKINFO`), returns `None`.
    fn enter_block(&mut self) -> Result<Option<StreamEntry>, Error> {
        let block_id = self.cursor.read_vbr(8)?;
        let new_width = self.cursor.read_vbr(4)?;

        self.cursor.align32();

        if new_width < 1 {
            return Err(Error::BadScope(format!(
                "can't enter block: invalid code side: {}",
                new_width
            )));
        }

        // The encoded block length is measured in 32-bit words, so our
        // actual block length in bytes is the word count times the bytesize
        // of each word.
        let block_len = self.cursor.read(32)? * 4;
        log::debug!(
            "entered block: ID={}, new abbrev width={}, block_len={} @ bit position {}",
            block_id,
            new_width,
            block_len,
            self.cursor.tell_bit()
        );

        // Create a new scope for the block we've just entered.
        self.scopes.push(Scope::new(new_width, block_id));

        // If our blockinfo map contains any abbrevs for the current block ID, add them here.
        if let Some(abbrevs) = self.blockinfo.get(&block_id).map(|a| a.to_vec()) {
            self.scope_mut().extend_abbrevs(abbrevs)?;
        }

        // If we've just entered a BLOCKINFO block, return `None` to avoid
        // surfacing parse details to the `advance()` API.
        if self.scope().is_blockinfo() {
            return Ok(None);
        }

        // Otherwise, return an appropriate entry.
        Ok(Some(StreamEntry::SubBlock(Block {
            block_id: block_id,
            len: block_len,
        })))
    }

    /// Exit a block, returning the scope to the appropriate state for the parent block.
    fn exit_block(&mut self) -> Result<Option<StreamEntry>, Error> {
        // An END_BLOCK record just aligns the stream.
        self.cursor.align32();

        // NOTE(ww): We never allow an END_BLOCK to pop the last scope,
        // since the last scope is synthetic and does not correspond to a real block.
        if self.scopes.len() <= 1 {
            return Err(Error::BadScope(
                "malformed stream: cannot perform END_BLOCK because scope stack is empty".into(),
            ));
        }

        // Unwrap safety: we check for at least one scope above, so this cannot fail.
        #[allow(clippy::unwrap_used)]
        let scope = self.scopes.pop().unwrap();

        log::debug!("exit_block: new active scope is {:?}", self.scope());

        // If we're exiting a BLOCKINFO, we have nothing to return.
        if scope.is_blockinfo() {
            return Ok(None);
        }

        Ok(Some(StreamEntry::EndBlock))
    }

    /// Interpret a `DEFINE_ABBREV` record.
    fn define_abbrev(&mut self) -> Result<(), Error> {
        let abbrev = abbrev::Abbrev::new(&mut self.cursor)?;
        log::debug!("new abbrev: {:?}", abbrev);

        // `DEFINE_ABBREV` occurs in two contexts: either in a `BLOCKINFO`
        // block (where it affects all blocks with block ID defined by the current `SETBID`),
        // or in any other block, where it affects only the current scope.
        // For the latter case we assume that any `BLOCKINFO`-defined abbrevs have
        // already been loaded into the current scope.
        if self.scope().is_blockinfo() {
            let block_id = self.scope().blockinfo_block_id().ok_or_else(|| {
                Error::StreamParse("DEFINE_ABBREV in BLOCKINFO but no preceding SETBID".into())
            })?;
            self.blockinfo
                .entry(block_id)
                .or_insert_with(Vec::new)
                .push(abbrev);
        } else {
            self.scope_mut().extend_abbrevs(iter::once(abbrev))?;
        }

        Ok(())
    }

    /// Interpret an `UNABBREV_RECORD` record.
    fn parse_unabbrev(&mut self) -> Result<Option<StreamEntry>, Error> {
        // Sanity check: `UNABBREV_RECORD` can only occur inside a block,
        // so the current scope must be a block.
        if matches!(self.scope(), Scope::Initial) {
            return Err(Error::StreamParse(
                "UNABBREV_RECORD outside of any block scope".into(),
            ));
        }

        // An unabbrev record looks like this:
        // [code:VBR6, numops:VBR6, op0:VBR6, op1:VBR6, ...]
        // This isn't worth generalizing, so do it all in the body here.
        let code: u64 = self.cursor.read_vbr(6)?;
        let num_opnds = self.cursor.read_vbr(6)?;

        log::debug!("unabbrev record code={}, num_opnds={}", code, num_opnds);

        let mut values = vec![];
        for _ in 0..num_opnds {
            values.push(Value::Unsigned(self.cursor.read_vbr(6)?));
        }

        let record = Record::from_unabbrev(code, values);
        if self.scope().is_blockinfo() {
            let code: BlockInfoCode = record.code.try_into()?;
            match code {
                BlockInfoCode::SetBid => {
                    let block_id: u64 = record.values[0].clone().try_into()?;
                    log::debug!("SETBID: BLOCKINFO block ID is now {}", block_id);
                    self.scope_mut().set_blockinfo_block_id(block_id)?;
                }
                BlockInfoCode::BlockName => log::debug!("skipping BLOCKNAME code in BLOCKINFO"),
                BlockInfoCode::SetRecordName => {
                    log::debug!("skipping SETRECORDNAME code in BLOCKINFO")
                }
            };
            return Ok(None);
        }

        Ok(Some(StreamEntry::Record(record)))
    }

    /// Interpret a record using its corresponding abbreviation definition.
    fn parse_with_abbrev(&mut self, abbrev_id: u64) -> Result<Option<StreamEntry>, Error> {
        // To parse a record according to an abbreviation definition, we
        // fetch the corresponding abbreviation (failing if we don't have one),
        // then use the abbreviation for the parse.
        // TODO(ww): The clone at the end here is a little annoying, but we
        // need it to avoid mixing mutable and immutable borrows here.
        // There is absolutely a better way to do that.
        let abbrev = self.scope().get_abbrev(abbrev_id)?.clone();

        let mut values = abbrev.parse(&mut self.cursor)?;
        log::debug!("parsed values: {:?}", values);

        // Panic safety: every abbrev contains at least one operand, so this cannot panic.
        // We also expect the first operand to always be a u64, indicating the record code.
        let code: u64 = values.remove(0).try_into()?;

        if self.scope().is_blockinfo() {
            return Ok(None);
        }

        Ok(Some(StreamEntry::Record(Record {
            abbrev_id: Some(abbrev_id),
            code: code,
            values: values,
        })))
    }

    /// Return the next [`StreamEntry`](StreamEntry) in this bitstream.
    ///
    /// Returns an error on any parsing error, *or* the special
    /// [`Error::Exhausted`](Error::Exhausted) if the bitstream has
    /// been fully consumed.
    pub fn advance(&mut self) -> Result<StreamEntry, Error> {
        if self.cursor.exhausted() {
            return Err(Error::Exhausted);
        }

        log::debug!(
            "advancing, current scope: {:?} @ bit position {}",
            self.scope(),
            self.cursor.tell_bit()
        );

        // To return the next stream entry, we read the next abbreviation ID using
        // our current width. The abbreviation ID we read determines our subsequent
        // parse strategy and the kind of entry we return.
        let id: abbrev::AbbrevId = self
            .cursor
            .read(self.scope().abbrev_id_width() as usize)?
            .into();
        log::debug!("next entry ID: {:?}", id);

        // NOTE(ww): The strange `map` + `unwrap_or_else` pattern below is to keep the parser
        // generalized without having to return `StreamEntries` that correspond to
        // parse details that a stream consumer shouldn't have to be aware of
        // (such as abbrev definitions and the BLOCKINFO block).
        match id {
            AbbrevId::Reserved(ReservedAbbrevId::EndBlock) => {
                self.exit_block()?.map(Ok).unwrap_or_else(|| self.advance())
            }
            AbbrevId::Reserved(ReservedAbbrevId::EnterSubBlock) => self
                .enter_block()?
                .map(Ok)
                .unwrap_or_else(|| self.advance()),
            AbbrevId::Reserved(ReservedAbbrevId::DefineAbbrev) => {
                // DEFINE_ABBREV is always a parse detail, so we don't even bother
                // trying to return a StreamEntry for it.
                self.define_abbrev()?;
                self.advance()
            }
            AbbrevId::Reserved(ReservedAbbrevId::UnabbrevRecord) => self
                .parse_unabbrev()?
                .map(Ok)
                .unwrap_or_else(|| self.advance()),
            AbbrevId::Defined(abbrev_id) => self
                .parse_with_abbrev(abbrev_id)?
                .map(Ok)
                .unwrap_or_else(|| self.advance()),
        }
    }
}
