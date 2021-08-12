//! Abbreviation definition and abbreviated record parsing and handling for `llvm-bitstream`.

use std::convert::{From, TryFrom, TryInto};

use llvm_bitcursor::BitCursor;
use llvm_constants::{AbbrevOpEnc, ReservedAbbrevId};

use crate::error::Error;
use crate::record::Value;

/// An abbreviation ID, whether reserved or defined by the stream itself.
#[derive(Clone, Copy, Debug)]
pub enum AbbrevId {
    /// A reserved abbreviation ID.
    Reserved(ReservedAbbrevId),
    /// An abbreviation ID that's been defined within the stream.
    Defined(u64),
}

impl From<u64> for AbbrevId {
    fn from(value: u64) -> Self {
        ReservedAbbrevId::try_from(value)
            .map_or_else(|_| AbbrevId::Defined(value), AbbrevId::Reserved)
    }
}

/// The valid abbreviation operand forms.
#[derive(Clone, Debug, PartialEq)]
pub enum AbbrevOp {
    /// A literal, constant operand.
    Literal(u64),
    /// A VBR whose width is is associated as extra data.
    Vbr(u64),
    /// A fixed-width field whose width is associated as extra data.
    Fixed(u64),
    /// A fixed-length array whose member elements are specified.
    Array(Box<AbbrevOp>),
    /// A single Char6.
    Char6,
    /// A fixed-length blob of bytes.
    Blob,
}

impl AbbrevOp {
    /// Parse a single abbreviation operand from the stream, returning an
    /// appropriate [`Value`](crate::record::Value).
    pub(self) fn parse<T: AsRef<[u8]>>(&self, cur: &mut BitCursor<T>) -> Result<Value, Error> {
        Ok(match self {
            AbbrevOp::Literal(val) => Value::Unsigned(*val),
            AbbrevOp::Vbr(width) => Value::Unsigned(cur.read_vbr(*width as usize)?),
            AbbrevOp::Fixed(width) => Value::Unsigned(cur.read_as::<u64>(*width as usize)?),
            AbbrevOp::Array(elem) => {
                // An array operand is encoded as a length (VBR6), followed by
                // each encoded element of the array.
                // TODO(ww): Sanity check array_len here.
                let array_len = cur.read_vbr(6)? as usize;

                let mut array = Vec::with_capacity(array_len);
                for _ in 0..array_len {
                    array.push(elem.parse(cur)?);
                }

                Value::Array(array)
            }
            AbbrevOp::Char6 => Value::Char6(cur.read_as::<u8>(6)?),
            AbbrevOp::Blob => {
                // A blob operand is encoded as a length (VBR6), followed by a 32-bit aligned
                // sequence of bytes, followed by another alignment back to 32 bits.

                // TODO(ww): Sanity check blob_len here: it probably shouldn't be 0,
                // and it definitely can't be longer than the stream.
                let blob_len = cur.read_vbr(6)? as usize;
                cur.align32();

                // TODO(ww): This read loop is probably slower than it needs to be;
                // `BitCursor` could probably learn a `read_bytes` API that's
                // only allowed when the stream is byte-aligned.
                let mut blob = Vec::with_capacity(blob_len);
                for _ in 0..blob_len {
                    blob.push(cur.read_exact::<u8>()?);
                }
                cur.align32();

                Value::Blob(blob)
            }
        })
    }
}

/// Represents a defined abbreviation, as specified by a `DEFINE_ABBREV` record.
#[derive(Clone, Debug)]
pub struct Abbrev {
    /// The abstract operands for this abbreviation definition.
    pub operands: Vec<AbbrevOp>,
}

impl Abbrev {
    /// Parse a new `Abbrev` from the stream.
    ///
    /// Assumes that the `DEFINE_ABBREV` ID has already been consumed.
    pub fn new<T: AsRef<[u8]>>(cur: &mut BitCursor<T>) -> Result<Self, Error> {
        // TODO(ww): This and other structures should probably implement a `FromStream`
        // trait instead, for construction.

        // Per the LLVM docs: abbreviation records look like this:
        // [DEFINE_ABBREV, VBR5:numabbrevops, abbrevop0, abbrevop1, ...]
        // Our surrounding parse context should have consumed the DEFINE_ABBREV
        // already, so we start with numabbrevops.
        let num_abbrev_opnds = cur.read_vbr(5)?;
        if num_abbrev_opnds < 1 {
            return Err(Error::AbbrevParse(
                "expected at least one abbrev operand".into(),
            ));
        }

        log::debug!("expecting {} operands", num_abbrev_opnds);

        // Abbreviated records must have at least one operand.
        if num_abbrev_opnds < 1 {
            return Err(Error::AbbrevParse(
                "expected abbrev operand count to be nonzero".into(),
            ));
        }

        // Decode each abbreviation operand.
        let mut operands = vec![];
        let mut done_early = false;
        for idx in 0..num_abbrev_opnds {
            // Each operand starts with a single bit that indicates whether
            // the operand is "literal" (i.e., a VBR8) or an "encoded" operand.
            let operand_kind = cur.read(1)?;

            // If this operand is a literal, then we read it as a VBR8.
            if operand_kind == 1 {
                let val = cur.read_vbr(8)?;

                // NOTE(ww): This error is exceedingly unlikely (usize would have to be larger
                // than u64). But you never know.
                operands.push(AbbrevOp::Literal(val));

                continue;
            }

            // Otherwise, we need to suss the encoding representation out of it.
            // This is always a 3-bit field (**not** a VBR3), which in turn tells us whether the
            // operand encoding includes extra data.
            let enc: AbbrevOpEnc = cur.read(3)?.try_into()?;
            let opnd = match enc {
                AbbrevOpEnc::Fixed => AbbrevOp::Fixed(cur.read_vbr(5)?),
                AbbrevOpEnc::Vbr => AbbrevOp::Vbr(cur.read_vbr(5)?),
                AbbrevOpEnc::Array => {
                    // There is only ever one array operand in an abbreviation definition,
                    // and it is always the second-to-last operand. Anything else is an error.
                    if idx != num_abbrev_opnds - 2 {
                        return Err(Error::AbbrevParse("array operand at invalid index".into()));
                    }

                    // NOTE(ww): We get a little clever here: instead of parsing
                    // the inner array operand on its own, we steal it here and set
                    // `done_early` to indicate that we're done with operand parsing.
                    // This works since array operands are guaranteed to be second-to-last,
                    // followed only by their element operand encoding.
                    cur.read(1)?;
                    let elem_enc: AbbrevOpEnc = cur.read(3)?.try_into()?;
                    done_early = true;

                    let elem = match elem_enc {
                        AbbrevOpEnc::Fixed => AbbrevOp::Fixed(cur.read_vbr(5)?),
                        AbbrevOpEnc::Vbr => AbbrevOp::Vbr(cur.read_vbr(5)?),
                        AbbrevOpEnc::Char6 => AbbrevOp::Char6,
                        _ => {
                            // Blobs and arrays cannot themselves be member types.
                            return Err(Error::AbbrevParse(format!(
                                "invalid element type for an array: {:?}",
                                elem_enc
                            )));
                        }
                    };

                    AbbrevOp::Array(Box::new(elem))
                }
                AbbrevOpEnc::Char6 => AbbrevOp::Char6,
                AbbrevOpEnc::Blob => {
                    // Similarly to arrays: there is only ever one blob operand.
                    // Blobs don't have an element type, so they're always the last operand.
                    if idx != num_abbrev_opnds - 1 {
                        return Err(Error::AbbrevParse("blob operand at invalid index".into()));
                    }

                    AbbrevOp::Blob
                }
            };

            operands.push(opnd);

            // See above: don't complete the entire operand parsing loop if we've successfully
            // stolen the last operand as part of an array.
            if done_early {
                break;
            }
        }

        Ok(Self { operands: operands })
    }

    /// Parse an abbreviated record from this stream, returning its values.
    pub fn parse<T: AsRef<[u8]>>(&self, cur: &mut BitCursor<T>) -> Result<Vec<Value>, Error> {
        self.operands.iter().map(|opnd| opnd.parse(cur)).collect()
    }
}
