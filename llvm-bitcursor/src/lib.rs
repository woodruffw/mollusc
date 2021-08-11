//! `llvm-bitcursor` is a no-frills library for reading unaligned fields from a bitstream.
//! The APIs provided by this crate are specialized for internal use in an LLVM bitstream parser,
//! and may be less useful outside of that context.

#![deny(broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

pub mod error;

use std::io;

use num::NumCast;

use crate::error::Error;

// Stupid hack trait to give `NumCast` implementations a bitsize.
trait Bitsize {
    fn bitsize() -> usize;
}

impl<T: NumCast> Bitsize for T {
    fn bitsize() -> usize {
        std::mem::size_of::<T>() * 8
    }
}

/// A no-copy cursor wrapper for a bitstream.
///
/// Any type that implements `AsRef<[u8]>` can be used with `BitCursor`.
#[derive(Debug)]
pub struct BitCursor<T: AsRef<[u8]>> {
    /// The cursor-accessible length of the buffer. This is normally the same
    /// as the buffer's length, but can be shorter for uses where `inner`
    /// is a multi-purpose buffer.
    byte_len: usize,

    /// Our inner buffer.
    inner: T,

    /// Our current byte index in `inner`, which may be ahead of our
    /// current bit position (if `current_block` is not exhausted).
    byte_pos: usize,

    /// The last `u64`-sized block read from `inner`.
    current_block: u64,

    /// The number of bits in `current_block` that are valid (i.e., not
    /// yet consumed).
    bit_index: usize,
}

impl<T: AsRef<[u8]>> BitCursor<T> {
    const BLOCK_SIZE: usize = std::mem::size_of::<u64>();
    const BLOCK_SIZE_BITS: usize = u64::BITS as usize;
    const MAX_VBR_BITS: usize = 32;

    /// Create a new `BitCursor` for the `inner` buffer.
    pub fn new(inner: T) -> Self {
        Self {
            byte_len: inner.as_ref().len(),
            inner: inner,
            byte_pos: 0,
            current_block: 0,
            bit_index: 0,
        }
    }

    /// Create a new `BitCursor` for the `inner` buffer, limiting to `byte_len` bytes.
    ///
    /// Returns an error if `byte_len` exceeds `inner`'s range.
    pub fn new_with_len(inner: T, byte_len: usize) -> Result<Self, Error> {
        if byte_len > inner.as_ref().len() {
            return Err(Error::InvalidLength);
        }

        Ok(Self {
            byte_len: byte_len,
            inner: inner,
            byte_pos: 0,
            current_block: 0,
            bit_index: 0,
        })
    }

    /// Return the length of the data wrapped by this cursor, in bytes.
    pub fn byte_len(&self) -> usize {
        self.byte_len
    }

    /// Return the length of the data wrapped by this cursor, in bits.
    pub fn bit_len(&self) -> usize {
        self.byte_len() * 8
    }

    /// Return the current position in the data, at bit granularity.
    pub fn tell_bit(&self) -> usize {
        (self.byte_pos * 8) - self.bit_index
    }

    /// Return the current position in the data, at byte granularity.
    pub fn tell_byte(&self) -> usize {
        self.tell_bit() / 8
    }

    /// Return whether the underlying data is "exhausted", i.e. whether it's
    /// impossible to read any further from the cursor's current position.
    pub fn exhausted(&self) -> bool {
        self.bit_index == 0 && self.byte_len() <= self.byte_pos
    }

    /// Seek to the given bit-granular position in the bitstream.
    ///
    /// NOTE: This is a bit-granular absolute seek. If you only need byte granularity
    /// or would like to do a relative (start or end) seek, use the [`Seek`](std::io::Seek)
    /// implementation.
    pub fn seek_bit(&mut self, pos: usize) -> Result<(), Error> {
        log::debug!("seek_bit: seeking to {}", pos);

        // Get the byte corresponding to this bit.
        let byte_pos = (pos / 8) & !(Self::BLOCK_SIZE - 1);

        if byte_pos > self.byte_len() {
            return Err(Error::Eof);
        }

        // Change our position, and clear any internal block state.
        self.byte_pos = byte_pos;
        self.clear_block_state();

        // Finally, we need to bring our internal block state into sync
        // with our bit position by consuming any bits at the current
        // word before our new position.
        // NOTE(ww): LLVM's BitstreamReader prefers the equivalent of
        // `pos & (usize::BITS - 1)`, presumably to avoid a modulo operation.
        // But (experimentally) LLVM is more than smart enough to optimize
        // this down to a single AND, so I used the modulo version here for
        // clarity.
        let bits_to_consume = pos % Self::BLOCK_SIZE_BITS;
        log::debug!("bits_to_consume={}", bits_to_consume);
        if bits_to_consume > 0 {
            self.read(bits_to_consume)?;
        }

        Ok(())
    }

    /// Clear our internal block state.
    ///
    /// This should be called as part of any operation that modifies the cursor's
    /// position within the bitstream, as any change in position invalidates the
    /// block.
    fn clear_block_state(&mut self) {
        self.current_block = 0;
        self.bit_index = 0;
    }

    /// Fill the internal block state, updating our cursor position in the process.
    ///
    /// This tries to read up to `usize` bytes from the underlying data,
    /// reading fewer if a full block isn't available.
    fn load_current_block(&mut self) -> Result<(), Error> {
        if self.tell_byte() >= self.byte_len() {
            return Err(Error::Eof);
        }

        // NOTE(ww): We've consumed all of the bits in our current block, so clear our state.
        // This is essential to the correct behavior of `load_current_block`,
        // as it uses `tell_byte` to determine which byte to begin at for the next block load.
        self.clear_block_state();

        // Do either a full or a short read, depending on how much data
        // we have left.
        let block_bytes = if self.tell_byte() + Self::BLOCK_SIZE < self.byte_len() {
            &self.inner.as_ref()[self.tell_byte()..(self.tell_byte() + Self::BLOCK_SIZE)]
        } else {
            &self.inner.as_ref()[self.tell_byte()..self.byte_len()]
        };

        self.current_block = 0;
        for (idx, byte) in block_bytes.iter().enumerate() {
            self.current_block |= (*byte as u64) << (idx * 8);
        }

        // We've advanced by this many bytes.
        self.byte_pos += block_bytes.len();

        // We have this many valid bits in the current block.
        self.bit_index = block_bytes.len() * 8;

        log::debug!(
            "load_current_block finished: current_block={}, bit_index={}",
            self.current_block,
            self.bit_index
        );

        Ok(())
    }

    /// Read `nbits` bits of data at the current position. The data is returned
    /// as a `u64`.
    ///
    /// Returns an error if the requested read is invalid (e.g. EOF or not enough data)
    /// or if `nbits` is invalid (zero, or >= `u64::BITS`).
    pub fn read(&mut self, nbits: usize) -> Result<u64, Error> {
        log::debug!(
            "read: nbits={}, current_block={}, bit_index={}",
            nbits,
            self.current_block,
            self.bit_index
        );

        if nbits == 0 || nbits >= Self::BLOCK_SIZE_BITS {
            return Err(Error::InvalidReadSize);
        }

        // If we have enough bits in the current block, steal them and
        // return fast.
        if self.bit_index >= nbits {
            log::debug!("we have enough bits!");

            let read = self.current_block & (!0 >> (Self::BLOCK_SIZE_BITS - nbits));

            self.current_block >>= nbits;
            self.bit_index -= nbits;

            return Ok(read);
        }

        // If we don't have enough bits, use the ones we have and fetch
        // a new `current_block`, completing the read with its contents.
        let bits_left = nbits - self.bit_index;
        let part_1 = if self.bit_index > 0 {
            self.current_block
        } else {
            0
        };

        self.load_current_block()?;

        // `load_current_block` might succeed, but might not load in enough
        // bits to fully service the read.
        if bits_left > self.bit_index {
            return Err(Error::Short);
        }

        let part_2 = self.current_block & (!0 >> (Self::BLOCK_SIZE_BITS - bits_left));

        self.current_block >>= bits_left;
        self.bit_index -= bits_left;

        log::debug!(
            "part_2 done: current_block={}, bit_index={}",
            self.current_block,
            self.bit_index
        );

        // Mash the parts together.
        Ok(part_1 | (part_2 << (nbits - bits_left)))
    }

    /// Read a `nbits` of data at the current position into the given scalar type.
    ///
    /// Returns an error under all of the same conditions as [`read`](BitCursor::read),
    /// as well as if the read value doesn't fit into the given scalar.
    pub fn read_as<Int: NumCast>(&mut self, nbits: usize) -> Result<Int, Error> {
        let res: Int = num::cast(self.read(nbits)?).ok_or(Error::BadCast)?;
        Ok(res)
    }

    /// Read exactly the size of `Int` at the current position.
    ///
    /// Returns an error under all of the same conditions as [`read`](BitCursor::read).
    pub fn read_exact<Int: NumCast>(&mut self) -> Result<Int, Error> {
        self.read_as::<Int>(Int::bitsize())
    }

    /// Read a `width`-wide VBR-encoded integer.
    ///
    /// This function returns only unsigned integers. For signed integers,
    /// use `read_svbr`.
    #[cfg(any(feature = "vbr", doc))]
    pub fn read_vbr(&mut self, width: usize) -> Result<u64, Error> {
        // Sanity check: widths under 2 can't be VBR encodings, and, like LLVM itself,
        // we simply don't support widths above 32.
        if !(2..=Self::MAX_VBR_BITS).contains(&width) {
            return Err(Error::InvalidVbrWidth);
        }

        let block_mask = 1 << (width - 1);

        // Read each VBR block until we encounter a block that doesn't include the
        // continuation bit.
        let mut result: u64 = 0;
        let mut shift = 0;
        loop {
            // Read a block, add it to the result (with the potential continuation bit masked off)
            let block = self.read(width)?;
            log::debug!("block: {:#b}, masked: {:#b}", block, block & !block_mask);
            result |= (block & !block_mask) << shift;

            // If we don't have a continuation bit, then we're done with the VBR.
            let continuation = (block & block_mask) != 0;
            if !continuation {
                break;
            };

            // Calculate the shift needed for the next block.
            shift += width - 1;
        }

        Ok(result)
    }

    /// Return a `width`-side signed VBR-encoded integer from `cursor`.
    ///
    /// This function returns only signed integers, assuming LLVM's signed VBR
    /// representation.
    #[cfg(any(feature = "vbr", doc))]
    pub fn read_svbr(&mut self, width: usize) -> Result<isize, Error> {
        let mut result = self.read_vbr(width)?;

        // The lowest bit indicates the actual sign: high for negative and low for positive.
        let sgn = (result & 1) != 0;
        result >>= 1;

        if sgn {
            Ok(-(result as isize))
        } else {
            Ok(result as isize)
        }
    }

    /// Align the stream on the next 32-bit boundary.
    ///
    /// Any data consumed during alignment is discarded.
    pub fn align32(&mut self) {
        log::debug!("aligning the cursor");

        if self.bit_index >= 32 {
            self.current_block >>= self.bit_index - 32;
            self.bit_index = 32;
        } else {
            self.clear_block_state();
        }
    }
}

/// A `Seek` implementation for `BitCursor`.
///
/// Seeking past the end of a `BitCursor` is always invalid, and always returns
/// an error.
///
/// NOTE: This is a byte-granular implementation of `Seek`.
/// For bit-granular seeking, use [`seek_bit`](BitCursor::seek_bit).
impl<T: AsRef<[u8]>> io::Seek for BitCursor<T> {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        // Note the ugly as-casting below: we ultimately turn `off` into a
        // `usize` to make it compatible with indexing (since we always have
        // a backing buffer), but we first have to round-trip it through i64
        // for relative seeks.
        let off = match pos {
            io::SeekFrom::Start(pos) => pos,
            io::SeekFrom::End(pos) => {
                if pos >= 0 {
                    return Err(io::Error::new(
                        io::ErrorKind::Unsupported,
                        "cannot seek past end",
                    ));
                }

                // Seeking backwards from the end is perfectly fine.
                ((self.byte_len() as i64) + pos) as u64
            }
            io::SeekFrom::Current(pos) => ((self.tell_byte() as i64) + pos) as u64,
        } as usize;

        // Sanity check: we can't seek before or beyond the backing buffer.
        // We can, however, seek to the exact end of the backing buffer, to
        // indicate an EOF condition.
        // We don't need to check for a negative offset here, since we've cast
        // back into the land of unsigned integers.
        if off > self.byte_len() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "impossible seek requested",
            ));
        }

        // Actually update our location.
        self.byte_pos = off;

        // Regardless of the kind of seek, we reset our current block state to ensure that any
        // subsequent reads are correct.
        self.clear_block_state();

        Ok(off as u64)
    }

    fn stream_position(&mut self) -> io::Result<u64> {
        Ok(self.tell_byte() as u64)
    }

    // TODO(ww): Supply this when it's stabilized.
    // fn stream_len(&mut self) -> io::Result<u64> {
    //     Ok(self.byte_len() as u64)
    // }
}

#[cfg(test)]
mod tests {
    use std::io::Seek;

    use super::*;

    fn cursor(buf: &[u8]) -> BitCursor<&[u8]> {
        BitCursor::new(&buf)
    }

    #[test]
    fn test_new_with_len_invalid_length() {
        assert!(BitCursor::new_with_len(&[0xff, 0xee], 3).is_err());
    }

    #[test]
    fn test_read_basic() {
        let mut cur = cursor(&[0b00011011]);

        // Our initial state is reasonable.
        assert_eq!(cur.bit_len(), 8);
        assert_eq!(cur.byte_len(), 1);
        assert_eq!(cur.tell_bit(), 0);
        assert_eq!(cur.tell_byte(), 0);

        // After each read, we advance by the appropriate number of bits/bytes.
        assert_eq!(cur.read(2).unwrap(), 0b11);
        assert_eq!(cur.tell_bit(), 2);
        assert_eq!(cur.tell_byte(), 0);
        assert_eq!(cur.read(2).unwrap(), 0b10);
        assert_eq!(cur.tell_bit(), 4);
        assert_eq!(cur.tell_byte(), 0);
        assert_eq!(cur.read(2).unwrap(), 0b01);
        assert_eq!(cur.tell_bit(), 6);
        assert_eq!(cur.tell_byte(), 0);
        assert_eq!(cur.read(2).unwrap(), 0b00);
        assert_eq!(cur.tell_bit(), 8);
        assert_eq!(cur.tell_byte(), 1);

        // We've fully consumed the stream, so this read produces an error.
        assert!(cur.read(1).is_err());
    }

    #[cfg(feature = "vbr")]
    #[test]
    fn test_invalid_reads() {
        let mut cur = cursor(&[0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x11, 0x22]);

        // VBRs over 32 bits just aren't supported.
        assert!(cur.read_vbr(33).is_err());

        // Normal reads >= 64 bits just aren't supported.
        assert!(cur.read(64).is_err());
    }

    #[test]
    fn test_read_multiple_sizes() {
        let mut cur = cursor(&[0xAA, 0xBB, 0xCC, 0b10010101]);

        assert_eq!(cur.read(24).unwrap(), 0xCCBBAA);
        assert_eq!(cur.read(5).unwrap(), 0b10101);
        assert_eq!(cur.read(3).unwrap(), 0b100);

        // We've fully consumed the stream, so this read produces an error.
        assert!(cur.read(1).is_err());
    }

    #[test]
    fn test_read_bounds() {
        let mut cur = cursor(&[0xAA]);

        // Reads below 1 bit or above the usize bitwidth aren't allowed.
        assert!(cur.read(0).is_err());
        assert!(cur.read(usize::BITS as usize + 1).is_err());
    }

    #[test]
    fn test_read_llvm_wrapper_magic() {
        let mut cur = cursor(&[0xde, 0xc0, 0x17, 0x0b]);

        assert_eq!(cur.read(32).unwrap(), 0x0B17C0DE);
    }

    #[test]
    fn test_read_llvm_raw_magic() {
        let mut cur = cursor(&[b'B', b'C', 0xc0, 0xde]);

        assert_eq!(cur.read(32).unwrap(), 0xdec04342);
    }

    #[test]
    fn test_read_across_blocks() {
        #[rustfmt::skip]
        let mut cur = cursor(&[
            0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
            0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
        ]);

        assert_eq!(cur.read(56).unwrap(), 0x77665544332211);
        assert_eq!(cur.read(24).unwrap(), 0x221188);
    }

    #[test]
    fn test_read_across_blocks_unaligned() {
        #[rustfmt::skip]
        let mut cur = cursor(&[
            0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0b11111111,
            0b00011001, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
        ]);

        assert_eq!(cur.read(56).unwrap(), 0x77665544332211);
        assert_eq!(cur.read(5).unwrap(), 0b11111);
        assert_eq!(cur.read(5).unwrap(), 0b01111);
        assert_eq!(cur.read(6).unwrap(), 0b000110);
    }

    #[test]
    fn test_read_and_align() {
        #[rustfmt::skip]
        let mut cur = cursor(&[
            0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0b11111111,
            0b00011001, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
        ]);

        assert_eq!(cur.read(56).unwrap(), 0x77665544332211);
        assert_eq!(cur.read(5).unwrap(), 0b11111);
        assert_eq!(cur.read(5).unwrap(), 0b01111);
        cur.align32();
        assert_eq!(cur.read(8).unwrap(), 0x55);
        assert_eq!(cur.read(16).unwrap(), 0x7766);
        assert_eq!(cur.read(5).unwrap(), 0b01000);
        assert_eq!(cur.read(3).unwrap(), 0b100);
        assert!(cur.read(1).is_err());
    }

    #[test]
    fn test_read_as() {
        let mut cur = cursor(&[0xAA, 0xBB, 0xCC, 0xDD]);

        assert_eq!(cur.read_as::<u16>(16).unwrap(), 0xBBAA);
        assert_eq!(cur.read_as::<u32>(16).unwrap(), 0xDDCC);
    }

    #[test]
    fn test_read_as_bounds() {
        let mut cur = cursor(&[0xFF, 0xFF, 0xFF, 0xFF]);

        // Attempting to read a value into a type that can't hold that value
        // produces an error.
        assert!(cur.read_as::<u16>(17).is_err());
    }

    #[test]
    fn test_read_exact() {
        let mut cur = cursor(&[0xAA, 0xBB, 0xCC, 0xDD, 0xEE]);

        // read_exact reads exactly the type's bitsize.
        assert_eq!(cur.read_exact::<u32>().unwrap(), 0xDDCCBBAA);
        assert_eq!(cur.tell_bit(), u32::BITS as usize);
        assert_eq!(cur.tell_byte(), (u32::BITS / 8) as usize);

        assert_eq!(cur.read_exact::<u8>().unwrap(), 0xEE);
        assert_eq!(cur.tell_bit(), (u32::BITS + u8::BITS) as usize);
        assert_eq!(cur.tell_byte(), ((u32::BITS + u8::BITS) / 8) as usize);
    }

    #[test]
    fn test_seek_bit() {
        let mut cur = cursor(&[0b1111_1110, 0b1010_0111]);

        assert_eq!(cur.read(4).unwrap(), 0b1110);

        // Seek halfway into the first byte.
        cur.seek_bit(4).unwrap();
        assert_eq!(cur.tell_bit(), 4);
        assert_eq!(cur.tell_byte(), 0);
        assert_eq!(cur.bit_index, 12);

        // Read the next byte's worth.
        // NOTE(ww): The value here is unintuitive from the cursor initialization
        // above: remember that values are always read LSB first, so our next byte
        // comes from the low nibble of the 2nd byte of input plus the high nibble
        // of the 1st.
        assert_eq!(cur.read(8).unwrap(), 0b0111_1111);
        assert_eq!(cur.tell_bit(), 12);
        assert_eq!(cur.tell_byte(), 1);
        assert_eq!(cur.bit_index, 4);

        // Consume the last nibble.
        assert_eq!(cur.read(4).unwrap(), 0b1010);

        // Sanity check: we should be fully consumed.
        assert!(cur.read(1).is_err());
    }

    #[test]
    fn test_seek() {
        let mut cur = cursor(&[0xAA, 0xBB, 0xCC, 0xDD]);

        // Consume the whole thing, putting us at the end.
        assert_eq!(cur.read(32).unwrap(), 0xDDCCBBAA);
        assert_eq!(cur.tell_bit(), 32);
        assert_eq!(cur.tell_byte(), 4);

        // Seek relative, backwards by two bytes.
        cur.seek(io::SeekFrom::Current(-2)).unwrap();
        assert_eq!(cur.tell_bit(), 16);
        assert_eq!(cur.tell_byte(), 2);
        assert_eq!(cur.read(16).unwrap(), 0xDDCC);
        assert_eq!(cur.tell_bit(), 32);
        assert_eq!(cur.tell_byte(), 4);

        // Go back to the start.
        cur.seek(io::SeekFrom::Start(0)).unwrap();
        assert_eq!(cur.tell_bit(), 0);
        assert_eq!(cur.tell_byte(), 0);
        assert_eq!(cur.read(32).unwrap(), 0xDDCCBBAA);
        assert_eq!(cur.tell_bit(), 32);
        assert_eq!(cur.tell_byte(), 4);

        // Seek somewhere in the middle.
        cur.seek(io::SeekFrom::Start(1)).unwrap();
        assert_eq!(cur.tell_bit(), 8);
        assert_eq!(cur.tell_byte(), 1);
        assert_eq!(cur.read(8).unwrap(), 0xBB);

        // Seek backwards from the end.
        cur.seek(io::SeekFrom::End(-1)).unwrap();
        assert_eq!(cur.tell_bit(), 24);
        assert_eq!(cur.tell_byte(), 3);
        assert_eq!(cur.read(8).unwrap(), 0xDD);

        // Seeking past the end is completely unsupported.
        assert!(cur.seek(io::SeekFrom::End(1)).is_err())
    }

    #[cfg(feature = "vbr")]
    #[test]
    fn test_vbr2_continuation() {
        let mut cur = cursor(&[0b01101011]);

        assert_eq!(cur.read_vbr(2).unwrap(), 9);
    }

    #[cfg(feature = "vbr")]
    #[test]
    fn test_vbr4_basic() {
        let mut cur = cursor(&[0b00000111]);

        assert_eq!(cur.read_vbr(4).unwrap(), 7);
    }

    #[cfg(feature = "vbr")]
    #[test]
    fn test_vbr4_continuation() {
        let mut cur = cursor(&[0b0011_1011]);

        assert_eq!(cur.read_vbr(4).unwrap(), 27);
    }

    #[cfg(feature = "vbr")]
    #[test]
    fn test_vbr6_basic() {
        let mut cur = cursor(&[0b00_010000]);
        assert_eq!(cur.read_vbr(6).unwrap(), 16);
        assert_eq!(cur.tell_bit(), 6);
    }

    #[cfg(feature = "vbr")]
    #[test]
    fn test_vbr6_continuation() {
        let mut cur = cursor(&[0b01_100001, 0b0011_1001, 0b100111_00]);
        assert_eq!(cur.read_vbr(6).unwrap(), 3233);
        assert_eq!(cur.read(3).unwrap(), 0b111);
        assert_eq!(cur.read(3).unwrap(), 0b100);
    }

    #[cfg(feature = "vbr")]
    #[test]
    fn test_svbr4() {
        // -3 as a signed VBR4 is `(-(-3) << 1) | 1`, i.e. 7, i.e. 0b0111.
        let mut cur = cursor(&[0b0000_0111]);

        assert_eq!(cur.read_svbr(4).unwrap(), -3);
    }

    #[test]
    fn test_align32() {
        {
            let mut cur = cursor(&[0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x11, 0x22]);

            assert_eq!(cur.read(8).unwrap(), 0xAA);
            cur.align32();
            assert_eq!(cur.tell_bit(), 32);
            assert_eq!(cur.read(8).unwrap(), 0xEE);
            assert_eq!(cur.read(24).unwrap(), 0x2211FF);
            assert_eq!(cur.tell_bit(), 64);
        }

        {
            let mut cur = cursor(&[0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x11, 0x22]);

            cur.align32();
            assert_eq!(cur.tell_bit(), 0);

            cur.read(32).unwrap();
            cur.align32();
            assert_eq!(cur.tell_bit(), 32);
        }

        {
            #[rustfmt::skip]
            let mut cur = cursor(&[
                0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
                0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x00,
            ]);

            cur.read(63).unwrap();
            cur.read(1).unwrap();
            assert_eq!(cur.tell_bit(), 64);
            cur.align32();
            assert_eq!(cur.tell_bit(), 64);

            cur.seek_bit(0).unwrap();
            cur.read(63).unwrap();
            cur.read(1).unwrap();
            cur.read(32).unwrap();
            cur.align32();
            assert_eq!(cur.tell_bit(), 96);
            cur.read(1).unwrap();
            cur.align32();
            assert_eq!(cur.tell_bit(), 128);
        }
    }

    #[test]
    fn test_align32_unaligned() {
        let mut cur = cursor(&[0b00011100, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x11, 0x22]);

        assert_eq!(cur.read(5).unwrap(), 0b11100);
        cur.align32();
        assert_eq!(cur.tell_bit(), 32);
        assert_eq!(cur.read(32).unwrap(), 0x2211FFEE);
        assert_eq!(cur.tell_bit(), 64);
    }

    #[test]
    fn test_align32_next_block() {
        {
            #[rustfmt::skip]
            let mut cur = cursor(&[
                0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
                0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x00,
            ]);

            cur.read(56).unwrap();
            cur.align32();
            assert_eq!(cur.read(32).unwrap(), 0xCCBBAA99);
            assert_eq!(cur.tell_bit(), 96);
        }

        {
            #[rustfmt::skip]
            let mut cur = cursor(&[
                0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
                0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x00,
            ]);

            cur.read(56).unwrap();
            cur.read(17).unwrap();
            cur.align32();
            assert_eq!(cur.read(32).unwrap(), 0x00FFEEDD);
            assert_eq!(cur.tell_bit(), 128);
        }
    }

    #[cfg(feature = "vbr")]
    #[test]
    fn test_parse_unabbrev() {
        // assuming abbrev id width=2
        #[rustfmt::skip]
        let mut cur = cursor(&[
            0b0001_01_11, 0b000001_00, 0b00_000110, 0xFF,
            0b0001_01_11, 0b000001_00, 0b00_000110, 0b11111111,
            0b1_01_11_101, 0b001_00000, 0b00000_000, 0b00000011,
        ]);

        assert_eq!(cur.read_vbr(2).unwrap(), 3); // DEFINE_UNABBREV
        assert_eq!(cur.read_vbr(6).unwrap(), 1); // code 1
        assert_eq!(cur.read_vbr(6).unwrap(), 1); // 1 field
        assert_eq!(cur.read_vbr(6).unwrap(), 6); // value 6

        cur.align32();

        assert_eq!(cur.read_vbr(2).unwrap(), 3); // DEFINE_UNABBREV
        assert_eq!(cur.read_vbr(6).unwrap(), 1); // code 1
        assert_eq!(cur.read_vbr(6).unwrap(), 1); // 1 field
        assert_eq!(cur.read_vbr(6).unwrap(), 6); // value 6

        assert_eq!(cur.tell_bit(), 54);
        assert_eq!(cur.read(13).unwrap(), 0b101_11111111_00);
        assert_eq!(cur.read_vbr(2).unwrap(), 3); // DEFINE_UNABBREV
        assert_eq!(cur.read_vbr(6).unwrap(), 1); // code 1
        assert_eq!(cur.read_vbr(6).unwrap(), 1); // 1 field
        assert_eq!(cur.read_vbr(6).unwrap(), 32); // value 32
    }

    #[cfg(feature = "vbr")]
    #[test]
    fn test_pseudo_bitstream1() {
        let bytes = b"\xAA\xAA\x42\x43\xC0\xDE\x35\x14\x00\x00\x05\x00\x00\x00\x62\x0C";
        let mut cur = cursor(bytes);

        assert_eq!(cur.read(16).unwrap(), 0xAAAA);
        assert_eq!(cur.read(32).unwrap(), 0xDEC04342);
        assert_eq!(cur.read(2).unwrap(), 0b01); // ENTER_SUBBLOCK
        assert_eq!(cur.read_vbr(8).unwrap(), 13); // Block ID #13 (IDENTIFICATION_BLOCK)
        assert_eq!(cur.read_vbr(5).unwrap(), 5); // New abbrev width=5
        assert_eq!(cur.bit_index, 1);
        assert_eq!(cur.tell_bit(), 63);
        cur.align32();
        assert_eq!(cur.bit_index, 0);
        assert_eq!(cur.current_block, 0);
        assert_eq!(cur.tell_bit(), 64);
        cur.read(16).unwrap();
        assert_eq!(cur.read(32).unwrap(), 5);
    }
}
