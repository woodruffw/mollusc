//! `llvm-mapper` is a library for mapping entities in LLVM's bitstream
//! format into higher-level IR and bitcode metadata models.

#![deny(broken_intra_doc_links)]
#![deny(missing_docs)]
#![allow(clippy::redundant_field_names)]
#![forbid(unsafe_code)]

pub mod block;
pub mod context;
pub mod error;
mod map;
pub mod record;
pub mod unroll;

use crate::block::{Identification, Module};

/// Represents a string table.
#[derive(Debug)]
pub struct Strtab(Vec<u8>);

impl AsRef<[u8]> for Strtab {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Strtab {
    /// Get a string in the string table by its index and length.
    ///
    /// Returns `None` if either the index or size is invalid, or if the
    /// requested slice isn't a valid string.
    pub fn get(&self, idx: usize, size: usize) -> Option<&str> {
        let inner = self.as_ref();

        if size == 0 || idx >= inner.len() || idx + size > inner.len() {
            return None;
        }

        std::str::from_utf8(&inner[idx..idx + size]).ok()
    }
}

/// Represents a symbol table.
#[derive(Debug)]
pub struct Symtab(Vec<u8>);

impl AsRef<[u8]> for Symtab {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Symtab {
    /// Get a symbol in the symbol table by its index and length.
    ///
    /// Returns `None` if either the index or size is invalid, or if the
    /// requested slice isn't a valid string.
    pub fn get(&self, idx: usize, size: usize) -> Option<&str> {
        let inner = self.as_ref();

        if size == 0 || idx >= inner.len() || idx + size > inner.len() {
            return None;
        }

        std::str::from_utf8(&inner[idx..idx + size]).ok()
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
    fn test_strtab() {
        let inner = "this is a string table";
        let strtab = Strtab(inner.into());
        assert_eq!(strtab.get(0, 4).unwrap(), "this");
        assert_eq!(strtab.get(0, 7).unwrap(), "this is");
        assert_eq!(strtab.get(8, 14).unwrap(), "a string table");
        assert_eq!(
            strtab.get(0, inner.len()).unwrap(),
            "this is a string table"
        );

        assert!(strtab.get(inner.len(), 0).is_none());
        assert!(strtab.get(0, inner.len() + 1).is_none());
        assert!(strtab.get(0, 0).is_none());
    }
}
