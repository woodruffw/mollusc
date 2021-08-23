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

/// A `BitstreamModule` encapsulates the top-level pieces of bitstream state needed for
/// a single LLVM bitcode module: the `IDENTIFICATION_BLOCK`, the `MODULE_BLOCK` itself,
/// a `STRTAB_BLOCK`, and a `SYMTAB_BLOCK` (if present). A bitstream can contain multiple
/// LLVM modules (e.g. if produced by `llvm-cat -b`), so parsing a bitstream can result
/// in multiple `BitstreamModule`s.
#[derive(Debug)]
pub struct BitstreamModule {
    /// The string table associated with this module.
    pub strtab: Strtab,

    /// The symbol table associated with this module, if it has one.
    pub symtab: Option<Symtab>,
}

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
