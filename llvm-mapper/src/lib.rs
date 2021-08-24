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
