//! Traits for mapping bitstream types to models.

use thiserror::Error;

use crate::block::Strtab;
use crate::block::{AttributeGroups, Attributes, TypeTable};

/// Errors that can occur when accessing a [`MapCtx`](MapCtx).
#[derive(Debug, Error)]
pub enum MapCtxError {
    /// The version field is needed, but unavailable.
    #[error("mapping context requires a version for disambiguation, but none is available")]
    NoVersion,
    /// The string table is needed, but unavailable.
    #[error("mapping context requires a string table, but none is available")]
    NoStrtab,
    /// The attribute group table is needed, but unavailable.
    #[error("mapping context requires attribute groups, but none are available")]
    NoAttributeGroups,
    /// The type table is needed, but unavailable.
    #[error("mapping context requires types, but none are available")]
    NoTypeTable,
}

/// A handle for various bits of state that are necessary for correct block
/// and record mapping in the context of a particular IR module.
///
/// Internally, this is a mushy state object that may or may not contain
/// sufficient information for parsing a particular block or record; hence
/// the fallible access methods.
///
/// Block and record mapping operations are expected to update the supplied context,
/// as appropriate.
#[non_exhaustive]
#[derive(Debug, Default)]
pub struct MapCtx {
    // TODO(ww): Think harder about this struct. Maybe these should be non-Options, and
    // the Mappable trait should instead take an Option<MapCtx>. Then, we'd prefill
    // the MapCtx will all requisite state during the unroll phase, rather than deferring
    // it to module creation. Is that better or worse?
    pub(crate) version: Option<u64>,
    pub(crate) strtab: Option<Strtab>,
    pub(crate) attribute_groups: Option<AttributeGroups>,
    pub(crate) attributes: Option<Attributes>,
    pub(crate) type_table: Option<TypeTable>,
    // TODO(ww): Maybe symtab and identification in here?
}

impl MapCtx {
    /// Returns the version stored in this context, or an error if no version is available.
    pub fn version(&self) -> Result<u64, MapCtxError> {
        self.version.ok_or(MapCtxError::NoVersion)
    }

    /// A helper function for whether or not to use an associated string table for string lookups.
    ///
    /// This corresponds to `MODULE_CODE_VERSION`s of 2 and higher.
    pub fn use_strtab(&self) -> Result<bool, MapCtxError> {
        self.version().map(|v| v >= 2)
    }

    /// A helper function for determining how operands are encoded.
    ///
    /// This corresponds to `MODULE_CODE_VERSION`s of 1 and higher.
    pub fn use_relative_ids(&self) -> Result<bool, MapCtxError> {
        self.version().map(|v| v >= 1)
    }

    /// Returns the string table stored in this context, or an error if no string table is available.
    pub fn strtab(&self) -> Result<&Strtab, MapCtxError> {
        self.strtab.as_ref().ok_or(MapCtxError::NoStrtab)
    }

    /// Returns the attribute groups stored in this context, or an error if not available.
    pub fn attribute_groups(&self) -> Result<&AttributeGroups, MapCtxError> {
        self.attribute_groups
            .as_ref()
            .ok_or(MapCtxError::NoAttributeGroups)
    }

    /// Returns the type table stored in this context, or an error if not available.
    pub fn type_table(&self) -> Result<&TypeTable, MapCtxError> {
        self.type_table.as_ref().ok_or(MapCtxError::NoTypeTable)
    }
}

/// A trait for mapping some raw `T` into a model type.
pub(crate) trait Mappable<T>: Sized {
    type Error;

    // TODO(ww): This should declare an associated type for the error, instead
    // of using the crate-wide Error.

    /// Attempt to map `T` into `Self` using the given [`MapCtx`](MapCtx).
    fn try_map(raw: &T, ctx: &mut MapCtx) -> Result<Self, Self::Error>;
}
