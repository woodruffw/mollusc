//! Traits for mapping bitstream types to models.

use thiserror::Error;

use crate::block::Strtab;
use crate::block::{AttributeGroups, Attributes, TypeTable};
use crate::record::{DataLayout, RecordStringError};
use crate::unroll::ConsistencyError;

/// Generic errors that can occur when mapping.
#[derive(Debug, Error)]
pub enum MapError {
    /// We couldn't map a block, for any number of reasons.
    #[error("error while mapping block: {0}")]
    BadBlockMap(String),

    /// We encountered an inconsistent block or record state.
    #[error("inconsistent block or record state")]
    Inconsistent(#[from] ConsistencyError),

    /// We encountered an unsupported feature or layout.
    #[error("unsupported: {0}")]
    Unsupported(String),

    /// We encountered an invalid state or combination of states.
    ///
    /// This variant should be used extremely sparingly.
    #[error("invalid: {0}")]
    Invalid(String),

    /// We couldn't extract a string from a record.
    #[error("error while extracting string: {0}")]
    RecordString(#[from] RecordStringError),

    /// We don't have the appropriate context for a mapping operation.
    #[error("missing context for mapping")]
    Context(MapCtxError),
}

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

/// A mushy container for various bits of state that are necessary for
/// correct block and record mapping in the context of a particular IR module.
///
/// This is the "partial" counterpart to the [`MapCtx`](MapCtx) structure,
/// which is produced from this structure with a call to [`reify`](PartialMapCtx::reify).
#[non_exhaustive]
#[derive(Debug, Default)]
pub(crate) struct PartialMapCtx {
    pub(crate) version: Option<u64>,
    pub(crate) datalayout: DataLayout,
    pub(crate) section_table: Vec<String>,
    pub(crate) gc_table: Vec<String>,
    pub(crate) strtab: Option<Strtab>,
    pub(crate) attribute_groups: Option<AttributeGroups>,
    pub(crate) attributes: Option<Attributes>,
    pub(crate) type_table: Option<TypeTable>,
}

impl PartialMapCtx {
    pub(crate) fn reify(&self) -> Result<MapCtx, MapCtxError> {
        Ok(MapCtx {
            version: self.version.ok_or(MapCtxError::NoVersion)?,
            datalayout: &self.datalayout,
            section_table: &self.section_table,
            gc_table: &self.gc_table,
            strtab: self.strtab.as_ref().ok_or(MapCtxError::NoStrtab)?,
            attribute_groups: self
                .attribute_groups
                .as_ref()
                .ok_or(MapCtxError::NoAttributeGroups)?,
            attributes: self
                .attributes
                .as_ref()
                .ok_or(MapCtxError::NoAttributeGroups)?,
            type_table: self.type_table.as_ref().ok_or(MapCtxError::NoTypeTable)?,
        })
    }

    /// Returns the attribute groups stored in this context, or an error if not available.
    pub fn attribute_groups(&self) -> Result<&AttributeGroups, MapCtxError> {
        self.attribute_groups
            .as_ref()
            .ok_or(MapCtxError::NoAttributeGroups)
    }
}

/// A handle for various bits of state that are necessary for correct block
/// and record mapping in the context of a particular IR module.
///
/// Block and record mapping operations are expected to update the supplied context,
/// as appropriate.
#[non_exhaustive]
#[derive(Debug)]
pub struct MapCtx<'ctx> {
    /// The `MODULE_CODE_VERSION` for the IR module being mapped.
    pub version: u64,

    /// The datalayout specification.
    pub datalayout: &'ctx DataLayout,

    /// The section table.
    pub section_table: &'ctx [String],

    /// The GC table.
    pub gc_table: &'ctx [String],

    /// The string table.
    pub strtab: &'ctx Strtab,

    /// Any attribute groups.
    pub attribute_groups: &'ctx AttributeGroups,

    /// Any raw attributes.
    pub attributes: &'ctx Attributes,

    /// The type table.
    pub type_table: &'ctx TypeTable,
    // TODO(ww): Maybe symtab and identification in here?
}

impl MapCtx<'_> {
    /// A helper function for whether or not to use an associated string table for string lookups.
    ///
    /// This corresponds to `MODULE_CODE_VERSION`s of 2 and higher.
    pub fn use_strtab(&self) -> bool {
        self.version >= 2
    }

    /// A helper function for determining how operands are encoded.
    ///
    /// This corresponds to `MODULE_CODE_VERSION`s of 1 and higher.
    pub fn use_relative_ids(&self) -> bool {
        self.version >= 1
    }
}

/// A trait for mapping some raw `T` into a model type.
///
/// This trait allows an implementer to modify the given [`PartialMapCtx`](PartialMapCtx),
/// filling it in with state before it's reified into a "real" [`MapCtx`](MapCtx).
///
/// This two-stage process is designed to limit the number of invalid
/// states that a `MapCtx` can be in, and to enable better lifetimes
/// later in the IR module mapping process.
pub(crate) trait PartialCtxMappable<T>: Sized {
    type Error;

    /// Attempt to map `T` into `Self` using the given [`PartialMapCtx`](PartialMapCtx).
    fn try_map(raw: &T, ctx: &mut PartialMapCtx) -> Result<Self, Self::Error>;
}

/// A trait for mapping some raw `T` into a model type.
///
/// Implementing this trait is *almost* always preferable over
/// [`PartialCtxMappable`](PartialCtxMappable) -- the former should really only
/// be used when a mapping implementation **absolutely** must modify its
/// [`MapCtx`](MapCtx), which should only happen early in IR module parsing.
pub(crate) trait CtxMappable<'ctx, T>: Sized {
    type Error;

    /// Attempt to map `T` into `Self` using the given [`MapCtx`](MapCtx).
    fn try_map(raw: &T, ctx: &'ctx MapCtx) -> Result<Self, Self::Error>;
}
