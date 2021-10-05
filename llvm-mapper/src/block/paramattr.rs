//! Functionality for mapping the `PARAMATTR_BLOCK` and `PARAMATTR_GROUP_BLOCK` blocks.

use num_enum::TryFromPrimitive;

/// Represents the different kinds of attributes.
#[non_exhaustive]
#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(u64)]
pub enum AttrKind {
    /// A well-known attribute.
    WellKnown = 0,
    /// A well-known attribute with an integer value.
    WellKnownValue,
    /// A string attribute.
    String,
    /// A string attribute with a string value.
    StringValue,
}

/// Represents the attributes for all function parameters in an IR module.
pub struct ParamAttrs;
