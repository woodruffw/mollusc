//! Functionality for mapping the `PARAMATTR_BLOCK` and `PARAMATTR_GROUP_BLOCK` blocks.

use std::convert::TryFrom;

use llvm_constants::{AttributeCode, IrBlockId};
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::block::{BlockMapError, IrBlock};
use crate::map::MapCtx;
use crate::record::RecordMapError;
use crate::unroll::UnrolledBlock;

/// Errors that can occur when mapping attribute blocks.
#[derive(Debug, Error)]
pub enum AttributeError {
    /// An unknown record code was seen.
    #[error("unknown attribute code")]
    UnknownAttributeCode(#[from] TryFromPrimitiveError<AttributeCode>),
    /// The given code was seen in an unexpected block.
    #[error("wrong block for code: {0:?}")]
    WrongBlock(AttributeCode),
}

/// Maps all attributes in an IR module.
///
/// This is a zero-sized type that, when mapped, updates the associated
/// [`MapCtx`](MapCtx) as appropriate.
pub struct Attributes;

impl IrBlock for Attributes {
    const BLOCK_ID: IrBlockId = IrBlockId::ParamAttr;

    fn try_map_inner(_block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        unimplemented!();
    }
}

/// Maps all attribute groups in an IR module.
///
/// This is a zero-sized type that, when mapped, updates the associated
/// [`MapCtx`](MapCtx) as appropriate.
pub struct AttributeGroups;

impl IrBlock for AttributeGroups {
    const BLOCK_ID: IrBlockId = IrBlockId::ParamAttrGroup;

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        for record in block.all_records() {
            let code = AttributeCode::try_from(record.code()).map_err(AttributeError::from)?;

            if code != AttributeCode::GroupCodeEntry {
                return Err(AttributeError::WrongBlock(code).into());
            }

            // Structure: [grpid, idx, <attr0>, <attr1>, ...]
            // Where <attrN>: [kind, key[...], value[...]].
            // Every group record must have at least one attribute.
            if record.fields().len() < 3 {
                return Err(RecordMapError::BadRecordLayout(format!(
                    "too few fields in {:?}, expected {} >= 3",
                    code,
                    record.fields().len()
                ))
                .into());
            }
        }

        unimplemented!();
    }
}
