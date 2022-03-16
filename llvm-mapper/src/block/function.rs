//! Functionality for mapping `FUNCTION_BLOCK` blocks.

use std::convert::TryFrom;

use thiserror::Error;

use crate::{map::MapCtx, unroll::Block};

/// Errors that can occur when mapping function blocks.
#[derive(Debug, Error)]
pub enum FunctionError {}

/// Models the `MODULE_CODE_FUNCTION` record.
#[non_exhaustive]
#[derive(Debug)]
pub struct Function {}

impl TryFrom<(&'_ Block, &'_ MapCtx<'_>)> for Function {
    type Error = FunctionError;

    fn try_from((_block, _ctx): (&'_ Block, &'_ MapCtx)) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}
