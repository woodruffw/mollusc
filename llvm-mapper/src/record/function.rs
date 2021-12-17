//! Functionality for mapping the `MODULE_CODE_FUNCTION` record.

use thiserror::Error;

use crate::map::{MapCtx, Mappable};
use crate::unroll::UnrolledRecord;

/// Errors that can occur when mapping a function record.
#[derive(Debug, Error)]
pub enum FunctionError {}

/// Models the `MODULE_CODE_FUNCTION` record.
#[non_exhaustive]
#[derive(Debug)]
pub struct Function {}

impl Mappable<UnrolledRecord> for Function {
    type Error = FunctionError;

    fn try_map(_record: &UnrolledRecord, _ctx: &mut MapCtx) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}
