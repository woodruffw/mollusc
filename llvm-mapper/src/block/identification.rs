//! Functionality for mapping the `IDENTIFICATION_BLOCK` block.

use llvm_constants::{IdentificationCode, IrBlockId};
use thiserror::Error;

use crate::block::{BlockMapError, IrBlock};
use crate::map::PartialMapCtx;
use crate::record::RecordMapError;
use crate::unroll::UnrolledBlock;

/// Errors that can occur while mapping the identification block.
#[derive(Debug, Error)]
pub enum IdentificationError {
    /// The `IDENTIFICATION_CODE_EPOCH` couldn't be found.
    #[error("identification block has no epoch")]
    MissingEpoch,
}

/// Models the `IDENTIFICATION_BLOCK` block.
#[non_exhaustive]
#[derive(Debug)]
pub struct Identification {
    /// The name of the "producer" for this bitcode.
    pub producer: String,
    /// The compatibility epoch.
    pub epoch: u64,
}

impl IrBlock for Identification {
    const BLOCK_ID: IrBlockId = IrBlockId::Identification;

    fn try_map_inner(
        block: &UnrolledBlock,
        _ctx: &mut PartialMapCtx,
    ) -> Result<Self, BlockMapError> {
        let producer = {
            let producer = block.one_record(IdentificationCode::ProducerString as u64)?;

            producer.try_string(0).map_err(RecordMapError::from)?
        };

        let epoch = {
            let epoch = block.one_record(IdentificationCode::Epoch as u64)?;

            *epoch
                .fields()
                .get(0)
                .ok_or(IdentificationError::MissingEpoch)?
        };

        Ok(Self { producer, epoch })
    }
}
