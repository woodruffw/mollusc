//! Functionality for mapping the `IDENTIFICATION_BLOCK` block.

use llvm_support::bitcodes::{IdentificationCode, IrBlockId};
use thiserror::Error;

use crate::block::IrBlock;
use crate::map::{MapError, PartialMapCtx};
use crate::unroll::UnrolledBlock;

/// Errors that can occur while mapping the identification block.
#[derive(Debug, Error)]
pub enum IdentificationError {
    /// The `IDENTIFICATION_CODE_PRODUCER` couldn't be found.
    #[error("identification block has no producer")]
    MissingProducer,

    /// The producer string is malformed.
    #[error("malformed producer string")]
    BadProducer,

    /// The `IDENTIFICATION_CODE_EPOCH` couldn't be found.
    #[error("identification block has no epoch")]
    MissingEpoch,

    /// A generic mapping error occured.
    #[error("mapping error in string table")]
    Map(#[from] MapError),
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
    type Error = IdentificationError;

    const BLOCK_ID: IrBlockId = IrBlockId::Identification;

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut PartialMapCtx) -> Result<Self, Self::Error> {
        let producer = block
            .records()
            .one(IdentificationCode::ProducerString as u64)
            .ok_or(IdentificationError::MissingProducer)
            .and_then(|r| {
                r.try_string(0)
                    .map_err(|_| IdentificationError::BadProducer)
            })?;

        let epoch = *block
            .records()
            .one(IdentificationCode::Epoch as u64)
            .ok_or(IdentificationError::MissingEpoch)
            .and_then(|r| r.fields().get(0).ok_or(IdentificationError::MissingEpoch))?;

        Ok(Self { producer, epoch })
    }
}
