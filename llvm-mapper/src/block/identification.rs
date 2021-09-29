//! Functionality for mapping the `IDENTIFICATION_BLOCK` block.

use llvm_constants::{IdentificationCode, IrBlockId};

use crate::block::{BlockMapError, IrBlock};
use crate::map::MapCtx;
use crate::unroll::UnrolledBlock;

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

    fn try_map_inner(block: &UnrolledBlock, _ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        let producer = {
            let producer = block.one_record(IdentificationCode::ProducerString as u64)?;

            producer.try_string(0)?
        };

        let epoch = {
            let epoch = block.one_record(IdentificationCode::Epoch as u64)?;

            epoch.get_field(0)?
        };

        Ok(Self { producer, epoch })
    }
}
