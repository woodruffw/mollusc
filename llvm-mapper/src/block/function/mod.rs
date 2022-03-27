//! Functionality for mapping `FUNCTION_BLOCK` blocks.

mod basic_block;
mod instruction;

use std::convert::TryFrom;

pub use basic_block::*;
pub use instruction::*;
use llvm_support::bitcodes::FunctionCode;
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::map::{MapCtx, MapError};
use crate::unroll::Block;

/// Errors that can occur when mapping function blocks.
#[derive(Debug, Error)]
pub enum FunctionError {
    /// `FUNC_CODE_DECLAREBLOCKS` is either missing or zero.
    #[error("function does not declare block count or has zero blocks")]
    InvalidBlockCount,

    /// An unknown record code was seen.
    #[error("unknown function code")]
    UnknownFunctionCode(#[from] TryFromPrimitiveError<FunctionCode>),

    /// An invalid instruction encoding was seen.
    #[error("invalid instruction encoding: {0}")]
    BadInst(String),

    /// A generic mapping error occurred.
    #[error("generic mapping error")]
    Map(#[from] MapError),
}

/// Models the `MODULE_CODE_FUNCTION` record.
#[non_exhaustive]
#[derive(Debug)]
pub struct Function {
    /// The basic blocks of this function.
    pub blocks: Vec<BasicBlock>,
}

impl TryFrom<(&'_ Block, &'_ MapCtx<'_>)> for Function {
    type Error = FunctionError;

    fn try_from((block, _ctx): (&'_ Block, &'_ MapCtx)) -> Result<Self, Self::Error> {
        // TODO: Handle each `MODULE_CODE_FUNCTION`'s sub-blocks.

        // A function block should have exactly one DECLAREBLOCKS record.
        let nblocks = {
            let declareblocks = block
                .records
                .exactly_one(FunctionCode::DeclareBlocks)
                .map_err(MapError::Inconsistent)?;

            *declareblocks
                .fields()
                .get(0)
                .ok_or(FunctionError::InvalidBlockCount)?
        };

        // Like the type table, we need a little bit of a state machine to
        // construct each function's basic blocks and constituent instructions.
        let mut bbs: Vec<BasicBlock> = Vec::with_capacity(nblocks as usize);
        let mut bb = BasicBlock::default();

        for record in block.records.into_iter() {
            let code = FunctionCode::try_from(record.code())?;

            macro_rules! check_fields {
                ($n:literal) => {
                    if record.fields().len() < $n {
                        return Err(FunctionError::BadInst(format!(
                            "bad {code:?}: expected {} fields, got {}",
                            $n,
                            record.fields().len()
                        )));
                    }
                };
            }

            // Function codes fall into a few general categories:
            //
            // * State machine management (`DECLAREBLOCKS`)
            // * Instruction declaration (`INST_*`)
            // * Debug state (`DEBUG_LOC`, `DEBUG_LOC_AGAIN`)
            // * Operand bundles (`OPERAND_BUNDLE`)
            //
            // Each category is grouped below, with the smaller ones first.
            match code {
                // Handled above.
                FunctionCode::DeclareBlocks => continue,

                // Operand bundles.
                FunctionCode::OperandBundle => unimplemented!(),

                // Debug state.
                FunctionCode::DebugLoc => unimplemented!(),
                FunctionCode::DebugLocAgain => unimplemented!(),

                // The big one: all instructions.
                FunctionCode::InstBinop => {
                    // [opval, ty, opval, opcode]
                    check_fields!(4);
                }
                FunctionCode::InstCast => {
                    // [opval, opty, destty, castopc]
                    check_fields!(4);
                }
                FunctionCode::InstGepOld => todo!(),
                FunctionCode::InstSelect => todo!(),
                FunctionCode::InstExtractelt => todo!(),
                FunctionCode::InstInsertelt => todo!(),
                FunctionCode::InstShufflevec => todo!(),
                FunctionCode::InstCmp => todo!(),
                FunctionCode::InstRet => todo!(),
                FunctionCode::InstBr => todo!(),
                FunctionCode::InstSwitch => todo!(),
                FunctionCode::InstInvoke => todo!(),
                FunctionCode::InstUnreachable => todo!(),
                FunctionCode::InstPhi => todo!(),
                FunctionCode::InstAlloca => todo!(),
                FunctionCode::InstLoad => todo!(),
                FunctionCode::InstVaarg => todo!(),
                FunctionCode::InstStoreOld => todo!(),
                FunctionCode::InstExtractval => todo!(),
                FunctionCode::InstInsertval => todo!(),
                FunctionCode::InstCmp2 => todo!(),
                FunctionCode::InstVselect => todo!(),
                FunctionCode::InstInboundsGepOld => todo!(),
                FunctionCode::InstIndirectbr => todo!(),
                FunctionCode::InstCall => todo!(),
                FunctionCode::InstFence => todo!(),
                FunctionCode::InstCmpxchgOld => todo!(),
                FunctionCode::InstAtomicrmwOld => todo!(),
                FunctionCode::InstResume => todo!(),
                FunctionCode::InstLandingpadOld => todo!(),
                FunctionCode::InstLoadatomic => todo!(),
                FunctionCode::InstStoreatomicOld => todo!(),
                FunctionCode::InstGep => todo!(),
                FunctionCode::InstStore => todo!(),
                FunctionCode::InstStoreatomic => todo!(),
                FunctionCode::InstCmpxchg => todo!(),
                FunctionCode::InstLandingpad => todo!(),
                FunctionCode::InstCleanupret => todo!(),
                FunctionCode::InstCatchret => todo!(),
                FunctionCode::InstCatchpad => todo!(),
                FunctionCode::InstCleanuppad => todo!(),
                FunctionCode::InstCatchswitch => todo!(),
                FunctionCode::InstUnop => todo!(),
                FunctionCode::Instcallbr => todo!(),
                FunctionCode::InstFreeze => todo!(),
                FunctionCode::InstAtomicrmw => todo!(),
            }
        }

        unimplemented!()
    }
}
