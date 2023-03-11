//! Functionality for mapping `FUNCTION_BLOCK` blocks.

mod basic_block;
mod instruction;

use std::convert::TryFrom;

pub use basic_block::*;
pub use instruction::*;
use llvm_support::bitcodes::{FunctionCode, IrBlockId};
use llvm_support::{BinaryOp, BinaryOpError, UnaryOp, UnaryOpError};
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::map::{MapCtx, MapError};
use crate::unroll::Block;

use super::vst::{FunctionStyleVst, Vst, VstError};

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

    /// An invalid unary opcode was seen.
    #[error("invalid unary opcode")]
    BadUnOp(#[from] UnaryOpError),

    /// An invalid binary opcode was seen.
    #[error("invalid binary opcode")]
    BadBinOp(#[from] BinaryOpError),

    /// A generic mapping error occurred.
    #[error("generic mapping error")]
    Map(#[from] MapError),

    /// A VST mapping error occured.
    #[error("value symtab mapping error")]
    Vst(#[from] VstError),
}

/// Models the `MODULE_CODE_FUNCTION` record.
#[non_exhaustive]
#[derive(Debug)]
pub struct Function {
    /// The basic blocks of this function.
    pub blocks: Vec<BasicBlock>,
}

impl TryFrom<(&'_ Block, &'_ mut MapCtx<'_>)> for Function {
    type Error = FunctionError;

    fn try_from((block, ctx): (&'_ Block, &'_ mut MapCtx)) -> Result<Self, Self::Error> {
        // TODO: Handle each `MODULE_CODE_FUNCTION`'s sub-blocks.

        // A function block may have a VST sub-block, which we need to
        // parse up-front in order to resolve values.
        let vst = block
            .blocks
            .one_or_none(IrBlockId::ValueSymtab)
            .map_err(MapError::Inconsistent)?
            .map(|b| Vst::try_from((b, FunctionStyleVst {})))
            .transpose()?;

        log::debug!("function-level vst: {vst:?}");

        // A function block should have exactly one DECLAREBLOCKS record.
        let nblocks = {
            let declareblocks = block
                .records
                .exactly_one(FunctionCode::DeclareBlocks)
                .map_err(MapError::Inconsistent)?;

            *declareblocks
                .fields()
                .first()
                .ok_or(FunctionError::InvalidBlockCount)?
        };

        // Like the type table, we need a little bit of a state machine to
        // construct each function's basic blocks and constituent instructions.
        let mut _bbs: Vec<BasicBlock> = Vec::with_capacity(nblocks as usize);
        let mut _bb = BasicBlock::default();

        for record in block.records.into_iter() {
            let code = FunctionCode::try_from(record.code())?;

            macro_rules! unpack_fields {
                ($n:literal) => {
                    <[u64; $n]>::try_from(record.fields()).map_err(|_| {
                        FunctionError::BadInst(format!(
                            "bad {code:?}: expected {} fields, got {}",
                            $n,
                            record.fields().len()
                        ))
                    })
                };
            }

            macro_rules! get_type {
                ($ty:ident) => {
                    // TODO: This is wrong; the lookup here needs to be
                    // aware of forward references.
                    ctx.type_table.get($ty).ok_or_else(|| {
                        FunctionError::BadInst(format!(
                            "bad {code:?}: invalid type table reference: {}",
                            $ty
                        ))
                    })
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
                    let [lhs, ty, rhs, opcode] = unpack_fields!(4)?;
                    log::debug!("binop: lhs valno: {lhs}, rhs valno: {rhs}");
                    let ty = get_type!(ty)?;
                    let _opcode = BinaryOp::try_from((opcode, ty))?;
                }
                FunctionCode::InstCast => {
                    // [opval, opty, destty, castopc]
                    let [_opval, _opty, _destty, _castopc] = unpack_fields!(4)?;
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
                FunctionCode::InstAlloca => {
                    // [instty, opty, op, align]
                    let [_instty, _opty, _op, _align] = unpack_fields!(4)?;
                }
                FunctionCode::InstLoad => {
                    // [opty, op, align, vol]
                    let [_opty, _op, _align, _vol] = unpack_fields!(4)?;
                }
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
                FunctionCode::InstStore => {
                    // [ptrty, ptr, valty, val, align, vol]
                    let [_ptrty, _ptr, _valty, _val] = unpack_fields!(4)?;

                    log::debug!("store valno: {_val}");
                    // NOTE: Two more optional fields: align and vol.
                }
                FunctionCode::InstStoreatomic => todo!(),
                FunctionCode::InstCmpxchg => todo!(),
                FunctionCode::InstLandingpad => todo!(),
                FunctionCode::InstCleanupret => todo!(),
                FunctionCode::InstCatchret => todo!(),
                FunctionCode::InstCatchpad => todo!(),
                FunctionCode::InstCleanuppad => todo!(),
                FunctionCode::InstCatchswitch => todo!(),
                FunctionCode::InstUnop => {
                    // [opval, ty, opcode]
                    let [_opval, ty, opcode] = unpack_fields!(3)?;
                    let _ty = get_type!(ty)?;
                    let _opcode = UnaryOp::try_from(opcode)?;
                }
                FunctionCode::Instcallbr => todo!(),
                FunctionCode::InstFreeze => todo!(),
                FunctionCode::InstAtomicrmw => todo!(),
            }
        }

        unimplemented!()
    }
}
