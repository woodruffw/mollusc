//! Support code for instruction opcodes.

use std::convert::TryFrom;

use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::{
    bitcodes::{BinaryOpcode, UnaryOpcode},
    Type,
};

/// Represents the different classes of LLVM opcodes.
#[derive(Clone, Copy, Debug)]
pub enum Opcode {
    /// Opcodes that terminate basic blocks.
    Term(TermOp),
    /// Opcodes that take a single operand.
    Unary(UnaryOp),
    /// Opcodes that take two operands.
    Binary(BinaryOp),
    /// Opcodes that interact with memory.
    Mem(MemOp),
    /// Opcodes that cast between types and representations.
    Cast(CastOp),
    /// Funclet "landing pad" operands.
    FuncletPad(FuncletPadOp),
    /// "Other" operands of all sorts.
    Other(OtherOp),
}

/// Opcodes that terminate basic blocks. Every well-formed basic block ends
/// with an instruction with one of these opcodes.
#[derive(Clone, Copy, Debug)]
pub enum TermOp {
    /// `ret`
    Ret,
    /// `br`
    Br,
    /// `switch`
    Switch,
    /// `indirectbr`
    IndirectBr,
    /// `invoke`
    Invoke,
    /// `resume`
    Resume,
    /// `unreachable`
    Unreachable,
    /// `cleanupret`
    CleanupRet,
    /// `catchret`
    CatchRet,
    /// `callswitch`
    /// NOTE: Not documented?
    CatchSwitch,
    /// `callbr`
    CallBr,
}

/// Unary opcodes.
#[derive(Clone, Copy, Debug)]
pub enum UnaryOp {
    /// `fneg`
    FNeg,
}

/// Errors that can occur when constructing a `BinaryOp`.
#[derive(Debug, Error)]
pub enum UnaryOpError {
    /// The opcode given doesn't correspond to a known operation.
    #[error("unknown opcode")]
    Opcode(#[from] TryFromPrimitiveError<UnaryOpcode>),
}

impl TryFrom<u64> for UnaryOp {
    type Error = UnaryOpError;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        Ok(UnaryOpcode::try_from(value)?.into())
    }
}

impl From<UnaryOpcode> for UnaryOp {
    fn from(value: UnaryOpcode) -> Self {
        match value {
            UnaryOpcode::FNeg => UnaryOp::FNeg,
        }
    }
}

/// Binary opcodes.
#[derive(Clone, Copy, Debug)]
pub enum BinaryOp {
    /// `add`
    Add,
    /// `fadd`
    FAdd,
    /// `sub`
    Sub,
    /// `fsub`
    FSub,
    /// `mul`
    Mul,
    /// `fmul`
    FMul,
    /// `udiv`
    UDiv,
    /// `sdiv`
    SDiv,
    /// `fdiv`
    FDiv,
    /// `urem`
    URem,
    /// `srem`
    SRem,
    /// `frem`
    FRem,
    /// `shl`
    Shl,
    /// `lshl`
    LShr,
    /// `ashr`
    AShr,
    /// `and`
    And,
    /// `or`
    Or,
    /// `xor`
    Xor,
}

/// Errors that can occur when constructing a `BinaryOp`.
#[derive(Debug, Error)]
pub enum BinaryOpError {
    /// The specified type isn't valid for binary operations.
    #[error("invalid type for binary op {0:?}: {1:?}")]
    InvalidType(BinaryOpcode, Type),

    /// The specified type is incompatible with the operation.
    #[error("incompatible type for op {0:?}: {1:?}")]
    IncompatibleType(BinaryOpcode, Type),

    /// The opcode given doesn't correspond to a known operation.
    #[error("unknown opcode")]
    Opcode(#[from] TryFromPrimitiveError<BinaryOpcode>),
}

impl TryFrom<(u64, &Type)> for BinaryOp {
    type Error = BinaryOpError;

    fn try_from((opc, ty): (u64, &Type)) -> Result<Self, Self::Error> {
        let opc = BinaryOpcode::try_from(opc)?;

        let is_fp = ty.is_floating_or_floating_vector();

        // Binary operations are only valid on integer/fp types or vectors thereof.
        if !is_fp || !ty.is_integer_or_integer_vector() {
            return Err(BinaryOpError::InvalidType(opc, ty.clone()));
        }

        Ok(match (opc, is_fp) {
            (BinaryOpcode::Add, false) => BinaryOp::Add,
            (BinaryOpcode::Add, true) => BinaryOp::FAdd,
            (BinaryOpcode::Sub, false) => BinaryOp::Sub,
            (BinaryOpcode::Sub, true) => BinaryOp::FSub,
            (BinaryOpcode::Mul, false) => BinaryOp::Mul,
            (BinaryOpcode::Mul, true) => BinaryOp::FMul,
            (BinaryOpcode::UDiv, false) => BinaryOp::UDiv,
            // `udiv` can't be used with floating-point types.
            (BinaryOpcode::UDiv, true) => {
                return Err(BinaryOpError::IncompatibleType(opc, ty.clone()))
            }
            (BinaryOpcode::SDiv, false) => BinaryOp::SDiv,
            (BinaryOpcode::SDiv, true) => BinaryOp::FDiv,
            (BinaryOpcode::URem, false) => BinaryOp::URem,
            // `urem` can't be used with floating-point types.
            (BinaryOpcode::URem, true) => {
                return Err(BinaryOpError::IncompatibleType(opc, ty.clone()))
            }
            (BinaryOpcode::SRem, false) => BinaryOp::SRem,
            (BinaryOpcode::SRem, true) => BinaryOp::FRem,
            // The rest are all integer-type only.
            (BinaryOpcode::Shl, true) => BinaryOp::Shl,
            (BinaryOpcode::LShr, true) => BinaryOp::LShr,
            (BinaryOpcode::AShr, true) => BinaryOp::AShr,
            (BinaryOpcode::And, true) => BinaryOp::And,
            (BinaryOpcode::Or, true) => BinaryOp::Or,
            (BinaryOpcode::Xor, true) => BinaryOp::Xor,
            (_, false) => return Err(BinaryOpError::IncompatibleType(opc, ty.clone())),
        })
    }
}

/// Memory opcodes.
#[derive(Clone, Copy, Debug)]
pub enum MemOp {
    /// `alloca`
    Alloca,
    /// `load`
    Load,
    /// `store`
    Store,
    /// `getelementptr`
    GetElementPtr,
    /// `fence`
    Fence,
    /// `cmpxchg`
    AtomicCmpXchg,
    /// `atomicrmw`
    AtomicRMW,
}

/// Cast opcodes.
#[derive(Clone, Copy, Debug)]
pub enum CastOp {
    /// `trunc`
    Trunc,
    /// `zext`
    ZExt,
    /// `sext`
    SExt,
    /// `fptoui`
    FPToUI,
    /// `fptosi`
    FPToSI,
    /// `uitofp`
    UIToFP,
    /// `sitofp`
    SIToFP,
    /// `fptrunc`
    FPTrunc,
    /// `fpext`
    FPExt,
    /// `ptrtoint`
    PtrToInt,
    /// `inttoptr`
    IntToPtr,
    /// `bitcast`
    BitCast,
    /// `addrspacecast`
    AddrSpaceCast,
}

/// Funclet pad opcodes.
#[derive(Clone, Copy, Debug)]
pub enum FuncletPadOp {
    /// `cleanuppad`
    CleanupPad,
    /// `catchpad`
    CatchPad,
}

/// Other opcodes.
#[derive(Clone, Copy, Debug)]
pub enum OtherOp {
    /// `icmp`
    ICmp,
    /// `fcmp`
    FCmp,
    /// `phi`
    Phi,
    /// `call`
    Call,
    /// `select`
    Select,
    /// Internal pass opcode.
    UserOp1,
    /// Internal pass opcode.
    UserOp2,
    /// `va_arg`
    VAArg,
    /// `extractelement`
    ExtractElement,
    /// `insertelement`
    InsertElement,
    /// `shufflevector`
    ShuffleVector,
    /// `extractvalue`
    ExtractValue,
    /// `insertvalue`
    InsertValue,
    /// `landingpad`
    LandingPad,
    /// `freeze`
    Freeze,
}
