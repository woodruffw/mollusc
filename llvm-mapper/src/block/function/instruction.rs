//! Models and functionality for individual LLVM IR instructions.

use llvm_support::{BinaryOp, CastOp, UnaryOp};

/// Represents an LLVM instruction.
#[derive(Debug)]
pub enum Instruction {
    /// Unary instructions.
    Unary {
        /// The opcode.
        op: UnaryOp,
    },
    /// Binary instructions.
    Binary {
        /// The opcode.
        op: BinaryOp,
        // TODO: lhs, rhs
    },
    /// Cast instructions.
    Cast {
        /// The opcode.
        op: CastOp,
        // TODO: srcval, srcty, dstty
    },
    /// `getelementptr`
    GetElementPtr,
    /// `extractvalue`
    ExtractValue,
    /// `insertvalue`
    InsertValue,
    /// `select`
    Select,
    /// `extractelement`
    ExtractElement,
    /// `insertelement`
    InsertElement,
    /// `shufflevector`
    ShuffleVector,
    /// `cmp`
    Cmp,
    /// `ret`
    Ret,
    /// `br`
    Br,
    /// `cleanupret`
    CleanupRet,
    /// `catchret`
    CatchRet,
    /// `catchswitch`
    CatchSwitch,
    /// `catchpad`
    CatchPad,
    /// `switch`
    Switch,
    /// `indirectbr`
    IndirectBr,
    /// `invoke`
    Invoke,
    /// `resume`
    Resume,
    /// `callbr`
    CallBr,
    /// `unreachable`
    Unreachable,
    /// `landingpad`
    LandingPad,
    /// `alloca`
    Alloca,
    /// `load`
    Load,
    /// `store`
    Store,
    /// `cmpxchg`
    CmpXchg,
    /// `atomicrmw`
    AtomicRMW,
    /// `fence`
    Fence,
    /// `call`
    Call,
    /// `va_arg`
    VAArg,
    /// `freeze`
    Freeze,
}
