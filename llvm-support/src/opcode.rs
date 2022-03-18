//! Support code for instruction opcodes.

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
