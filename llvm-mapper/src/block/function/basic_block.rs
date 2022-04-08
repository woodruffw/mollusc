//! Models and functionality for basic blocks.

use super::Instruction;

/// Represents a basic block.
#[non_exhaustive]
#[derive(Debug, Default)]
pub struct BasicBlock {
    /// The instructions of this basic block.
    pub instructions: Vec<Instruction>,
}
