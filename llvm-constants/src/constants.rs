//! Numeric constants for `llvm-constants`.

/// The 32-bit magic that indicates a raw LLVM IR bitcode stream.
pub const LLVM_IR_MAGIC: u32 = 0xdec04342;

/// The 32-bit magic that indicates a bitcode wrapper, which in
/// turn points to the start of the actual bitcode stream.
pub const BITCODE_WRAPPER_MAGIC: u32 = 0x0b17c0de;

/// The initial abbreviation ID width in a bitstream.
pub const INITIAL_ABBREV_ID_WIDTH: u64 = 2;

/// All abbreviation IDs before this are defined by the bitstream format,
/// rather than the stream itself.
pub const FIRST_APPLICATION_ABBREV_ID: usize = 4;

/// All block IDs before this have their semantics defined by the bitstream
/// format, rather than the stream itself.
pub const FIRST_APPLICATION_BLOCK_ID: u64 = 8;

/// The lookup alphabet for the Char6 operand encoding.
pub const CHAR6_ALPHABET: &[u8] =
    b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._";

/// The current toolchain's target triple.
pub const TARGET_TRIPLE: &str = env!("TARGET_TRIPLE");

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_target_triple() {
        assert!(!TARGET_TRIPLE.is_empty());
    }
}
