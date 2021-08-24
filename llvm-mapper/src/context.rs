//! Functionality for managing an LLVM context.

// use std::convert::TryFrom;

// use llvm_constants::{IrBlockId, StrtabCode, SymtabCode};

// use crate::block::BlockId;
// use crate::error::Error;
// use crate::unroll::UnrolledBitstream;

// /// A context for data and data structures that aren't defined directly
// /// within an LLVM module.
// ///
// /// This structure is roughly analogous to LLVM's
// /// [llvm::LLVMContext](https://llvm.org/doxygen/classllvm_1_1LLVMContext.html).
// #[derive(Debug)]
// pub struct Context {
//     strtab: String,
//     symtab: Option<String>,
// }

// impl TryFrom<&UnrolledBitstream> for Context {
//     type Error = Error;

//     fn try_from(unrolled: &UnrolledBitstream) -> Result<Self, Self::Error> {
//         let strtab = {
//             // Unwrap safety: we only construct each block list if we have one or more
//             // blocks of the same ID, so this cannot fail.
//             // NOTE(ww): This only returns the first STRTAB_BLOCK, when a bitstream
//             // could potentially have multiple (one for each module, if multiple
//             // bitstreams have been concatenated together).
//             #[allow(clippy::unwrap_used)]
//             let strtab_block = unrolled
//                 .tops
//                 .get(&BlockId::Ir(IrBlockId::Strtab))
//                 .ok_or_else(|| Error::Context("no string table block to use for context".into()))?
//                 .get(0)
//                 .unwrap();

//             // TODO(ww): The docs also claim that there's only one STRTAB_BLOB per STRTAB_BLOCK,
//             // but at least one person has reported otherwise here:
//             // https://lists.llvm.org/pipermail/llvm-dev/2020-August/144327.html
//             // Needs investigation.
//             let strtab_record = strtab_block.one_record(StrtabCode::Blob as u64)?;

//             strtab_record.try_string(0)?
//         };

//         let symtab = {
//             // NOTE(ww): This only returns the first SYMTAB_BLOCK, when a bitstream
//             // could potentially have multiple (one for each module, if multiple
//             // bitstreams have been concatenated together).
//             let symtab_block = unrolled.tops.get(&BlockId::Ir(IrBlockId::Strtab));

//             if let Some(symtab_block) = symtab_block {
//                 // Panic/index safety: we only construct each block list if we have one or more
//                 // blocks of the same ID, so this cannot fail.
//                 let symtab_record = symtab_block[0].one_record(SymtabCode::Blob as u64)?;

//                 Some(symtab_record.try_string(0)?)
//             } else {
//                 None
//             }
//         };

//         Ok(Self { strtab, symtab })
//     }
// }
