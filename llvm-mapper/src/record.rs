//! Structures for mapping from bitstream records to LLVM models.

use std::convert::TryFrom;

use llvm_support::{
    AddressSpace, Align, AlignError, Endian, Mangling, PointerAlignElems, TypeAlignElems,
};
use thiserror::Error;

/// Potential errors when parsing an LLVM datalayout string.
#[derive(Debug, Error)]
pub enum DataLayoutError {
    /// The specified alignment is invalid.
    #[error("bad alignment value")]
    BadAlign(#[from] AlignError),
}

/// Models the `MODULE_CODE_DATALAYOUT` record.
#[derive(Debug)]
pub struct DataLayout {
    endianness: Endian,
    natural_stack_alignment: Option<Align>,
    program_address_space: AddressSpace,
    global_variable_address_space: AddressSpace,
    alloca_address_space: AddressSpace,
    type_alignments: TypeAlignElems,
    pointer_alignments: PointerAlignElems,
    aggregate_alignment: Align,
    function_pointer_alignment: Option<Align>,
    mangling: Option<Mangling>,
    native_integer_widths: Vec<u32>,
    non_integral_address_spaces: Vec<u32>,
}

impl Default for DataLayout {
    fn default() -> Self {
        #[allow(clippy::unwrap_used)]
        Self {
            endianness: Endian::Big,
            natural_stack_alignment: None,
            program_address_space: Default::default(),
            global_variable_address_space: Default::default(),
            alloca_address_space: Default::default(),
            type_alignments: TypeAlignElems::default(),
            pointer_alignments: PointerAlignElems::default(),
            aggregate_alignment: Align::ALIGN8,
            function_pointer_alignment: None,
            mangling: None,
            native_integer_widths: vec![],
            non_integral_address_spaces: vec![],
        }
    }
}

impl TryFrom<String> for DataLayout {
    type Error = DataLayoutError;

    fn try_from(_value: String) -> Result<Self, Self::Error> {
        // let mut datalayout = Self::default();

        unimplemented!();
    }
}
