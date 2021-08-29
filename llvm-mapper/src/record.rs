//! Structures for mapping from bitstream records to LLVM models.

use std::convert::TryInto;
use std::num::ParseIntError;
use std::str::FromStr;

use llvm_support::{
    AddressSpace, AddressSpaceError, Align, AlignError, Endian, Mangling, PointerAlignSpecs,
    TypeAlignSpecs,
};
use thiserror::Error;

/// Potential errors when parsing an LLVM datalayout string.
#[derive(Debug, Error)]
pub enum DataLayoutParseError {
    /// The specified alignment is invalid.
    #[error("bad alignment value")]
    BadAlign(#[from] AlignError),
    /// The specified address space is invalid.
    #[error("bad address space")]
    BadAddressSpace(#[from] AddressSpaceError),
    /// An unknown specification was encountered.
    #[error("unknown datalayout specification: {0}")]
    UnknownSpec(char),
    /// An empty specification was encountered.
    #[error("empty specification in datalayout")]
    EmptySpec,
    /// The datalayout string isn't in ASCII.
    #[error("non-ASCII characters in datalayout string")]
    BadEncoding,
    /// We couldn't parse a field as an integer.
    #[error("couldn't parse spec field")]
    BadInt(#[from] ParseIntError),
}

/// Models the `MODULE_CODE_DATALAYOUT` record.
#[derive(Debug)]
pub struct DataLayout {
    endianness: Endian,
    natural_stack_alignment: Option<Align>,
    program_address_space: AddressSpace,
    global_variable_address_space: AddressSpace,
    alloca_address_space: AddressSpace,
    type_alignments: TypeAlignSpecs,
    pointer_alignments: PointerAlignSpecs,
    aggregate_alignment: Align,
    function_pointer_alignment: Option<Align>,
    mangling: Option<Mangling>,
    native_integer_widths: Vec<u32>,
    non_integral_address_spaces: Vec<u32>,
}

impl Default for DataLayout {
    fn default() -> Self {
        Self {
            endianness: Endian::Big,
            natural_stack_alignment: None,
            program_address_space: Default::default(),
            global_variable_address_space: Default::default(),
            alloca_address_space: Default::default(),
            type_alignments: TypeAlignSpecs::default(),
            pointer_alignments: PointerAlignSpecs::default(),
            aggregate_alignment: Align::ALIGN8,
            function_pointer_alignment: None,
            mangling: None,
            native_integer_widths: vec![],
            non_integral_address_spaces: vec![],
        }
    }
}

impl FromStr for DataLayout {
    type Err = DataLayoutParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if !value.is_ascii() {
            return Err(DataLayoutParseError::BadEncoding);
        }

        let mut datalayout = Self::default();
        for spec in value.split('-') {
            if spec.is_empty() {
                return Err(DataLayoutParseError::EmptySpec);
            }

            let body = &spec[1..];

            // Unwrap safety: we check for a nonempty spec above.
            #[allow(clippy::unwrap_used)]
            match spec.chars().nth(0).unwrap() {
                'e' => datalayout.endianness = Endian::Little,
                'E' => datalayout.endianness = Endian::Big,
                'S' => {
                    datalayout.natural_stack_alignment =
                        Some(Align::from_bit_align(body.parse::<u64>()?)?);
                }
                'P' => {
                    datalayout.program_address_space = body.parse::<u32>()?.try_into()?;
                }
                'G' => {
                    datalayout.global_variable_address_space = body.parse::<u32>()?.try_into()?;
                }
                'A' => {
                    datalayout.alloca_address_space = body.parse::<u32>()?.try_into()?;
                }
                'p' => {
                    unimplemented!();
                }
                'i' => {
                    unimplemented!();
                }
                'v' => {
                    unimplemented!();
                }
                'f' => {
                    unimplemented!();
                }
                'a' => {
                    unimplemented!();
                }
                'F' => {
                    unimplemented!();
                }
                'm' => {
                    unimplemented!();
                }
                'n' => {
                    unimplemented!();
                    // TODO: 'ni'
                }
                u => return Err(DataLayoutParseError::UnknownSpec(u)),
            }
        }

        Ok(datalayout)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_datalayout_parses() {
        {
            assert_eq!(
                "not ascii ¬∫˙˚√∂∆˙√ß"
                    .parse::<DataLayout>()
                    .unwrap_err()
                    .to_string(),
                "non-ASCII characters in datalayout string"
            );
        }

        {
            assert_eq!(
                "z".parse::<DataLayout>().unwrap_err().to_string(),
                "unknown datalayout specification: z"
            );
        }

        {
            let dl = "E-S64".parse::<DataLayout>().unwrap();

            assert_eq!(dl.endianness, Endian::Big);
            assert_eq!(dl.natural_stack_alignment.unwrap().byte_align(), 8);
        }

        {
            let dl = "e-S32".parse::<DataLayout>().unwrap();

            assert_eq!(dl.endianness, Endian::Little);
            assert_eq!(dl.natural_stack_alignment.unwrap().byte_align(), 4);
        }
    }
}
