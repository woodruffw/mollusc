//! Functionality for mapping the `MODULE_CODE_DATALAYOUT` record.

use std::convert::{TryFrom, TryInto};
use std::num::ParseIntError;
use std::str::FromStr;

use llvm_support::{
    AddressSpace, AddressSpaceError, Align, AlignError, AlignSpecError, Endian,
    FunctionPointerAlign, Mangling, PointerAlignSpec, PointerAlignSpecs, TypeAlignSpec,
    TypeAlignSpecs,
};
use thiserror::Error;

use crate::map::{PartialCtxMappable, PartialMapCtx};
use crate::record::RecordStringError;
use crate::unroll::Record;

/// Potential errors when parsing an LLVM datalayout string.
#[derive(Debug, Error)]
pub enum DataLayoutError {
    /// The datalayout string can't be extracted from the record.
    #[error("malformed datalayout record: {0}")]
    BadString(#[from] RecordStringError),
    /// The specified alignment is invalid.
    #[error("bad alignment value: {0}")]
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
    #[error("couldn't parse spec field: {0}")]
    BadInt(#[from] ParseIntError),
    /// We couldn't parse an individual spec, for some reason.
    #[error("couldn't parse spec: {0}")]
    BadSpecParse(String),
    /// We couldn't parse an alignment spec.
    #[error("cou't parse alignment spec: {0}")]
    BadAlignSpec(#[from] AlignSpecError),
}

/// Models the `MODULE_CODE_DATALAYOUT` record.
#[non_exhaustive]
#[derive(Debug)]
pub struct DataLayout {
    /// The endianness of the target.
    pub endianness: Endian,
    /// The target's natural stack alignment, if present.
    pub natural_stack_alignment: Option<Align>,
    /// The address space for program memory.
    pub program_address_space: AddressSpace,
    /// The address space for global variables.
    pub global_variable_address_space: AddressSpace,
    /// The address space for objects created by `alloca`.
    pub alloca_address_space: AddressSpace,
    /// Non-pointer type alignment specifications for the target.
    pub type_alignments: TypeAlignSpecs,
    /// Pointer alignment specifications for the target.
    pub pointer_alignments: PointerAlignSpecs,
    /// Aggregate alignment for the target.
    pub aggregate_alignment: Align,
    /// Function pointer alignment for the target, if present.
    pub function_pointer_alignment: Option<FunctionPointerAlign>,
    /// The target's symbol mangling discipline, if present.
    pub mangling: Option<Mangling>,
    /// A list of integer widths (in bits) that are efficiently supported by the target.
    pub native_integer_widths: Vec<u32>,
    /// A list of address spaces that use non-integral pointers.
    pub non_integral_address_spaces: Vec<AddressSpace>,
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
    type Err = DataLayoutError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if !value.is_ascii() {
            return Err(DataLayoutError::BadEncoding);
        }

        let mut datalayout = Self::default();
        for spec in value.split('-') {
            if spec.is_empty() {
                return Err(DataLayoutError::EmptySpec);
            }

            let body = &spec[1..];

            // Unwrap safety: we check for a nonempty spec above.
            #[allow(clippy::unwrap_used)]
            match spec.chars().next().unwrap() {
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
                    // Pass the entire spec in here, since we need the spec identifier as well.
                    let align_spec = spec.parse::<PointerAlignSpec>()?;
                    datalayout.pointer_alignments.update(align_spec);
                }
                'i' | 'v' | 'f' | 'a' => {
                    // Pass the entire spec in here, since we need the spec identifier as well.
                    let align_spec = spec.parse::<TypeAlignSpec>()?;
                    datalayout.type_alignments.update(align_spec);
                }
                'F' => match body.chars().next() {
                    Some(id) => {
                        let align = Align::from_bit_align(body[1..].parse::<u64>()?)?;
                        let align = match id {
                            'i' => FunctionPointerAlign::Independent {
                                abi_alignment: align,
                            },
                            'n' => FunctionPointerAlign::MultipleOfFunctionAlign {
                                abi_alignment: align,
                            },
                            o => {
                                return Err(DataLayoutError::BadSpecParse(format!(
                                    "unknown function pointer alignment specifier: {}",
                                    o
                                )))
                            }
                        };
                        datalayout.function_pointer_alignment = Some(align);
                    }
                    None => {
                        return Err(DataLayoutError::BadSpecParse(
                            "function pointer alignment spec is empty".into(),
                        ))
                    }
                },
                'm' => {
                    // The mangling spec is `m:X`, where `X` is the mangling kind.
                    // We've already parsed `m`, so we expect exactly two characters.
                    let mut mangling = body.chars().take(2);
                    match mangling.next() {
                        Some(':') => {}
                        Some(u) => {
                            return Err(DataLayoutError::BadSpecParse(format!(
                                "bad separator for mangling spec: {}",
                                u
                            )))
                        }
                        None => {
                            return Err(DataLayoutError::BadSpecParse(
                                "mangling spec is empty".into(),
                            ))
                        }
                    }

                    // TODO(ww): This could be FromStr on Mangling.
                    let kind = match mangling.next() {
                        None => {
                            return Err(DataLayoutError::BadSpecParse(
                                "mangling spec has no mangling kind".into(),
                            ))
                        }
                        Some('e') => Mangling::Elf,
                        Some('m') => Mangling::Mips,
                        Some('o') => Mangling::Macho,
                        Some('x') => Mangling::WindowsX86Coff,
                        Some('w') => Mangling::WindowsCoff,
                        Some('a') => Mangling::XCoff,
                        Some(u) => {
                            return Err(DataLayoutError::BadSpecParse(format!(
                                "unknown mangling kind in spec: {}",
                                u
                            )))
                        }
                    };

                    datalayout.mangling = Some(kind);
                }
                'n' => {
                    // 'n' marks the start of either an 'n' or an 'ni' block.
                    match body.chars().next() {
                        Some('i') => {
                            datalayout.non_integral_address_spaces = body[1..]
                                .split(':')
                                .filter(|s| s.len() > 0)
                                .map(|s| {
                                    s.parse::<u32>()
                                        .map_err(DataLayoutError::from)
                                        .and_then(|a| AddressSpace::try_from(a).map_err(Into::into))
                                        .and_then(|a| {
                                            if a == AddressSpace::default() {
                                                Err(DataLayoutError::BadSpecParse(
                                                    "address space 0 cannot be non-integral".into(),
                                                ))
                                            } else {
                                                Ok(a)
                                            }
                                        })
                                })
                                .collect::<Result<_, _>>()?
                        }
                        Some(_) => {
                            datalayout.native_integer_widths = body
                                .split(':')
                                .map(|s| s.parse::<u32>())
                                .collect::<Result<_, _>>()?;
                        }
                        None => {
                            return Err(DataLayoutError::BadSpecParse(
                                "integer width spec is empty".into(),
                            ))
                        }
                    }
                }
                u => return Err(DataLayoutError::UnknownSpec(u)),
            }
        }

        Ok(datalayout)
    }
}

impl PartialCtxMappable<Record> for DataLayout {
    type Error = DataLayoutError;

    fn try_map(record: &Record, _ctx: &mut PartialMapCtx) -> Result<Self, Self::Error> {
        let datalayout = record.try_string(0)?;
        datalayout.parse::<Self>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_datalayout_has_defaults() {
        let dl = DataLayout::default();

        assert_eq!(dl.type_alignments, TypeAlignSpecs::default());
        assert_eq!(dl.pointer_alignments, PointerAlignSpecs::default());
    }

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

            assert_eq!(
                "z".parse::<DataLayout>().unwrap_err().to_string(),
                "unknown datalayout specification: z"
            );
        }

        {
            let dl = "E-S64".parse::<DataLayout>().unwrap();

            assert_eq!(dl.endianness, Endian::Big);
            assert_eq!(dl.natural_stack_alignment.unwrap().byte_align(), 8);
            assert!(dl.mangling.is_none());
        }

        {
            let dl = "e-S32".parse::<DataLayout>().unwrap();

            assert_eq!(dl.endianness, Endian::Little);
            assert_eq!(dl.natural_stack_alignment.unwrap().byte_align(), 4);
        }

        {
            let dl = "m:e".parse::<DataLayout>().unwrap();

            assert_eq!(dl.mangling, Some(Mangling::Elf));
        }

        {
            assert_eq!(
                "m".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec: mangling spec is empty"
            );

            assert_eq!(
                "m:".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec: mangling spec has no mangling kind"
            );

            assert_eq!(
                "m:?".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec: unknown mangling kind in spec: ?"
            );
        }

        {
            let dl = "Fi64".parse::<DataLayout>().unwrap();

            assert_eq!(
                dl.function_pointer_alignment,
                Some(FunctionPointerAlign::Independent {
                    abi_alignment: Align::ALIGN64
                })
            );
        }

        {
            let dl = "Fn8".parse::<DataLayout>().unwrap();

            assert_eq!(
                dl.function_pointer_alignment,
                Some(FunctionPointerAlign::MultipleOfFunctionAlign {
                    abi_alignment: Align::ALIGN8
                })
            );
        }

        {
            assert_eq!(
                "F".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec: function pointer alignment spec is empty"
            );

            assert_eq!(
                "Fn".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec field: cannot parse integer from empty string"
            );

            assert_eq!(
                "Fn123".parse::<DataLayout>().unwrap_err().to_string(),
                "bad alignment value: supplied value is not a multiple of 8: 123"
            );

            assert_eq!(
                "F?64".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec: unknown function pointer alignment specifier: ?"
            );
        }

        {
            let dl = "n8:16:32:64".parse::<DataLayout>().unwrap();

            assert_eq!(dl.native_integer_widths, vec![8, 16, 32, 64]);
        }

        {
            let dl = "n64".parse::<DataLayout>().unwrap();

            assert_eq!(dl.native_integer_widths, vec![64]);
        }

        {
            assert_eq!(
                "n".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec: integer width spec is empty"
            );

            assert_eq!(
                "nx".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec field: invalid digit found in string"
            );

            assert_eq!(
                "n:".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec field: cannot parse integer from empty string"
            );

            assert_eq!(
                "n8:".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec field: cannot parse integer from empty string"
            );
        }

        {
            let dl = "ni1:2:3".parse::<DataLayout>().unwrap();

            assert_eq!(
                dl.non_integral_address_spaces,
                vec![
                    AddressSpace::try_from(1_u32).unwrap(),
                    AddressSpace::try_from(2_u32).unwrap(),
                    AddressSpace::try_from(3_u32).unwrap()
                ]
            );
        }

        {
            let dl = "ni1".parse::<DataLayout>().unwrap();

            assert_eq!(
                dl.non_integral_address_spaces,
                vec![AddressSpace::try_from(1_u32).unwrap(),]
            );
        }

        {
            assert_eq!(
                "ni".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec field: cannot parse integer from empty string"
            );

            assert_eq!(
                "ni0".parse::<DataLayout>().unwrap_err().to_string(),
                "couldn't parse spec: address space 0 cannot be non-integral"
            );
        }
    }
}
