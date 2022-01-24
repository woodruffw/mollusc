//! Functionality for mapping the `MODULE_BLOCK` block.

use llvm_constants::{IrBlockId, ModuleCode, TARGET_TRIPLE};
use thiserror::Error;

use crate::block::attributes::{AttributeError, AttributeGroups, Attributes};
use crate::block::type_table::{TypeTable, TypeTableError};
use crate::block::{BlockId, IrBlock};
use crate::map::{CtxMappable, MapError, PartialCtxMappable, PartialMapCtx};
use crate::record::{
    Comdat, ComdatError, DataLayout, DataLayoutError, Function as FunctionRecord,
    FunctionError as FunctionRecordError,
};
use crate::unroll::UnrolledBlock;

/// Errors that can occur while mapping a module.
#[derive(Debug, Error)]
pub enum ModuleError {
    /// The `MODULE_CODE_VERSION` couldn't be found.
    #[error("bitcode module has no version")]
    MissingVersion,

    /// An error occured while mapping the datalayout record.
    #[error("invalid datalayout record")]
    DataLayoutRecord(#[from] DataLayoutError),

    /// An error occurred while mapping the type table block.
    #[error("invalid type table block")]
    TypeTableBlock(#[from] TypeTableError),

    /// An error occurred while mapping one of the attribute blocks.
    #[error("invalid attribute block")]
    AttributeBlock(#[from] AttributeError),

    /// An error occurred while mapping a COMDAT record.
    #[error("invalid COMDAT record")]
    ComdatRecord(#[from] ComdatError),

    /// An error occurred while mapping a function record.
    #[error("invalid function record")]
    FunctionRecord(#[from] FunctionRecordError),

    /// A generic mapping error occurred.
    #[error("mapping error in string table")]
    Map(#[from] MapError),
}

/// Models the `MODULE_BLOCK` block.
#[non_exhaustive]
#[derive(Debug)]
pub struct Module {
    /// The target triple specification.
    pub triple: String,
    /// Any assembly block lines in the module.
    pub asm: Vec<String>,
    /// Any dependent libraries listed in the module.
    pub deplibs: Vec<String>,
}

impl IrBlock for Module {
    type Error = ModuleError;

    const BLOCK_ID: IrBlockId = IrBlockId::Module;

    fn try_map_inner(block: &UnrolledBlock, ctx: &mut PartialMapCtx) -> Result<Self, Self::Error> {
        // Mapping the module requires us to fill in the `PartialMapCtx` first,
        // so we can reify it into a `MapCtx` for subsequent steps.
        ctx.version = Some({
            let version = block
                .records()
                .exactly_one(ModuleCode::Version)
                .map_err(MapError::Inconsistent)?;

            *version.fields().get(0).ok_or(ModuleError::MissingVersion)?
        });

        // Each module *should* have a datalayout record, but doesn't necessarily.
        if let Some(record) = block
            .records()
            .one_or_none(ModuleCode::DataLayout)
            .map_err(MapError::Inconsistent)?
        {
            ctx.datalayout = DataLayout::try_map(record, ctx)?;
        }

        // Build the section table. We'll reference this later.
        ctx.section_table = block
            .records()
            .by_code(ModuleCode::SectionName)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()
            .map_err(MapError::RecordString)?;

        // Build the GC table. We'll reference this later.
        ctx.gc_table = block
            .records()
            .by_code(ModuleCode::GcName)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()
            .map_err(MapError::RecordString)?;

        // Build the type table.
        ctx.type_table = Some(TypeTable::try_map(
            block
                .blocks()
                .exactly_one(BlockId::Ir(IrBlockId::Type))
                .map_err(MapError::Inconsistent)?,
            ctx,
        )?);

        // Collect all attribute groups and individual attribute references.
        // The order here is important: attribute groups must be mapped
        // and stored in the `PartialMapCtx` before the attribute block itself can be mapped.
        // Neither block is mandatory.
        ctx.attribute_groups = block
            .blocks()
            .one_or_none(BlockId::Ir(IrBlockId::ParamAttrGroup))
            .map_err(MapError::Inconsistent)?
            .map(|b| AttributeGroups::try_map(b, ctx))
            .transpose()?;

        ctx.attributes = block
            .blocks()
            .one_or_none(BlockId::Ir(IrBlockId::ParamAttr))
            .map_err(MapError::Inconsistent)?
            .map(|b| Attributes::try_map(b, ctx))
            .transpose()?;

        // Build the list of COMDATs. We'll reference this later.
        ctx.comdats = block
            .records()
            .by_code(ModuleCode::Comdat)
            .map(|rec| Comdat::try_map(rec, ctx))
            .collect::<Result<Vec<_>, _>>()?;

        // After this point, `ctx` refers to a fully reified `MapCtx`.
        let ctx = ctx.reify().map_err(MapError::Context)?;

        // Each module *should* have a target triple, but doesn't necessarily.
        let triple = match block
            .records()
            .one_or_none(ModuleCode::Triple)
            .map_err(MapError::Inconsistent)?
        {
            Some(record) => record.try_string(0).map_err(MapError::RecordString)?,
            None => TARGET_TRIPLE.into(),
        };

        // Each module has zero or exactly one MODULE_CODE_ASM records.
        let asm = match block
            .records()
            .one_or_none(ModuleCode::Asm)
            .map_err(MapError::Inconsistent)?
        {
            None => Vec::new(),
            Some(record) => record
                .try_string(0)
                .map_err(MapError::RecordString)?
                .split('\n')
                .map(String::from)
                .collect::<Vec<_>>(),
        };

        // Deplib records are deprecated, but we might be parsing an older bitstream.
        let deplibs = block
            .records()
            .by_code(ModuleCode::DepLib)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()
            .map_err(MapError::RecordString)?;

        // Collect the function records and blocks in this module.
        let functions = block
            .records()
            .by_code(ModuleCode::Function)
            .map(|rec| FunctionRecord::try_map(rec, &ctx))
            .collect::<Result<Vec<_>, _>>()?;

        log::debug!("functions: {:?}", functions);

        Ok(Self {
            triple,
            asm,
            deplibs,
        })
    }
}
