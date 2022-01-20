//! Functionality for mapping the `MODULE_BLOCK` block.

use llvm_constants::{IrBlockId, ModuleCode, TARGET_TRIPLE};
use thiserror::Error;

use crate::block::attributes::{AttributeGroups, Attributes};
use crate::block::type_table::TypeTable;
use crate::block::{BlockId, BlockMapError, IrBlock};
use crate::map::{CtxMappable, PartialCtxMappable, PartialMapCtx};
use crate::record::{Comdat, DataLayout, Function as FunctionRecord, RecordMapError};
use crate::unroll::{ByCode, UnrolledBlock};

/// Errors that can occur while mapping a module.
#[derive(Debug, Error)]
pub enum ModuleError {
    /// The `MODULE_CODE_VERSION` couldn't be found.
    #[error("bitcode module has no version")]
    MissingVersion,

    /// The module contains some unspecified invalid state.
    #[error("invalid module state: {0}")]
    Invalid(&'static str),
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
    const BLOCK_ID: IrBlockId = IrBlockId::Module;

    fn try_map_inner(
        block: &UnrolledBlock,
        ctx: &mut PartialMapCtx,
    ) -> Result<Self, BlockMapError> {
        // Mapping the module requires us to fill in the `PartialMapCtx` first,
        // so we can reify it into a `MapCtx` for subsequent steps.
        ctx.version = Some({
            let version = match block.records().exactly_one(ModuleCode::Version as u64) {
                ByCode::None | ByCode::TooMany => return Err(ModuleError::MissingVersion.into()),
                ByCode::One(record) => record,
            };

            *version.fields().get(0).ok_or(ModuleError::MissingVersion)?
        });

        // Each module *should* have a datalayout record, but doesn't necessarily.
        match block.records().exactly_one(ModuleCode::DataLayout as u64) {
            // ctx.datalayout is already default-constructed, so we don't need to redo it here.
            ByCode::None => (),
            ByCode::One(record) => {
                ctx.datalayout = DataLayout::try_map(record, ctx).map_err(RecordMapError::from)?
            }
            ByCode::TooMany => {
                return Err(ModuleError::Invalid("too many datalayout records").into())
            }
        }

        // Build the section table. We'll reference this later.
        let _section_table = block
            .records()
            .by_code(ModuleCode::SectionName as u64)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()
            .map_err(RecordMapError::from)?;

        // Build the GC table. We'll reference this later.
        let _gc_table = block
            .records()
            .by_code(ModuleCode::GcName as u64)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()
            .map_err(RecordMapError::from)?;

        // Build the type table.
        ctx.type_table = Some(TypeTable::try_map(
            block.one_block(BlockId::Ir(IrBlockId::Type))?,
            ctx,
        )?);

        // Collect all attribute groups and individual attribute references.
        // The order here is important: attribute groups must be mapped
        // and stored in the `PartialMapCtx` before the attribute block itself can be mapped.
        // Neither block is mandatory.
        ctx.attribute_groups = block
            .maybe_one_block(BlockId::Ir(IrBlockId::ParamAttrGroup))?
            .map(|b| AttributeGroups::try_map(b, ctx))
            .transpose()?;

        ctx.attributes = block
            .maybe_one_block(BlockId::Ir(IrBlockId::ParamAttr))?
            .map(|b| Attributes::try_map(b, ctx))
            .transpose()?;

        log::debug!("attributes: {:?}", ctx.attributes);

        // After this point, `ctx` refers to a fully reified `MapCtx`.
        let ctx = ctx.reify()?;

        // Each module *should* have a target triple, but doesn't necessarily.
        let triple = match block.records().exactly_one(ModuleCode::Triple as u64) {
            ByCode::None => TARGET_TRIPLE.into(),
            ByCode::One(record) => record.try_string(0).map_err(RecordMapError::from)?,
            ByCode::TooMany => {
                return Err(ModuleError::Invalid("too many target triple records").into())
            }
        };

        // Each module has zero or exactly one MODULE_CODE_ASM records.
        let asm = match block.records().exactly_one(ModuleCode::Asm as u64) {
            ByCode::None => Vec::new(),
            ByCode::One(record) => record
                .try_string(0)
                .map_err(RecordMapError::from)?
                .split('\n')
                .map(String::from)
                .collect::<Vec<_>>(),
            ByCode::TooMany => {
                return Err(ModuleError::Invalid("too many module inline assembly records").into())
            }
        };

        // Deplib records are deprecated, but we might be parsing an older bitstream.
        let deplibs = block
            .records()
            .by_code(ModuleCode::DepLib as u64)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()
            .map_err(RecordMapError::from)?;

        // Build the Comdat list. We'll reference this later.
        let _comdats = block
            .records()
            .by_code(ModuleCode::Comdat as u64)
            .map(|rec| Comdat::try_map(rec, &ctx))
            .collect::<Result<Vec<_>, _>>()
            .map_err(RecordMapError::from)?;

        // Collect the function records and blocks in this module.
        let functions = block
            .records()
            .by_code(ModuleCode::Function as u64)
            .map(|rec| FunctionRecord::try_map(rec, &ctx))
            .collect::<Result<Vec<_>, _>>()
            .map_err(RecordMapError::from)?;

        log::debug!("functions: {:?}", functions);

        Ok(Self {
            triple,
            asm,
            deplibs,
        })
    }
}
