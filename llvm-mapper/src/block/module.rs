//! Functionality for mapping the `MODULE_BLOCK` block.

use llvm_constants::{IrBlockId, ModuleCode, TARGET_TRIPLE};

use crate::block::attributes::{AttributeGroups, Attributes};
use crate::block::type_table::TypeTable;
use crate::block::{BlockId, BlockMapError, IrBlock};
use crate::map::{MapCtx, Mappable};
use crate::record::{Comdat, DataLayout};
use crate::unroll::UnrolledBlock;

/// Models the `MODULE_BLOCK` block.
#[non_exhaustive]
#[derive(Debug)]
pub struct Module {
    /// The format version.
    version: u64,
    /// The target triple specification.
    pub triple: String,
    /// The data layout specification.
    pub datalayout: DataLayout,
    /// Any assembly block lines in the module.
    pub asm: Vec<String>,
    /// Any dependent libraries listed in the module.
    pub deplibs: Vec<String>,
    /// The module's type table.
    pub type_table: TypeTable,
}

impl IrBlock for Module {
    const BLOCK_ID: IrBlockId = IrBlockId::Module;

    fn try_map_inner(block: &UnrolledBlock, ctx: &mut MapCtx) -> Result<Self, BlockMapError> {
        let version = {
            let version = block.one_record(ModuleCode::Version as u64)?;

            version.get_field(0)?
        };

        ctx.version = Some(version);

        // Each module *should* have a target triple, but doesn't necessarily.
        let triple = if let Some(record) = block.one_record_or_none(ModuleCode::Triple as u64)? {
            record.try_string(0)?
        } else {
            TARGET_TRIPLE.into()
        };

        // Each module *should* have a datalayout record, but doesn't necessarily.
        let datalayout =
            if let Some(record) = block.one_record_or_none(ModuleCode::DataLayout as u64)? {
                DataLayout::try_map(record, ctx)?
            } else {
                DataLayout::default()
            };

        // Each module has zero or exactly one MODULE_CODE_ASM records.
        let asm = match block.one_record_or_none(ModuleCode::Asm as u64)? {
            Some(rec) => rec
                .try_string(0)?
                .split('\n')
                .map(String::from)
                .collect::<Vec<_>>(),
            None => Vec::new(),
        };

        // Deplib records are deprecated, but we might be parsing an older bitstream.
        let deplibs = block
            .records(ModuleCode::DepLib as u64)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()?;

        // Build the section table. We'll reference this later.
        let _section_table = block
            .records(ModuleCode::SectionName as u64)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()?;

        // Build the GC table. We'll reference this later.
        let _gc_table = block
            .records(ModuleCode::GcName as u64)
            .map(|rec| rec.try_string(0))
            .collect::<Result<Vec<_>, _>>()?;

        // Build the Comdat list. We'll reference this later.
        let _comdats = block
            .records(ModuleCode::Comdat as u64)
            .map(|rec| Comdat::try_map(rec, ctx))
            .collect::<Result<Vec<_>, _>>()?;

        // Build the type table.
        let type_table = TypeTable::try_map(block.one_block(BlockId::Ir(IrBlockId::Type))?, ctx)?;

        // Collect all attribute groups and individual attribute references.
        // The order here is important: attribute groups must be mapped (into the `MapCtx`)
        // before the attribute block itself can be mapped.
        // Both of these mapping operations are side-effect only.
        AttributeGroups::try_map(
            block.one_block(BlockId::Ir(IrBlockId::ParamAttrGroup))?,
            ctx,
        )?;
        Attributes::try_map(block.one_block(BlockId::Ir(IrBlockId::ParamAttr))?, ctx)?;

        Ok(Self {
            version,
            triple,
            datalayout,
            asm,
            deplibs,
            type_table,
        })
    }
}
