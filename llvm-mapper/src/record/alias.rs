//! Functionality for mapping the `MODULE_CODE_ALIAS` record.

use std::convert::TryFrom;

use llvm_support::{
    DllStorageClass, Linkage, RuntimePreemption, ThreadLocalMode, Type, UnnamedAddr, Visibility,
};
use num_enum::TryFromPrimitiveError;
use thiserror::Error;

use crate::map::{CtxMappable, MapCtx};
use crate::record::StrtabError;
use crate::unroll::Record;

/// Errors that can occur while mapping an alias record.
#[derive(Debug, Error)]
pub enum AliasError {
    /// The alias record is too short to be well-formed.
    #[error("alias record too short: {0} < 5 fields")]
    TooShort(usize),

    /// The alias record is in an old unsupported format.
    #[error("unsupported alias record format (v1)")]
    V1Unsupported,

    /// Retrieving a string from a string table failed.
    #[error("error while accessing string table")]
    Strtab(#[from] StrtabError),

    /// The alias has a bad or unknown type.
    #[error("invalid type table index: {0}")]
    Type(u64),

    /// The alias has an invalid visibility.
    #[error("invalid visibility")]
    Visibility(#[from] TryFromPrimitiveError<Visibility>),

    /// The alias has an invalid DLL storage class.
    #[error("invalid storage class")]
    DllStorageClass(#[from] TryFromPrimitiveError<DllStorageClass>),
}

/// Models the `MODULE_CODE_ALIAS` record.
#[derive(Debug)]
pub struct Alias<'ctx> {
    /// The alias's name.
    pub name: &'ctx str,

    /// The alias's type.
    pub ty: &'ctx Type,

    /// The aliasee value index.
    pub value_index: u64,

    /// The alias's linkage.
    pub linkage: Linkage,

    /// The alias's visibility.
    pub visibility: Visibility,

    /// The alias's storage class.
    pub storage_class: DllStorageClass,

    /// The alias's thread local storage mode.
    pub tls_mode: ThreadLocalMode,

    /// The alias's `unnamed_addr` specifier.
    pub unnamed_addr: UnnamedAddr,

    /// The alias's preemption specifier.
    pub preemption_specifier: RuntimePreemption,
}

impl<'ctx> CtxMappable<'ctx, Record> for Alias<'ctx> {
    type Error = AliasError;

    fn try_map(record: &Record, ctx: &'ctx MapCtx) -> Result<Self, Self::Error> {
        let fields = record.fields();

        if !ctx.use_strtab() {
            return Err(AliasError::V1Unsupported);
        }

        // Every alias record has at least 5 fields, corresponding to
        // [strtab_offset, strtab_size, *v1], where v1 has 3 mandatory fields:
        // [alias type, aliasee value#, linkage, ...]
        if fields.len() < 5 {
            return Err(AliasError::TooShort(fields.len()));
        }

        let name = ctx.strtab.read_name(record)?;
        let ty = ctx
            .type_table
            .get(fields[2])
            .ok_or(AliasError::Type(fields[2]))?;
        let value_index = fields[3];
        let linkage = Linkage::from(fields[4]);

        let visibility = fields
            .get(5)
            .map_or_else(|| Ok(Visibility::Default), |v| Visibility::try_from(*v))?;

        let storage_class = fields.get(6).map_or_else(
            || Ok(DllStorageClass::Default),
            |v| DllStorageClass::try_from(*v),
        )?;

        let tls_mode = fields
            .get(7)
            .copied()
            .map(ThreadLocalMode::from)
            .unwrap_or(ThreadLocalMode::NotThreadLocal);

        let unnamed_addr = fields
            .get(8)
            .copied()
            .map(UnnamedAddr::from)
            .unwrap_or(UnnamedAddr::None);

        let preemption_specifier = fields
            .get(9)
            .copied()
            .map(RuntimePreemption::from)
            .unwrap_or(RuntimePreemption::DsoPreemptable);

        Ok(Alias {
            name,
            ty,
            value_index,
            linkage,
            visibility,
            storage_class,
            tls_mode,
            unnamed_addr,
            preemption_specifier,
        })
    }
}
