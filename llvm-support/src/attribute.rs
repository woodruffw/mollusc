//! Support code for LLVM attributes.

use num_enum::TryFromPrimitive;

/// Represents the different kinds of attributes.
#[derive(Debug, PartialEq, Eq, TryFromPrimitive)]
#[repr(u64)]
pub enum AttributeKind {
    /// A well-known enum attribute.
    Enum = 0,
    /// A well-known integral attribute with an integer value.
    IntKeyValue = 1,
    /// A string attribute.
    StrKey = 3,
    /// A string attribute with a string value.
    StrKeyValue = 4,
    // TODO(ww): 5 and 6 are attribute kinds in the LLVM codebase, but aren't documented.
}

/// Represents the IDs of different specific attributes.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, PartialEq, Eq, TryFromPrimitive)]
#[repr(u64)]
pub enum AttributeId {
    /// `align(<n>)`
    Alignment = 1,
    /// `alwaysinline`
    AlwaysInline = 2,
    /// `byval`
    ByVal = 3,
    /// `inlinehint`
    InlineHint = 4,
    /// `inreg`
    InReg = 5,
    /// `minsize`
    MinSize = 6,
    /// `naked`
    Naked = 7,
    /// `nest`
    Nest = 8,
    /// `noalias`
    NoAlias = 9,
    /// `nobuiltin`
    NoBuiltin = 10,
    /// `nocapture`
    NoCapture = 11,
    /// `noduplicate`
    NoDuplicate = 12,
    /// `noimplicitfloat`
    NoImplicitFloat = 13,
    /// `noinline`
    NoInline = 14,
    /// `nonlazybind`
    NonLazyBind = 15,
    /// `noredzone`
    NoRedZone = 16,
    /// `noreturn`
    NoReturn = 17,
    /// `nounwind`
    NoUnwind = 18,
    /// `optsize`
    OptimizeForSize = 19,
    /// `readnone`
    ReadNone = 20,
    /// `readonly`
    ReadOnly = 21,
    /// `returned`
    Returned = 22,
    /// `returns_twice`
    ReturnsTwice = 23,
    /// `signext`
    SExt = 24,
    /// `alignstack(<n>)`
    StackAlignment = 25,
    /// `ssp`
    StackProtect = 26,
    /// `sspreq`
    StackProtectReq = 27,
    /// `sspstrong`
    StackProtectStrong = 28,
    /// `sret`
    StructRet = 29,
    /// `sanitize_address`
    SanitizeAddress = 30,
    /// `sanitize_thread`
    SanitizeThread = 31,
    /// `sanitize_memory`
    SanitizeMemory = 32,
    /// `uwtable` ([variant])
    UwTable = 33,
    /// `zeroext`
    ZExt = 34,
    /// `builtin`
    Builtin = 35,
    /// `cold`
    Cold = 36,
    /// `optnone`
    OptimizeNone = 37,
    /// `inalloca`
    InAlloca = 38,
    /// `nonnull`
    NonNull = 39,
    /// `jumptable`
    JumpTable = 40,
    /// `dereferenceable(<n>)`
    Dereferenceable = 41,
    /// `dereferenceable_or_null(<n>)`
    DereferenceableOrNull = 42,
    /// `convergent`
    Convergent = 43,
    /// `safestack`
    SafeStack = 44,
    /// `argmemonly`
    ArgMemOnly = 45,
    /// `swiftself`
    SwiftSelf = 46,
    /// `swifterror`
    SwiftError = 47,
    /// `norecurse`
    NoRecurse = 48,
    /// `inaccessiblememonly`
    InaccessiblememOnly = 49,
    /// `inaccessiblememonly_or_argmemonly`
    InaccessiblememOrArgmemonly = 50,
    /// `allocsize(<EltSizeParam>[, <NumEltsParam>])`
    AllocSize = 51,
    /// `writeonly`
    WriteOnly = 52,
    /// `speculatable`
    Speculatable = 53,
    /// `strictfp`
    StrictFp = 54,
    /// `sanitize_hwaddress`
    SanitizeHwAddress = 55,
    /// `nocf_check`
    NoCfCheck = 56,
    /// `optforfuzzing`
    OptForFuzzing = 57,
    /// `shadowcallstack`
    Shadowcallstack = 58,
    /// `speculative_load_hardening`
    SpeculativeLoadHardening = 59,
    /// `immarg`
    ImmArg = 60,
    /// `willreturn`
    WillReturn = 61,
    /// `nofree`
    NoFree = 62,
    /// `nosync`
    NoSync = 63,
    /// `sanitize_memtag`
    SanitizeMemtag = 64,
    /// `preallocated`
    Preallocated = 65,
    /// `no_merge`
    NoMerge = 66,
    /// `null_pointer_is_valid`
    NullPointerIsValid = 67,
    /// `noundef`
    NoUndef = 68,
    /// `byref`
    ByRef = 69,
    /// `mustprogress`
    MustProgress = 70,
    /// `no_callback`
    NoCallback = 71,
    /// `hot`
    Hot = 72,
    /// `no_profile`
    NoProfile = 73,
    /// `vscale_range(<Min>[, <Max>])`
    VScaleRange = 74,
    /// `swift_async`
    SwiftAsync = 75,
    /// `nosanitize_coverage`
    NoSanitizeCoverage = 76,
    /// `elementtype`
    ElementType = 77,
    /// `disable_sanitizer_instrumentation`
    DisableSanitizerInstrumentation = 78,
    /// `nosanitize_bounds`
    NoSanitizeBounds = 79,
    /// `allocalign`
    AllocAlign = 80,
    /// `allocptr`
    AllocatedPointer = 81,
    /// `allockind (<KindBitset>)`
    AllocKind = 82,
    /// `presplitcoroutine`
    PresplitCoroutine = 83,
    /// `fn_ret_thunk_extern`
    FnretthunkExtern = 84,
    /// `skipprofile`
    SkipProfile = 85,
    /// `memory (<LayoutBitset>)`
    Memory = 86,
}
