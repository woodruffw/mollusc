//! Traits for mapping bitstream types to models.

use crate::error::Error;

/// A trait for mapping some raw `T` into a model type.
pub(crate) trait Mappable<T>: Sized {
    /// Attempt to map `T` into `Self`.
    fn try_map(raw: T) -> Result<Self, Error>;
}
