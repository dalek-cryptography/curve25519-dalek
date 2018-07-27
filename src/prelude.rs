//! Crate-local prelude (for alloc-dependent features like `Vec`)

// TODO: switch to alloc::prelude
#[cfg(all(feature = "alloc", not(feature = "std")))]
pub use alloc::vec::Vec;

#[cfg(feature = "std")]
pub use std::vec::Vec;
