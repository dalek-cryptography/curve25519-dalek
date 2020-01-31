//! The Lizard method for encoding/decoding 16 bytes into Ristretto points.

#![allow(non_snake_case)]

#[cfg(feature = "u32_backend")]
mod u32_constants;

#[cfg(feature = "u64_backend")]
mod u64_constants;

pub mod lizard_constants;
pub mod jacobi_quartic;
pub mod lizard_ristretto;
