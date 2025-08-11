//! The Lizard method for encoding/decoding 16 bytes into Ristretto points.

#![allow(non_snake_case)]

#[cfg(curve25519_dalek_bits = "32")]
mod u32_constants;

#[cfg(curve25519_dalek_bits = "64")]
mod u64_constants;

pub mod jacobi_quartic;
pub mod lizard_constants;
pub mod lizard_ristretto;
