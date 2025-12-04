//! The Lizard method for encoding/decoding 16 bytes into Ristretto points.

#[cfg(curve25519_dalek_bits = "32")]
mod u32_constants;

#[cfg(curve25519_dalek_bits = "64")]
mod u64_constants;

mod jacobi_quartic;
mod lizard_constants;
mod lizard_ristretto;
