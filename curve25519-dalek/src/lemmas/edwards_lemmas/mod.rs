//! Lemmas for Edwards curve operations
//!
//! This module contains proofs for operations on Ed25519 twisted Edwards curve points.
//!
//! ## Submodules
//!
//! - `constants_lemmas`: Lemmas about Edwards curve constants (EDWARDS_D)
//! - `curve_equation_lemmas`: General lemmas about the curve equation (negation, extended coords)
//! - `step1_lemmas`: Lemmas for step_1 of point decompression (curve equation, validity)
//! - `decompress_lemmas`: Lemmas for point decompression (sign bit, extended coords)
//!
pub mod constants_lemmas;
pub mod curve_equation_lemmas;
pub mod decompress_lemmas;
pub mod step1_lemmas;
