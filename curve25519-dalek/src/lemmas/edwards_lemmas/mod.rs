//! Lemmas for Edwards curve operations
//!
//! This module contains proofs for operations on Ed25519 twisted Edwards curve points.
//!
//! ## Submodules
//!
//! - `constants_lemmas`: Lemmas about Edwards curve constants (EDWARDS_D, BASEPOINT_ORDER_PRIVATE)
//! - `curve_equation_lemmas`: Lemmas about the curve equation and scalar multiplication
//! - `mul_base_lemmas`: Specs and lemmas for mul_base (Pippenger scalar multiplication)
//! - `step1_lemmas`: Lemmas for step_1 of point decompression (curve equation, validity)
//! - `decompress_lemmas`: Lemmas for point decompression (sign bit, extended coords)
//!
pub mod constants_lemmas;
pub mod curve_equation_lemmas;
pub mod decompress_lemmas;
pub mod mul_base_lemmas;
pub mod step1_lemmas;
