//! Lemmas about Edwards curve constants (EDWARDS_D)
//!
//! This module contains proofs about the properties of Edwards curve constants.
//! These are the curve parameters used in the twisted Edwards curve equation.
//!
//! ## Mathematical Background
//!
//! EDWARDS_D is the curve parameter `d` in the twisted Edwards curve equation:
//! ```text
//! -x² + y² = 1 + d·x²·y²
//! ```
//!
//! The constant is represented in 51-bit limb form:
//! ```text
//! d = limbs[0] + 2^51·limbs[1] + 2^102·limbs[2] + 2^153·limbs[3] + 2^204·limbs[4]
//! ```
//!
//! ## Note
//!
//! - EDWARDS_D2 (= 2·d) lemmas are in `unused_constants_lemmas.rs` (currently unused).
#![allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// EDWARDS_D Lemmas
// =============================================================================
/// EDWARDS_D has 51-bit bounded limbs
///
/// ## Mathematical Proof
/// Each limb of EDWARDS_D is a specific constant < 2^51:
/// - limbs[0] = 929955233495203 < 2^51 ✓
/// - limbs[1] = 466365720129213 < 2^51 ✓
/// - limbs[2] = 1662059464998953 < 2^51 ✓
/// - limbs[3] = 2033849074728123 < 2^51 ✓
/// - limbs[4] = 1442794654840575 < 2^51 ✓
pub(crate) proof fn lemma_edwards_d_limbs_bounded()
    ensures
        fe51_limbs_bounded(&EDWARDS_D, 51),
{
    // Goal: All EDWARDS_D limbs < 2^51
    assert(fe51_limbs_bounded(&EDWARDS_D, 51)) by {
        assert(929955233495203u64 < (1u64 << 51)) by (bit_vector);
        assert(466365720129213u64 < (1u64 << 51)) by (bit_vector);
        assert(1662059464998953u64 < (1u64 << 51)) by (bit_vector);
        assert(2033849074728123u64 < (1u64 << 51)) by (bit_vector);
        assert(1442794654840575u64 < (1u64 << 51)) by (bit_vector);
    };
}

/// EDWARDS_D has 54-bit bounded limbs
///
/// ## Mathematical Proof
/// 51-bit bounded ⟹ 54-bit bounded since 2^51 < 2^54
pub(crate) proof fn lemma_edwards_d_limbs_bounded_54()
    ensures
        fe51_limbs_bounded(&EDWARDS_D, 54),
{
    // Goal: All EDWARDS_D limbs < 2^54
    assert(fe51_limbs_bounded(&EDWARDS_D, 54)) by {
        lemma_edwards_d_limbs_bounded();
        assert((1u64 << 51) < (1u64 << 54)) by (bit_vector);
    };
}

} // verus!
