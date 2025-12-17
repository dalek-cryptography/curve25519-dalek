//! Lemmas about the ONE field element constant
//!
//! This module contains fully proved lemmas about the FieldElement::ONE constant.
//!
//! ## Mathematical Background
//!
//! Field elements in the 51-bit limb representation have the form:
//! ```text
//! value = limbs[0] + 2^51·limbs[1] + 2^102·limbs[2] + 2^153·limbs[3] + 2^204·limbs[4]
//! ```
//!
//! ONE = [1, 0, 0, 0, 0] represents 1:
//! - `u64_5_as_nat([1, 0, 0, 0, 0]) = 1 + 0 + 0 + 0 + 0 = 1` (since n·0 = 0)
//! - `spec_field_element(ONE) = 1 % p = 1` (since p > 2 > 1)
//!
//! ## Note
//!
//! - Edwards curve-specific constants (EDWARDS_D, EDWARDS_D2) are in `edwards_lemmas::constants_lemmas`.
//! - ZERO constant lemmas are in `unused_constants_lemmas.rs` (currently unused).
#![allow(unused_imports)]
use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// FieldElement::ONE Lemmas
// =============================================================================
/// ONE = [1, 0, 0, 0, 0] has 51-bit bounded limbs
///
/// ## Mathematical Proof
/// Each limb must be < 2^51:
/// - limbs[0] = 1 < 2^51 ✓
/// - limbs[1..4] = 0 < 2^51 ✓
pub proof fn lemma_one_limbs_bounded_51()
    ensures
        fe51_limbs_bounded(&FieldElement51::ONE, 51),
{
    assert(fe51_limbs_bounded(&FieldElement51::ONE, 51)) by {
        assert(0u64 < (1u64 << 51) && 1u64 < (1u64 << 51)) by (bit_vector);
    };
}

/// spec_field_element(ONE) = 1  ✅ FULLY PROVED
///
/// ## Mathematical Proof
/// ```text
/// u64_5_as_nat([1, 0, 0, 0, 0])
///   = 1 + 2^51·0 + 2^102·0 + 2^153·0 + 2^204·0
///   = 1 + 0 + 0 + 0 + 0        (since n·0 = 0 for all n)
///   = 1
///
/// spec_field_element(ONE) = 1 % p = 1  (since p > 2 > 1, by lemma_small_mod)
/// ```
pub proof fn lemma_one_field_element_value()
    ensures
        spec_field_element(&FieldElement51::ONE) == 1,
{
    // Goal: spec_field_element(ONE) = u64_5_as_nat(ONE.limbs) % p = 1
    //
    // Mathematical reasoning:
    //   ONE.limbs = [1, 0, 0, 0, 0]
    //   u64_5_as_nat([1, 0, 0, 0, 0])
    //     = 1 + 2^51·0 + 2^102·0 + 2^153·0 + 2^204·0
    //     = 1    (since n·0 = 0 for all n)
    //   1 % p = 1    (since p > 2 > 1, by lemma_small_mod)
    assert(spec_field_element(&FieldElement51::ONE) == 1) by {
        // Subgoal 1: ONE.limbs = [1, 0, 0, 0, 0]
        assert(FieldElement51::ONE.limbs[0] == 1);
        assert(FieldElement51::ONE.limbs[1] == 0);
        assert(FieldElement51::ONE.limbs[2] == 0);
        assert(FieldElement51::ONE.limbs[3] == 0);
        assert(FieldElement51::ONE.limbs[4] == 0);

        // Subgoal 2: u64_5_as_nat([1, 0, 0, 0, 0]) = 1
        // SMT recognizes: 1 + pow2(51)*0 + pow2(102)*0 + pow2(153)*0 + pow2(204)*0 = 1
        assert(u64_5_as_nat(FieldElement51::ONE.limbs) == 1);

        // Subgoal 3: 1 % p = 1
        p_gt_2();  // proves p > 2, hence p > 1
        lemma_small_mod(1, p());  // x < m ==> x % m = x
    };
}

} // verus!
