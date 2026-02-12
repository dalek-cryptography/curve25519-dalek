//! Lemmas about field element constants (ZERO, ONE, and selected curve constants)
//!
//! This module contains fully proved lemmas about FieldElement::ZERO and FieldElement::ONE constants.
//!
//! ## Mathematical Background
//!
//! Field elements in the 51-bit limb representation have the form:
//! ```text
//! value = limbs[0] + 2^51·limbs[1] + 2^102·limbs[2] + 2^153·limbs[3] + 2^204·limbs[4]
//! ```
//!
//! ZERO = [0, 0, 0, 0, 0] represents 0:
//! - `u64_5_as_nat([0, 0, 0, 0, 0]) = 0` (all terms are 0)
//! - `fe51_as_canonical_nat(ZERO) = 0 % p = 0`
//!
//! ONE = [1, 0, 0, 0, 0] represents 1:
//! - `u64_5_as_nat([1, 0, 0, 0, 0]) = 1 + 0 + 0 + 0 + 0 = 1` (since n·0 = 0)
//! - `fe51_as_canonical_nat(ONE) = 1 % p = 1` (since p > 2 > 1)
//!
//! ## Note
//!
//! - Edwards curve-specific constants (EDWARDS_D, EDWARDS_D2) are in `edwards_lemmas::constants_lemmas`.
#![allow(unused_imports)]
use crate::backend::serial::u64::constants::{MONTGOMERY_A, MONTGOMERY_A_NEG};
use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// FieldElement::ZERO Lemmas
// =============================================================================
/// ZERO = [0, 0, 0, 0, 0] has 51-bit bounded limbs
pub proof fn lemma_zero_limbs_bounded_51()
    ensures
        fe51_limbs_bounded(&FieldElement51::ZERO, 51),
{
    assert(fe51_limbs_bounded(&FieldElement51::ZERO, 51)) by {
        assert(0u64 < (1u64 << 51)) by (bit_vector);
    };
}

/// fe51_as_canonical_nat(ZERO) = 0  ✅ FULLY PROVED
///
/// ## Mathematical Proof
/// ```text
/// u64_5_as_nat([0, 0, 0, 0, 0])
///   = 0 + 2^51·0 + 2^102·0 + 2^153·0 + 2^204·0
///   = 0
///
/// fe51_as_canonical_nat(ZERO) = 0 % p = 0  (since 0 < p)
/// ```
pub proof fn lemma_zero_field_element_value()
    ensures
        fe51_as_canonical_nat(&FieldElement51::ZERO) == 0,
{
    assert(fe51_as_canonical_nat(&FieldElement51::ZERO) == 0) by {
        // Subgoal 1: ZERO.limbs = [0, 0, 0, 0, 0]
        assert(FieldElement51::ZERO.limbs[0] == 0);
        assert(FieldElement51::ZERO.limbs[1] == 0);
        assert(FieldElement51::ZERO.limbs[2] == 0);
        assert(FieldElement51::ZERO.limbs[3] == 0);
        assert(FieldElement51::ZERO.limbs[4] == 0);

        // Subgoal 2: u64_5_as_nat([0, 0, 0, 0, 0]) = 0
        assert(u64_5_as_nat(FieldElement51::ZERO.limbs) == 0);

        // Subgoal 3: 0 % p = 0
        p_gt_2();
        lemma_small_mod(0nat, p());
    };
}

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

/// fe51_as_canonical_nat(ONE) = 1  ✅ FULLY PROVED
///
/// ## Mathematical Proof
/// ```text
/// u64_5_as_nat([1, 0, 0, 0, 0])
///   = 1 + 2^51·0 + 2^102·0 + 2^153·0 + 2^204·0
///   = 1 + 0 + 0 + 0 + 0        (since n·0 = 0 for all n)
///   = 1
///
/// fe51_as_canonical_nat(ONE) = 1 % p = 1  (since p > 2 > 1, by lemma_small_mod)
/// ```
pub proof fn lemma_one_field_element_value()
    ensures
        fe51_as_canonical_nat(&FieldElement51::ONE) == 1,
{
    // Goal: fe51_as_canonical_nat(ONE) = u64_5_as_nat(ONE.limbs) % p = 1
    //
    // Mathematical reasoning:
    //   ONE.limbs = [1, 0, 0, 0, 0]
    //   u64_5_as_nat([1, 0, 0, 0, 0])
    //     = 1 + 2^51·0 + 2^102·0 + 2^153·0 + 2^204·0
    //     = 1    (since n·0 = 0 for all n)
    //   1 % p = 1    (since p > 2 > 1, by lemma_small_mod)
    assert(fe51_as_canonical_nat(&FieldElement51::ONE) == 1) by {
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

// =============================================================================
// Curve constants (backend::serial::u64::constants)
// =============================================================================
/// `MONTGOMERY_A` has 51-bit bounded limbs.
///
/// (Moved here from `montgomery_constants_lemmas.rs` to keep small constant facts centralized.)
pub proof fn lemma_montgomery_a_limbs_bounded_51()
    ensures
        fe51_limbs_bounded(&MONTGOMERY_A, 51),
{
    assert(fe51_limbs_bounded(&MONTGOMERY_A, 51)) by {
        assert(0u64 < (1u64 << 51) && 486662u64 < (1u64 << 51)) by (bit_vector);
    };
}

/// `MONTGOMERY_A_NEG` has 51-bit bounded limbs.
pub proof fn lemma_montgomery_a_neg_limbs_bounded_51()
    ensures
        fe51_limbs_bounded(&MONTGOMERY_A_NEG, 51),
{
    assert(fe51_limbs_bounded(&MONTGOMERY_A_NEG, 51)) by {
        assert(2251799813198567u64 < (1u64 << 51) && 2251799813685247u64 < (1u64 << 51))
            by (bit_vector);
    };
}

} // verus!
