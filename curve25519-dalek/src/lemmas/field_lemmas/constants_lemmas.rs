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
use crate::backend::serial::u64::constants::{
    EDWARDS_D, EDWARDS_D_MINUS_ONE_SQUARED, INVSQRT_A_MINUS_D, MONTGOMERY_A, MONTGOMERY_A_NEG,
    ONE_MINUS_EDWARDS_D_SQUARED, SQRT_AD_MINUS_ONE, SQRT_M1,
};
use crate::backend::serial::u64::field::FieldElement51;
#[cfg(verus_keep_ghost)]
use crate::lemmas::edwards_lemmas::constants_lemmas::{
    lemma_edwards_d_limbs_bounded, lemma_edwards_d_limbs_bounded_54,
};
#[cfg(verus_keep_ghost)]
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::lemma_sqrt_m1_limbs_bounded;
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
// FieldElement::MINUS_ONE Lemmas
// =============================================================================
/// MINUS_ONE has 51-bit bounded limbs
pub proof fn lemma_minus_one_limbs_bounded_51()
    ensures
        fe51_limbs_bounded(&FieldElement51::MINUS_ONE, 51),
{
    assert(fe51_limbs_bounded(&FieldElement51::MINUS_ONE, 51)) by {
        // MINUS_ONE = [2^51-20, 2^51-1, 2^51-1, 2^51-1, 2^51-1]
        assert(2251799813685228u64 < (1u64 << 51)) by (bit_vector);
        assert(2251799813685247u64 < (1u64 << 51)) by (bit_vector);
    };
}

/// fe51_as_canonical_nat(MINUS_ONE) = -1 (mod p)
///
/// MINUS_ONE limbs = [2^51-20, 2^51-1, 2^51-1, 2^51-1, 2^51-1]
/// u64_5_as_nat telescopes to pow2(255) - 20 = p - 1.
pub proof fn lemma_minus_one_field_element_value()
    ensures
        fe51_as_canonical_nat(&FieldElement51::MINUS_ONE) == field_sub(0, 1),
        fe51_as_canonical_nat(&FieldElement51::MINUS_ONE) == field_neg(1),
{
    let limbs = FieldElement51::MINUS_ONE.limbs;
    let p51 = 2251799813685248nat;

    assert(pow2(51) == p51) by {
        lemma2_to64_rest();
    };
    assert(pow2(102) == pow2(51) * pow2(51)) by {
        lemma_pow2_adds(51, 51);
    };
    assert(pow2(153) == pow2(51) * pow2(102)) by {
        lemma_pow2_adds(51, 102);
    };
    assert(pow2(204) == pow2(51) * pow2(153)) by {
        lemma_pow2_adds(51, 153);
    };
    assert(pow2(255) == pow2(51) * pow2(204)) by {
        lemma_pow2_adds(51, 204);
    };

    assert(limbs[0] as nat == p51 - 20);
    assert(limbs[1] as nat == p51 - 1);
    assert(limbs[2] as nat == p51 - 1);
    assert(limbs[3] as nat == p51 - 1);
    assert(limbs[4] as nat == p51 - 1);

    assert(p51 * (p51 - 1) == pow2(102) - p51) by (nonlinear_arith)
        requires
            pow2(102) == p51 * p51,
    ;
    assert(pow2(102) * (p51 - 1) == pow2(153) - pow2(102)) by (nonlinear_arith)
        requires
            pow2(153) == p51 * pow2(102),
    ;
    assert(pow2(153) * (p51 - 1) == pow2(204) - pow2(153)) by (nonlinear_arith)
        requires
            pow2(204) == p51 * pow2(153),
    ;
    assert(pow2(204) * (p51 - 1) == pow2(255) - pow2(204)) by (nonlinear_arith)
        requires
            pow2(255) == p51 * pow2(204),
    ;

    assert(u64_5_as_nat(limbs) == pow2(255) - 20) by (nonlinear_arith)
        requires
            limbs[0] as nat == p51 - 20,
            limbs[1] as nat == p51 - 1,
            limbs[2] as nat == p51 - 1,
            limbs[3] as nat == p51 - 1,
            limbs[4] as nat == p51 - 1,
            p51 * (p51 - 1) == pow2(102) - p51,
            pow2(102) * (p51 - 1) == pow2(153) - pow2(102),
            pow2(153) * (p51 - 1) == pow2(204) - pow2(153),
            pow2(204) * (p51 - 1) == pow2(255) - pow2(204),
            u64_5_as_nat(limbs) == limbs[0] as nat + p51 * limbs[1] as nat + pow2(102)
                * limbs[2] as nat + pow2(153) * limbs[3] as nat + pow2(204) * limbs[4] as nat,
    ;

    assert(u64_5_as_nat(limbs) == (p() - 1) as nat) by (nonlinear_arith)
        requires
            u64_5_as_nat(limbs) == pow2(255) - 20,
            p() == (pow2(255) - 19) as nat,
    ;
    assert(u64_5_as_nat(limbs) % p() == (p() - 1) as nat) by {
        lemma_small_mod((p() - 1) as nat, p());
    };
    p_gt_2();
    assert(fe51_as_canonical_nat(&FieldElement51::MINUS_ONE) == (p() - 1) as nat);
    assert(field_neg(1) == (p() - 1) as nat) by {
        lemma_small_mod(1nat, p());
        lemma_small_mod((p() - 1) as nat, p());
    };
}

/// Crate-local pow2/u5_nat/p() that the Verus `by (compute_only)` interpreter
/// can evaluate.  vstd's `pow2` is cross-crate, so the interpreter refuses it.
/// After the compute phase, `lemma_bridge_local_pow2` equates each local_pow2(k)
/// with pow2(k), letting Z3 unify local_u5_nat/local_p with u64_5_as_nat/p().
#[verifier::memoize]
spec fn local_pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * local_pow2((n - 1) as nat)
    }
}

spec fn local_u5_nat(limbs: [u64; 5]) -> nat {
    (limbs[0] as nat) + local_pow2(51) * (limbs[1] as nat) + local_pow2(102) * (limbs[2] as nat)
        + local_pow2(153) * (limbs[3] as nat) + local_pow2(204) * (limbs[4] as nat)
}

spec fn local_p() -> nat {
    (local_pow2(255) - 19) as nat
}

/// Bridge: local_pow2(k) == pow2(k) for k ∈ {51, 102, 153, 204, 255}.
///
/// After this, Z3 can derive local_u5_nat(l) == u64_5_as_nat(l) and
/// local_p() == p() automatically.
proof fn lemma_bridge_local_pow2()
    ensures
        local_pow2(51) == pow2(51),
        local_pow2(102) == pow2(102),
        local_pow2(153) == pow2(153),
        local_pow2(204) == pow2(204),
        local_pow2(255) == pow2(255),
{
    assert(local_pow2(51) == 2251799813685248nat) by (compute_only);
    assert(pow2(51) == 2251799813685248nat) by {
        lemma2_to64_rest();
    };

    assert(local_pow2(102) == local_pow2(51) * local_pow2(51)) by (compute_only);
    assert(pow2(102) == pow2(51) * pow2(51)) by {
        lemma_pow2_adds(51, 51);
    };

    assert(local_pow2(153) == local_pow2(51) * local_pow2(102)) by (compute_only);
    assert(pow2(153) == pow2(51) * pow2(102)) by {
        lemma_pow2_adds(51, 102);
    };

    assert(local_pow2(204) == local_pow2(51) * local_pow2(153)) by (compute_only);
    assert(pow2(204) == pow2(51) * pow2(153)) by {
        lemma_pow2_adds(51, 153);
    };

    assert(local_pow2(255) == local_pow2(51) * local_pow2(204)) by (compute_only);
    assert(pow2(255) == pow2(51) * pow2(204)) by {
        lemma_pow2_adds(51, 204);
    };
}

/// ONE_MINUS_EDWARDS_D_SQUARED = (1−d)(1+d) mod p
///
/// Proved by computation (local_pow2 evaluated by interpreter) then bridged to
/// spec-level functions via `lemma_bridge_local_pow2`.
pub proof fn lemma_one_minus_d_squared_value()
    ensures
        fe51_as_canonical_nat(&ONE_MINUS_EDWARDS_D_SQUARED) == field_mul(
            field_sub(1, fe51_as_canonical_nat(&crate::backend::serial::u64::constants::EDWARDS_D)),
            field_add(1, fe51_as_canonical_nat(&crate::backend::serial::u64::constants::EDWARDS_D)),
        ),
{
    assert({
        let lp = local_p();
        let omd_val = local_u5_nat(ONE_MINUS_EDWARDS_D_SQUARED.limbs) % lp;
        let d_val = local_u5_nat(crate::backend::serial::u64::constants::EDWARDS_D.limbs) % lp;
        let one_minus_d = (((1nat % lp) + lp - (d_val % lp)) as nat) % lp;
        let one_plus_d = (1nat + d_val) % lp;
        omd_val == (one_minus_d * one_plus_d) % lp
    }) by (compute_only);

    lemma_bridge_local_pow2();
}

/// EDWARDS_D_MINUS_ONE_SQUARED = (d−1)² mod p
///
/// Proved by computation (local_pow2 evaluated by interpreter) then bridged to
/// spec-level functions via `lemma_bridge_local_pow2`.
pub proof fn lemma_d_minus_one_squared_value()
    ensures
        fe51_as_canonical_nat(&EDWARDS_D_MINUS_ONE_SQUARED) == field_square(
            field_sub(fe51_as_canonical_nat(&crate::backend::serial::u64::constants::EDWARDS_D), 1),
        ),
{
    assert({
        let lp = local_p();
        let dmo_val = local_u5_nat(EDWARDS_D_MINUS_ONE_SQUARED.limbs) % lp;
        let d_val = local_u5_nat(crate::backend::serial::u64::constants::EDWARDS_D.limbs) % lp;
        let d_minus_one = (((d_val % lp) + lp - (1nat % lp)) as nat) % lp;
        dmo_val == (d_minus_one * d_minus_one) % lp
    }) by (compute_only);

    lemma_bridge_local_pow2();
}

/// d + 1 is nonzero in GF(p), i.e., d != p - 1.
///
/// Proved by concrete evaluation: d is the Edwards curve parameter stored in
/// EDWARDS_D, and (d + 1) mod p is computed to be nonzero via the interpreter.
pub proof fn lemma_d_plus_one_nonzero()
    ensures
        field_add(fe51_as_canonical_nat(&EDWARDS_D), 1) != 0,
{
    assert({
        let lp = local_p();
        let d_val = local_u5_nat(EDWARDS_D.limbs) % lp;
        let d_plus_one = (d_val + 1) % lp;
        d_plus_one != 0
    }) by (compute_only);

    assert(field_add(fe51_as_canonical_nat(&EDWARDS_D), 1) != 0) by {
        lemma_bridge_local_pow2();
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

// =============================================================================
// INVSQRT_A_MINUS_D Lemmas
// =============================================================================
/// INVSQRT_A_MINUS_D = 1/sqrt(a-d) has 51-bit bounded limbs.
///
/// limbs = [278908739862762, 821645201101625, 8113234426968, 1777959178193151, 2118520810568447]
/// max limb = 2118520810568447 < 2^51 = 2251799813685248
pub proof fn lemma_invsqrt_a_minus_d_limbs_bounded()
    ensures
        fe51_limbs_bounded(&INVSQRT_A_MINUS_D, 51),
        fe51_limbs_bounded(&INVSQRT_A_MINUS_D, 54),
{
    assert(fe51_limbs_bounded(&INVSQRT_A_MINUS_D, 51)) by {
        assert(278908739862762u64 < (1u64 << 51)) by (bit_vector);
        assert(821645201101625u64 < (1u64 << 51)) by (bit_vector);
        assert(8113234426968u64 < (1u64 << 51)) by (bit_vector);
        assert(1777959178193151u64 < (1u64 << 51)) by (bit_vector);
        assert(2118520810568447u64 < (1u64 << 51)) by (bit_vector);
    };
    assert(fe51_limbs_bounded(&INVSQRT_A_MINUS_D, 54)) by {
        assert(278908739862762u64 < (1u64 << 54)) by (bit_vector);
        assert(821645201101625u64 < (1u64 << 54)) by (bit_vector);
        assert(8113234426968u64 < (1u64 << 54)) by (bit_vector);
        assert(1777959178193151u64 < (1u64 << 54)) by (bit_vector);
        assert(2118520810568447u64 < (1u64 << 54)) by (bit_vector);
    };
}

// =============================================================================
// Ristretto Elligator Constants
// =============================================================================
/// SQRT_AD_MINUS_ONE = sqrt(a*d - 1) has 51-bit bounded limbs.
///
/// limbs = [2241493124984347, 425987919032274, 2207028919301688, 1220490630685848, 974799131293748]
/// max limb = 2241493124984347 < 2^51 = 2251799813685248
pub proof fn lemma_sqrt_ad_minus_one_limbs_bounded()
    ensures
        fe51_limbs_bounded(&SQRT_AD_MINUS_ONE, 51),
        fe51_limbs_bounded(&SQRT_AD_MINUS_ONE, 54),
{
    assert(fe51_limbs_bounded(&SQRT_AD_MINUS_ONE, 51)) by {
        assert(2241493124984347u64 < (1u64 << 51)) by (bit_vector);
        assert(425987919032274u64 < (1u64 << 51)) by (bit_vector);
        assert(2207028919301688u64 < (1u64 << 51)) by (bit_vector);
        assert(1220490630685848u64 < (1u64 << 51)) by (bit_vector);
        assert(974799131293748u64 < (1u64 << 51)) by (bit_vector);
    };
    assert(fe51_limbs_bounded(&SQRT_AD_MINUS_ONE, 54)) by {
        assert(2241493124984347u64 < (1u64 << 54)) by (bit_vector);
        assert(425987919032274u64 < (1u64 << 54)) by (bit_vector);
        assert(2207028919301688u64 < (1u64 << 54)) by (bit_vector);
        assert(1220490630685848u64 < (1u64 << 54)) by (bit_vector);
        assert(974799131293748u64 < (1u64 << 54)) by (bit_vector);
    };
}

/// ONE_MINUS_EDWARDS_D_SQUARED = 1 - d² has 51-bit bounded limbs.
///
/// limbs = [1136626929484150, 1998550399581263, 496427632559748, 118527312129759, 45110755273534]
/// max limb = 1998550399581263 < 2^51 = 2251799813685248
pub proof fn lemma_one_minus_d_squared_limbs_bounded()
    ensures
        fe51_limbs_bounded(&ONE_MINUS_EDWARDS_D_SQUARED, 51),
        fe51_limbs_bounded(&ONE_MINUS_EDWARDS_D_SQUARED, 54),
{
    assert(fe51_limbs_bounded(&ONE_MINUS_EDWARDS_D_SQUARED, 51)) by {
        assert(1136626929484150u64 < (1u64 << 51)) by (bit_vector);
        assert(1998550399581263u64 < (1u64 << 51)) by (bit_vector);
        assert(496427632559748u64 < (1u64 << 51)) by (bit_vector);
        assert(118527312129759u64 < (1u64 << 51)) by (bit_vector);
        assert(45110755273534u64 < (1u64 << 51)) by (bit_vector);
    };
    assert(fe51_limbs_bounded(&ONE_MINUS_EDWARDS_D_SQUARED, 54)) by {
        assert(1136626929484150u64 < (1u64 << 54)) by (bit_vector);
        assert(1998550399581263u64 < (1u64 << 54)) by (bit_vector);
        assert(496427632559748u64 < (1u64 << 54)) by (bit_vector);
        assert(118527312129759u64 < (1u64 << 54)) by (bit_vector);
        assert(45110755273534u64 < (1u64 << 54)) by (bit_vector);
    };
}

/// EDWARDS_D_MINUS_ONE_SQUARED = (d - 1)^2 has 51-bit bounded limbs.
///
/// limbs = [1507062230895904, 1572317787530805, 683053064812840, 317374165784489, 1572899562415810]
/// max limb = 1572899562415810 < 2^51 = 2251799813685248
pub proof fn lemma_d_minus_one_squared_limbs_bounded()
    ensures
        fe51_limbs_bounded(&EDWARDS_D_MINUS_ONE_SQUARED, 51),
        fe51_limbs_bounded(&EDWARDS_D_MINUS_ONE_SQUARED, 54),
{
    assert(fe51_limbs_bounded(&EDWARDS_D_MINUS_ONE_SQUARED, 51)) by {
        assert(1507062230895904u64 < (1u64 << 51)) by (bit_vector);
        assert(1572317787530805u64 < (1u64 << 51)) by (bit_vector);
        assert(683053064812840u64 < (1u64 << 51)) by (bit_vector);
        assert(317374165784489u64 < (1u64 << 51)) by (bit_vector);
        assert(1572899562415810u64 < (1u64 << 51)) by (bit_vector);
    };
    assert(fe51_limbs_bounded(&EDWARDS_D_MINUS_ONE_SQUARED, 54)) by {
        assert(1507062230895904u64 < (1u64 << 54)) by (bit_vector);
        assert(1572317787530805u64 < (1u64 << 54)) by (bit_vector);
        assert(683053064812840u64 < (1u64 << 54)) by (bit_vector);
        assert(317374165784489u64 < (1u64 << 54)) by (bit_vector);
        assert(1572899562415810u64 < (1u64 << 54)) by (bit_vector);
    };
}

/// SQRT_AD_MINUS_ONE is nonzero as a field element.
///
/// Proved by computation: local_u5_nat(limbs) % local_p() != 0,
/// then bridged to spec-level functions via pow2 equalities.
pub proof fn lemma_sqrt_ad_minus_one_nonzero()
    ensures
        fe51_as_canonical_nat(&SQRT_AD_MINUS_ONE) != 0,
        fe51_as_canonical_nat(&SQRT_AD_MINUS_ONE) % p() != 0,
{
    assert(local_u5_nat(SQRT_AD_MINUS_ONE.limbs) % local_p() != 0) by (compute_only);

    assert(local_pow2(51) == 2251799813685248nat) by (compute_only);
    assert(pow2(51) == 2251799813685248nat) by {
        lemma2_to64_rest();
    };
    assert(local_pow2(102) == local_pow2(51) * local_pow2(51)) by (compute_only);
    assert(pow2(102) == pow2(51) * pow2(51)) by {
        lemma_pow2_adds(51, 51);
    };
    assert(local_pow2(153) == local_pow2(51) * local_pow2(102)) by (compute_only);
    assert(pow2(153) == pow2(51) * pow2(102)) by {
        lemma_pow2_adds(51, 102);
    };
    assert(local_pow2(204) == local_pow2(51) * local_pow2(153)) by (compute_only);
    assert(pow2(204) == pow2(51) * pow2(153)) by {
        lemma_pow2_adds(51, 153);
    };
    assert(local_pow2(255) == local_pow2(51) * local_pow2(204)) by (compute_only);
    assert(pow2(255) == pow2(51) * pow2(204)) by {
        lemma_pow2_adds(51, 204);
    };

    assert(fe51_as_canonical_nat(&SQRT_AD_MINUS_ONE) != 0);
    assert(fe51_as_canonical_nat(&SQRT_AD_MINUS_ONE) % p() != 0) by {
        lemma_mod_bound(fe51_as_nat(&SQRT_AD_MINUS_ONE) as int, p() as int);
        lemma_small_mod(fe51_as_canonical_nat(&SQRT_AD_MINUS_ONE), p());
    };
}

/// Bundle all constant limb-bound facts needed by elligator_ristretto_flavor.
///
/// Establishes 51-bit and 54-bit bounds for: SQRT_M1, EDWARDS_D, ONE, MINUS_ONE,
/// ONE_MINUS_EDWARDS_D_SQUARED, EDWARDS_D_MINUS_ONE_SQUARED, SQRT_AD_MINUS_ONE.
pub proof fn lemma_elligator_constants_bounded()
    ensures
        fe51_limbs_bounded(&SQRT_M1, 54),
        fe51_limbs_bounded(&EDWARDS_D, 51),
        fe51_limbs_bounded(&EDWARDS_D, 54),
        fe51_limbs_bounded(&FieldElement51::ONE, 51),
        fe51_limbs_bounded(&FieldElement51::MINUS_ONE, 51),
        fe51_limbs_bounded(&ONE_MINUS_EDWARDS_D_SQUARED, 51),
        fe51_limbs_bounded(&EDWARDS_D_MINUS_ONE_SQUARED, 51),
        fe51_limbs_bounded(&SQRT_AD_MINUS_ONE, 51),
{
    lemma_sqrt_m1_limbs_bounded();
    lemma_edwards_d_limbs_bounded();
    lemma_edwards_d_limbs_bounded_54();
    lemma_one_limbs_bounded_51();
    lemma_minus_one_limbs_bounded_51();
    lemma_one_minus_d_squared_limbs_bounded();
    lemma_d_minus_one_squared_limbs_bounded();
    lemma_sqrt_ad_minus_one_limbs_bounded();
}

} // verus!
