//! Lemma for proving t3 = x^11 in pow22501
//!
//! This lemma proves the first checkpoint in the pow22501 exponentiation chain:
//! Starting from x, we compute:
//! - t0 = x^2         (square)
//! - t0_sq = x^4      (square of t0)
//! - t1 = x^8         (square of t0_sq)
//! - t2 = x^9         (multiply: x * x^8)
//! - t3 = x^11        (multiply: x^2 * x^9)
//!
//! This proof uses helper lemmas from pow_chain_lemmas for conciseness.
//!
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::prelude::*;

use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::lemmas::field_lemmas::pow_chain_lemmas::*;
use crate::specs::field_specs_u64::*;

verus! {

/// Proves that t3 = x^11 given the computation chain from pow22501
///
/// # Arguments
/// * `self_limbs` - The base value x
/// * `t0_limbs` - x^2 (result of self.square())
/// * `t0_sq_limbs` - x^4 (result of t0.square())
/// * `t1_limbs` - x^8 (result of t0_sq.square())
/// * `t2_limbs` - x^9 (result of self * t1)
/// * `t3_limbs` - x^11 (result of t0 * t2)
///
/// # Preconditions
/// * Limbs are properly bounded (< 2^54)
/// * Each step follows the correct field operation postconditions
///
/// # Postconditions
/// * u64_5_as_nat(t3_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 11) as nat % p()
/// * Also proves intermediate values: t0_sq = x^4, t1 = x^8, t2 = x^9
pub proof fn lemma_pow22501_prove_t3(
    self_limbs: [u64; 5],
    t0_limbs: [u64; 5],
    t0_sq_limbs: [u64; 5],
    t1_limbs: [u64; 5],
    t2_limbs: [u64; 5],
    t3_limbs: [u64; 5],
)
    requires
// Limbs are bounded

        forall|i: int| 0 <= i < 5 ==> self_limbs[i] < 1u64 << 54,
        forall|i: int| 0 <= i < 5 ==> t0_limbs[i] < 1u64 << 54,
        forall|i: int| 0 <= i < 5 ==> t0_sq_limbs[i] < 1u64 << 54,
        forall|i: int| 0 <= i < 5 ==> t1_limbs[i] < 1u64 << 54,
        forall|i: int| 0 <= i < 5 ==> t2_limbs[i] < 1u64 << 54,
        forall|i: int| 0 <= i < 5 ==> t3_limbs[i] < 1u64 << 54,
        // Computational relationships (from field operation postconditions)
        u64_5_as_nat(t0_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 2) as nat % p(),
        u64_5_as_nat(t0_sq_limbs) % p() == pow(u64_5_as_nat(t0_limbs) as int, 2) as nat % p(),
        u64_5_as_nat(t1_limbs) % p() == pow(u64_5_as_nat(t0_sq_limbs) as int, 2) as nat % p(),
        u64_5_as_nat(t2_limbs) % p() == (u64_5_as_nat(self_limbs) * u64_5_as_nat(t1_limbs)) % p(),
        u64_5_as_nat(t3_limbs) % p() == (u64_5_as_nat(t0_limbs) * u64_5_as_nat(t2_limbs)) % p(),
    ensures
        u64_5_as_nat(t3_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 11) as nat % p(),
        u64_5_as_nat(t0_sq_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 4) as nat % p(),
        u64_5_as_nat(t1_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 8) as nat % p(),
        u64_5_as_nat(t2_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 9) as nat % p(),
{
    let base = u64_5_as_nat(self_limbs) as int;

    assert(p() > 0) by {
        pow255_gt_19();
    }

    // ========================================================================
    // Prove t0_sq = x^4 using lemma_prove_pow2k_step
    // ========================================================================
    // t0_sq = (x^2)^2 = x^(2*2) = x^4
    lemma_prove_pow2k_step(base, u64_5_as_nat(t0_limbs), u64_5_as_nat(t0_sq_limbs), 2, 2);
    assert(u64_5_as_nat(t0_sq_limbs) % p() == pow(base, 4) as nat % p());

    // ========================================================================
    // Prove t1 = x^8 using lemma_prove_pow2k_step
    // ========================================================================
    // t1 = (x^4)^2 = x^(4*2) = x^8
    lemma_prove_pow2k_step(base, u64_5_as_nat(t0_sq_limbs), u64_5_as_nat(t1_limbs), 4, 2);
    assert(u64_5_as_nat(t1_limbs) % p() == pow(base, 8) as nat % p());

    // ========================================================================
    // Prove t2 = x^9 using lemma_prove_geometric_mul_step
    // ========================================================================
    // t2 = x^1 * x^8 = x^(1+8) = x^9
    assert(pow(base, 1) == base) by {
        lemma_pow1(base);
    }
    assert(pow(base, 1) as nat == u64_5_as_nat(self_limbs));
    lemma_prove_geometric_mul_step(
        base,
        u64_5_as_nat(self_limbs),
        u64_5_as_nat(t1_limbs),
        u64_5_as_nat(t2_limbs),
        1,
        8,
    );
    assert(u64_5_as_nat(t2_limbs) % p() == pow(base, 9) as nat % p());

    // ========================================================================
    // Prove t3 = x^11 using lemma_prove_geometric_mul_step
    // ========================================================================
    // t3 = x^2 * x^9 = x^(2+9) = x^11
    lemma_prove_geometric_mul_step(
        base,
        u64_5_as_nat(t0_limbs),
        u64_5_as_nat(t2_limbs),
        u64_5_as_nat(t3_limbs),
        2,
        9,
    );
    assert(u64_5_as_nat(t3_limbs) % p() == pow(base, 11) as nat % p());
}

} // verus!
