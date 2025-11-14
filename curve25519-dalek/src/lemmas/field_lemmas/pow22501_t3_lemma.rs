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
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::prelude::*;

use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
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
/// * as_nat(t3_limbs) % p() == pow(as_nat(self_limbs) as int, 11) as nat % p()
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
        as_nat(t0_limbs) % p() == pow(as_nat(self_limbs) as int, 2) as nat % p(),
        as_nat(t0_sq_limbs) % p() == pow(as_nat(t0_limbs) as int, 2) as nat % p(),
        as_nat(t1_limbs) % p() == pow(as_nat(t0_sq_limbs) as int, 2) as nat % p(),
        as_nat(t2_limbs) % p() == (as_nat(self_limbs) * as_nat(t1_limbs)) % p(),
        as_nat(t3_limbs) % p() == (as_nat(t0_limbs) * as_nat(t2_limbs)) % p(),
    ensures
        as_nat(t3_limbs) % p() == pow(as_nat(self_limbs) as int, 11) as nat % p(),
        as_nat(t0_sq_limbs) % p() == pow(as_nat(self_limbs) as int, 4) as nat % p(),
        as_nat(t1_limbs) % p() == pow(as_nat(self_limbs) as int, 8) as nat % p(),
        as_nat(t2_limbs) % p() == pow(as_nat(self_limbs) as int, 9) as nat % p(),
{
    let base = as_nat(self_limbs) as int;

    assert(p() > 0) by {
        pow255_gt_19();
    }

    // ========================================================================
    // Prove t0_sq = x^4
    // ========================================================================
    // From postcondition: t0_sq = (x^2)^2
    // By lemma_pow_multiplies: (x^2)^2 = x^(2*2) = x^4

    // Prove pow(base, 2) >= 0 and pow(base, 4) >= 0
    assert(pow(base, 2) >= 0) by {
        lemma_pow_even_nonnegative(base, 1);
    }
    assert(pow(base, 4) >= 0) by {
        lemma_pow_even_nonnegative(base, 2);
    }

    // Establish t0_limbs = x^2 (from precondition)
    assert(as_nat(t0_limbs) % p() == pow(base, 2) as nat % p());

    // Prove pow(t0_limbs, 2) >= 0
    let t0_val = as_nat(t0_limbs) as int;
    assert(t0_val >= 0);
    assert(pow(t0_val, 2) >= 0) by {
        lemma_pow_even_nonnegative(t0_val, 1);
    }

    // Convert int modulo to nat modulo for both sides
    assert((pow(as_nat(t0_limbs) as int, 2) as nat) % p() == (pow(as_nat(t0_limbs) as int, 2) % (
    p() as int)) as nat);
    assert((pow(base, 4) as nat) % p() == (pow(base, 4) % (p() as int)) as nat);

    // Apply power congruence: since t0_limbs ≡ x^2 (mod p), then t0_limbs^2 ≡ (x^2)^2 (mod p)
    assert((pow(as_nat(t0_limbs) as int, 2) % (p() as int)) as nat == (pow(pow(base, 2), 2) % (
    p() as int)) as nat) by {
        lemma_pow_mod_congruent(as_nat(t0_limbs) as int, pow(base, 2), 2, p() as int);
    }

    // Apply power multiplication: (x^2)^2 = x^4
    assert(pow(pow(base, 2), 2) == pow(base, 4)) by {
        lemma_pow_multiplies(base, 2, 2);
    }

    assert(as_nat(t0_sq_limbs) % p() == pow(base, 4) as nat % p());

    // ========================================================================
    // Prove t1 = x^8
    // ========================================================================
    // From postcondition: t1 = (x^4)^2
    // By lemma_pow_multiplies: (x^4)^2 = x^(4*2) = x^8

    assert(pow(base, 8) >= 0) by {
        lemma_pow_even_nonnegative(base, 4);
    }

    // Prove pow(t0_sq_limbs, 2) >= 0
    let t0_sq_val = as_nat(t0_sq_limbs) as int;
    assert(t0_sq_val >= 0);
    assert(pow(t0_sq_val, 2) >= 0) by {
        lemma_pow_even_nonnegative(t0_sq_val, 1);
    }

    // Convert int modulo to nat modulo for both sides
    assert((pow(as_nat(t0_sq_limbs) as int, 2) as nat) % p() == (pow(as_nat(t0_sq_limbs) as int, 2)
        % (p() as int)) as nat);
    assert((pow(base, 8) as nat) % p() == (pow(base, 8) % (p() as int)) as nat);

    // Apply power congruence: since t0_sq_limbs ≡ x^4 (mod p), then t0_sq_limbs^2 ≡ (x^4)^2 (mod p)
    assert((pow(as_nat(t0_sq_limbs) as int, 2) % (p() as int)) as nat == (pow(pow(base, 4), 2) % (
    p() as int)) as nat) by {
        lemma_pow_mod_congruent(as_nat(t0_sq_limbs) as int, pow(base, 4), 2, p() as int);
    }

    // Apply power multiplication: (x^4)^2 = x^8
    assert(pow(pow(base, 4), 2) == pow(base, 8)) by {
        lemma_pow_multiplies(base, 4, 2);
    }

    assert(as_nat(t1_limbs) % p() == pow(base, 8) as nat % p());

    // ========================================================================
    // Prove t2 = x^9
    // ========================================================================
    // From postcondition: t2 = x^1 * x^8
    // By lemma_pow_adds: x^1 * x^8 = x^(1+8) = x^9

    assert(pow(base, 1) == base) by {
        lemma_pow1(base);
    }
    assert(pow(base, 1) as nat == as_nat(self_limbs));

    // Expand multiplication modulo using the standard identity: (a * b) % p = ((a % p) * (b % p)) % p
    assert(as_nat(t2_limbs) % p() == ((as_nat(self_limbs) % p()) * (as_nat(t1_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(self_limbs) as int, as_nat(t1_limbs) as int, p() as int);
    }

    // Substitute known powers: self_limbs = x^1, t1_limbs = x^8
    assert(as_nat(t2_limbs) % p() == ((pow(base, 1) as nat % p()) * (pow(base, 8) as nat % p()))
        % p());

    // Apply modular multiplication lemma: ((a % p) * (b % p)) % p = (a * b) % p
    assert(as_nat(t2_limbs) % p() == (pow(base, 1) as nat * pow(base, 8) as nat) % p()) by {
        lemma_mul_mod_noop_general(
            pow(base, 1) as nat as int,
            pow(base, 8) as nat as int,
            p() as int,
        );
    }

    // Prove x^1 * x^8 = x^9 in int
    assert(pow(base, 1) * pow(base, 8) == pow(base, 9)) by {
        lemma_pow_adds(base, 1, 8);
    }

    // Convert to nat: casting preserves multiplication for non-negative values
    assert(pow(base, 9) >= 0) by {
        lemma_pow_nonnegative(base, 9);
    }
    assert(pow(base, 1) as nat * pow(base, 8) as nat == (pow(base, 1) * pow(base, 8)) as nat);
    assert(pow(base, 1) as nat * pow(base, 8) as nat == pow(base, 9) as nat);

    assert(as_nat(t2_limbs) % p() == pow(base, 9) as nat % p());

    // ========================================================================
    // Prove t3 = x^11
    // ========================================================================
    // From postcondition: t3 = x^2 * x^9
    // By lemma_pow_adds: x^2 * x^9 = x^(2+9) = x^11

    // Expand multiplication modulo using the standard identity: (a * b) % p = ((a % p) * (b % p)) % p
    assert(as_nat(t3_limbs) % p() == ((as_nat(t0_limbs) % p()) * (as_nat(t2_limbs) % p())) % p())
        by {
        lemma_mul_mod_noop_general(as_nat(t0_limbs) as int, as_nat(t2_limbs) as int, p() as int);
    }

    // Substitute known powers: t0_limbs = x^2, t2_limbs = x^9
    assert(as_nat(t3_limbs) % p() == ((pow(base, 2) as nat % p()) * (pow(base, 9) as nat % p()))
        % p());

    // Apply modular multiplication lemma: ((a % p) * (b % p)) % p = (a * b) % p
    assert(as_nat(t3_limbs) % p() == (pow(base, 2) as nat * pow(base, 9) as nat) % p()) by {
        lemma_mul_mod_noop_general(
            pow(base, 2) as nat as int,
            pow(base, 9) as nat as int,
            p() as int,
        );
    }

    // Prove x^2 * x^9 = x^11 in int
    assert(pow(base, 2) * pow(base, 9) == pow(base, 11)) by {
        lemma_pow_adds(base, 2, 9);
    }

    // Convert to nat: casting preserves multiplication for non-negative values
    assert(pow(base, 11) >= 0) by {
        lemma_pow_nonnegative(base, 11);
    }
    assert(pow(base, 2) as nat * pow(base, 9) as nat == (pow(base, 2) * pow(base, 9)) as nat);
    assert(pow(base, 2) as nat * pow(base, 9) as nat == pow(base, 11) as nat);

    assert(as_nat(t3_limbs) % p() == pow(base, 11) as nat % p());
}

} // verus!
