#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::super::common_verus::div_mod_lemmas::*;
use super::super::common_verus::mul_lemmas::*;
use super::super::common_verus::pow_lemmas::*;
use super::field_core::*; // For as_nat, p, as_nat_32_u8, as_nat_32_u8_nonrec

verus! {

// ============================================================================
// UNUSED HELPER LEMMAS
// ============================================================================
// This file contains proof lemmas that were written but are not currently
// used in the main verification. They are kept here for potential future use
// or as reference implementations.
// ============================================================================

///this is https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Div/Lemmas.html#Nat.div_eq_zero_iff_lt
/// Status: UNUSED - Only called by `lemma_div_converse` which is also unused.
pub proof fn lemma_small_div(x: int, d: int)
    requires
        0 <= x < d,
        d > 0,
    ensures
        x / d == 0,
{
    // Use fundamental division theorem: x = (x / d) * d + (x % d)
    lemma_fundamental_div_mod(x, d);
    let q = x / d;
    let r = x % d;
    lemma_mod_bound(x, d);

    // We have: x = q * d + r where 0 <= r < d
    // Since x < d and r < d, we need q * d < d
    // If q >= 1, then q * d >= d, which would make x >= d (contradiction)
    if q >= 1 {
        lemma_mul_left_inequality(d, 1, q);
        assert(false);
    }
    // If q <= -1, then q * d <= -d < 0, which would make x < 0 (contradiction)
    if q <= -1 {
        lemma_mul_inequality(q, -1, d);
        assert(false);
    }
    // Therefore q must be 0
}

/// Helper lemma: proves the converse of the fundamental div/mod theorem
/// If you have a number in the form (u * d + r) where 0 <= r < d, then dividing by d gives u
///
/// Status: UNUSED - Written as a general-purpose lemma but never actually called.
/// vstd's `lemma_fundamental_div_mod_converse_div` serves the same purpose.
/// Proof by induction on |u|: base case u=0, inductive cases u±1.
pub proof fn lemma_div_converse(u: int, d: int, r: int)
    requires
        d != 0,
        0 <= r < d,
    ensures
        u == (u * d + r) / d,
    decreases
        if u >= 0 { u } else { -u },
{
    if u < 0 {
        // By induction: u + 1 == ((u+1)*d + r) / d
        lemma_div_converse(u + 1, d, r);

        // Show (u+1)*d + r == u*d + r + d
        assert((u + 1) * d + r == u * d + r + d) by {
            lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
        }

        // Prove (u*d + r + d) / d == (u*d + r) / d + 1 using division uniqueness
        lemma_fundamental_div_mod(u * d + r, d);
        let q_target = (u * d + r) / d;
        let r_target = (u * d + r) % d;
        lemma_mod_bound(u * d + r, d);

        // u*d + r + d = d*(q_target + 1) + r_target, so its quotient is q_target + 1
        assert(u * d + r + d == d * (q_target + 1) + r_target) by {
            lemma_mul_is_distributive_add(d, q_target, 1);
        }
        assert((q_target + 1) * d + r_target == u * d + r + d) by {
            lemma_mul_is_commutative(q_target + 1, d);
        }
        lemma_fundamental_div_mod_converse_div(u * d + r + d, d, q_target + 1, r_target);
        assert((u * d + r + d) / d == q_target + 1);

        // Connect: u + 1 == (u*d + r + d) / d == q_target + 1, so u == q_target
        assert(u == q_target);
    } else if u == 0 {
        // Base case: 0*d + r = r, and r/d = 0 since r < d
        lemma_small_div(r, d);
        assert(0 * d == 0);
        assert((u * d + r) == r);
        assert(u == (u * d + r) / d);
    } else {
        // By induction: u - 1 == ((u-1)*d + r) / d
        lemma_div_converse(u - 1, d, r);

        // Show (u-1)*d + r + d == u*d + r
        assert((u - 1) * d + r + d == u * d + r) by {
            lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
        }

        // Prove (u*d + r) / d == ((u-1)*d + r) / d + 1 using division uniqueness
        lemma_fundamental_div_mod((u - 1) * d + r, d);
        let q_target = ((u - 1) * d + r) / d;
        let r_target = ((u - 1) * d + r) % d;
        lemma_mod_bound((u - 1) * d + r, d);

        assert((u - 1) * d + r + d == d * (q_target + 1) + r_target) by {
            lemma_mul_is_distributive_add(d, q_target, 1);
        }
        assert((q_target + 1) * d + r_target == (u - 1) * d + r + d) by {
            lemma_mul_is_commutative(q_target + 1, d);
        }
        lemma_fundamental_div_mod_converse_div((u - 1) * d + r + d, d, q_target + 1, r_target);
        assert(((u - 1) * d + r + d) / d == q_target + 1);

        // Connect: u - 1 == q_target and (u*d + r) / d == q_target + 1, so u == (u*d + r) / d
        assert((u * d + r) / d == u);
    }
}

/// Helper lemma: (x + d) / d == x / d + 1
///
/// Status: UNUSED - originally written for lemma_div_converse but ended up
/// being inlined there instead.
pub proof fn lemma_div_plus_one(x: int, d: int)
    requires
        d > 0,
    ensures
        (x + d) / d == x / d + 1,
    decreases
        if (x / d) + 1 >= 0 { (x / d) + 1 } else { -((x / d) + 1) },
{
    lemma_fundamental_div_mod(x, d);
    let q = x / d;
    let r = x % d;
    assert(x == d * q + r);
    lemma_mod_bound(x, d);
    assert(0 <= r < d);

    // x + d = d * q + r + d = d * (q + 1) + r
    assert(x + d == d * (q + 1) + r) by {
        lemma_mul_is_distributive_add(d, q, 1);
    }

    // Since 0 <= r < d, by the fundamental theorem: (x + d) / d = q + 1
    // Note: This calls lemma_div_converse which is used elsewhere
    lemma_fundamental_div_mod_converse_div(x + d, d, q + 1, r);
    assert((x + d) / d == q + 1);
    assert((x + d) / d == x / d + 1);
}

/// Helper lemma: geometric series sum for radix 2^51 with 5 limbs
///
/// Status: UNUSED - superseded by lemma_radix_51_partial_geometric_sum which
/// is actually used in the proof of lemma_radix51_remainder_bound.
pub proof fn lemma_radix_51_geometric_sum()
    ensures
        1 + pow2(51) + pow2(102) + pow2(153) + pow2(204) < 2 * pow2(204),
{
    // The sum: 1 + 2^51 + 2^102 + 2^153 + 2^204
    // is dominated by its largest term 2^204

    // Since each term is strictly less than the next:
    lemma_pow2_strictly_increases(0, 51);
    lemma_pow2_strictly_increases(51, 102);
    lemma_pow2_strictly_increases(102, 153);
    lemma_pow2_strictly_increases(153, 204);

    // So: 1 < 2^51 < 2^102 < 2^153 < 2^204
    // Each term is less than the last term:
    assert(1 < pow2(204));
    assert(pow2(51) < pow2(204));
    assert(pow2(102) < pow2(204));
    assert(pow2(153) < pow2(204));

    // So the sum is less than 5 * 2^204, but we need tighter
    // Key insight: 2^153 < 2^204, so even 2^153 + 2^153 < 2^204
    // More specifically: 2^153 * 2 = 2^154 < 2^204
    lemma_pow2_adds(153, 1);
    assert(pow2(153 + 1) == pow2(153) * pow2(1));
    assert(pow2(1) == 2) by {
        lemma2_to64();
    }
    assert(2 * pow2(153) == pow2(154));
    lemma_pow2_strictly_increases(154, 204);
    assert(pow2(154) < pow2(204));
    assert(2 * pow2(153) < pow2(204));

    // So: 1 + 2^51 + 2^102 + 2^153 < 2^153 + 2^153 = 2 * 2^153 < 2^204
    // The sum of smaller terms is dominated by the largest
    lemma_pow2_strictly_increases(102, 153);
    assert(pow2(102) < pow2(153));
    // 1 + 2^51 + 2^102 < 2^102 + 2^102 + 2^102 = 3 * 2^102 < 2^153
    // Actually, even simpler: 2^102 + 2^102 = 2^103 < 2^153
    lemma_pow2_adds(102, 1);
    assert(2 * pow2(102) == pow2(103));
    lemma_pow2_strictly_increases(103, 153);
    assert(pow2(103) < pow2(153));
    assert(pow2(102) + pow2(102) < pow2(153));
    assert(1 + pow2(51) + pow2(102) < pow2(102) + pow2(102) + pow2(102));
    assert(1 + pow2(51) + pow2(102) < pow2(153));  // Each term << 2^153
    assert(1 + pow2(51) + pow2(102) + pow2(153) < pow2(153) + pow2(153));
    assert(1 + pow2(51) + pow2(102) + pow2(153) < 2 * pow2(153));
    assert(1 + pow2(51) + pow2(102) + pow2(153) < pow2(204));

    // Therefore: 1 + 2^51 + 2^102 + 2^153 + 2^204 < 2^204 + 2^204 = 2 * 2^204
    assert(1 + pow2(51) + pow2(102) + pow2(153) + pow2(204) < pow2(204) + pow2(204));
    assert(pow2(204) + pow2(204) == 2 * pow2(204));
}

/// Helper lemma: Upper bound on as_nat from limb bounds
///
/// Status: UNUSED - This lemma is a tautology (ensures == requires).
/// It was kept for documentation purposes to show that the limb bounds
/// alone (< 2^52) are NOT sufficient to prove as_nat < 2*p(), and the property
/// must come from the calling context.
///
/// The bound `as_nat < 2*p()` comes from the calling context (specifically
/// from `reduce()`'s postcondition), not from the limb bounds alone.
pub proof fn lemma_as_nat_bound_from_limbs(limbs: [u64; 5])
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        // The key precondition that makes this provable:
        as_nat(limbs) < 2 * p(),
    ensures
        as_nat(limbs) < 2 * p(),
{
    // This is a tautology - the ensure is the same as the require.
    // The point is to document that this property cannot be derived from
    // limb bounds alone and must come from the calling context.
}

/// Proves that the recursive and non-recursive definitions are equivalent
///
/// Status: UNUSED - Contains assume(false) and is never called.
/// This was intended to prove equivalence between two definitions of as_nat_32_u8
/// but was never completed or needed in the actual proofs.
pub proof fn lemma_as_nat_32_u8_equivalence(limbs: [u8; 32])
    ensures
        as_nat_32_u8(limbs) == as_nat_32_u8_nonrec(limbs)
{
    assume(false); // TODO: prove this by induction
}

}
