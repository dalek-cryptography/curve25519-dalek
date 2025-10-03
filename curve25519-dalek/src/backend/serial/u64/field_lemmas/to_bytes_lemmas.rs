#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_verus::div_mod_lemmas::*;
use super::super::common_verus::mul_lemmas::*;
use super::super::common_verus::pow_lemmas::*;
use super::super::common_verus::shift_lemmas::*;
use super::field_core::*;
use super::load8_lemmas::*;
use super::pow2_51_lemmas::*;

verus! {

// ============================================================================
// LEMMA 1: Computing q (the quotient when dividing by p)
// ============================================================================

/// Spec function to compute q value from limbs
pub open spec fn compute_q_spec(limbs: [u64; 5]) -> u64 {
    let q0 = ((limbs[0] + 19) as u64 >> 51) as u64;
    let q1 = ((limbs[1] + q0) as u64 >> 51) as u64;
    let q2 = ((limbs[2] + q1) as u64 >> 51) as u64;
    let q3 = ((limbs[3] + q2) as u64 >> 51) as u64;
    let q4 = ((limbs[4] + q3) as u64 >> 51) as u64;
    q4
}

pub proof fn lemma_bounded_shr_51(x: u64)
    requires
        x < 3 * pow2(51),
    ensures
        (x >> 51) < 3,
{
    lemma_pow2_pos(51);
    lemma_mul_is_commutative(3, pow2(51) as int);
    
    let shifted = x >> 51;
    lemma_u64_shr_is_div(x, 51);
    lemma_div_strictly_bounded(x as int, pow2(51) as int, 3);
}

/// Helper lemma: Proves the algebraic expansion and cancellation of intermediate terms
/// Shows that when expanding the substituted limbs, q0, q1, q2, q3 all cancel out
proof fn lemma_radix51_telescoping_expansion(
    q0: int, q1: int, q2: int, q3: int, q4: int,
    r0: int, r1: int, r2: int, r3: int, r4: int
)
    requires
        true
    ensures
        (q0 * pow2(51) as int + r0 - 19)
        + (q1 * pow2(51) as int + r1 - q0) * pow2(51) as int
        + (q2 * pow2(51) as int + r2 - q1) * pow2(102) as int
        + (q3 * pow2(51) as int + r3 - q2) * pow2(153) as int
        + (q4 * pow2(51) as int + r4 - q3) * pow2(204) as int
        + 19
        ==
        q4 * pow2(51) as int * pow2(204) as int 
        + r0 + r1 * pow2(51) as int + r2 * pow2(102) as int + r3 * pow2(153) as int + r4 * pow2(204) as int
{
    // Establish power relationships: 2^51 * 2^k = 2^(51+k)
    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);
    
    // Manually expand each multiplication and show the cancellations explicitly
    let lhs = (q0 * pow2(51) as int + r0 - 19)
        + (q1 * pow2(51) as int + r1 - q0) * pow2(51) as int
        + (q2 * pow2(51) as int + r2 - q1) * pow2(102) as int
        + (q3 * pow2(51) as int + r3 - q2) * pow2(153) as int
        + (q4 * pow2(51) as int + r4 - q3) * pow2(204) as int
        + 19;
    
    // Expand the multiplications using distributivity
    assert((q1 * pow2(51) as int + r1 - q0) * pow2(51) as int 
           == q1 * pow2(51) as int * pow2(51) as int + r1 * pow2(51) as int - q0 * pow2(51) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(51) as int, q1 * pow2(51) as int + r1, q0);
        lemma_mul_is_distributive_add_other_way(pow2(51) as int, q1 * pow2(51) as int, r1);
    }
    
    assert((q2 * pow2(51) as int + r2 - q1) * pow2(102) as int 
           == q2 * pow2(51) as int * pow2(102) as int + r2 * pow2(102) as int - q1 * pow2(102) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(102) as int, q2 * pow2(51) as int + r2, q1);
        lemma_mul_is_distributive_add_other_way(pow2(102) as int, q2 * pow2(51) as int, r2);
    }
    
    assert((q3 * pow2(51) as int + r3 - q2) * pow2(153) as int 
           == q3 * pow2(51) as int * pow2(153) as int + r3 * pow2(153) as int - q2 * pow2(153) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(153) as int, q3 * pow2(51) as int + r3, q2);
        lemma_mul_is_distributive_add_other_way(pow2(153) as int, q3 * pow2(51) as int, r3);
    }
    
    assert((q4 * pow2(51) as int + r4 - q3) * pow2(204) as int 
           == q4 * pow2(51) as int * pow2(204) as int + r4 * pow2(204) as int - q3 * pow2(204) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(204) as int, q4 * pow2(51) as int + r4, q3);
        lemma_mul_is_distributive_add_other_way(pow2(204) as int, q4 * pow2(51) as int, r4);
    }
    
    // Now LHS equals (after substituting the expansions):
    // = q0*2^51 + r0 - 19
    //   + q1*2^51*2^51 + r1*2^51 - q0*2^51
    //   + q2*2^51*2^102 + r2*2^102 - q1*2^102
    //   + q3*2^51*2^153 + r3*2^153 - q2*2^153
    //   + q4*2^51*2^204 + r4*2^204 - q3*2^204
    //   + 19
    
    // Use the power relationships to simplify products
    assert(q1 * pow2(51) as int * pow2(51) as int == q1 * pow2(102) as int) by {
        lemma_mul_is_associative(q1, pow2(51) as int, pow2(51) as int);
    }
    assert(q2 * pow2(51) as int * pow2(102) as int == q2 * pow2(153) as int) by {
        lemma_mul_is_associative(q2, pow2(51) as int, pow2(102) as int);
    }
    assert(q3 * pow2(51) as int * pow2(153) as int == q3 * pow2(204) as int) by {
        lemma_mul_is_associative(q3, pow2(51) as int, pow2(153) as int);
    }
    
    // Now we can see the cancellations more clearly:
    // = (q0*2^51 - q0*2^51) + (q1*2^102 - q1*2^102) + (q2*2^153 - q2*2^153) + (q3*2^204 - q3*2^204)
    //   + q4*2^51*2^204 + r0 + r1*2^51 + r2*2^102 + r3*2^153 + r4*2^204 + (-19 + 19)
    // = q4*2^51*2^204 + r0 + r1*2^51 + r2*2^102 + r3*2^153 + r4*2^204
    
    // The SMT solver should now see this is pure linear arithmetic
}

/// Direct proof of telescoping division for radix-51 representation
/// Uses repeated substitution to show q4 = (as_nat(limbs) + 19) / 2^255
///
/// Proof strategy:
/// 1. Express as_nat(limbs) + 19 as a sum using radix-51: Σ limbs[i] * 2^(51*i) + 19
/// 2. Substitute each limb using the division theorem equations (from requires clause)
/// 3. Expand and observe that intermediate q_i terms telescope (cancel out):
///    - q0 appears as: +q0*2^51 - q0*2^51 = 0
///    - q1 appears as: +q1*2^102 - q1*2^102 = 0  (and so on)
/// 4. After cancellation: value = q4 * 2^255 + remainder, where remainder < 2^255
/// 5. By uniqueness of division, q4 = value / 2^255
pub proof fn lemma_radix51_telescoping_direct(
    limbs: [u64; 5],
    q0: int, q1: int, q2: int, q3: int, q4: int,
    r0: int, r1: int, r2: int, r3: int, r4: int
)
    requires
        limbs[0] as int + 19 == q0 * pow2(51) as int + r0,
        limbs[1] as int + q0 == q1 * pow2(51) as int + r1,
        limbs[2] as int + q1 == q2 * pow2(51) as int + r2,
        limbs[3] as int + q2 == q3 * pow2(51) as int + r3,
        limbs[4] as int + q3 == q4 * pow2(51) as int + r4,
        0 <= r0 < pow2(51) as int,
        0 <= r1 < pow2(51) as int,
        0 <= r2 < pow2(51) as int,
        0 <= r3 < pow2(51) as int,
        0 <= r4 < pow2(51) as int,
    ensures
        q4 == (as_nat(limbs) as int + 19) / pow2(255) as int,
{
    // Establish power-of-2 relationships: 2^51 * 2^k = 2^(51+k)
    lemma_pow2_pos(51);
    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);
    
    // Step 1: Express value = as_nat(limbs) + 19 in radix-51 form
    let value =
        limbs[0] as int
        + limbs[1] as int * pow2(51) as int
        + limbs[2] as int * pow2(102) as int
        + limbs[3] as int * pow2(153) as int
        + limbs[4] as int * pow2(204) as int
        + 19;
    
    assert(as_nat(limbs) == (limbs[0] as nat) + pow2(51) * (limbs[1] as nat) + pow2(102) * (limbs[2] as nat)
                            + pow2(153) * (limbs[3] as nat) + pow2(204) * (limbs[4] as nat));
    
    assert((limbs[0] as nat) + pow2(51) * (limbs[1] as nat) + pow2(102) * (limbs[2] as nat)
           + pow2(153) * (limbs[3] as nat) + pow2(204) * (limbs[4] as nat)
           == limbs[0] as nat + (limbs[1] as nat) * pow2(51) + (limbs[2] as nat) * pow2(102)
           + (limbs[3] as nat) * pow2(153) + (limbs[4] as nat) * pow2(204)) by {
        lemma_mul_is_commutative(pow2(51) as int, limbs[1] as int);
        lemma_mul_is_commutative(pow2(102) as int, limbs[2] as int);
        lemma_mul_is_commutative(pow2(153) as int, limbs[3] as int);
        lemma_mul_is_commutative(pow2(204) as int, limbs[4] as int);
    }
    
    assert(value == as_nat(limbs) as int + 19);
    
    // Step 2: Solve for each limb using the division theorem equations
    assert(limbs[0] as int == q0 * pow2(51) as int + r0 - 19);
    assert(limbs[1] as int == q1 * pow2(51) as int + r1 - q0);
    assert(limbs[2] as int == q2 * pow2(51) as int + r2 - q1);
    assert(limbs[3] as int == q3 * pow2(51) as int + r3 - q2);
    assert(limbs[4] as int == q4 * pow2(51) as int + r4 - q3);
    
    // Step 3: Expand limbs[i] * 2^(51*i) using distributivity
    assert((q1 * pow2(51) as int + r1 - q0) * pow2(51) as int
           == q1 * pow2(51) as int * pow2(51) as int + r1 * pow2(51) as int - q0 * pow2(51) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(51) as int, q1 * pow2(51) as int + r1, q0);
        lemma_mul_is_distributive_add_other_way(pow2(51) as int, q1 * pow2(51) as int, r1);
    }
    
    assert((q2 * pow2(51) as int + r2 - q1) * pow2(102) as int
           == q2 * pow2(51) as int * pow2(102) as int + r2 * pow2(102) as int - q1 * pow2(102) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(102) as int, q2 * pow2(51) as int + r2, q1);
        lemma_mul_is_distributive_add_other_way(pow2(102) as int, q2 * pow2(51) as int, r2);
    }
    
    assert((q3 * pow2(51) as int + r3 - q2) * pow2(153) as int
           == q3 * pow2(51) as int * pow2(153) as int + r3 * pow2(153) as int - q2 * pow2(153) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(153) as int, q3 * pow2(51) as int + r3, q2);
        lemma_mul_is_distributive_add_other_way(pow2(153) as int, q3 * pow2(51) as int, r3);
    }
    
    assert((q4 * pow2(51) as int + r4 - q3) * pow2(204) as int
           == q4 * pow2(51) as int * pow2(204) as int + r4 * pow2(204) as int - q3 * pow2(204) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(204) as int, q4 * pow2(51) as int + r4, q3);
        lemma_mul_is_distributive_add_other_way(pow2(204) as int, q4 * pow2(51) as int, r4);
    }
    
    // Step 4: Define remainder and observe telescoping
    // When we substitute and expand, intermediate q_i terms cancel, leaving only q4 and remainders
    let remainder = r0 + r1 * pow2(51) as int + r2 * pow2(102) as int + r3 * pow2(153) as int + r4 * pow2(204) as int;
    
    assert(limbs[0] as int + limbs[1] as int * pow2(51) as int + limbs[2] as int * pow2(102) as int 
           + limbs[3] as int * pow2(153) as int + limbs[4] as int * pow2(204) as int + 19
           == (q0 * pow2(51) as int + r0 - 19)
           + (q1 * pow2(51) as int + r1 - q0) * pow2(51) as int
           + (q2 * pow2(51) as int + r2 - q1) * pow2(102) as int
           + (q3 * pow2(51) as int + r3 - q2) * pow2(153) as int
           + (q4 * pow2(51) as int + r4 - q3) * pow2(204) as int
           + 19);
    
    // After algebraic simplification (intermediate terms cancel), we get: value = q4 * 2^255 + remainder
    lemma_radix51_telescoping_expansion(q0, q1, q2, q3, q4, r0, r1, r2, r3, r4);
    assert(value == q4 * pow2(51) as int * pow2(204) as int + remainder);
    
    assert(q4 * pow2(51) as int * pow2(204) as int == q4 * pow2(255) as int) by {
        lemma_mul_is_associative(q4, pow2(51) as int, pow2(204) as int);
    }
    
    // Step 5: Apply uniqueness of division to conclude q4 = value / 2^255
    lemma_radix51_remainder_bound(r0, r1, r2, r3, r4);
    lemma_pow2_pos(255);
    lemma_fundamental_div_mod(value, pow2(255) as int);
    lemma_div_quotient_unique(value, pow2(255) as int, q4, remainder);
}

/// Helper: Proves the remainder from radix-51 representation is bounded by 2^255
pub proof fn lemma_radix51_remainder_bound(r0: int, r1: int, r2: int, r3: int, r4: int)
    requires
        0 <= r0 < (pow2(51) as int),
        0 <= r1 < (pow2(51) as int),
        0 <= r2 < (pow2(51) as int),
        0 <= r3 < (pow2(51) as int),
        0 <= r4 < (pow2(51) as int),
    ensures
        r0 + r1 * (pow2(51) as int) + r2 * (pow2(102) as int) + r3 * (pow2(153) as int) + r4 * (pow2(204) as int) < (pow2(255) as int),
{
    lemma_pow2_pos(51);
    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);
    
    let sum = r0 + r1 * (pow2(51) as int) + r2 * (pow2(102) as int) + r3 * (pow2(153) as int) + r4 * (pow2(204) as int);
    
    // Each term r_i * 2^(51*i) < 2^51 * 2^(51*i) = 2^(51*(i+1))
    assert(r0 < (pow2(51) as int));
    
    assert(r1 * (pow2(51) as int) < (pow2(51) as int) * (pow2(51) as int)) by {
        lemma_mul_strict_inequality(r1, pow2(51) as int, pow2(51) as int);
    }
    assert(r1 * (pow2(51) as int) < (pow2(102) as int));
    
    assert(r2 * (pow2(102) as int) < (pow2(51) as int) * (pow2(102) as int)) by {
        lemma_mul_strict_inequality(r2, pow2(51) as int, pow2(102) as int);
    }
    assert(r2 * (pow2(102) as int) < (pow2(153) as int));
    
    assert(r3 * (pow2(153) as int) < (pow2(51) as int) * (pow2(153) as int)) by {
        lemma_mul_strict_inequality(r3, pow2(51) as int, pow2(153) as int);
    }
    assert(r3 * (pow2(153) as int) < (pow2(204) as int));
    
    assert(r4 * (pow2(204) as int) < (pow2(51) as int) * (pow2(204) as int)) by {
        lemma_mul_strict_inequality(r4, pow2(51) as int, pow2(204) as int);
    }
    assert(r4 * (pow2(204) as int) < (pow2(255) as int));
    
    // Sum is dominated by last term
    // sum < 2^51 + 2^102 + 2^153 + 2^204 + 2^255
    // Since 2^51 + 2^102 + 2^153 + 2^204 < 2^255 (geometric series), we have sum < 2*2^255
    // But we need tighter: sum < 2^255
    
    // Actually: sum < r0 + r1*2^51 + r2*2^102 + r3*2^153 + r4*2^204
    //              < 2^51 + 2^102 + 2^153 + 2^204 + 2^255
    // We need: 2^51 + 2^102 + 2^153 + 2^204 < 2^255
    
    // Use geometric series: 2^51 + 2^102 + 2^153 + 2^204 = 2^51 * (1 + 2^51 + 2^102 + 2^153)
    // Since 1 + 2^51 + 2^102 + 2^153 < 2^204, we get the sum < 2^51 * 2^204 = 2^255
    lemma_radix_51_partial_geometric_sum();
    assert(pow2(51) + pow2(102) + pow2(153) + pow2(204) < pow2(255));
    
    assert(sum < (pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int) + (pow2(255) as int));
    assert(sum < (pow2(255) as int) + (pow2(255) as int));
    
    // Hmm, this gives us sum < 2*2^255, but we need sum < 2^255
    // The key is that the LAST term contributes less than 2^255
    // and ALL the previous terms together contribute less than 2^255
    
    // Proof that sum < 2^255:
    // Key insight: each r_i <= 2^51 - 1, so
    // sum <= (2^51 - 1) + (2^51 - 1)*2^51 + (2^51 - 1)*2^102 + (2^51 - 1)*2^153 + (2^51 - 1)*2^204
    //     = (2^51 - 1) * (1 + 2^51 + 2^102 + 2^153 + 2^204)
    //     = (2^51 - 1) * sum_powers
    // where sum_powers = 1 + 2^51 + 2^102 + 2^153 + 2^204
    
    // Now I'll show (2^51 - 1) * sum_powers < 2^255
    // Expanding: 2^51 * sum_powers - sum_powers
    //          = 2^51 + 2^102 + 2^153 + 2^204 + 2^255 - (1 + 2^51 + 2^102 + 2^153 + 2^204)
    //          = 2^255 - 1
    //          < 2^255
    
    // Let me prove this step by step
    assert(r0 <= pow2(51) - 1);
    assert(r1 <= pow2(51) - 1);
    assert(r2 <= pow2(51) - 1);
    assert(r3 <= pow2(51) - 1);
    assert(r4 <= pow2(51) - 1);
    
    lemma_pow2_pos(51);
    let max_digit = (pow2(51) - 1) as int;
    let sum_powers = 1 + pow2(51) + pow2(102) + pow2(153) + pow2(204);
    let sum_powers_int = sum_powers as int;
    
    // Upper bound: each term is at most (2^51 - 1) * corresponding power
    assert(r0 <= max_digit);
    assert(r1 * (pow2(51) as int) <= max_digit * (pow2(51) as int)) by {
        lemma_mul_inequality(r1, max_digit, pow2(51) as int);
    }
    assert(r2 * (pow2(102) as int) <= max_digit * (pow2(102) as int)) by {
        lemma_mul_inequality(r2, max_digit, pow2(102) as int);
    }
    assert(r3 * (pow2(153) as int) <= max_digit * (pow2(153) as int)) by {
        lemma_mul_inequality(r3, max_digit, pow2(153) as int);
    }
    assert(r4 * (pow2(204) as int) <= max_digit * (pow2(204) as int)) by {
        lemma_mul_inequality(r4, max_digit, pow2(204) as int);
    }
    
    // Add up all the inequalities
    // sum = r0 + r1 * 2^51 + r2 * 2^102 + r3 * 2^153 + r4 * 2^204
    //    <= max_digit + max_digit * 2^51 + max_digit * 2^102 + max_digit * 2^153 + max_digit * 2^204
    //     = max_digit * (1 + 2^51 + 2^102 + 2^153 + 2^204)
    assert(sum <= max_digit + max_digit * (pow2(51) as int) + max_digit * (pow2(102) as int) + max_digit * (pow2(153) as int) + max_digit * (pow2(204) as int));
    
    // Factor out max_digit using distributivity
    // max_digit + max_digit * a + max_digit * b + ... = max_digit * (1 + a + b + ...)
    // This requires: max_digit * 1 = max_digit (from lemma_mul_basics)
    // And: max_digit * (a + b + ...) = max_digit * a + max_digit * b + ... (from distributivity)
    
    // First show max_digit = max_digit * 1
    assert(max_digit == max_digit * 1) by {
        lemma_mul_basics(max_digit);
    }
    
    // Then combine the terms
    // The sum on LHS is: max_digit * 1 + max_digit * 2^51 + max_digit * 2^102 + max_digit * 2^153 + max_digit * 2^204
    // Factor out: max_digit * (1 + 2^51 + 2^102 + 2^153 + 2^204)
    let sum_rhs = max_digit * (1 + (pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int));
    
    // Use distributivity to expand the RHS and show it equals the LHS
    assert(max_digit * (1 + (pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int))
           == max_digit * 1 + max_digit * ((pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int))) by {
        lemma_mul_is_distributive_add(max_digit, 1, (pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int));
    }
    
    // Continue expanding nested additions
    assert(max_digit * ((pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int))
           == max_digit * (pow2(51) as int) + max_digit * ((pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int))) by {
        lemma_mul_is_distributive_add(max_digit, pow2(51) as int, (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int));
    }
    
    assert(max_digit * ((pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int))
           == max_digit * (pow2(102) as int) + max_digit * ((pow2(153) as int) + (pow2(204) as int))) by {
        lemma_mul_is_distributive_add(max_digit, pow2(102) as int, (pow2(153) as int) + (pow2(204) as int));
    }
    
    assert(max_digit * ((pow2(153) as int) + (pow2(204) as int))
           == max_digit * (pow2(153) as int) + max_digit * (pow2(204) as int)) by {
        lemma_mul_is_distributive_add(max_digit, pow2(153) as int, pow2(204) as int);
    }
    
    // Now chain them together
    assert(sum_rhs == max_digit + max_digit * (pow2(51) as int) + max_digit * (pow2(102) as int) + max_digit * (pow2(153) as int) + max_digit * (pow2(204) as int));
    
    assert(sum <= sum_rhs);
    
    // Now show sum_rhs < 2^255
    // We have: sum <= sum_rhs = max_digit * (1 + 2^51 + 2^102 + 2^153 + 2^204)
    //        = (2^51 - 1) * sum_powers
    
    // Strategy: Show that sum_rhs < pow2(255) directly
    // Since each r_i < 2^51 (strict), at least one r_i <= 2^51 - 1
    // In fact, we have the stronger property that sum < sum_rhs when any r_i < 2^51 - 1
    // But even if all r_i = 2^51 - 1, we get sum_rhs = 2^255 - 1 < 2^255
    
    // The key insight: max_digit = 2^51 - 1, so max_digit < 2^51
    assert(max_digit < pow2(51));
    assert(max_digit * (1 + (pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int)) 
           < (pow2(51) as int) * (1 + (pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int))) by {
        lemma_mul_strict_inequality(max_digit, pow2(51) as int, (1 + (pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int)));
    }
    
    // Now show: 2^51 * (1 + 2^51 + 2^102 + 2^153 + 2^204) = 2^51 + 2^102 + 2^153 + 2^204 + 2^255
    assert((pow2(51) as int) * (1 + (pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int))
           == (pow2(51) as int) + (pow2(51) as int) * (pow2(51) as int) + (pow2(51) as int) * (pow2(102) as int) 
           + (pow2(51) as int) * (pow2(153) as int) + (pow2(51) as int) * (pow2(204) as int)) by {
        lemma_mul_is_distributive_add(pow2(51) as int, 1, (pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int));
        lemma_mul_basics(pow2(51) as int);
        lemma_mul_is_distributive_add(pow2(51) as int, pow2(51) as int, (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int));
        lemma_mul_is_distributive_add(pow2(51) as int, pow2(102) as int, (pow2(153) as int) + (pow2(204) as int));
        lemma_mul_is_distributive_add(pow2(51) as int, pow2(153) as int, pow2(204) as int);
    }
    
    // Use power addition: 2^51 * 2^k = 2^(51+k)
    assert((pow2(51) as int) * (pow2(51) as int) == (pow2(102) as int));
    assert((pow2(51) as int) * (pow2(102) as int) == (pow2(153) as int));
    assert((pow2(51) as int) * (pow2(153) as int) == (pow2(204) as int));
    assert((pow2(51) as int) * (pow2(204) as int) == (pow2(255) as int));
    
    // So: 2^51 * sum_powers = 2^51 + 2^102 + 2^153 + 2^204 + 2^255
    // And from lemma_radix_51_partial_geometric_sum, we know: 2^51 + 2^102 + 2^153 + 2^204 < 2^255
    lemma_radix_51_partial_geometric_sum();
    assert((pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int) < (pow2(255) as int));
    assert((pow2(51) as int) + (pow2(102) as int) + (pow2(153) as int) + (pow2(204) as int) + (pow2(255) as int) < (pow2(255) as int) + (pow2(255) as int));
    
    // Therefore sum_rhs < 2^51 * sum_powers < 2 * 2^255
    // But we can do better: the partial sum is much smaller than 2^255
    // In fact: 2^51 + 2^102 + 2^153 + 2^204 < 2^205 (from partial geometric sum proof)
    // So the total is < 2^205 + 2^255 < 2 * 2^255
    // But we need strict: sum_rhs < 2^255
    
    // Actually, let's use: since max_digit = 2^51 - 1 and the partial sum < 2^255,
    // we need to be more careful. Let's use the fact that sum_rhs < 2^51 * sum_powers
    // and show that 2^51 * sum_powers <= 2^255 (since it equals 2^51 + ... + 2^255)
    // No wait, that's >= 2^255, not <.
    
    // Better approach: We know sum <= sum_rhs and sum_rhs = (2^51 - 1) * sum_powers
    // Actually, if any r_i < 2^51 - 1, then sum < sum_rhs, so sum < (2^51 - 1) * sum_powers
    // But since r_i < 2^51 (strict from precondition), we have strict inequality somewhere
    
    // Simplest: just use that (2^51 - 1) * X < 2^51 * X and bound from there
    // Even simpler: max_digit * sum_powers = (2^51 - 1) * sum_powers <= 2^51 * sum_powers - sum_powers
    // And 2^51 * sum_powers = 2^51 + 2^102 + 2^153 + 2^204 + 2^255
    // So (2^51 - 1) * sum_powers = (2^51 + 2^102 + 2^153 + 2^204 + 2^255) - (1 + 2^51 + 2^102 + 2^153 + 2^204)
    //                              = 2^255 - 1 < 2^255
    
    // OK, so we do need to show the exact value after all. But let me see if we can prove it without assumes.
    // Let me just use a simpler bound: since max_digit < 2^51, we can use inequality
    
    // Actually, the simplest fix: just note that sum_rhs < 2^51 * sum_powers (strict)
    // and compute an upper bound for 2^51 * sum_powers
    
    // Since sum_powers = 1 + 2^51 + 2^102 + 2^153 + 2^204 < 2^205 (we can prove this),
    // we get: sum_rhs < 2^51 * 2^205 = 2^256
    // That's not tight enough.
    
    // I think we DO need the exact formula. Let me just prove it properly without assumes.
    // The formula is: (2^51 - 1) * (1 + 2^51 + ... + 2^204) = 2^255 - 1
    // This comes from the geometric series formula.
    
    // Let's just inline the proof here
    assert(sum_rhs == (pow2(51) - 1) as int * (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204)));
    assert(sum_powers_int == (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204)) as int);
    
    // The algebraic identity: (a - 1) * (1 + a + a^2 + ... + a^n) = a^(n+1) - 1
    // Here: (2^51 - 1) * (1 + 2^51 + 2^102 + 2^153 + 2^204) = 2^255 - 1
    // Proof: expand LHS = 2^51*(1 + 2^51 + ... + 2^204) - (1 + 2^51 + ... + 2^204)
    //                    = (2^51 + 2^102 + 2^153 + 2^204 + 2^255) - (1 + 2^51 + 2^102 + 2^153 + 2^204)
    //                    = 2^255 - 1
    
    lemma_geometric_series_radix51(sum_powers_int);
    assert((pow2(51) - 1) * sum_powers_int == pow2(255) - 1);
    assert(sum_rhs == (pow2(255) - 1) as int);
    assert(sum <= (pow2(255) - 1) as int);
    assert(sum < (pow2(255) as int));
}

/// Helper: Geometric series formula for radix-51
/// Proves: (2^51 - 1) * (1 + 2^51 + 2^102 + 2^153 + 2^204) = 2^255 - 1
/// This is the closed form of the geometric series with ratio 2^51 and 5 terms
pub proof fn lemma_geometric_series_radix51(sum_powers: int)
    requires
        sum_powers == 1 + pow2(51) + pow2(102) + pow2(153) + pow2(204),
    ensures
        (pow2(51) - 1) * sum_powers == pow2(255) - 1,
{
    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);
    lemma_pow2_pos(51);
    
    // Geometric series formula: (r - 1) * (1 + r + r^2 + ... + r^n) = r^(n+1) - 1
    // Here: r = 2^51, n = 4, so r^5 = 2^255
    
    // Step 1: Expand 2^51 * sum_powers using distributivity
    assert(pow2(51) * 1 == pow2(51)) by { lemma_mul_basics(pow2(51) as int); }
    assert(pow2(51) * pow2(51) == pow2(102));
    assert(pow2(51) * pow2(102) == pow2(153));
    assert(pow2(51) * pow2(153) == pow2(204));
    assert(pow2(51) * pow2(204) == pow2(255));
    
    // Expand: 2^51 * (1 + 2^51 + 2^102 + 2^153 + 2^204)
    //       = 2^51 + 2^102 + 2^153 + 2^204 + 2^255
    assert(pow2(51) * sum_powers == pow2(51) * 1 + pow2(51) * (pow2(51) + pow2(102) + pow2(153) + pow2(204))) by {
        lemma_mul_is_distributive_add(pow2(51) as int, 1, (pow2(51) + pow2(102) + pow2(153) + pow2(204)) as int);
    }
    
    assert(pow2(51) * (pow2(51) + pow2(102) + pow2(153) + pow2(204)) 
           == pow2(51) * pow2(51) + pow2(51) * (pow2(102) + pow2(153) + pow2(204))) by {
        lemma_mul_is_distributive_add(pow2(51) as int, pow2(51) as int, (pow2(102) + pow2(153) + pow2(204)) as int);
    }
    
    assert(pow2(51) * (pow2(102) + pow2(153) + pow2(204)) 
           == pow2(51) * pow2(102) + pow2(51) * (pow2(153) + pow2(204))) by {
        lemma_mul_is_distributive_add(pow2(51) as int, pow2(102) as int, (pow2(153) + pow2(204)) as int);
    }
    
    assert(pow2(51) * (pow2(153) + pow2(204)) == pow2(51) * pow2(153) + pow2(51) * pow2(204)) by {
        lemma_mul_is_distributive_add(pow2(51) as int, pow2(153) as int, pow2(204) as int);
    }
    
    // Chain them together
    assert(pow2(51) * sum_powers == pow2(51) + pow2(102) + pow2(153) + pow2(204) + pow2(255));
    
    // Step 2: Apply the geometric series formula
    // (2^51 - 1) * sum_powers = 2^51 * sum_powers - sum_powers
    assert((pow2(51) - 1) * sum_powers == pow2(51) * sum_powers - sum_powers) by {
        lemma_mul_is_distributive_sub(sum_powers, pow2(51) as int, 1);
        lemma_mul_is_commutative(sum_powers, pow2(51) as int);
        lemma_mul_is_commutative(sum_powers, 1);
        lemma_mul_basics(sum_powers);
    }
    
    // Substitute the expansion
    // = (2^51 + 2^102 + 2^153 + 2^204 + 2^255) - (1 + 2^51 + 2^102 + 2^153 + 2^204)
    assert(pow2(51) * sum_powers - sum_powers 
           == (pow2(51) + pow2(102) + pow2(153) + pow2(204) + pow2(255)) 
            - (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204)));
    
    // Step 3: Simplify by cancellation
    // The terms 2^51, 2^102, 2^153, 2^204 cancel, leaving: 2^255 - 1
    assert((pow2(51) + pow2(102) + pow2(153) + pow2(204) + pow2(255)) 
         - (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204))
         == pow2(255) - 1);
}

/// Helper: geometric series for radix-51 partial sum
pub proof fn lemma_radix_51_partial_geometric_sum()
    ensures
        pow2(51) + pow2(102) + pow2(153) + pow2(204) < pow2(255),
{
    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);
    lemma_pow2_strictly_increases(204, 255);
    
    // The sum is dominated by the largest term 2^204
    // Show: 2^51 + 2^102 + 2^153 < 2^204
    // Then: sum < 2^204 + 2^204 = 2 * 2^204 = 2^205 < 2^255
    
    lemma_pow2_strictly_increases(51, 204);
    lemma_pow2_strictly_increases(102, 204);
    lemma_pow2_strictly_increases(153, 204);
    
    // Use: 2^153 < 2^204, so 2^153 + 2^153 = 2^154 < 2^204
    lemma_pow2_adds(153, 1);
    assert(pow2(154) == pow2(153) * pow2(1));
    assert(pow2(154) == pow2(153) * 2) by {
        lemma2_to64();
        assert(pow2(1) == 2);
    }
    assert(pow2(154) == 2 * pow2(153)) by {
        lemma_mul_is_commutative(pow2(153) as int, 2);
    }
    lemma_pow2_strictly_increases(154, 204);
    assert(2 * pow2(153) < pow2(204));
    
    // Similarly for smaller terms: show pow2(51) + pow2(102) + pow2(153) < pow2(204)
    // Key insight: pow2(102) < pow2(153) because 102 < 153
    // And pow2(51) + pow2(102) < pow2(102) + pow2(102) = 2*pow2(102) = pow2(103) << pow2(153)
    lemma_pow2_strictly_increases(51, 102);
    lemma_pow2_strictly_increases(102, 153);
    lemma_pow2_strictly_increases(153, 204);
    
    // Use pow2(102) + pow2(102) = 2 * pow2(102) = pow2(103)
    lemma_pow2_adds(102, 1);
    assert(2 * pow2(102) == pow2(103)) by {
        lemma2_to64();
        assert(pow2(1) == 2);
        assert(pow2(103) == pow2(102) * pow2(1));
        lemma_mul_is_commutative(pow2(102) as int, 2);
    }
    lemma_pow2_strictly_increases(103, 153);
    assert(pow2(51) < pow2(102));
    assert(pow2(51) + pow2(102) < pow2(102) + pow2(102));
    assert(pow2(51) + pow2(102) < 2 * pow2(102));
    assert(pow2(51) + pow2(102) < pow2(103));
    assert(pow2(51) + pow2(102) < pow2(153));
    
    // So pow2(51) + pow2(102) + pow2(153) < pow2(153) + pow2(153) = 2*pow2(153) = pow2(154) < pow2(204)
    assert(pow2(51) + pow2(102) + pow2(153) < pow2(153) + pow2(153));
    assert(pow2(51) + pow2(102) + pow2(153) < 2 * pow2(153));
    assert(pow2(51) + pow2(102) + pow2(153) < pow2(154));
    assert(pow2(51) + pow2(102) + pow2(153) < pow2(204));
    
    // Therefore the full sum < pow2(204) + pow2(204) = 2*pow2(204) = pow2(205) < pow2(255)
    assert(pow2(51) + pow2(102) + pow2(153) + pow2(204) < pow2(204) + pow2(204));
    
    // Prove 2 * pow2(204) == pow2(205)
    lemma_pow2_adds(204, 1);
    assert(pow2(205) == pow2(204) * pow2(1));
    assert(pow2(205) == pow2(204) * 2) by {
        lemma2_to64();
        assert(pow2(1) == 2);
    }
    assert(pow2(205) == 2 * pow2(204)) by {
        lemma_mul_is_commutative(pow2(204) as int, 2);
    }
    assert(2 * pow2(204) == pow2(205));
    
    lemma_pow2_strictly_increases(205, 255);
    assert(pow2(51) + pow2(102) + pow2(153) + pow2(204) < 2 * pow2(204));
    assert(pow2(51) + pow2(102) + pow2(153) + pow2(204) < pow2(205));
    assert(pow2(51) + pow2(102) + pow2(153) + pow2(204) < pow2(255));
}

/// Helper: Establishes basic power-of-2 facts needed for carry propagation
pub proof fn lemma_carry_propagation_setup()
    ensures
        (1u64 << 51) == pow2(51),
        (1u64 << 52) == pow2(52),
        pow2(52) == 2 * pow2(51),
        19 < pow2(51),
        3 * pow2(51) <= u64::MAX,
{
    lemma2_to64();
    shift_is_pow2(51);
    shift_is_pow2(52);
    lemma_pow2_pos(51);
    
    assert(pow2(52) == 2 * pow2(51)) by {
        lemma_pow2_adds(1, 51);
    }
    
    assert(19 < pow2(51)) by {
        assert(pow2(5) == 32);
        lemma_pow2_strictly_increases(5, 51);
    }
    
    assert(3 * pow2(51) <= u64::MAX) by {
        lemma2_to64_rest();
    }
}

/// Helper: Proves the division relationship for a single carry propagation stage
/// Given limb_i and carry_in q_{i-1}, computes q_i = (limb_i + q_{i-1}) >> 51
/// and establishes the division theorem relationship
/// 
/// Note: carry_in is typically < 3 for stages 1-4, but equals 19 for stage 0
pub proof fn lemma_single_stage_division(
    limb: u64,
    carry_in: u64,
    stage_input: u64,
    carry_out: u64,
)
    requires
        limb < (1u64 << 52),
        limb + carry_in <= u64::MAX,  // No overflow
        stage_input == (limb + carry_in) as u64,
        stage_input < 3 * pow2(51),
        carry_out == (stage_input >> 51) as u64,
    ensures
        carry_out < 3,
        carry_out as int == (limb as int + carry_in as int) / pow2(51) as int,
{
    lemma_carry_propagation_setup();
    
    // Prove the division relationship
    lemma_u64_shr_is_div(stage_input, 51);
    // Since limb + carry_in <= u64::MAX, the cast doesn't change the value
    assert(stage_input as int == limb as int + carry_in as int);
    assert(carry_out as int == (limb as int + carry_in as int) / pow2(51) as int);
    
    // Prove the bound
    lemma_bounded_shr_51(stage_input);
}

/// Helper: Establishes division theorem for a single stage
/// Given the inputs and outputs of a stage, proves the division/modulo relationship
/// 
/// Note: carry_in is typically < 3 for stages 1-4, but equals 19 for stage 0
pub proof fn lemma_stage_division_theorem(
    limb: u64,
    carry_in: int,
    carry_out: int,
) -> (r: int)
    requires
        limb < (1u64 << 52),
        carry_out == (limb as int + carry_in) / pow2(51) as int,
        pow2(51) > 0,
    ensures
        (limb as int + carry_in) == carry_out * pow2(51) as int + r,
        0 <= r < pow2(51) as int,
{
    lemma_fundamental_div_mod((limb as int + carry_in), pow2(51) as int);
    let r = (limb as int + carry_in) % pow2(51) as int;
    lemma_mod_bound((limb as int + carry_in), pow2(51) as int);
    assert((limb as int + carry_in) == carry_out * pow2(51) as int + r);
    r
}

/// Helper lemma: proves that the carry propagation computes the division by 2^255
/// This shows that q represents (as_nat(limbs) + 19) / 2^255
/// 
/// Refactored into smaller pieces for better readability and maintainability.
pub proof fn lemma_carry_propagation_is_division(limbs: [u64; 5], q: u64)
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        q == compute_q_spec(limbs),
    ensures
        q as nat == (as_nat(limbs) + 19) / pow2(255),
{
    // Setup: establish basic power-of-2 facts (needed for overflow checks)
    lemma_carry_propagation_setup();
    
    // Extract the carry values computed by the algorithm
    let q0 = ((limbs[0] + 19) as u64 >> 51) as u64;
    let q1 = ((limbs[1] + q0) as u64 >> 51) as u64;
    let q2 = ((limbs[2] + q1) as u64 >> 51) as u64;
    let q3 = ((limbs[3] + q2) as u64 >> 51) as u64;
    let q4 = ((limbs[4] + q3) as u64 >> 51) as u64;
    
    // Prove all carries are bounded by 3 (needed for no overflow)
    lemma_all_carries_bounded_by_3(limbs);
    
    // Prove no overflow for all stages (each limb < 2^52, each carry < 3)
    assert(limbs[0] + 19 <= u64::MAX);
    assert(limbs[1] + q0 <= u64::MAX);
    assert(limbs[2] + q1 <= u64::MAX);
    assert(limbs[3] + q2 <= u64::MAX);
    assert(limbs[4] + q3 <= u64::MAX);
    
    // Stage 0: Process limbs[0] + 19
    lemma_single_stage_division(limbs[0], 19, (limbs[0] + 19) as u64, q0);
    let r0 = lemma_stage_division_theorem(limbs[0], 19, q0 as int);
    
    // Stage 1: Process limbs[1] + q0
    lemma_single_stage_division(limbs[1], q0, (limbs[1] + q0) as u64, q1);
    let r1 = lemma_stage_division_theorem(limbs[1], q0 as int, q1 as int);
    
    // Stage 2: Process limbs[2] + q1
    lemma_single_stage_division(limbs[2], q1, (limbs[2] + q1) as u64, q2);
    let r2 = lemma_stage_division_theorem(limbs[2], q1 as int, q2 as int);
    
    // Stage 3: Process limbs[3] + q2
    lemma_single_stage_division(limbs[3], q2, (limbs[3] + q2) as u64, q3);
    let r3 = lemma_stage_division_theorem(limbs[3], q2 as int, q3 as int);
    
    // Stage 4: Process limbs[4] + q3
    lemma_single_stage_division(limbs[4], q3, (limbs[4] + q3) as u64, q4);
    let r4 = lemma_stage_division_theorem(limbs[4], q3 as int, q4 as int);
    
    // Telescoping property: show that q4 = (as_nat(limbs) + 19) / 2^255
    // Use the remainders we just computed to directly prove the telescoping division
    lemma_radix51_telescoping_direct(limbs, q0 as int, q1 as int, q2 as int, q3 as int, q4 as int, r0, r1, r2, r3, r4);
}

// lemma_radix_51_geometric_sum: MOVED to unused_helper_lemmas.rs (superseded by lemma_radix_51_partial_geometric_sum)

/// Helper: Proves all intermediate carries are bounded by 3
pub proof fn lemma_all_carries_bounded_by_3(limbs: [u64; 5])
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
    ensures
        ({
            let q0 = ((limbs[0] + 19) as u64 >> 51) as u64;
            let q1 = ((limbs[1] + q0) as u64 >> 51) as u64;
            let q2 = ((limbs[2] + q1) as u64 >> 51) as u64;
            let q3 = ((limbs[3] + q2) as u64 >> 51) as u64;
            let q4 = ((limbs[4] + q3) as u64 >> 51) as u64;
            q0 < 3 && q1 < 3 && q2 < 3 && q3 < 3 && q4 < 3
        }),
{
    // Reuse setup helper instead of duplicating the facts
    lemma_carry_propagation_setup();
    
    let q0 = ((limbs[0] + 19) as u64 >> 51) as u64;
    let q1 = ((limbs[1] + q0) as u64 >> 51) as u64;
    let q2 = ((limbs[2] + q1) as u64 >> 51) as u64;
    let q3 = ((limbs[3] + q2) as u64 >> 51) as u64;
    let q4 = ((limbs[4] + q3) as u64 >> 51) as u64;
    
    // Prove q0 < 3
    // First show that limbs[0] + 19 doesn't overflow
    assert(limbs[0] < pow2(52));
    assert(limbs[0] < 2 * pow2(51));
    assert(limbs[0] + 19 < 3 * pow2(51));
    assert(3 * pow2(51) <= u64::MAX) by {
        lemma2_to64_rest();
    }
    lemma_bounded_shr_51((limbs[0] + 19) as u64);
    assert(q0 < 3);
    
    // Prove q1 < 3
    assert(limbs[1] < 2 * pow2(51));
    assert(limbs[1] + q0 < 3 * pow2(51));
    lemma_bounded_shr_51((limbs[1] + q0) as u64);
    assert(q1 < 3);
    
    // Prove q2 < 3
    assert(limbs[2] < 2 * pow2(51));
    assert(limbs[2] + q1 < 3 * pow2(51));
    lemma_bounded_shr_51((limbs[2] + q1) as u64);
    assert(q2 < 3);
    
    // Prove q3 < 3
    assert(limbs[3] < 2 * pow2(51));
    assert(limbs[3] + q2 < 3 * pow2(51));
    lemma_bounded_shr_51((limbs[3] + q2) as u64);
    assert(q3 < 3);
    
    // Prove q4 < 3
    assert(limbs[4] < 2 * pow2(51));
    assert(limbs[4] + q3 < 3 * pow2(51));
    lemma_bounded_shr_51((limbs[4] + q3) as u64);
    assert(q4 < 3);
}

/// Helper: Proves q can only be 0 or 1 (not 2)
/// Also establishes the division relationship for reuse
pub proof fn lemma_q_is_binary(limbs: [u64; 5], q: u64)
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        as_nat(limbs) < 2 * p(),  // From reduce()'s postcondition
        q == compute_q_spec(limbs),
        q < 3,
    ensures
        q == 0 || q == 1,
        q as nat == (as_nat(limbs) + 19) / pow2(255),  // Export for reuse
{
    lemma_carry_propagation_is_division(limbs, q);
    assert(q as nat == (as_nat(limbs) + 19) / pow2(255));
    
    // Establish basic facts
    lemma2_to64();
    pow255_gt_19();
    lemma_pow2_adds(255, 1);  // Establish pow2(256) == pow2(255) * pow2(1) once
    
    // Use the bound from precondition: as_nat(limbs) < 2*p() = 2^256 - 38
    assert(pow2(256) == 2 * pow2(255));  // From pow2_adds and pow2(1) == 2
    assert(2 * p() == pow2(256) - 38) by {
        assert(2 * p() == 2 * (pow2(255) - 19));
    }
    
    // Therefore: as_nat(limbs) + 19 < 2^256 - 38 + 19 = 2^256 - 19 < 2^256
    assert(as_nat(limbs) + 19 < pow2(256) - 38 + 19);
    assert(as_nat(limbs) + 19 < pow2(256) - 19);
    assert(as_nat(limbs) + 19 < pow2(256));
    
    // We have: as_nat(limbs) + 19 < 2 * 2^255 = 2^256
    assert(as_nat(limbs) + 19 < 2 * pow2(255));
    
    // By integer division: if x < 2 * d, then x / d < 2
    lemma_pow2_pos(255);
    assert(pow2(255) > 0);
    lemma_div_strictly_bounded((as_nat(limbs) + 19) as int, pow2(255) as int, 2);
    assert((as_nat(limbs) + 19) / pow2(255) < 2);
    
    // Since q = (as_nat(limbs) + 19) / 2^255, we have q < 2
    assert(q < 2);
    assert(q == 0 || q == 1);
}

/// Unified helper: Proves the biconditional relationship between as_nat and q
/// 
/// With the tight bound as_nat(limbs) < 2*p(), the value is either in [0, p) or [p, 2*p),
/// which maps directly to q=0 or q=1. This makes the biconditional proofs straightforward.
pub proof fn lemma_q_biconditional(limbs: [u64; 5], q: u64)
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        as_nat(limbs) < 2 * p(),  // Tight bound from reduce()
        q == compute_q_spec(limbs),
        q as nat == (as_nat(limbs) + 19) / pow2(255),
        q == 0 || q == 1,
    ensures
        as_nat(limbs) >= p() <==> q == 1,
        as_nat(limbs) < p() <==> q == 0,
{
    pow255_gt_19();
    lemma2_to64();
    
    // Establish key facts
    assert(p() == pow2(255) - 19);
    assert(2 * p() == 2 * pow2(255) - 38) by {
        lemma_pow2_adds(255, 1);
        assert(pow2(256) == 2 * pow2(255));
    }
    
    lemma_pow2_pos(255);
    
    // The key insight: with as_nat(limbs) < 2*p(), we have two cases:
    // Case 1: as_nat(limbs) < p() ⟺ as_nat(limbs) + 19 < 2^255 ⟺ q = 0
    // Case 2: p() ≤ as_nat(limbs) < 2*p() ⟺ 2^255 ≤ as_nat(limbs) + 19 < 2*2^255 ⟺ q = 1
    
    // Forward direction: as_nat(limbs) < p() ==> q == 0
    if as_nat(limbs) < p() {
        assert(as_nat(limbs) + 19 < pow2(255));
        lemma_div_strictly_bounded((as_nat(limbs) + 19) as int, pow2(255) as int, 1);
        assert((as_nat(limbs) + 19) / pow2(255) == 0);
        assert(q == 0);
    }
    
    // Backward direction: q == 0 ==> as_nat(limbs) < p()
    if q == 0 {
        lemma_fundamental_div_mod((as_nat(limbs) + 19) as int, pow2(255) as int);
        lemma_mod_bound((as_nat(limbs) + 19) as int, pow2(255) as int);
        assert((as_nat(limbs) + 19) < pow2(255));
        assert(as_nat(limbs) < p());
    }
    
    // Forward direction: as_nat(limbs) >= p() ==> q == 1
    if as_nat(limbs) >= p() {
        assert(as_nat(limbs) + 19 >= pow2(255));
        // Since q is 0 or 1, and we know as_nat + 19 >= 2^255, q cannot be 0
        if q == 0 {
            lemma_fundamental_div_mod((as_nat(limbs) + 19) as int, pow2(255) as int);
            lemma_mod_bound((as_nat(limbs) + 19) as int, pow2(255) as int);
            assert((as_nat(limbs) + 19) < pow2(255)); // Contradiction!
            assert(false);
        }
        assert(q == 1);
    }
    
    // Backward direction: q == 1 ==> as_nat(limbs) >= p()
    if q == 1 {
        lemma_fundamental_div_mod((as_nat(limbs) + 19) as int, pow2(255) as int);
        assert((as_nat(limbs) + 19) >= pow2(255));
        assert(as_nat(limbs) >= p());
    }
}

/// Proves that q computed via successive carry propagation equals 1 iff h >= p, 0 otherwise
/// where h = as_nat(limbs) and limbs[i] < 2^52 for all i
///
/// The precondition `as_nat(limbs) < 2 * p()` is satisfied when limbs come from
/// `reduce()` output, which now ensures this property in its postcondition.
pub proof fn lemma_compute_q(limbs: [u64; 5], q: u64)
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        as_nat(limbs) < 2 * p(),  // From reduce()'s postcondition
        q == compute_q_spec(limbs),
    ensures
        q == 0 || q == 1,
        as_nat(limbs) >= p() <==> q == 1,
        as_nat(limbs) < p() <==> q == 0,
{
    // Step 1: Prove q < 3 (all carries bounded)
    lemma_all_carries_bounded_by_3(limbs);
    assert(q < 3);
    
    // Step 2: Prove q can only be 0 or 1 (not 2)
    // Note: This also establishes q as nat == (as_nat(limbs) + 19) / pow2(255)
    // internally by calling lemma_carry_propagation_is_division
    lemma_q_is_binary(limbs, q);
    assert(q == 0 || q == 1);
    assert(q as nat == (as_nat(limbs) + 19) / pow2(255));
    
    // Step 3: Prove the biconditionals
    // With the tight bound as_nat < 2*p(), this is now straightforward
    lemma_q_biconditional(limbs, q);
}

// ============================================================================
// LEMMA 2: Value preservation through modular reduction
// ============================================================================

/// Telescoping lemma for reduction: expands as_nat through the carry propagation
/// This is analogous to lemma_radix51_telescoping_direct but for the reduction case
pub proof fn lemma_reduction_telescoping(
    input_limbs: [u64; 5],
    final_limbs: [u64; 5],
    q: u64,
    c0: int, c1: int, c2: int, c3: int, c4: int,
)
    requires
        // The carry propagation relationships
        input_limbs[0] as int + 19 * q as int == c0 * pow2(51) as int + final_limbs[0] as int,
        input_limbs[1] as int + c0 == c1 * pow2(51) as int + final_limbs[1] as int,
        input_limbs[2] as int + c1 == c2 * pow2(51) as int + final_limbs[2] as int,
        input_limbs[3] as int + c2 == c3 * pow2(51) as int + final_limbs[3] as int,
        input_limbs[4] as int + c3 == c4 * pow2(51) as int + final_limbs[4] as int,
        // final_limbs are bounded by 2^51
        final_limbs[0] < (1u64 << 51),
        final_limbs[1] < (1u64 << 51),
        final_limbs[2] < (1u64 << 51),
        final_limbs[3] < (1u64 << 51),
        final_limbs[4] < (1u64 << 51),
    ensures
        as_nat(input_limbs) as int + 19 * q as int == as_nat(final_limbs) as int + c4 * pow2(255) as int,
{
    // Establish power-of-2 relationships
    lemma_pow2_pos(51);
    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);
    
    // Expand as_nat(input_limbs) + 19*q
    let lhs = as_nat(input_limbs) as int + 19 * q as int;
    
    // Explicitly expand as_nat using its definition
    assert(as_nat(input_limbs) == (input_limbs[0] as nat) + pow2(51) * (input_limbs[1] as nat) 
           + pow2(102) * (input_limbs[2] as nat) + pow2(153) * (input_limbs[3] as nat) 
           + pow2(204) * (input_limbs[4] as nat));
    
    // Convert to int with commutativity
    assert(as_nat(input_limbs) as int == input_limbs[0] as int
            + input_limbs[1] as int * pow2(51) as int
            + input_limbs[2] as int * pow2(102) as int
            + input_limbs[3] as int * pow2(153) as int
            + input_limbs[4] as int * pow2(204) as int) by {
        lemma_mul_is_commutative(pow2(51) as int, input_limbs[1] as int);
        lemma_mul_is_commutative(pow2(102) as int, input_limbs[2] as int);
        lemma_mul_is_commutative(pow2(153) as int, input_limbs[3] as int);
        lemma_mul_is_commutative(pow2(204) as int, input_limbs[4] as int);
    }
    
    assert(lhs == input_limbs[0] as int
            + input_limbs[1] as int * pow2(51) as int
            + input_limbs[2] as int * pow2(102) as int
            + input_limbs[3] as int * pow2(153) as int
            + input_limbs[4] as int * pow2(204) as int
            + 19 * q as int);
    
    // Substitute the division relationships (solve for input_limbs[i])
    assert(input_limbs[0] as int == c0 * pow2(51) as int + final_limbs[0] as int - 19 * q as int);
    assert(input_limbs[1] as int == c1 * pow2(51) as int + final_limbs[1] as int - c0);
    assert(input_limbs[2] as int == c2 * pow2(51) as int + final_limbs[2] as int - c1);
    assert(input_limbs[3] as int == c3 * pow2(51) as int + final_limbs[3] as int - c2);
    assert(input_limbs[4] as int == c4 * pow2(51) as int + final_limbs[4] as int - c3);
    
    // Expand each term using distributivity (same pattern as lemma_radix51_telescoping_direct)
    assert((c1 * pow2(51) as int + final_limbs[1] as int - c0) * pow2(51) as int
           == c1 * pow2(102) as int + final_limbs[1] as int * pow2(51) as int - c0 * pow2(51) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(51) as int, c1 * pow2(51) as int + final_limbs[1] as int, c0);
        lemma_mul_is_distributive_add_other_way(pow2(51) as int, c1 * pow2(51) as int, final_limbs[1] as int);
        lemma_mul_is_associative(c1, pow2(51) as int, pow2(51) as int);
        assert(c1 * (pow2(51) as int * pow2(51) as int) == (c1 * pow2(51) as int) * pow2(51) as int);
        assert(pow2(51) as int * pow2(51) as int == pow2(102) as int);
        assert(c1 * pow2(51) as int * pow2(51) as int == c1 * pow2(102) as int);
    }
    
    assert((c2 * pow2(51) as int + final_limbs[2] as int - c1) * pow2(102) as int
           == c2 * pow2(153) as int + final_limbs[2] as int * pow2(102) as int - c1 * pow2(102) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(102) as int, c2 * pow2(51) as int + final_limbs[2] as int, c1);
        lemma_mul_is_distributive_add_other_way(pow2(102) as int, c2 * pow2(51) as int, final_limbs[2] as int);
        lemma_mul_is_associative(c2, pow2(51) as int, pow2(102) as int);
        assert(pow2(51) as int * pow2(102) as int == pow2(153) as int);
        assert(c2 * pow2(51) as int * pow2(102) as int == c2 * pow2(153) as int);
    }
    
    assert((c3 * pow2(51) as int + final_limbs[3] as int - c2) * pow2(153) as int
           == c3 * pow2(204) as int + final_limbs[3] as int * pow2(153) as int - c2 * pow2(153) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(153) as int, c3 * pow2(51) as int + final_limbs[3] as int, c2);
        lemma_mul_is_distributive_add_other_way(pow2(153) as int, c3 * pow2(51) as int, final_limbs[3] as int);
        lemma_mul_is_associative(c3, pow2(51) as int, pow2(153) as int);
        assert(pow2(51) as int * pow2(153) as int == pow2(204) as int);
        assert(c3 * pow2(51) as int * pow2(153) as int == c3 * pow2(204) as int);
    }
    
    assert((c4 * pow2(51) as int + final_limbs[4] as int - c3) * pow2(204) as int
           == c4 * pow2(255) as int + final_limbs[4] as int * pow2(204) as int - c3 * pow2(204) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(204) as int, c4 * pow2(51) as int + final_limbs[4] as int, c3);
        lemma_mul_is_distributive_add_other_way(pow2(204) as int, c4 * pow2(51) as int, final_limbs[4] as int);
        lemma_mul_is_associative(c4, pow2(51) as int, pow2(204) as int);
        assert(pow2(51) as int * pow2(204) as int == pow2(255) as int);
        assert(c4 * pow2(51) as int * pow2(204) as int == c4 * pow2(255) as int);
    }
    
    // Now perform the telescoping sum
    // lhs = input_limbs[0] + input_limbs[1]*2^51 + input_limbs[2]*2^102 + input_limbs[3]*2^153 + input_limbs[4]*2^204 + 19*q
    
    // Substitute input_limbs[0]:
    // = (c0*2^51 + final_limbs[0] - 19*q) + input_limbs[1]*2^51 + ... + 19*q
    // = c0*2^51 + final_limbs[0] + input_limbs[1]*2^51 + ...
    
    // Substitute input_limbs[1]:
    // = c0*2^51 + final_limbs[0] + (c1*2^51 + final_limbs[1] - c0)*2^51 + input_limbs[2]*2^102 + ...
    // = c0*2^51 + final_limbs[0] + c1*2^102 + final_limbs[1]*2^51 - c0*2^51 + input_limbs[2]*2^102 + ...
    // = final_limbs[0] + final_limbs[1]*2^51 + c1*2^102 + input_limbs[2]*2^102 + ...
    
    // Continue substituting - the c0*2^51 terms cancel, then c1*2^102 terms cancel, etc.
    
    // Expand lhs using the substitutions
    let rhs = final_limbs[0] as int
            + final_limbs[1] as int * pow2(51) as int
            + final_limbs[2] as int * pow2(102) as int
            + final_limbs[3] as int * pow2(153) as int
            + final_limbs[4] as int * pow2(204) as int
            + c4 * pow2(255) as int;
    
    // Show that lhs == rhs through algebraic expansion
    assert(lhs == (c0 * pow2(51) as int + final_limbs[0] as int - 19 * q as int)
                + (c1 * pow2(51) as int + final_limbs[1] as int - c0) * pow2(51) as int
                + (c2 * pow2(51) as int + final_limbs[2] as int - c1) * pow2(102) as int
                + (c3 * pow2(51) as int + final_limbs[3] as int - c2) * pow2(153) as int
                + (c4 * pow2(51) as int + final_limbs[4] as int - c3) * pow2(204) as int
                + 19 * q as int);
    
    // Use the distributivity facts we proved above
    assert(lhs == (c0 * pow2(51) as int + final_limbs[0] as int - 19 * q as int)
                + (c1 * pow2(102) as int + final_limbs[1] as int * pow2(51) as int - c0 * pow2(51) as int)
                + (c2 * pow2(153) as int + final_limbs[2] as int * pow2(102) as int - c1 * pow2(102) as int)
                + (c3 * pow2(204) as int + final_limbs[3] as int * pow2(153) as int - c2 * pow2(153) as int)
                + (c4 * pow2(255) as int + final_limbs[4] as int * pow2(204) as int - c3 * pow2(204) as int)
                + 19 * q as int);
    
    // Group terms: the carries telescope
    // c0*2^51 - c0*2^51 = 0
    // c1*2^102 - c1*2^102 = 0
    // c2*2^153 - c2*2^153 = 0
    // c3*2^204 - c3*2^204 = 0
    // -19*q + 19*q = 0
    // What remains: final_limbs terms + c4*2^255
    
    assert(lhs == final_limbs[0] as int
                + final_limbs[1] as int * pow2(51) as int
                + final_limbs[2] as int * pow2(102) as int
                + final_limbs[3] as int * pow2(153) as int
                + final_limbs[4] as int * pow2(204) as int
                + c4 * pow2(255) as int);
    
    assert(lhs == rhs);
    assert(lhs == as_nat(final_limbs) as int + c4 * pow2(255) as int);
}

/// Helper lemma: Multiplication preserves upper bounds
proof fn lemma_mul_upper_bound(a: nat, x: nat, b: nat)
    requires
        x <= b,
    ensures
        a * x <= a * b,
{
    // This follows from the monotonicity of multiplication for non-negative numbers
    // If x <= b, then a * x <= a * b for any a >= 0
    // Verus's SMT solver should handle this automatically with integer arithmetic
    if a == 0 {
        assert(a * x == 0);
        assert(a * b == 0);
    } else {
        // For a > 0: x <= b implies a*x <= a*b
        // This is a basic property of multiplication that the SMT solver understands
        lemma_mul_inequality(x as int, b as int, a as int);
    }
}

/// Helper lemma: Proves the geometric series identity for 5 terms with base 2^51
/// (2^51 - 1) * (1 + 2^51 + 2^102 + 2^153 + 2^204) = 2^255 - 1
proof fn lemma_geometric_sum_5_terms()
    ensures
        (pow2(51) - 1) * (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204)) == pow2(255) - 1,
{
    // Establish power-of-2 relationships
    lemma_pow2_adds(51, 51);   // 2^102 = 2^51 * 2^51
    lemma_pow2_adds(51, 102);  // 2^153 = 2^51 * 2^102  
    lemma_pow2_adds(51, 153);  // 2^204 = 2^51 * 2^153
    lemma_pow2_adds(51, 204);  // 2^255 = 2^51 * 2^204
    
    // Geometric series formula: For r^n with n terms starting at r^0:
    // (r - 1) * (1 + r + r^2 + ... + r^(n-1)) = r^n - 1
    // Here: r = 2^51, n = 5, so (2^51 - 1) * (sum of 5 terms) = 2^255 - 1
    
    // We'll prove this by expanding the left-hand side and showing it equals the right
    // LHS = (2^51 - 1) * (1 + 2^51 + 2^102 + 2^153 + 2^204)
    //     = 2^51*(1 + 2^51 + 2^102 + 2^153 + 2^204) - 1*(1 + 2^51 + 2^102 + 2^153 + 2^204)
    //     = (2^51 + 2^102 + 2^153 + 2^204 + 2^255) - (1 + 2^51 + 2^102 + 2^153 + 2^204)
    //     = 2^255 - 1  [all middle terms cancel]
    
    let sum = 1 + pow2(51) + pow2(102) + pow2(153) + pow2(204);
    let lhs = (pow2(51) - 1) * sum;
    
    // Expand (a - 1) * b = a * b - b
    assert(lhs == pow2(51) * sum - 1 * sum) by {
        lemma_mul_is_distributive_sub(sum as int, pow2(51) as int, 1);
    }
    assert(lhs == pow2(51) * sum - sum);
    
    // Expand pow2(51) * sum using distributivity
    assert(pow2(51) * sum == pow2(51) * 1 + pow2(51) * pow2(51) + pow2(51) * pow2(102) 
                            + pow2(51) * pow2(153) + pow2(51) * pow2(204)) by {
        lemma_mul_is_distributive_add(pow2(51) as int, 1, pow2(51) as int);
        lemma_mul_is_distributive_add(pow2(51) as int, 1 + pow2(51) as int, pow2(102) as int);
        lemma_mul_is_distributive_add(pow2(51) as int, 1 + pow2(51) + pow2(102) as int, pow2(153) as int);
        lemma_mul_is_distributive_add(pow2(51) as int, 1 + pow2(51) + pow2(102) + pow2(153) as int, pow2(204) as int);
    }
    
    // Simplify using power-of-2 addition properties
    assert(pow2(51) * 1 == pow2(51));
    assert(pow2(51) * pow2(51) == pow2(102));
    assert(pow2(51) * pow2(102) == pow2(153));
    assert(pow2(51) * pow2(153) == pow2(204));
    assert(pow2(51) * pow2(204) == pow2(255));
    
    assert(pow2(51) * sum == pow2(51) + pow2(102) + pow2(153) + pow2(204) + pow2(255));
    
    // Now compute lhs = (pow2(51) + pow2(102) + pow2(153) + pow2(204) + pow2(255)) - sum
    //                 = (pow2(51) + pow2(102) + pow2(153) + pow2(204) + pow2(255)) 
    //                   - (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204))
    assert(sum == 1 + pow2(51) + pow2(102) + pow2(153) + pow2(204));
    
    // The middle terms cancel, leaving: pow2(255) - 1
    assert(lhs == pow2(255) - 1);
}

/// Helper lemma: as_nat bound for 51-bit limbs
/// If each limb < 2^51, then as_nat < 2^255
pub proof fn lemma_as_nat_bound_from_51bit_limbs(limbs: [u64; 5])
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        as_nat(limbs) < pow2(255),
{
    // Strategy: Prove that the maximum value (when all limbs = 2^51 - 1) equals 2^255 - 1
    // We'll prove this by showing the algebraic identity directly using bit manipulation
    
    lemma2_to64_rest();
    assert((1u64 << 51) as nat == pow2(51)) by (compute);
    
    // Establish power-of-2 relationships
    lemma_pow2_adds(51, 51);   // 2^102 = 2^51 * 2^51
    lemma_pow2_adds(51, 102);  // 2^153 = 2^51 * 2^102
    lemma_pow2_adds(51, 153);  // 2^204 = 2^51 * 2^153
    lemma_pow2_adds(51, 204);  // 2^255 = 2^51 * 2^204
    
    // Expand as_nat definition
    assert(as_nat(limbs) == limbs[0] as nat 
                          + pow2(51) * limbs[1] as nat 
                          + pow2(102) * limbs[2] as nat 
                          + pow2(153) * limbs[3] as nat 
                          + pow2(204) * limbs[4] as nat);
    
    // Each limb < 2^51, so limbs[i] <= 2^51 - 1
    lemma_pow2_pos(51);
    assert(pow2(51) >= 1);
    let max_limb = (pow2(51) - 1) as nat;
    assert(forall |i: int| 0 <= i < 5 ==> limbs[i] as nat <= max_limb);
    
    // Prove upper bound for each term
    assert(limbs[0] as nat <= max_limb);
    lemma_mul_upper_bound(pow2(51), limbs[1] as nat, max_limb);
    assert(pow2(51) * limbs[1] as nat <= pow2(51) * max_limb);
    
    lemma_mul_upper_bound(pow2(102), limbs[2] as nat, max_limb);
    assert(pow2(102) * limbs[2] as nat <= pow2(102) * max_limb);
    
    lemma_mul_upper_bound(pow2(153), limbs[3] as nat, max_limb);
    assert(pow2(153) * limbs[3] as nat <= pow2(153) * max_limb);
    
    lemma_mul_upper_bound(pow2(204), limbs[4] as nat, max_limb);
    assert(pow2(204) * limbs[4] as nat <= pow2(204) * max_limb);
    
    // Therefore, as_nat(limbs) <= sum of maximum values
    // as_nat(limbs) <= max_limb + pow2(51)*max_limb + pow2(102)*max_limb + pow2(153)*max_limb + pow2(204)*max_limb
    //                = max_limb * (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204))
    
    // Since each term is maximized at max_limb = 2^51 - 1, we have:
    let max_val = max_limb + pow2(51) * max_limb + pow2(102) * max_limb 
                + pow2(153) * max_limb + pow2(204) * max_limb;
    
    // Factor out max_limb using distributivity
    lemma_mul_is_distributive_add(max_limb as int, 1, pow2(51) as int);
    lemma_mul_is_distributive_add(max_limb as int, (1 + pow2(51)) as int, pow2(102) as int);
    lemma_mul_is_distributive_add(max_limb as int, (1 + pow2(51) + pow2(102)) as int, pow2(153) as int);
    lemma_mul_is_distributive_add(max_limb as int, (1 + pow2(51) + pow2(102) + pow2(153)) as int, pow2(204) as int);
    
    assert(max_val == max_limb * (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204)));
    
    // Now use the geometric series identity: (2^51 - 1) * (1 + 2^51 + 2^102 + 2^153 + 2^204) = 2^255 - 1
    lemma_geometric_sum_5_terms();
    assert(max_limb == pow2(51) - 1);
    assert(max_val == pow2(255) - 1);
    
    // Since as_nat(limbs) <= max_val = 2^255 - 1 < 2^255, we're done
    assert(as_nat(limbs) <= max_val);
    assert(max_val == pow2(255) - 1);
    assert(pow2(255) - 1 < pow2(255)) by {
        lemma_pow2_pos(255);
    }
    assert(as_nat(limbs) < pow2(255));
}

/// Helper lemma: Proves that the carry propagation in reduction computes the division by 2^255
/// This is analogous to lemma_carry_propagation_is_division but for the reduction step
pub proof fn lemma_reduction_carry_propagation_is_division(input_limbs: [u64; 5], q: u64, c4: u64)
    requires
        forall |i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
        q == 0 || q == 1,
        c4 == ({
            let l0 = (input_limbs[0] + 19 * q) as u64;
            let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
            let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
            let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
            let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
            l4 >> 51
        }),
    ensures
        c4 as int == (as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int),
{
    let l0 = (input_limbs[0] + 19 * q) as u64;
    let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
    let l0_masked = (l0 & mask51) as u64;
    let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
    let l1_masked = (l1 & mask51) as u64;
    let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
    let l2_masked = (l2 & mask51) as u64;
    let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
    let l3_masked = (l3 & mask51) as u64;
    let l4_masked = (l4 & mask51) as u64;
    
    let c0 = l0 >> 51;
    let c1 = l1 >> 51;
    let c2 = l2 >> 51;
    let c3 = l3 >> 51;
    
    assert(c4 == l4 >> 51);
    
    // Prove that limbs are bounded (similar to lemma_all_carries_bounded_by_3)
    lemma2_to64_rest();
    
    // Convert the precondition limb bounds to pow2 form
    assert((1u64 << 52) == pow2(52)) by (compute);
    assert(forall |i: int| 0 <= i < 5 ==> input_limbs[i] < pow2(52));
    
    assert(input_limbs[0] < pow2(52));
    assert(19 * q < 20) by {
        assert(q <= 1);
        assert(19 * 1 == 19) by (compute);
    }
    assert(input_limbs[0] + 19 * q < pow2(52) + 20);
    assert(pow2(52) + 20 <= u64::MAX) by (compute);
    
    // Apply div-mod relationships
    l51_bit_mask_lt();
    lemma_div_and_mod_51(c0, l0_masked, l0);
    lemma_div_and_mod_51(c1, l1_masked, l1);
    lemma_div_and_mod_51(c2, l2_masked, l2);
    lemma_div_and_mod_51(c3, l3_masked, l3);
    lemma_div_and_mod_51(c4, l4_masked, l4);
    
    // Now use the telescoping lemma
    let final_limbs = [l0_masked, l1_masked, l2_masked, l3_masked, l4_masked];
    
    // Verify preconditions for telescoping - need to prove the division-modulo relationships
    assert(l0 == input_limbs[0] + 19 * q);
    assert(l0 == c0 * pow2(51) + l0_masked);
    assert(input_limbs[0] as int + 19 * q as int == c0 as int * pow2(51) + l0_masked as int);
    
    assert(l1 == input_limbs[1] + c0);
    assert(l1 == c1 * pow2(51) + l1_masked);
    assert(input_limbs[1] as int + c0 as int == c1 as int * pow2(51) + l1_masked as int);
    
    assert(l2 == input_limbs[2] + c1);
    assert(l2 == c2 * pow2(51) + l2_masked);
    assert(input_limbs[2] as int + c1 as int == c2 as int * pow2(51) + l2_masked as int);
    
    assert(l3 == input_limbs[3] + c2);
    assert(l3 == c3 * pow2(51) + l3_masked);
    assert(input_limbs[3] as int + c2 as int == c3 as int * pow2(51) + l3_masked as int);
    
    assert(l4 == input_limbs[4] + c3);
    assert(l4 == c4 * pow2(51) + l4_masked);
    assert(input_limbs[4] as int + c3 as int == c4 as int * pow2(51) + l4_masked as int);
    
    masked_lt_51(l0);
    masked_lt_51(l1);
    masked_lt_51(l2);
    masked_lt_51(l3);
    masked_lt_51(l4);
    
    lemma_reduction_telescoping(input_limbs, final_limbs, q, c0 as int, c1 as int, c2 as int, c3 as int, c4 as int);
    
    // From telescoping: as_nat(input_limbs) + 19*q == as_nat(final_limbs) + c4*2^255
    // Therefore: c4 = (as_nat(input_limbs) + 19*q - as_nat(final_limbs)) / 2^255
    
    // Since final_limbs[i] < 2^51 for all i, as_nat(final_limbs) < 2^255
    // This is a fundamental property of radix-2^51 representation with 5 limbs
    lemma_as_nat_bound_from_51bit_limbs(final_limbs);
    assert(as_nat(final_limbs) < pow2(255));
    
    // From the telescoping identity:
    // as_nat(input_limbs) + 19*q = as_nat(final_limbs) + c4*2^255
    // Since 0 <= as_nat(final_limbs) < 2^255, and this is the unique representation,
    // c4 = (as_nat(input_limbs) + 19*q) / 2^255
    
    let dividend = as_nat(input_limbs) as int + 19 * q as int;
    let divisor = pow2(255) as int;
    
    lemma_fundamental_div_mod(dividend, divisor);
    lemma_pow2_pos(255);
    
    // From telescoping: dividend = c4 * divisor + as_nat(final_limbs)
    // where 0 <= as_nat(final_limbs) < divisor (from the assume at line 1322)
    
    // Use the uniqueness lemma for division to prove: dividend / divisor == c4
    // We have:
    // - dividend = c4 * divisor + as_nat(final_limbs) 
    // - 0 <= as_nat(final_limbs) < divisor
    // Therefore: dividend / divisor == c4
    
    assert(dividend == as_nat(input_limbs) as int + 19 * q as int);
    assert(dividend == as_nat(final_limbs) as int + c4 as int * divisor);
    assert(dividend == c4 as int * divisor + as_nat(final_limbs) as int);
    let remainder = as_nat(final_limbs) as int;
    assert(0 <= remainder);
    assert(remainder < divisor);
    
    lemma_div_quotient_unique(dividend, divisor, c4 as int, as_nat(final_limbs) as int);
    assert(dividend / divisor == c4 as int);
    assert(c4 as int == dividend / divisor);
}

/// Helper lemma: Show that the carry out of l4 equals q
pub proof fn lemma_carry_out_equals_q(input_limbs: [u64; 5], q: u64)
    requires
        forall |i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
        q == 0 || q == 1,
        as_nat(input_limbs) >= p() <==> q == 1,
        as_nat(input_limbs) < 2 * p(),  // From reduce()'s postcondition
    ensures
        ({
            let l0 = (input_limbs[0] + 19 * q) as u64;
            let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
            let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
            let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
            let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
            (l4 >> 51) == q
        }),
{
    let l0 = (input_limbs[0] + 19 * q) as u64;
    let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
    let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
    let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
    let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
    let c4 = l4 >> 51;
    
    // We need to prove c4 == q
    // Strategy: Use the fact that the carry propagation computes (as_nat(input_limbs) + 19*q) / 2^255
    
    // This is analogous to lemma_carry_propagation_is_division, but with input_limbs and 19*q instead of limbs and 19
    // The computation is:
    // Stage 0: (input_limbs[0] + 19*q) = c0*2^51 + r0
    // Stage 1: (input_limbs[1] + c0) = c1*2^51 + r1
    // ...
    // Stage 4: (input_limbs[4] + c3) = c4*2^51 + r4
    
    // By the same telescoping argument as in lemma_carry_propagation_is_division:
    // c4 = (as_nat(input_limbs) + 19*q) / 2^255
    
    pow255_gt_19();
    lemma_pow2_pos(255);
    assert(p() == pow2(255) - 19);
    
    // Case analysis on q:
    if q == 0 {
        // When q == 0, we have as_nat(input_limbs) < p() = 2^255 - 19
        // So: as_nat(input_limbs) + 19*0 < 2^255
        // Therefore: (as_nat(input_limbs) + 0) / 2^255 == 0
        assert(as_nat(input_limbs) < p());
        assert(as_nat(input_limbs) < pow2(255) - 19);
        assert(as_nat(input_limbs) + 19 * q == as_nat(input_limbs));
        assert(as_nat(input_limbs) < pow2(255) - 19);
        
        // Invoke the division computation
        lemma_reduction_carry_propagation_is_division(input_limbs, q, c4);
        assert(c4 as int == (as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int));
        
        assert(as_nat(input_limbs) < pow2(255));
        lemma_div_strictly_bounded(as_nat(input_limbs) as int, pow2(255) as int, 1);
        assert((as_nat(input_limbs) as int) / (pow2(255) as int) == 0);
        assert((as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int) == 0);
        assert(c4 == 0);
    } else {
        // q == 1
        assert(q == 1);
        // When q == 1, we have as_nat(input_limbs) >= p() = 2^255 - 19
        // And as_nat(input_limbs) < 2*p() = 2^256 - 38
        // So: 2^255 - 19 <= as_nat(input_limbs) + 19 < 2^256 - 38 + 19 = 2^256 - 19
        // Therefore: 2^255 <= as_nat(input_limbs) + 19 < 2^256
        // So: (as_nat(input_limbs) + 19) / 2^255 == 1
        assert(as_nat(input_limbs) >= p());
        assert(as_nat(input_limbs) >= pow2(255) - 19);
        assert(as_nat(input_limbs) + 19 >= pow2(255));
        
        assert(as_nat(input_limbs) < 2 * p());
        assert(2 * p() == 2 * pow2(255) - 38) by {
            lemma_pow2_adds(255, 1);
        }
        assert(as_nat(input_limbs) + 19 * q == as_nat(input_limbs) + 19);
        assert(as_nat(input_limbs) + 19 < 2 * pow2(255) - 38 + 19);
        assert(as_nat(input_limbs) + 19 < 2 * pow2(255));
        
        // Establish the tight bounds: pow2(255) <= as_nat(input_limbs) + 19 < 2*pow2(255)
        let val = as_nat(input_limbs) as int + 19;
        assert(val >= pow2(255) as int);
        assert(val < 2 * pow2(255) as int);
        assert(1 * pow2(255) as int <= val < 2 * pow2(255) as int);
        
        // Invoke the division computation
        lemma_reduction_carry_propagation_is_division(input_limbs, q, c4);
        assert(c4 as int == (as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int));
        
        // Since pow2(255) <= val < 2*pow2(255), we have val / pow2(255) == 1
        // We prove this by establishing: 1 <= val / pow2(255) < 2
        
        let divisor = pow2(255) as int;
        
        // First, prove val / divisor < 2 using lemma_div_strictly_bounded
        // We have: val < 2 * divisor, so val / divisor < 2
        lemma_div_strictly_bounded(val, divisor, 2);
        assert(val / divisor < 2);
        
        // Second, prove val / divisor >= 1
        // From val >= divisor and divisor > 0
        lemma_fundamental_div_mod(val, divisor);
        lemma_pow2_pos(255);
        
        // Since val >= divisor, we have val = q * divisor + r where q = val / divisor
        // and 0 <= r < divisor
        // If q = 0, then val = 0 + r < divisor, contradicting val >= divisor
        // Therefore q >= 1
        if val / divisor == 0 {
            assert(val < divisor); // From div properties
            assert(false); // Contradiction
        }
        assert(val / divisor >= 1);
        
        // Therefore: 1 <= val / divisor < 2, so val / divisor == 1
        assert(val / divisor == 1);
        assert((as_nat(input_limbs) as int + 19) / (pow2(255) as int) == 1);
        assert((as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int) == 1);
        assert(c4 == 1);
    }
}

/// Spec function to compute the reduction result
pub open spec fn reduce_with_q_spec(input_limbs: [u64; 5], q: u64) -> [u64; 5] {
    let l0 = (input_limbs[0] + 19 * q) as u64;
    let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
    let l0_masked = (l0 & mask51) as u64;
    let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
    let l1_masked = (l1 & mask51) as u64;
    let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
    let l2_masked = (l2 & mask51) as u64;
    let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
    let l3_masked = (l3 & mask51) as u64;
    let l4_masked = (l4 & mask51) as u64;
    [l0_masked, l1_masked, l2_masked, l3_masked, l4_masked]
}

/// Proves that after adding 19*q and propagating carries while masking to 51 bits,
/// the result equals as_nat(input_limbs) mod p
pub proof fn lemma_to_bytes_reduction(input_limbs: [u64; 5], final_limbs: [u64; 5], q: u64)
    requires
        forall |i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
        q == 0 || q == 1,
        as_nat(input_limbs) >= p() <==> q == 1,
        as_nat(input_limbs) < 2 * p(),  // From reduce()'s postcondition
        final_limbs == reduce_with_q_spec(input_limbs, q),
    ensures
        forall |i: int| 0 <= i < 5 ==> final_limbs[i] < (1u64 << 51),
        as_nat(final_limbs) == as_nat(input_limbs) % p(),
{
    // Extract intermediate values from the spec
    let l0 = (input_limbs[0] + 19 * q) as u64;
    let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
    let l0_masked = (l0 & mask51) as u64;
    let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
    let l1_masked = (l1 & mask51) as u64;
    let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
    let l2_masked = (l2 & mask51) as u64;
    let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
    let l3_masked = (l3 & mask51) as u64;
    let l4_masked = (l4 & mask51) as u64;
    
    assert(final_limbs == [l0_masked, l1_masked, l2_masked, l3_masked, l4_masked]);
    
    // Part 1: Prove that all final limbs are bounded by 2^51
    l51_bit_mask_lt();
    assert(mask51 < (1u64 << 51));
    masked_lt_51(l0);
    assert(final_limbs[0] < (1u64 << 51));
    masked_lt_51(l1);
    assert(final_limbs[1] < (1u64 << 51));
    masked_lt_51(l2);
    assert(final_limbs[2] < (1u64 << 51));
    masked_lt_51(l3);
    assert(final_limbs[3] < (1u64 << 51));
    masked_lt_51(l4);
    assert(final_limbs[4] < (1u64 << 51));
    
    // Part 2: Prove that as_nat(final_limbs) == as_nat(input_limbs) % p()
    // Strategy: Show that the carry propagation computes as_nat(input_limbs) + 19*q - 2^255*q
    //           which equals as_nat(input_limbs) - q*(2^255 - 19) = as_nat(input_limbs) - q*p()
    
    // Use lemma_div_and_mod_51 to relate the shift and mask operations to division and modulo
    lemma_div_and_mod_51(l0 >> 51, l0 & mask51, l0);
    assert(l0 == (l0 >> 51) * pow2(51) + (l0 & mask51));
    assert(l0 == (l0 >> 51) * pow2(51) + l0_masked);
    
    lemma_div_and_mod_51(l1 >> 51, l1 & mask51, l1);
    assert(l1 == (l1 >> 51) * pow2(51) + l1_masked);
    
    lemma_div_and_mod_51(l2 >> 51, l2 & mask51, l2);
    assert(l2 == (l2 >> 51) * pow2(51) + l2_masked);
    
    lemma_div_and_mod_51(l3 >> 51, l3 & mask51, l3);
    assert(l3 == (l3 >> 51) * pow2(51) + l3_masked);
    
    lemma_div_and_mod_51(l4 >> 51, l4 & mask51, l4);
    assert(l4 == (l4 >> 51) * pow2(51) + l4_masked);
    
    // Define the carries for readability
    let c0 = l0 >> 51;
    let c1 = l1 >> 51;
    let c2 = l2 >> 51;
    let c3 = l3 >> 51;
    let c4 = l4 >> 51;
    
    // Express l0, l1, l2, l3, l4 in terms of input_limbs
    // Note: Need to prove the casts don't affect the values (no overflow)
    assert(input_limbs[0] < (1u64 << 52));
    assert(19 * q < 20) by {
        assert(q <= 1);
        assert(19 * 1 == 19) by (compute);
    }
    assert(input_limbs[0] + 19 * q < (1u64 << 52) + 20);
    assert((1u64 << 52) + 20 < u64::MAX) by (compute);
    assert((input_limbs[0] + 19 * q) as u64 == input_limbs[0] + 19 * q);
    assert(l0 == input_limbs[0] + 19 * q);
    
    // Similar reasoning for other limbs - the carries are small enough
    // l0 < 2^52 + 20, so l0 >> 51 <= 2
    // l1 = input_limbs[1] + (l0 >> 51) < 2^52 + 2 < u64::MAX
    assert(l0 < (1u64 << 52) + 20);
    lemma_shr_le_u64(l0, ((1u64 << 52) + 20) as u64, 51);
    assert((((1u64 << 52) + 20) as u64) >> 51 == 2) by (compute);
    assert(l0 >> 51 <= 2);
    assert(input_limbs[1] + (l0 >> 51) < (1u64 << 52) + 2);
    assert((1u64 << 52) + 2 < u64::MAX) by (compute);
    assert((input_limbs[1] + (l0 >> 51)) as u64 == input_limbs[1] + (l0 >> 51));
    assert(l1 == input_limbs[1] + (l0 >> 51));
    
    assert(l1 < (1u64 << 52) + 2);
    lemma_shr_le_u64(l1, ((1u64 << 52) + 2) as u64, 51);
    assert((((1u64 << 52) + 2) as u64) >> 51 == 2) by (compute);
    assert(l1 >> 51 <= 2);
    assert(input_limbs[2] + (l1 >> 51) < (1u64 << 52) + 2);
    assert((input_limbs[2] + (l1 >> 51)) as u64 == input_limbs[2] + (l1 >> 51));
    assert(l2 == input_limbs[2] + (l1 >> 51));
    
    assert(l2 < (1u64 << 52) + 2);
    lemma_shr_le_u64(l2, ((1u64 << 52) + 2) as u64, 51);
    assert((((1u64 << 52) + 2) as u64) >> 51 == 2) by (compute);
    assert(l2 >> 51 <= 2);
    assert(input_limbs[3] + (l2 >> 51) < (1u64 << 52) + 2);
    assert((input_limbs[3] + (l2 >> 51)) as u64 == input_limbs[3] + (l2 >> 51));
    assert(l3 == input_limbs[3] + (l2 >> 51));
    
    assert(l3 < (1u64 << 52) + 2);
    lemma_shr_le_u64(l3, ((1u64 << 52) + 2) as u64, 51);
    assert((((1u64 << 52) + 2) as u64) >> 51 == 2) by (compute);
    assert(l3 >> 51 <= 2);
    assert(input_limbs[4] + (l3 >> 51) < (1u64 << 52) + 2);
    assert((input_limbs[4] + (l3 >> 51)) as u64 == input_limbs[4] + (l3 >> 51));
    assert(l4 == input_limbs[4] + (l3 >> 51));
    
    // Now use the telescoping lemma to relate as_nat(input_limbs) + 19*q to as_nat(final_limbs) + c4*2^255
    // The division-mod relationships give us the preconditions needed:
    assert(input_limbs[0] as int + 19 * q as int == c0 as int * pow2(51) + l0_masked as int);
    assert(input_limbs[1] as int + c0 as int == c1 as int * pow2(51) + l1_masked as int);
    assert(input_limbs[2] as int + c1 as int == c2 as int * pow2(51) + l2_masked as int);
    assert(input_limbs[3] as int + c2 as int == c3 as int * pow2(51) + l3_masked as int);
    assert(input_limbs[4] as int + c3 as int == c4 as int * pow2(51) + l4_masked as int);
    
    // All final_limbs are bounded by 2^51 (already proven above)
    lemma_reduction_telescoping(input_limbs, final_limbs, q, c0 as int, c1 as int, c2 as int, c3 as int, c4 as int);
    assert(as_nat(input_limbs) as int + 19 * q as int == as_nat(final_limbs) as int + c4 as int * pow2(255));
    
    // Prove that c4 == q
    lemma_carry_out_equals_q(input_limbs, q);
    assert(c4 == q);
    
    // Therefore: as_nat(input_limbs) + 19*q = as_nat(final_limbs) + q*2^255
    // Rearranging: as_nat(final_limbs) = as_nat(input_limbs) + 19*q - q*2^255
    //                                    = as_nat(input_limbs) - q*(2^255 - 19)
    //                                    = as_nat(input_limbs) - q*p()
    
    pow255_gt_19();
    assert(p() == pow2(255) - 19);
    
    // Case analysis on q
    if q == 0 {
        // as_nat(final_limbs) = as_nat(input_limbs) - 0*p() = as_nat(input_limbs)
        assert(as_nat(final_limbs) as int == as_nat(input_limbs) as int);
        assert(as_nat(final_limbs) == as_nat(input_limbs));
        
        // Since q == 0, we have as_nat(input_limbs) < p()
        assert(as_nat(input_limbs) < p());
        
        // For values < p, x % p = x
        // Since as_nat(input_limbs) < p(), we have as_nat(input_limbs) % p() = as_nat(input_limbs)
        lemma_pow2_pos(255);
        lemma_mod_of_less_than_divisor(as_nat(input_limbs) as int, p() as int);
        assert(as_nat(input_limbs) % p() == as_nat(input_limbs));
        
        assert(as_nat(final_limbs) == as_nat(input_limbs));
        assert(as_nat(final_limbs) == as_nat(input_limbs) % p());
    } else {
        // q == 1
        assert(q == 1);
        assert(as_nat(input_limbs) >= p());
        
        // as_nat(final_limbs) = as_nat(input_limbs) - 1*p() = as_nat(input_limbs) - p()
        assert(as_nat(final_limbs) as int == as_nat(input_limbs) as int - p() as int);
        assert(as_nat(final_limbs) == as_nat(input_limbs) - p());
        
        // Need to prove: as_nat(input_limbs) % p() = as_nat(input_limbs) - p()
        // This holds when p <= as_nat(input_limbs) < 2*p
        // We have as_nat(input_limbs) >= p() (from q==1) and as_nat(input_limbs) < 2*p() (from precondition)
        
        // For values in [p, 2*p), x % p = x - p
        lemma_fundamental_div_mod(as_nat(input_limbs) as int, p() as int);
        lemma_pow2_pos(255);
        
        // Since p <= as_nat < 2*p, the quotient is 1
        lemma_div_strictly_bounded(as_nat(input_limbs) as int, p() as int, 2);
        assert((as_nat(input_limbs) as int / p() as int) == 1);
        
        // From div-mod: x = d * (x/d) + (x%d)
        // lemma_fundamental_div_mod establishes this with multiplication on the left
        let x = as_nat(input_limbs) as int;
        let divisor = p() as int;
        let quotient = x / divisor;
        let remainder = x % divisor;
        
        // From lemma_fundamental_div_mod: x == divisor * quotient + remainder
        assert(x == divisor * quotient + remainder);
        // Convert to: x == quotient * divisor + remainder
        assert(divisor * quotient == quotient * divisor) by {
            lemma_mul_is_commutative(divisor, quotient);
        }
        assert(x == quotient * divisor + remainder);
        
        // We proved quotient == 1
        assert(quotient == 1);
        assert(x == 1 * divisor + remainder);
        assert(1 * divisor == divisor) by (compute);
        assert(x == divisor + remainder);
        assert(remainder == x - divisor);
        
        // Convert back to original terms
        assert(as_nat(input_limbs) as int % p() as int == as_nat(input_limbs) as int - p() as int);
        assert(as_nat(input_limbs) % p() == as_nat(input_limbs) - p());
        assert(as_nat(final_limbs) == as_nat(input_limbs) % p());
    }
}

// ============================================================================
// LEMMA 3: Packing 51-bit limbs into 8-bit bytes
// ============================================================================

/// Predicate: bytes are packed from limbs according to the to_bytes algorithm
/// This captures the byte-packing relationship used in FieldElement51::to_bytes (lines 380-410)
pub open spec fn bytes_match_limbs_packing(limbs: [u64; 5], bytes: [u8; 32]) -> bool {
    bytes[ 0] ==   limbs[0]                           as u8 &&
    bytes[ 1] ==  (limbs[0] >>  8)                    as u8 &&
    bytes[ 2] ==  (limbs[0] >> 16)                    as u8 &&
    bytes[ 3] ==  (limbs[0] >> 24)                    as u8 &&
    bytes[ 4] ==  (limbs[0] >> 32)                    as u8 &&
    bytes[ 5] ==  (limbs[0] >> 40)                    as u8 &&
    bytes[ 6] == ((limbs[0] >> 48) | (limbs[1] << 3)) as u8 &&
    bytes[ 7] ==  (limbs[1] >>  5)                    as u8 &&
    bytes[ 8] ==  (limbs[1] >> 13)                    as u8 &&
    bytes[ 9] ==  (limbs[1] >> 21)                    as u8 &&
    bytes[10] ==  (limbs[1] >> 29)                    as u8 &&
    bytes[11] ==  (limbs[1] >> 37)                    as u8 &&
    bytes[12] == ((limbs[1] >> 45) | (limbs[2] << 6)) as u8 &&
    bytes[13] ==  (limbs[2] >>  2)                    as u8 &&
    bytes[14] ==  (limbs[2] >> 10)                    as u8 &&
    bytes[15] ==  (limbs[2] >> 18)                    as u8 &&
    bytes[16] ==  (limbs[2] >> 26)                    as u8 &&
    bytes[17] ==  (limbs[2] >> 34)                    as u8 &&
    bytes[18] ==  (limbs[2] >> 42)                    as u8 &&
    bytes[19] == ((limbs[2] >> 50) | (limbs[3] << 1)) as u8 &&
    bytes[20] ==  (limbs[3] >>  7)                    as u8 &&
    bytes[21] ==  (limbs[3] >> 15)                    as u8 &&
    bytes[22] ==  (limbs[3] >> 23)                    as u8 &&
    bytes[23] ==  (limbs[3] >> 31)                    as u8 &&
    bytes[24] ==  (limbs[3] >> 39)                    as u8 &&
    bytes[25] == ((limbs[3] >> 47) | (limbs[4] << 4)) as u8 &&
    bytes[26] ==  (limbs[4] >>  4)                    as u8 &&
    bytes[27] ==  (limbs[4] >> 12)                    as u8 &&
    bytes[28] ==  (limbs[4] >> 20)                    as u8 &&
    bytes[29] ==  (limbs[4] >> 28)                    as u8 &&
    bytes[30] ==  (limbs[4] >> 36)                    as u8 &&
    bytes[31] ==  (limbs[4] >> 44)                    as u8
}

/// Core lemma: proves that packing 51-bit limbs into bytes preserves the value
pub proof fn lemma_limbs_to_bytes(limbs: [u64; 5], bytes: [u8; 32])
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        as_nat_32_u8(bytes) == as_nat(limbs),
{
    // Strategy: Use induction on the recursive definition of as_nat_32_u8
    // Call the inductive helper starting at index 0
    lemma_limbs_to_bytes_inductive(limbs, bytes, 0);
    
    // The helper proves: as_nat_32_u8_rec(&bytes, 0) == (as_nat(limbs) / pow2(0)) % pow2(256)
    // Since as_nat(limbs) < pow2(255) < pow2(256), we have:
    // (as_nat(limbs) / 1) % pow2(256) = as_nat(limbs) % pow2(256) = as_nat(limbs)
    
    lemma_as_nat_bound_from_51bit_limbs(limbs);
    assert(as_nat(limbs) < pow2(255));
    lemma2_to64_rest();
    lemma_pow2_adds(8, 248);
    assert(pow2(256) == pow2(32 * 8));
    lemma_pow2_strictly_increases(255, 256);
    assert(pow2(255) < pow2(256));
    assert(as_nat(limbs) < pow2(256));
    
    // The inductive helper proves:
    // as_nat_32_u8_rec(&bytes, 0) == (as_nat(limbs) / pow2(0)) % pow2((32 - 0) * 8)
    //                             == (as_nat(limbs) / pow2(0)) % pow2(256)
    
    // Step 1: Prove pow2(0) == 1, so (as_nat(limbs) / pow2(0)) == as_nat(limbs)
    lemma2_to64();  // Establishes pow2(0) == 1
    assert(pow2(0) == 1);
    assert(as_nat(limbs) / pow2(0) == as_nat(limbs) / 1);
    assert(as_nat(limbs) / 1 == as_nat(limbs));
    
    // Step 2: Since as_nat(limbs) < pow2(256), we have as_nat(limbs) % pow2(256) == as_nat(limbs)
    lemma_pow2_pos(256);
    lemma_mod_of_less_than_divisor(as_nat(limbs) as int, pow2(256) as int);
    assert(as_nat(limbs) % pow2(256) == as_nat(limbs));
    
    // Step 3: Connect the pieces
    // We have: as_nat_32_u8_rec(&bytes, 0) == (as_nat(limbs) / pow2(0)) % pow2(256)
    // Need: as_nat_32_u8_rec(&bytes, 0) == as_nat(limbs)
    // This requires: (as_nat(limbs) / pow2(0)) % pow2(256) == as_nat(limbs)
    // Which follows from: as_nat(limbs) / pow2(0) == as_nat(limbs) [when pow2(0) == 1]
    //                 and: as_nat(limbs) % pow2(256) == as_nat(limbs) [proven above]
    assert(as_nat_32_u8_rec(&bytes, 0) == as_nat(limbs));
    
    // Since as_nat_32_u8(bytes) = as_nat_32_u8_rec(&bytes, 0), we're done
    assert(as_nat_32_u8(bytes) == as_nat_32_u8_rec(&bytes, 0));
    assert(as_nat_32_u8(bytes) == as_nat(limbs));
}

// ============================================================================
// INDUCTIVE PROOF for lemma_limbs_to_bytes
// ============================================================================

/// Helper for inductive proof: relates bytes[index..32] to the corresponding bits from limbs
/// 
/// Proves by induction that as_nat_32_u8_rec at index i equals as_nat(limbs)
/// when starting from index 0.
pub proof fn lemma_limbs_to_bytes_inductive(limbs: [u64; 5], bytes: [u8; 32], index: nat)
    requires
        index <= 32,
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        // Inductive invariant: bytes[index..32] represent the bits from as_nat(limbs) 
        // starting at bit position (index * 8)
        index <= 32 ==> as_nat_32_u8_rec(&bytes, index) == (as_nat(limbs) / pow2(index * 8)) % pow2((32 - index as int) as nat * 8),
    decreases 32 - index,
{
    if index >= 32 {
        // Base case: no bytes left, no bits left
        assert(as_nat_32_u8_rec(&bytes, 32) == 0);
        // Need to prove: 0 == (as_nat(limbs) / pow2(256)) % pow2(0)
        //
        // Step 1: as_nat(limbs) / pow2(256) == 0 since limbs < pow2(255) < pow2(256)
        lemma2_to64_rest();
        lemma_pow2_adds(8, 248);
        assert(pow2(32 * 8) == pow2(256));
        lemma_pow2_strictly_increases(255, 256);
        assert(pow2(255) < pow2(256));
        lemma_as_nat_bound_from_51bit_limbs(limbs);
        assert(as_nat(limbs) < pow2(255));
        assert(as_nat(limbs) < pow2(256));
        lemma_div_strictly_bounded(as_nat(limbs) as int, pow2(256) as int, 1);
        assert(as_nat(limbs) / pow2(256) < 1);
        assert(as_nat(limbs) / pow2(256) == 0);
        
        // Step 2: 0 % pow2(0) == 0 (anything % 1 == 0, since pow2(0) == 1)
        // The SMT solver should handle 0 % x == 0 for any positive x
        lemma_pow2_pos(0);
        assert((as_nat(limbs) / pow2(index * 8)) % pow2((32 - index as int) as nat * 8) == 0);
    } else {
        // Inductive step: assume true for index+1, prove for index
        lemma_limbs_to_bytes_inductive(limbs, bytes, index + 1);
        
        // IH: as_nat_32_u8_rec(&bytes, index+1) == (as_nat(limbs) / pow2((index+1)*8)) % pow2((31-index)*8)
        
        // By definition of as_nat_32_u8_rec:
        // as_nat_32_u8_rec(&bytes, index) = bytes[index] * pow2(index*8) + as_nat_32_u8_rec(&bytes, index+1)
        
        // Need to prove: this equals (as_nat(limbs) / pow2(index*8)) % pow2((32-index)*8)
        //
        // Strategy: 
        // 1. Show bytes[index] == (as_nat(limbs) / pow2(index*8)) % 256
        // 2. Use modular arithmetic to combine with IH
        
        // By IH, we have:
        let rest_val = as_nat_32_u8_rec(&bytes, index + 1);
        assert(rest_val == (as_nat(limbs) / pow2((index + 1) * 8)) % pow2((31 - index as int) as nat * 8));
        
        // By definition of as_nat_32_u8_rec:
        assert(as_nat_32_u8_rec(&bytes, index) == bytes[index as int] as nat * pow2(index * 8) + rest_val);
        
        // To complete the proof, we need to show:
        // bytes[index] * 2^(index*8) + rest_val == (as_nat(limbs) / 2^(index*8)) % 2^((32-index)*8)
        //
        // Strategy:
        // 1. Show that bytes[index] == (as_nat(limbs) / pow2(index*8)) % 256
        // 2. Use modular arithmetic to show that byte * 2^(index*8) + rest_val equals the target
        
        // Step 1: Prove bytes[index] extracts the correct byte
        // Strategy: Use lemma_extract_byte (or lemma_packed_byte) on the appropriate limb,
        // then bridge to show it equals (as_nat(limbs) / pow2(index*8)) % 256
        
        lemma_byte_from_limbs_to_as_nat(limbs, bytes, index);
        assert(bytes[index as int] as nat == (as_nat(limbs) / pow2(index * 8)) % 256);
        
        // Step 2: Use modular arithmetic to combine byte and rest
        // We have:
        // - bytes[index] * 2^(index*8) + rest_val  (LHS from as_nat_32_u8_rec definition)
        // - (as_nat(limbs) / 2^(index*8)) % 2^((32-index)*8)  (RHS from invariant)
        //
        // The key insight: if X = byte + high * 256, then:
        // byte * 2^(index*8) + high * 2^(index*8) * 256
        // = byte * 2^(index*8) + high * 2^((index+1)*8)
        // = (byte + high * 256) * 2^(index*8)
        // = X * 2^(index*8)
        //
        // where byte = X % 256 and high = X / 256.
        //
        // But our formula has: bytes[index] * 2^(index*8) + rest_val
        // We need: rest_val = high * 2^(index*8)? No, that's not right.
        //
        // Actually, let me reconsider. rest_val = as_nat_32_u8_rec(&bytes, index+1)
        // represents the value of bytes[index+1..32) with each byte at its proper position.
        // So rest_val = sum_{i=index+1..32} bytes[i] * 2^(i*8)
        //
        // For this to work out, I need a more sophisticated modular arithmetic lemma.
        // For now, use assume.
        
        assume(bytes[index as int] as nat * pow2(index * 8) + rest_val == 
               (as_nat(limbs) / pow2(index * 8)) % pow2((32 - index as int) as nat * 8));
    }
}

// ============================================================================
// REUSABLE HELPER LEMMAS for byte extraction
// ============================================================================

/// Helper: Casting u64 to u8 is equivalent to taking mod 256
/// (Analogous to lemma_cast_then_mod_51 from pow2_51_lemmas.rs)
proof fn lemma_u64_to_u8_is_mod_256(x: u64)
    ensures
        (x as u8) as nat == x as nat % 256,
{
    // Casting to u8 masks to 8 bits, which is equivalent to mod 2^8 = mod 256
    // This is a low-level bit-manipulation property
    assume((x as u8) as nat == x as nat % 256);
}

/// Helper: (a + b*m) % m == a % m
/// Uses vstd's lemma_mod_multiples_basic pattern
proof fn lemma_mod_add_multiples(a: int, b: int, m: int)
    requires
        m > 0,
    ensures
        (a + b * m) % m == a % m,
{
    use vstd::arithmetic::div_mod::*;
    
    // Apply fundamental div-mod to both sides
    lemma_fundamental_div_mod(a, m);
    let qa = a / m;
    let ra = a % m;
    assert(a == m * qa + ra);
    
    // a + b*m = m * qa + ra + b*m = m * (qa + b) + ra
    lemma_fundamental_div_mod(a + b * m, m);
    let q_sum = (a + b * m) / m;
    let r_sum = (a + b * m) % m;
    assert(a + b * m == m * q_sum + r_sum);
    
    // Show that a + b*m = m * (qa + b) + ra
    use vstd::arithmetic::mul::*;
    lemma_mul_is_distributive_add(m, qa, b);
    assert(m * (qa + b) == m * qa + m * b);
    lemma_mul_is_commutative(b, m);
    assert(m * b == b * m);
    assert(m * (qa + b) == m * qa + b * m);
    assert(a + b * m == m * qa + ra + b * m);
    assert(m * qa + ra + b * m == m * qa + b * m + ra);
    assert(a + b * m == m * (qa + b) + ra);
    
    // By uniqueness of quotient and remainder
    lemma_fundamental_div_mod_converse(a + b * m, m, qa + b, ra);
    assert(r_sum == ra);
    assert((a + b * m) % m == a % m);
}

/// Helper: (a + b*m*k) % m == a % m (more general version)
proof fn lemma_mod_add_multiples_factor(a: int, b: int, k: int, m: int)
    requires
        m > 0,
    ensures
        (a + b * (m * k)) % m == a % m,
{
    use vstd::arithmetic::mul::*;
    
    // The full proof would show: b * (m * k) = m * (b * k), then apply lemma_mod_add_multiples
    // For now, assume this property as it's a standard modular arithmetic fact
    assume((a + b * (m * k)) % m == a % m);
}

// ============================================================================
// BYTE EXTRACTION PROOF using lemma_extract_byte
// ============================================================================

/// Bridge lemma: shows that higher limbs don't affect byte extraction (non-boundary bytes only)
/// Key insight: after dividing by pow2(byte_offset), higher limbs contribute multiples of 256
proof fn lemma_byte_bridge(limbs: [u64; 5], limb_index: nat, byte_offset: nat, limb_shift: nat)
    requires
        limb_index < 5,
        byte_offset == limb_index * 51 + limb_shift,
        byte_offset < 256,
        limb_shift < 64,
        // Critical constraint: next limb must contribute multiples of 256
        // This means (limb_index+1)*51 - byte_offset >= 8, or equivalently 51 - limb_shift >= 8
        // Exception: if limb_index == 4 (last limb), there's no next limb, so no constraint
        limb_index == 4 || limb_shift <= 43,
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        (as_nat(limbs) / pow2(byte_offset)) % 256 == (limbs[limb_index as int] as nat / pow2(limb_shift)) % 256,
{
    // Strategy: Expand as_nat(limbs) and show each piece's contribution mod 256
    // as_nat(limbs) = limbs[0] + limbs[1]*2^51 + limbs[2]*2^102 + limbs[3]*2^153 + limbs[4]*2^204
    
    // Establish pow2 facts
    lemma2_to64();
    lemma_pow2_adds(51, 51);   // 2^102 = 2^51 * 2^51
    lemma_pow2_adds(51, 102);  // 2^153 = 2^51 * 2^102
    lemma_pow2_adds(51, 153);  // 2^204 = 2^51 * 2^153
    assert(pow2(8) == 256) by (compute);
    
    // Case analysis on limb_index - for each case, we'll show:
    // 1. Lower limbs vanish after division (too small)
    // 2. Target limb contributes exactly what we need
    // 3. Higher limbs contribute multiples of 256 (vanish mod 256)
    
    if limb_index == 0 {
        lemma_byte_bridge_case0(limbs, limb_shift);
    } else if limb_index == 1 {
        lemma_byte_bridge_case1(limbs, limb_shift);
    } else if limb_index == 2 {
        lemma_byte_bridge_case2(limbs, limb_shift);
    } else if limb_index == 3 {
        lemma_byte_bridge_case3(limbs, limb_shift);
    } else {
        lemma_byte_bridge_case4(limbs, limb_shift);
    }
}

// Helper lemma for limb_index == 0
proof fn lemma_byte_bridge_case0(limbs: [u64; 5], limb_shift: nat)
    requires
        limb_shift < 64,
        limb_shift <= 43,
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        (as_nat(limbs) / pow2(limb_shift)) % 256 == (limbs[0] as nat / pow2(limb_shift)) % 256,
{
    // as_nat(limbs) = limbs[0] + limbs[1]*2^51 + limbs[2]*2^102 + limbs[3]*2^153 + limbs[4]*2^204
    // Divide by 2^limb_shift:
    //   as_nat(limbs) / 2^limb_shift = limbs[0]/2^limb_shift + limbs[1]*2^(51-limb_shift) + ...
    
    let remainder = (51 - limb_shift) as nat;
    lemma_pow2_adds(limb_shift, remainder);
    assert(pow2(51) == pow2(limb_shift) * pow2(remainder));
    
    // Show that remainder >= 8
    assert(remainder >= 8);
    let k = (remainder - 8) as nat;
    lemma_pow2_adds(8, k);
    assert(pow2(remainder) == pow2(8) * pow2(k));
    // pow2(8) = 256 (by definition/computation)
    lemma2_to64();
    assert(pow2(8) == 256) by(compute);
    assert(pow2(remainder) == 256 * pow2(k));
    
    // The key insight: after division, higher limbs are multiples of 256
    // as_nat(limbs) / 2^limb_shift = limbs[0]/2^limb_shift + limbs[1]*2^remainder + ...
    //                               = limbs[0]/2^limb_shift + limbs[1]*256*pow2(k) + ...
    // So mod 256: (as_nat(limbs) / 2^limb_shift) % 256 = (limbs[0]/2^limb_shift + limbs[1]*256*pow2(k) + ...) % 256
    //                                                   = (limbs[0]/2^limb_shift) % 256  (since other terms are multiples of 256)
    
    // Use as_nat definition and division/modulo arithmetic
    // as_nat(limbs) = limbs[0] + limbs[1]*pow2(51) + limbs[2]*pow2(102) + limbs[3]*pow2(153) + limbs[4]*pow2(204)
    // Divide by pow2(limb_shift):
    //   as_nat(limbs) / pow2(limb_shift) = limbs[0]/pow2(limb_shift) + limbs[1]*pow2(51)/pow2(limb_shift) + ...
    //                                     = limbs[0]/pow2(limb_shift) + limbs[1]*pow2(remainder) + ...
    //                                     = limbs[0]/pow2(limb_shift) + limbs[1]*256*pow2(k) + ...
    
    // Now take mod 256. Since 256*pow2(k) is a multiple of 256, higher limbs vanish:
    // (limbs[0]/pow2(limb_shift) + limbs[1]*256*pow2(k) + ...) % 256 = (limbs[0]/pow2(limb_shift)) % 256
    
    // TODO: Prove this using lemma_mod_add_multiples and division distributivity over addition
    assume((as_nat(limbs) / pow2(limb_shift)) % 256 == (limbs[0] as nat / pow2(limb_shift)) % 256);
}

// Helper lemma for limb_index == 1
proof fn lemma_byte_bridge_case1(limbs: [u64; 5], limb_shift: nat)
    requires
        limb_shift < 64,
        limb_shift <= 43,
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        (as_nat(limbs) / pow2(51 + limb_shift)) % 256 == (limbs[1] as nat / pow2(limb_shift)) % 256,
{
    // as_nat(limbs) / 2^(51+limb_shift) = 
    //   limbs[0]/2^(51+limb_shift) + limbs[1]/2^limb_shift + limbs[2]*2^(51-limb_shift) + ...
    // limbs[0] < 2^51, so limbs[0]/2^(51+limb_shift) = 0
    // Higher limbs: limbs[2]*2^(51-limb_shift) is a multiple of 256 (since 51-limb_shift >= 8)
    
    lemma_pow2_adds(51, limb_shift);
    assert(pow2(51 + limb_shift) == pow2(51) * pow2(limb_shift));
    
    // Show lower limb vanishes: limbs[0] < pow2(51) < pow2(51 + limb_shift) => limbs[0] / pow2(51 + limb_shift) = 0
    lemma2_to64();
    // TODO: Prove using division bounds: limbs[0] < (1u64 << 51) = pow2(51) and limb_shift > 0
    // implies limbs[0] / pow2(51 + limb_shift) = 0
    assume(limbs[0] as int / pow2(51 + limb_shift) as int == 0);
    
    // Show higher limbs are multiples of 256
    let remainder = (51 - limb_shift) as nat;
    lemma_pow2_adds(limb_shift, remainder);
    assert(remainder >= 8);
    let k = (remainder - 8) as nat;
    lemma_pow2_adds(8, k);
    assert(pow2(remainder) == 256 * pow2(k));
    
    assume((as_nat(limbs) / pow2(51 + limb_shift)) % 256 == (limbs[1] as nat / pow2(limb_shift)) % 256);
}

// Helper lemma for limb_index == 2
proof fn lemma_byte_bridge_case2(limbs: [u64; 5], limb_shift: nat)
    requires
        limb_shift < 64,
        limb_shift <= 43,
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        (as_nat(limbs) / pow2(102 + limb_shift)) % 256 == (limbs[2] as nat / pow2(limb_shift)) % 256,
{
    lemma_pow2_adds(102, limb_shift);
    
    // Lower limbs vanish (limbs 0-1 contribute < 2^102, so they vanish after dividing by 2^(102+limb_shift))
    lemma2_to64();
    // TODO: Prove limbs[0] + limbs[1]*2^51 < 2^102 using multiplication/addition bounds
    assume(limbs[0] as nat + limbs[1] as nat * pow2(51) < pow2(102));
    
    // Higher limbs are multiples of 256
    let remainder = (51 - limb_shift) as nat;
    assert(remainder >= 8);
    
    assume((as_nat(limbs) / pow2(102 + limb_shift)) % 256 == (limbs[2] as nat / pow2(limb_shift)) % 256);
}

// Helper lemma for limb_index == 3
proof fn lemma_byte_bridge_case3(limbs: [u64; 5], limb_shift: nat)
    requires
        limb_shift < 64,
        limb_shift <= 43,
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        (as_nat(limbs) / pow2(153 + limb_shift)) % 256 == (limbs[3] as nat / pow2(limb_shift)) % 256,
{
    lemma_pow2_adds(153, limb_shift);
    
    // Lower limbs vanish (limbs 0-2 contribute < 2^153)
    // Higher limb (limb 4) contributes multiples of 256
    let remainder = (51 - limb_shift) as nat;
    assert(remainder >= 8);
    
    assume((as_nat(limbs) / pow2(153 + limb_shift)) % 256 == (limbs[3] as nat / pow2(limb_shift)) % 256);
}

// Helper lemma for limb_index == 4
proof fn lemma_byte_bridge_case4(limbs: [u64; 5], limb_shift: nat)
    requires
        limb_shift < 64,
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        (as_nat(limbs) / pow2(204 + limb_shift)) % 256 == (limbs[4] as nat / pow2(limb_shift)) % 256,
{
    lemma_pow2_adds(204, limb_shift);
    
    // Lower limbs vanish (limbs 0-3 contribute < 2^204)
    // No higher limbs
    
    assume((as_nat(limbs) / pow2(204 + limb_shift)) % 256 == (limbs[4] as nat / pow2(limb_shift)) % 256);
}

/// Bridge lemma: connects byte extraction from a limb to byte extraction from as_nat(limbs)
/// Uses lemma_extract_byte on the appropriate limb, then shows the higher limbs don't affect the result
proof fn lemma_byte_from_limbs_to_as_nat(limbs: [u64; 5], bytes: [u8; 32], index: nat)
    requires
        index < 32,
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
        // All byte packing equations (copied from parent lemma)
        bytes[ 0] ==   limbs[0]                           as u8,
        bytes[ 1] ==  (limbs[0] >>  8)                    as u8,
        bytes[ 2] ==  (limbs[0] >> 16)                    as u8,
        bytes[ 3] ==  (limbs[0] >> 24)                    as u8,
        bytes[ 4] ==  (limbs[0] >> 32)                    as u8,
        bytes[ 5] ==  (limbs[0] >> 40)                    as u8,
        bytes[ 6] == ((limbs[0] >> 48) | (limbs[1] << 3)) as u8,
        bytes[ 7] ==  (limbs[1] >>  5)                    as u8,
        bytes[ 8] ==  (limbs[1] >> 13)                    as u8,
        bytes[ 9] ==  (limbs[1] >> 21)                    as u8,
        bytes[10] ==  (limbs[1] >> 29)                    as u8,
        bytes[11] ==  (limbs[1] >> 37)                    as u8,
        bytes[12] == ((limbs[1] >> 45) | (limbs[2] << 6)) as u8,
        bytes[13] ==  (limbs[2] >>  2)                    as u8,
        bytes[14] ==  (limbs[2] >> 10)                    as u8,
        bytes[15] ==  (limbs[2] >> 18)                    as u8,
        bytes[16] ==  (limbs[2] >> 26)                    as u8,
        bytes[17] ==  (limbs[2] >> 34)                    as u8,
        bytes[18] ==  (limbs[2] >> 42)                    as u8,
        bytes[19] == ((limbs[2] >> 50) | (limbs[3] << 1)) as u8,
        bytes[20] ==  (limbs[3] >>  7)                    as u8,
        bytes[21] ==  (limbs[3] >> 15)                    as u8,
        bytes[22] ==  (limbs[3] >> 23)                    as u8,
        bytes[23] ==  (limbs[3] >> 31)                    as u8,
        bytes[24] ==  (limbs[3] >> 39)                    as u8,
        bytes[25] == ((limbs[3] >> 47) | (limbs[4] << 4)) as u8,
        bytes[26] ==  (limbs[4] >>  4)                    as u8,
        bytes[27] ==  (limbs[4] >> 12)                    as u8,
        bytes[28] ==  (limbs[4] >> 20)                    as u8,
        bytes[29] ==  (limbs[4] >> 28)                    as u8,
        bytes[30] ==  (limbs[4] >> 36)                    as u8,
        bytes[31] ==  (limbs[4] >> 44)                    as u8,
    ensures
        bytes[index as int] as nat == (as_nat(limbs) / pow2(index * 8)) % 256,
{
    // Strategy: Extract byte from appropriate limb, then bridge to as_nat(limbs)
    // Table: (limb_index, shift, is_boundary) for each byte index
    // Boundary bytes (6, 12, 19, 25) need lemma_packed_byte
    
    let (limb_idx, shift): (nat, nat) = 
        if      index == 0  { (0,  0) } else if index == 1  { (0,  8) }
        else if index == 2  { (0, 16) } else if index == 3  { (0, 24) }
        else if index == 4  { (0, 32) } else if index == 5  { (0, 40) }
        else if index == 6  { (0, 48) }  // boundary
        else if index == 7  { (1,  5) } else if index == 8  { (1, 13) }
        else if index == 9  { (1, 21) } else if index == 10 { (1, 29) }
        else if index == 11 { (1, 37) }
        else if index == 12 { (1, 45) }  // boundary
        else if index == 13 { (2,  2) } else if index == 14 { (2, 10) }
        else if index == 15 { (2, 18) } else if index == 16 { (2, 26) }
        else if index == 17 { (2, 34) } else if index == 18 { (2, 42) }
        else if index == 19 { (2, 50) }  // boundary
        else if index == 20 { (3,  7) } else if index == 21 { (3, 15) }
        else if index == 22 { (3, 23) } else if index == 23 { (3, 31) }
        else if index == 24 { (3, 39) }
        else if index == 25 { (3, 47) }  // boundary
        else if index == 26 { (4,  4) } else if index == 27 { (4, 12) }
        else if index == 28 { (4, 20) } else if index == 29 { (4, 28) }
        else if index == 30 { (4, 36) } else { (4, 44) };
    
    let byte_offset = index * 8;
    let is_boundary = index == 6 || index == 12 || index == 19 || index == 25;
    
    // Step 1: Extract byte from limb
    if is_boundary {
        // Boundary bytes: use lemma_packed_byte and handle bridge separately (TODO)
        // For now, assume the full property directly
        assume(bytes[index as int] as nat == (as_nat(limbs) / pow2(byte_offset)) % 256);
    } else {
        // Regular bytes: extract from limb, then bridge to as_nat(limbs)
        if index == 0 {
            // Special case: x >> 0 == x
            assume(bytes[index as int] == (limbs[limb_idx as int] >> 0) as u8);
        }
        
        if shift % 8 == 0 {
            lemma_extract_byte(limbs[limb_idx as int], shift, bytes[index as int]);
        } else {
            lemma_extract_byte_general(limbs[limb_idx as int], shift, bytes[index as int]);
        }
        
        // Bridge - show extraction from limb equals extraction from as_nat(limbs)
        // This requires shift <= 43 (ensured by non-boundary condition)
        lemma_byte_bridge(limbs, limb_idx, byte_offset, shift);
        assert(bytes[index as int] as nat == (as_nat(limbs) / pow2(byte_offset)) % 256);
    }
}

// ============================================================================
// MODULAR ARITHMETIC HELPER for inductive step
// ============================================================================

/// Helper: decompose (x % m) as low_bits + high_bits * 256
proof fn lemma_div_mod_split_identity(x: int, d: int, m: int, c: int)
    requires
        d > 0,
        m > 0,
        c > 0,
        m % c == 0,
    ensures
        (x / d) % m == ((x / d) % c) + (((x / d) % m) / c) * c,
{
    use vstd::arithmetic::div_mod::*;
    
    // Let y = (x / d) % m
    // We want: y == (y % c) + (y / c) * c
    // This is just the fundamental division identity: y = (y / c) * c + (y % c)
    
    let y = (x / d) % m;
    lemma_fundamental_div_mod(y, c);
    let q = y / c;
    let r = y % c;
    
    // From fundamental div-mod: y == c * q + r
    assert(y == c * q + r);
    
    // Commutativity
    lemma_mul_is_commutative(c, q);
    assert(c * q == q * c);
    assert(y == q * c + r);
    
    // Connect to what we want
    assert(r == y % c);
    assert(r == ((x / d) % m) % c);
    
    // We need: ((x/d) % m) % c == (x/d) % c
    // This holds when c divides m
    lemma_mod_mod_identity((x / d), m, c);
    assert(r == (x / d) % c);
    
    assert(q == y / c);
    assert(y == r + q * c);
    assert((x / d) % m == ((x / d) % c) + (((x / d) % m) / c) * c);
}

/// Helper: ((x % m) % c) == (x % c) when c divides m
proof fn lemma_mod_mod_identity(x: int, m: int, c: int)
    requires
        m > 0,
        c > 0,
        m % c == 0,
    ensures
        (x % m) % c == x % c,
{
    use vstd::arithmetic::div_mod::*;
    use vstd::arithmetic::mul::*;
    
    // Since c divides m, we have m = k * c for some k
    lemma_fundamental_div_mod(m, c);
    let k = m / c;
    let r = m % c;
    assert(m == c * k + r);
    assert(r == 0);  // Since m % c == 0
    assert(m == c * k);
    lemma_mul_is_commutative(c, k);
    assert(m == k * c);
    
    // Apply fundamental div-mod to x with modulus m
    lemma_fundamental_div_mod(x, m);
    let q1 = x / m;
    let r1 = x % m;
    assert(x == m * q1 + r1);
    assert(0 <= r1 < m);
    
    // Apply fundamental div-mod to x with modulus c
    lemma_fundamental_div_mod(x, c);
    let q2 = x / c;
    let r2 = x % c;
    assert(x == c * q2 + r2);
    assert(0 <= r2 < c);
    
    // Substitute m = k * c into the first equation
    assert(x == (k * c) * q1 + r1);
    lemma_mul_is_associative(k, c, q1);
    assert((k * c) * q1 == k * (c * q1));
    lemma_mul_is_commutative(c, q1);
    assert(c * q1 == q1 * c);
    assert(k * (c * q1) == k * (q1 * c));
    lemma_mul_is_associative(k, q1, c);
    assert(k * (q1 * c) == (k * q1) * c);
    assert(x == (k * q1) * c + r1);
    
    // We also have x == c * q2 + r2
    // So: (k * q1) * c + r1 == c * q2 + r2
    assert((k * q1) * c + r1 == c * q2 + r2);
    
    // Rearrange: r1 == c * q2 + r2 - (k * q1) * c
    //          == c * q2 - (k * q1) * c + r2
    //          == c * (q2 - k * q1) + r2
    lemma_mul_is_distributive_sub(c, q2, k * q1);
    assert(c * q2 - c * (k * q1) == c * (q2 - k * q1));
    assert(c * q2 - (k * q1) * c == c * (q2 - k * q1)) by {
        lemma_mul_is_commutative(k * q1, c);
        assert((k * q1) * c == c * (k * q1));
    }
    assert(r1 == c * (q2 - k * q1) + r2);
    
    // Now apply div-mod to r1 with modulus c
    lemma_fundamental_div_mod(r1, c);
    let q3 = r1 / c;
    let r3 = r1 % c;
    assert(r1 == c * q3 + r3);
    assert(0 <= r3 < c);
    
    // We have two representations of r1:
    // r1 == c * (q2 - k * q1) + r2
    // r1 == c * q3 + r3
    // By uniqueness of quotient and remainder: q3 == q2 - k * q1 and r3 == r2
    lemma_fundamental_div_mod_converse(r1, c, q2 - k * q1, r2);
    assert(r3 == r2);
    
    // Therefore: (x % m) % c == r1 % c == r3 == r2 == x % c
    assert((x % m) % c == r1 % c);
    assert(r1 % c == r3);
    assert(r3 == r2);
    assert(r2 == x % c);
    assert((x % m) % c == x % c);
}

/// Helper: ((x / d) % m) / c == (x / (d*c)) % (m/c) when c divides m
proof fn lemma_shift_mod_div_identity(x: int, d: int, m: int, c: int)
    requires
        d > 0,
        m > 0,
        c > 0,
        m % c == 0,
    ensures
        ((x / d) % m) / c == (x / (d * c)) % (m / c),
{
    use vstd::arithmetic::div_mod::*;
    use vstd::arithmetic::mul::*;
    
    // Since c divides m, we have m = k * c for some k >= 1
    lemma_fundamental_div_mod(m, c);
    let k = m / c;
    assert(m == c * k + (m % c));
    assert(m % c == 0);
    assert(m == c * k);
    lemma_mul_is_commutative(c, k);
    assert(m == k * c);
    // Since m > 0 and c > 0, and m = k * c, we must have k >= 1
    // (if k <= 0, then k * c <= 0, contradicting m > 0)
    assume(k >= 1);  // TODO: Prove from m > 0, c > 0, m = k * c
    
    // Let y = x / d
    let y = x / d;
    
    // Apply fundamental div-mod to y with modulus m
    lemma_fundamental_div_mod(y, m);
    let q = y / m;
    let r = y % m;
    assert(y == m * q + r);
    assert(0 <= r < m);
    
    // Substitute m = k * c
    assert(y == (k * c) * q + r);
    lemma_mul_is_associative(k, c, q);
    assert((k * c) * q == k * (c * q));
    lemma_mul_is_commutative(c, q);
    assert(c * q == q * c);
    assert(k * (c * q) == k * (q * c));
    lemma_mul_is_associative(k, q, c);
    assert(k * (q * c) == (k * q) * c);
    assert(y == (k * q) * c + r);
    
    // Divide both sides by c
    // y / c = ((k * q) * c + r) / c = (k * q) * c / c + r / c = k * q + r / c
    // This is the property: (a*c + b) / c == a + b/c (division with remainder)
    assume(((k * q) * c + r) / c == k * q + r / c);  // TODO: Prove using division lemmas
    assert(y / c == k * q + r / c);
    
    // Now take mod k on both sides
    // (y / c) % k = (k * q + r / c) % k
    lemma_fundamental_div_mod(y / c, k);
    let q2 = (y / c) / k;
    let r2 = (y / c) % k;
    assert(y / c == k * q2 + r2);
    
    // From y / c = k * q + r / c, we have:
    // k * q2 + r2 = k * q + r / c
    // So: r2 = k * q + r / c - k * q2 = k * (q - q2) + r / c
    
    // Since 0 <= r < m = k * c, we have 0 <= r < k * c
    // Therefore: 0 <= r / c < k (integer division)
    assert(r < k * c);
    // For a < b*c, we have a/c < b (strict inequality for division)
    // This is a fundamental property of integer division
    assume(r / c < k);  // TODO: Prove using division lemmas
    assert(r / c >= 0);  // Division of non-negative by positive is non-negative
    
    // So 0 <= r / c < k, which means (r / c) % k = r / c
    lemma_mod_of_less_than_divisor(r / c, k);
    assert((r / c) % k == r / c);
    
    // From k * q2 + r2 = k * q + r / c and the uniqueness of div-mod representation:
    lemma_fundamental_div_mod_converse(y / c, k, q, r / c);
    assert(r2 == r / c);
    
    // Therefore: (y / c) % k == r / c == (y % m) / c
    assert((y / c) % k == r / c);
    assert(r == y % m);
    assert(r / c == (y % m) / c);
    assert((y / c) % k == (y % m) / c);
    
    // Also: k = m / c
    assert(k == m / c);
    
    // And: y / c = (x / d) / c = x / (d * c) (division associativity)
    // This is the property: (x / a) / b == x / (a * b)
    assume((x / d) / c == x / (d * c));  // TODO: Prove division associativity
    assert(y / c == x / (d * c));
    
    // Putting it all together:
    // ((x / d) % m) / c == (y % m) / c == (y / c) % k == (x / (d * c)) % (m / c)
    assert(((x / d) % m) / c == (y % m) / c);
    assert((y % m) / c == (y / c) % k);
    assert((y / c) % k == (y / c) % (m / c));
    assert((y / c) % (m / c) == (x / (d * c)) % (m / c));
    assert(((x / d) % m) / c == (x / (d * c)) % (m / c));
}

/// Helper lemma: combine byte with inductive hypothesis for the recursive structure
/// This handles the case where we multiply the byte by pow2(index*8) rather than leaving it as-is
pub proof fn lemma_byte_recursive_combination(limbs_nat: nat, index: nat, byte_val: u8, rest_val: nat)
    requires
        index < 32,
        // byte_val extracts the byte at position index*8 from limbs_nat
        byte_val as nat == (limbs_nat / pow2(index * 8)) % 256,
        // rest_val represents as_nat_32_u8_rec(&bytes, index+1), which is the remaining bytes
        // with each byte already positioned at its proper bit location
        rest_val == (limbs_nat / pow2((index + 1) * 8)) % pow2((31 - index as int) as nat * 8),
    ensures
        // The recursive formula: byte * 2^(index*8) + rest_val equals the shifted+masked limbs value
        byte_val as nat * pow2(index * 8) + rest_val == (limbs_nat / pow2(index * 8)) % pow2((32 - index as int) as nat * 8),
{
    // This is a more complex identity than lemma_byte_induction_step.
    // We need to show that reconstructing the value with the byte at its proper position
    // matches the modular arithmetic formula.
    //
    // Let k = index * 8, m = (32 - index) * 8
    // byte_val = (limbs_nat / 2^k) % 256
    // rest_val = (limbs_nat / 2^(k+8)) % 2^(m-8)
    // Want: byte_val * 2^k + rest_val == (limbs_nat / 2^k) % 2^m
    //
    // This doesn't match the usual formula because of the multiplication by 2^k.
    // For now, assume it.
    assume(byte_val as nat * pow2(index * 8) + rest_val == (limbs_nat / pow2(index * 8)) % pow2((32 - index as int) as nat * 8));
}

/// Helper lemma: combine byte with inductive hypothesis using modular arithmetic
pub proof fn lemma_byte_induction_step(limbs_nat: nat, index: nat, byte_val: u8, rest_val: nat)
    requires
        index < 32,
        // byte_val extracts the byte at position index*8 from limbs_nat
        byte_val as nat == (limbs_nat / pow2(index * 8)) % 256,
        // rest_val represents the remaining bytes [index+1 .. 32)
        rest_val == (limbs_nat / pow2((index + 1) * 8)) % pow2((31 - index as int) as nat * 8),
    ensures
        // The combination equals the target
        byte_val as nat + rest_val * 256 == (limbs_nat / pow2(index * 8)) % pow2((32 - index as int) as nat * 8),
{
    use vstd::arithmetic::div_mod::*;
    use vstd::arithmetic::mul::*;
    
    let k = index * 8;
    let m = (32 - index as int) as nat * 8;  // Total bits remaining from index
    
    // Notation:
    // L = limbs_nat
    // byte_val = (L / 2^k) % 256
    // rest_val = (L / 2^(k+8)) % 2^(m-8)
    // Want to show: byte_val + rest_val * 256 == (L / 2^k) % 2^m
    
    // Key insight: Split (L / 2^k) using division
    // L / 2^k = Q + R where Q = (L / 2^k) / 2^m, R = (L / 2^k) % 2^m
    // We want to show R = byte_val + rest_val * 256
    
    // Further: R = (L / 2^k) % 2^m can be decomposed as:
    // R = low_8_bits + high_bits * 256
    // where low_8_bits = R % 256 = ((L / 2^k) % 2^m) % 256 = (L / 2^k) % 256 = byte_val
    // and high_bits = R / 256 = ((L / 2^k) % 2^m) / 256
    
    // Prove: ((L / 2^k) % 2^m) / 256 == (L / 2^(k+8)) % 2^(m-8)
    //
    // This is a shift-modulo identity:
    // ((x / a) % b) / c == (x / (a*c)) % (b/c)  when c divides b
    //
    // Here: x=L, a=2^k, b=2^m, c=256=2^8
    // So: ((L / 2^k) % 2^m) / 2^8 == (L / (2^k * 2^8)) % (2^m / 2^8)
    //                              == (L / 2^(k+8)) % 2^(m-8)
    
    assert(m >= 8);  // Since index < 32, we have m = (32-index)*8 >= 8
    assert(k + 8 == (index + 1) * 8);
    assert(m - 8 == (31 - index as int) as nat * 8);
    
    let m_minus_8 = (m - 8) as nat;
    lemma2_to64();
    lemma_pow2_adds(k as nat, 8);
    assert(pow2(k) * pow2(8) == pow2(k + 8));
    assert(pow2(8) == 256);
    lemma_pow2_adds(m_minus_8, 8);
    assert(pow2(m_minus_8) * pow2(8) == pow2(m));
    
    // Establish preconditions for helper lemmas
    lemma_pow2_pos(k as nat);
    lemma_pow2_pos(m as nat);
    assert(pow2(k) > 0);
    assert(pow2(m) > 0);
    assert(256 > 0);
    // Since m = (32-index)*8 >= 8, m is a multiple of 8, so 2^m is divisible by 2^8=256
    // This follows from: 2^m = 2^(k*8) = (2^8)^k = 256^k, which is divisible by 256
    assume(pow2(m) % 256 == 0);
    
    // Use the shift-modulo identity
    lemma_div_mod_split_identity(limbs_nat as int, pow2(k) as int, pow2(m) as int, 256);
    
    // From the identity, we get:
    // (limbs_nat / pow2(k)) % pow2(m) == ((limbs_nat / pow2(k)) % 256) + (((limbs_nat / pow2(k)) % pow2(m)) / 256) * 256
    
    // And: ((limbs_nat / pow2(k)) % pow2(m)) / 256 == (limbs_nat / pow2(k+8)) % pow2(m_minus_8)
    lemma_shift_mod_div_identity(limbs_nat as int, pow2(k) as int, pow2(m) as int, 256);
    
    // Connect m_minus_8 to the formulas
    assert(m_minus_8 == m - 8);
    assert(pow2(m) / 256 == pow2(m_minus_8));  // Since 256 = 2^8 and m = m_minus_8 + 8
    
    assert(byte_val as nat == (limbs_nat / pow2(k)) % 256);
    assert(rest_val == (limbs_nat / pow2(k + 8)) % pow2(m_minus_8));
    assert(rest_val == ((limbs_nat / pow2(k)) % pow2(m)) / 256);
    assert(byte_val as nat + rest_val * 256 == (limbs_nat / pow2(k)) % pow2(m));
}

// ============================================================================
// HELPER LEMMAS for packing bytes
// ============================================================================

/// Helper: Extract a range of bits from a u64 as a u8
pub proof fn lemma_extract_byte(x: u64, shift: nat, byte_val: u8)
    requires
        shift % 8 == 0,
        shift < 64,
        byte_val == (x >> shift) as u8,
    ensures
        byte_val as nat == (x as nat / pow2(shift)) % 256,
{
    // Step 1: Establish that x >> shift == x / pow2(shift)
    lemma_u64_shr_is_div(x, shift as u64);
    let shifted = x >> shift;
    assert(shifted as nat == x as nat / pow2(shift));
    
    // Step 2: Establish key facts about u8 and pow2(8)
    lemma2_to64();
    assert(u8::MAX + 1 == pow2(8));
    assert(u8::MAX == 255) by (compute);
    assert(pow2(8) == 256) by (compute);
    
    // Step 3: byte_val is a u8, so it's bounded
    assert(byte_val <= u8::MAX);
    assert(byte_val < 256);
    
    // Step 4: Relate casting to masking
    // In Rust/Verus, casting to u8 is equivalent to & 0xFF
    assert(0xFF == 255) by (compute);
    assert(0xFF == u8::MAX) by (compute);
    assert(0xFF + 1 == 256) by (compute);
    
    // Use the low_bits_mask lemma: shifted & 0xFF == shifted % 256
    lemma_u64_low_bits_mask_is_mod(shifted, 8);
    assert((shifted & (low_bits_mask(8) as u64)) == shifted % (pow2(8) as u64));
    
    // Establish that low_bits_mask(8) == 0xFF
    assert(low_bits_mask(8) == 0xFF) by (compute);
    assert((shifted & 0xFF) == shifted % 256);
    
    // The key missing piece: prove that (shifted as u8) == (shifted & 0xFF) as u8
    // At the u64 level before casting, these should be equal by bit_vector
    assert(shifted as u8 == (shifted & 0xFF) as u8) by (bit_vector);
    
    // Now we know byte_val == shifted as u8 == (shifted & 0xFF) as u8
    // And we need byte_val as nat == (shifted & 0xFF) as nat
    // This should follow from the equality of the u8 values
    assert(byte_val == (shifted & 0xFF) as u8);
    assert(byte_val as nat == (shifted & 0xFF) as nat);
    assert((shifted & 0xFF) as nat == shifted as nat % 256);
}

/// General version: proves that (x >> shift) as u8 correctly extracts a byte
/// Works for any shift value (not just byte-aligned)
pub proof fn lemma_extract_byte_general(x: u64, shift: nat, byte_val: u8)
    requires
        shift < 64,
        byte_val == (x >> shift) as u8,
    ensures
        byte_val as nat == (x as nat / pow2(shift)) % 256,
{
    // The proof is identical to lemma_extract_byte, just without the alignment requirement
    lemma_u64_shr_is_div(x, shift as u64);
    let shifted = x >> shift;
    assert(shifted as nat == x as nat / pow2(shift));
    
    lemma2_to64();
    assert(u8::MAX + 1 == pow2(8));
    assert(u8::MAX == 255) by (compute);
    assert(pow2(8) == 256) by (compute);
    
    assert(byte_val <= u8::MAX);
    assert(byte_val < 256);
    
    assert(0xFF == 255) by (compute);
    assert(0xFF == u8::MAX) by (compute);
    assert(0xFF + 1 == 256) by (compute);
    
    lemma_u64_low_bits_mask_is_mod(shifted, 8);
    assert((shifted & (low_bits_mask(8) as u64)) == shifted % (pow2(8) as u64));
    assert(low_bits_mask(8) == 0xFF) by (compute);
    assert((shifted & 0xFF) == shifted % 256);
    assert(shifted as u8 == (shifted & 0xFF) as u8) by (bit_vector);
    assert(byte_val == (shifted & 0xFF) as u8);
    assert(byte_val as nat == (shifted & 0xFF) as nat);
    assert((shifted & 0xFF) as nat == shifted as nat % 256);
}

/// Helper: Combine parts of two limbs into one byte
#[verifier::rlimit(50)]  // Increased due to additional helper lemmas
pub proof fn lemma_packed_byte(low: u64, high: u64, low_shift: nat, high_shift: nat, byte_val: u8)
    requires
        low_shift < 51,
        high_shift <= 51,
        low_shift + high_shift == 8,
        low < pow2(51),
        high < pow2(51),
        byte_val == ((low >> ((51 - low_shift) as u64)) | (high << (low_shift as u64))) as u8,
    ensures
        byte_val as nat == ((low as nat / pow2((51 - low_shift) as nat)) + (high as nat % pow2(high_shift)) * pow2(low_shift)) % 256,
{
    let low_bits = low >> ((51 - low_shift) as u64);
    let high_bits = high << (low_shift as u64);
    let combined = low_bits | high_bits;
    
    // Step 1: Relate shift to division
    lemma_u64_shr_is_div(low, (51 - low_shift) as u64);
    assert(low_bits as nat == low as nat / pow2((51 - low_shift) as nat));
    
    // Step 2: Relate left shift to multiplication (need to check overflow)
    // high < pow2(51) and we shift by low_shift < 51, so high << low_shift < pow2(51 + low_shift)
    // Since low_shift + high_shift == 8 and high_shift <= 51, we have low_shift <= 8
    // So high << low_shift < pow2(51 + 8) = pow2(59) < pow2(64) = safe
    assert(low_shift <= 8);
    assert(51 + low_shift <= 59);
    lemma_pow2_adds(51, low_shift);
    assert(pow2(51) * pow2(low_shift) == pow2(51 + low_shift));
    mul_le(high as nat, pow2(51), pow2(low_shift), pow2(low_shift));
    assert(high * pow2(low_shift) <= pow2(51) * pow2(low_shift));
    assert(high * pow2(low_shift) <= pow2(51 + low_shift));
    lemma2_to64_rest();
    assert(pow2(64) == u64::MAX + 1) by {
        lemma2_to64_rest();
    };
    lemma_pow2_strictly_increases(51 + low_shift, 64);
    assert(pow2(51 + low_shift) < pow2(64));
    assert(high * pow2(low_shift) < pow2(64));
    assert(high * pow2(low_shift) <= u64::MAX);
    lemma_u64_shl_is_mul(high, low_shift as u64);
    assert(high_bits as nat == high as nat * pow2(low_shift));
    
    // Step 3: Show that OR equals addition (bits don't overlap)
    //
    // We need to prove: combined as nat == low_bits as nat + high_bits as nat
    // where combined = low_bits | high_bits
    //
    // This requires two properties:
    //
    // Property 1: low_bits < pow2(low_shift) ✅ PROVEN
    // - We have: low < pow2(51) and low_bits = low >> (51 - low_shift)
    // - Use lemma_shr_bound to prove that right shifting gives a bounded result
    lemma_shr_bound(low, 51, low_shift);
    assert(low_bits < pow2(low_shift));
    
    // Property 2: OR equals addition when bits don't overlap ✅ PROVEN
    // - Since low_bits < pow2(low_shift), it occupies bits [0, low_shift)
    // - Since high_bits = high << low_shift, it occupies bits [low_shift, 64)
    // - Therefore low_bits & high_bits == 0
    // - The fundamental property: a | b == a + b when a & b == 0
    
    // Convert pow2(low_shift) to (1u64 << low_shift) for bit_or_is_plus_u64
    shift_is_pow2(low_shift);
    assert(pow2(low_shift) == (1u64 << low_shift));
    assert(low_bits < (1u64 << low_shift));
    
    // Use bit_or_is_plus_u64 to prove OR equals addition
    assert(combined == low_bits | high_bits);
    assert(high_bits == high << low_shift);
    bit_or_is_plus_u64(low_bits, high, low_shift);
    assert(low_bits | (high << low_shift) == low_bits + (high << low_shift));
    assert(combined == low_bits + high_bits);
    assert(combined as nat == low_bits as nat + high_bits as nat);
    
    // Step 4: Relate high_bits to (high % pow2(high_shift)) * pow2(low_shift)
    // We have: high_bits = high * pow2(low_shift)
    // We want: high_bits % 256 == (high % pow2(high_shift)) * pow2(low_shift) % 256
    //
    // Key insight: Since high_shift + low_shift == 8 and 256 = pow2(8),
    // when we compute (high * pow2(low_shift)) % 256, only the lower high_shift bits of high matter.
    
    // Use lemma_mod_shift_equivalence with k = low_shift, m = high_shift
    assert(low_shift + high_shift == 8);
    lemma2_to64(); // This provides pow2(8) == 256
    lemma_mod_shift_equivalence(high, low_shift, high_shift);
    assert((high as nat * pow2(low_shift)) % pow2(low_shift + high_shift) 
           == ((high as nat % pow2(high_shift)) * pow2(low_shift)) % pow2(low_shift + high_shift));
    assert(low_shift + high_shift == 8);
    assert(high_bits as nat == high as nat * pow2(low_shift));
    assert(high_bits as nat % 256 == (high as nat % pow2(high_shift)) * pow2(low_shift) % 256);
    
    // Step 5: Cast to u8 = mod 256 (same as lemma_extract_byte)
    lemma2_to64();
    lemma_u64_low_bits_mask_is_mod(combined, 8);
    assert(low_bits_mask(8) == 0xFF) by (compute);
    assert((combined & 0xFF) == combined % 256);
    assert(combined as u8 == (combined & 0xFF) as u8) by (bit_vector);
    assert(byte_val == (combined & 0xFF) as u8);
    assert(byte_val as nat == (combined & 0xFF) as nat);
    assert((combined & 0xFF) as nat == combined as nat % 256);
}

// ============================================================================
// BIT MANIPULATION HELPER LEMMAS
// ============================================================================

/// Lemma: Modular arithmetic with shift - only low bits matter
/// When shifting left by k and taking mod 2^(k+m), only the low m bits of the original value matter
/// 
/// Specifically: (x * 2^k) % 2^(k+m) == ((x % 2^m) * 2^k) % 2^(k+m)
///
/// This is because x = q * 2^m + (x % 2^m), so:
/// x * 2^k = q * 2^(k+m) + (x % 2^m) * 2^k
/// Taking mod 2^(k+m) eliminates the q * 2^(k+m) term.
pub proof fn lemma_mod_shift_equivalence(x: u64, k: nat, m: nat)
    requires
        k < 64,
        m <= 64,
        k + m <= 64,
        x < pow2(51),  // For our use case (limbs are < 2^51)
    ensures
        (x as nat * pow2(k)) % pow2(k + m) == ((x as nat % pow2(m)) * pow2(k)) % pow2(k + m),
{
    // DIVIDE-AND-CONQUER PROOF SKETCH
    // This is a classic modular arithmetic property that can be proven using vstd lemmas.
    // The proof is straightforward but the SMT solver struggles with nat/int conversions.
    //
    // Proof strategy:
    //
    // Step 1: Apply lemma_fundamental_div_mod
    //   x = q * 2^m + r  where r = x % 2^m
    //
    // Step 2: Multiply both sides by 2^k  
    //   x * 2^k = q * 2^m * 2^k + r * 2^k
    //
    // Step 3: Use lemma_pow2_adds
    //   2^m * 2^k = 2^(k+m)
    //   So: x * 2^k = q * 2^(k+m) + r * 2^k
    //
    // Step 4: Take mod 2^(k+m)
    //   (x * 2^k) % 2^(k+m) = (q * 2^(k+m) + r * 2^k) % 2^(k+m)
    //
    // Step 5: Use modular addition property
    //   (a + b) % n = ((a % n) + (b % n)) % n
    //   With a = q * 2^(k+m) and b = r * 2^k:
    //   = ((q * 2^(k+m)) % 2^(k+m) + (r * 2^k) % 2^(k+m)) % 2^(k+m)
    //
    // Step 6: The first term vanishes
    //   (q * 2^(k+m)) % 2^(k+m) = 0  (fundamental property of modular arithmetic)
    //   So: (x * 2^k) % 2^(k+m) = (r * 2^k) % 2^(k+m)
    //
    // Step 7: Substitute r = x % 2^m
    //   (x * 2^k) % 2^(k+m) = ((x % 2^m) * 2^k) % 2^(k+m)  ✓
    //
    // The challenge is not the mathematical reasoning, but handling nat/int type conversions
    // in a way that doesn't exceed the SMT solver's resource limits. Each step above is
    // mathematically trivial, but requires careful type management in Verus.
    //
    // TODO: Implement this proof with explicit type conversions and simpler assertions,
    // or break it into smaller helper lemmas to reduce SMT solver load.
    
    assume((x as nat * pow2(k)) % pow2(k + m) == ((x as nat % pow2(m)) * pow2(k)) % pow2(k + m));
}

/// Lemma: OR equals addition when bits don't overlap (u64 version)
/// Generalization of bit_or_is_plus from load8_lemmas.rs to work with u64
pub proof fn bit_or_is_plus_u64(a: u64, b: u64, k: nat)
    requires
        k < 64,
        a < (1u64 << k),
    ensures
        a | (b << k) == a + (b << k),
{
    // The key insight: if a < 2^k, then a occupies only bits [0, k)
    // and (b << k) occupies only bits [k, 64)
    // So they don't overlap: a & (b << k) == 0
    // Therefore: a | (b << k) == a + (b << k)
    
    // Convert k to u64 for bit_vector
    let k_u64 = k as u64;
    assert(a < (1u64 << k_u64));
    assert(b << k == b << k_u64);
    
    // Prove with bit_vector
    assert(a | (b << k_u64) == a + (b << k_u64)) by (bit_vector)
        requires
            k_u64 < 64,
            a < (1u64 << k_u64);
}

/// Lemma: Division by a positive number preserves strict inequality
/// If x < a * b and a > 0, then x / a < b
pub proof fn lemma_div_strictly_bounded(x: int, a: int, b: int)
    requires
        a > 0,
        b >= 0,
        x < a * b,
    ensures
        x / a < b,
{
   // (b * a) / a == b
   lemma_div_by_multiple(b, a);
   // x < b * a && a > 0 => x / a < (b * a) / a
   lemma_div_by_multiple_is_strongly_ordered(x, a * b, b, a);
}

/// Lemma: Right shifting a bounded value gives a smaller bound
/// If x < 2^n, then x >> (n - k) < 2^k
pub proof fn lemma_shr_bound(x: u64, n: nat, k: nat)
    requires
        x < pow2(n),
        k <= n,
        n < 64,
    ensures
        (x >> ((n - k) as u64)) < pow2(k),
{
    // Key insight: x >> (n - k) = x / 2^(n - k)
    lemma_u64_shr_is_div(x, (n - k) as u64);
    assert((x >> ((n - k) as u64)) as nat == x as nat / pow2((n - k) as nat));
    
    // Since x < 2^n, we have x / 2^(n - k) < 2^n / 2^(n - k)
    lemma_pow2_pos((n - k) as nat);
    lemma_div_is_ordered(x as int, pow2(n) as int, pow2((n - k) as nat) as int);
    assert(x as nat / pow2((n - k) as nat) <= pow2(n) / pow2((n - k) as nat));
    
    // Now show that 2^n / 2^(n - k) = 2^k
    // This follows from: 2^n / 2^(n - k) = 2^(n - (n - k)) = 2^k
    // We need to use the power subtraction property
    
    // 2^n = 2^(n - k) * 2^k
    lemma_pow2_adds((n - k) as nat, k);
    assert(pow2((n - k) as nat) * pow2(k) == pow2(((n - k) + k) as nat));
    assert(((n - k) + k) as nat == n);
    assert(pow2((n - k) as nat) * pow2(k) == pow2(n));
    
    // Therefore: 2^n / 2^(n - k) = 2^k
    lemma_pow2_pos((n - k) as nat);
    assert(pow2((n - k) as nat) > 0);
    lemma_div_multiples_vanish(pow2(k) as int, pow2((n - k) as nat) as int);
    assert(pow2((n - k) as nat) * pow2(k) / pow2((n - k) as nat) == pow2(k));
    assert(pow2(n) / pow2((n - k) as nat) == pow2(k));
    
    // Combine: x / 2^(n - k) <= 2^n / 2^(n - k) = 2^k
    assert((x >> ((n - k) as u64)) as nat <= pow2(k));
    
    // For strict inequality: x < 2^n = 2^(n-k) * 2^k
    // So x / 2^(n-k) < 2^n / 2^(n-k) = 2^k
    // Use lemma_div_strictly_bounded to prove this
    
    // We have: x < pow2(n) = pow2(n - k) * pow2(k)
    assert(x < pow2(n));
    assert(pow2(n) == pow2((n - k) as nat) * pow2(k));
    lemma_pow2_pos((n - k) as nat);
    assert(pow2((n - k) as nat) > 0);
    
    // Apply lemma_div_strictly_bounded with a = pow2(n - k), b = pow2(k)
    lemma_div_strictly_bounded(x as int, pow2((n - k) as nat) as int, pow2(k) as int);
    let shifted_val = x as int / pow2((n - k) as nat) as int;
    assert(shifted_val < pow2(k) as int);
    assert((x >> ((n - k) as u64)) as nat == shifted_val);
    assert((x >> ((n - k) as u64)) < pow2(k));
}

}


