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
    q0: int,
    q1: int,
    q2: int,
    q3: int,
    q4: int,
    r0: int,
    r1: int,
    r2: int,
    r3: int,
    r4: int,
)
    requires
        true,
    ensures
        (q0 * pow2(51) as int + r0 - 19) + (q1 * pow2(51) as int + r1 - q0) * pow2(51) as int + (q2
            * pow2(51) as int + r2 - q1) * pow2(102) as int + (q3 * pow2(51) as int + r3 - q2)
            * pow2(153) as int + (q4 * pow2(51) as int + r4 - q3) * pow2(204) as int + 19 == q4
            * pow2(51) as int * pow2(204) as int + r0 + r1 * pow2(51) as int + r2 * pow2(102) as int
            + r3 * pow2(153) as int + r4 * pow2(204) as int,
{
    // Establish power relationships: 2^51 * 2^k = 2^(51+k)
    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);

    // Manually expand each multiplication and show the cancellations explicitly
    let lhs = (q0 * pow2(51) as int + r0 - 19) + (q1 * pow2(51) as int + r1 - q0) * pow2(51) as int
        + (q2 * pow2(51) as int + r2 - q1) * pow2(102) as int + (q3 * pow2(51) as int + r3 - q2)
        * pow2(153) as int + (q4 * pow2(51) as int + r4 - q3) * pow2(204) as int + 19;

    // Expand the multiplications using distributivity
    assert((q1 * pow2(51) as int + r1 - q0) * pow2(51) as int == q1 * pow2(51) as int * pow2(
        51,
    ) as int + r1 * pow2(51) as int - q0 * pow2(51) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(51) as int, q1 * pow2(51) as int + r1, q0);
        lemma_mul_is_distributive_add_other_way(pow2(51) as int, q1 * pow2(51) as int, r1);
    }

    assert((q2 * pow2(51) as int + r2 - q1) * pow2(102) as int == q2 * pow2(51) as int * pow2(
        102,
    ) as int + r2 * pow2(102) as int - q1 * pow2(102) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(102) as int, q2 * pow2(51) as int + r2, q1);
        lemma_mul_is_distributive_add_other_way(pow2(102) as int, q2 * pow2(51) as int, r2);
    }

    assert((q3 * pow2(51) as int + r3 - q2) * pow2(153) as int == q3 * pow2(51) as int * pow2(
        153,
    ) as int + r3 * pow2(153) as int - q2 * pow2(153) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(153) as int, q3 * pow2(51) as int + r3, q2);
        lemma_mul_is_distributive_add_other_way(pow2(153) as int, q3 * pow2(51) as int, r3);
    }

    assert((q4 * pow2(51) as int + r4 - q3) * pow2(204) as int == q4 * pow2(51) as int * pow2(
        204,
    ) as int + r4 * pow2(204) as int - q3 * pow2(204) as int) by {
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
    q0: int,
    q1: int,
    q2: int,
    q3: int,
    q4: int,
    r0: int,
    r1: int,
    r2: int,
    r3: int,
    r4: int,
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
    let value = limbs[0] as int + limbs[1] as int * pow2(51) as int + limbs[2] as int * pow2(
        102,
    ) as int + limbs[3] as int * pow2(153) as int + limbs[4] as int * pow2(204) as int + 19;

    assert(as_nat(limbs) == (limbs[0] as nat) + pow2(51) * (limbs[1] as nat) + pow2(102) * (
    limbs[2] as nat) + pow2(153) * (limbs[3] as nat) + pow2(204) * (limbs[4] as nat));

    assert((limbs[0] as nat) + pow2(51) * (limbs[1] as nat) + pow2(102) * (limbs[2] as nat) + pow2(
        153,
    ) * (limbs[3] as nat) + pow2(204) * (limbs[4] as nat) == limbs[0] as nat + (limbs[1] as nat)
        * pow2(51) + (limbs[2] as nat) * pow2(102) + (limbs[3] as nat) * pow2(153) + (
    limbs[4] as nat) * pow2(204)) by {
        lemma_mul_is_commutative(pow2(51) as int, limbs[1] as int);
        lemma_mul_is_commutative(pow2(102) as int, limbs[2] as int);
        lemma_mul_is_commutative(pow2(153) as int, limbs[3] as int);
        lemma_mul_is_commutative(pow2(204) as int, limbs[4] as int);
    }

    // Step 2: Solve for each limb using the division theorem equations

    // Step 3: Expand limbs[i] * 2^(51*i) using distributivity
    assert((q1 * pow2(51) as int + r1 - q0) * pow2(51) as int == q1 * pow2(51) as int * pow2(
        51,
    ) as int + r1 * pow2(51) as int - q0 * pow2(51) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(51) as int, q1 * pow2(51) as int + r1, q0);
        lemma_mul_is_distributive_add_other_way(pow2(51) as int, q1 * pow2(51) as int, r1);
    }

    assert((q2 * pow2(51) as int + r2 - q1) * pow2(102) as int == q2 * pow2(51) as int * pow2(
        102,
    ) as int + r2 * pow2(102) as int - q1 * pow2(102) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(102) as int, q2 * pow2(51) as int + r2, q1);
        lemma_mul_is_distributive_add_other_way(pow2(102) as int, q2 * pow2(51) as int, r2);
    }

    assert((q3 * pow2(51) as int + r3 - q2) * pow2(153) as int == q3 * pow2(51) as int * pow2(
        153,
    ) as int + r3 * pow2(153) as int - q2 * pow2(153) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(153) as int, q3 * pow2(51) as int + r3, q2);
        lemma_mul_is_distributive_add_other_way(pow2(153) as int, q3 * pow2(51) as int, r3);
    }

    assert((q4 * pow2(51) as int + r4 - q3) * pow2(204) as int == q4 * pow2(51) as int * pow2(
        204,
    ) as int + r4 * pow2(204) as int - q3 * pow2(204) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(204) as int, q4 * pow2(51) as int + r4, q3);
        lemma_mul_is_distributive_add_other_way(pow2(204) as int, q4 * pow2(51) as int, r4);
    }

    // Step 4: Define remainder and observe telescoping
    // When we substitute and expand, intermediate q_i terms cancel, leaving only q4 and remainders
    let remainder = r0 + r1 * pow2(51) as int + r2 * pow2(102) as int + r3 * pow2(153) as int + r4
        * pow2(204) as int;

    assert(limbs[0] as int + limbs[1] as int * pow2(51) as int + limbs[2] as int * pow2(102) as int
        + limbs[3] as int * pow2(153) as int + limbs[4] as int * pow2(204) as int + 19 == (q0
        * pow2(51) as int + r0 - 19) + (q1 * pow2(51) as int + r1 - q0) * pow2(51) as int + (q2
        * pow2(51) as int + r2 - q1) * pow2(102) as int + (q3 * pow2(51) as int + r3 - q2) * pow2(
        153,
    ) as int + (q4 * pow2(51) as int + r4 - q3) * pow2(204) as int + 19);

    // After algebraic simplification (intermediate terms cancel), we get: value = q4 * 2^255 + remainder
    lemma_radix51_telescoping_expansion(q0, q1, q2, q3, q4, r0, r1, r2, r3, r4);

    assert(q4 * pow2(51) as int * pow2(204) as int == q4 * pow2(255) as int) by {
        lemma_mul_is_associative(q4, pow2(51) as int, pow2(204) as int);
    }

    // Step 5: Apply uniqueness of division to conclude q4 = value / 2^255
    lemma_radix51_remainder_bound(r0, r1, r2, r3, r4);
    lemma_pow2_pos(255);
    lemma_fundamental_div_mod(value, pow2(255) as int);
    lemma_div_multiples_vanish_fancy(q4, remainder, pow2(255) as int);
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
        r0 + r1 * (pow2(51) as int) + r2 * (pow2(102) as int) + r3 * (pow2(153) as int) + r4 * (
        pow2(204) as int) < (pow2(255) as int),
{
    lemma_pow2_pos(51);
    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);

    let sum = r0 + r1 * (pow2(51) as int) + r2 * (pow2(102) as int) + r3 * (pow2(153) as int) + r4
        * (pow2(204) as int);

    // Each term r_i * 2^(51*i) < 2^51 * 2^(51*i) = 2^(51*(i+1))

    assert(r1 * pow2(51) <= pow2(102) - pow2(51)) by {
        pow2_mul_general(r1 as nat, 51, 51);
    }

    assert(r2 * pow2(102) <= pow2(153) - pow2(102)) by {
        pow2_mul_general(r2 as nat, 51, 102);
    }

    assert(r3 * pow2(153) <= pow2(204) - pow2(153)) by {
        pow2_mul_general(r3 as nat, 51, 153);
    }

    assert(r4 * pow2(204) <= pow2(255) - pow2(204)) by {
        pow2_mul_general(r4 as nat, 51, 204);
    }

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

    // Expand: 2^51 * (1 + 2^51 + 2^102 + 2^153 + 2^204)
    //       = 2^51 + 2^102 + 2^153 + 2^204 + 2^255
    assert(pow2(51) * sum_powers == pow2(51) * 1 + pow2(51) * (pow2(51) + pow2(102) + pow2(153)
        + pow2(204))) by {
        lemma_mul_is_distributive_add(
            pow2(51) as int,
            1,
            (pow2(51) + pow2(102) + pow2(153) + pow2(204)) as int,
        );
    }

    assert(pow2(51) * (pow2(51) + pow2(102) + pow2(153) + pow2(204)) == pow2(51) * pow2(51) + pow2(
        51,
    ) * (pow2(102) + pow2(153) + pow2(204))) by {
        lemma_mul_is_distributive_add(
            pow2(51) as int,
            pow2(51) as int,
            (pow2(102) + pow2(153) + pow2(204)) as int,
        );
    }

    assert(pow2(51) * (pow2(102) + pow2(153) + pow2(204)) == pow2(51) * pow2(102) + pow2(51) * (
    pow2(153) + pow2(204))) by {
        lemma_mul_is_distributive_add(
            pow2(51) as int,
            pow2(102) as int,
            (pow2(153) + pow2(204)) as int,
        );
    }

    assert(pow2(51) * (pow2(153) + pow2(204)) == pow2(51) * pow2(153) + pow2(51) * pow2(204)) by {
        lemma_mul_is_distributive_add(pow2(51) as int, pow2(153) as int, pow2(204) as int);
    }

    // Chain them together

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
    assert(pow2(51) * sum_powers - sum_powers == (pow2(51) + pow2(102) + pow2(153) + pow2(204)
        + pow2(255)) - (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204)));

    // Step 3: Simplify by cancellation
    // The terms 2^51, 2^102, 2^153, 2^204 cancel, leaving: 2^255 - 1
    assert((pow2(51) + pow2(102) + pow2(153) + pow2(204) + pow2(255)) - (1 + pow2(51) + pow2(102)
        + pow2(153) + pow2(204)) == pow2(255) - 1);
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
    assert(pow2(154) == pow2(153) * 2) by {
        lemma2_to64();
    }
    assert(pow2(154) == 2 * pow2(153)) by {
        lemma_mul_is_commutative(pow2(153) as int, 2);
    }
    lemma_pow2_strictly_increases(154, 204);

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
        lemma_mul_is_commutative(pow2(102) as int, 2);
    }
    lemma_pow2_strictly_increases(103, 153);

    // So pow2(51) + pow2(102) + pow2(153) < pow2(153) + pow2(153) = 2*pow2(153) = pow2(154) < pow2(204)

    // Therefore the full sum < pow2(204) + pow2(204) = 2*pow2(204) = pow2(205) < pow2(255)

    // Prove 2 * pow2(204) == pow2(205)
    lemma_pow2_adds(204, 1);
    assert(pow2(205) == pow2(204) * 2) by {
        lemma2_to64();
    }
    assert(pow2(205) == 2 * pow2(204)) by {
        lemma_mul_is_commutative(pow2(204) as int, 2);
    }

    lemma_pow2_strictly_increases(205, 255);
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
pub proof fn lemma_single_stage_division(limb: u64, carry_in: u64, stage_input: u64, carry_out: u64)
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

    // Prove the bound
    lemma_bounded_shr_51(stage_input);
}

/// Helper: Establishes division theorem for a single stage
/// Given the inputs and outputs of a stage, proves the division/modulo relationship
///
/// Note: carry_in is typically < 3 for stages 1-4, but equals 19 for stage 0
pub proof fn lemma_stage_division_theorem(limb: u64, carry_in: int, carry_out: int) -> (r: int)
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
    r
}

/// Helper lemma: proves that the carry propagation computes the division by 2^255
/// This shows that q represents (as_nat(limbs) + 19) / 2^255
///
/// Refactored into smaller pieces for better readability and maintainability.
pub proof fn lemma_carry_propagation_is_division(limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
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
    lemma_radix51_telescoping_direct(
        limbs,
        q0 as int,
        q1 as int,
        q2 as int,
        q3 as int,
        q4 as int,
        r0,
        r1,
        r2,
        r3,
        r4,
    );
}

// lemma_radix_51_geometric_sum: MOVED to unused_helper_lemmas.rs (superseded by lemma_radix_51_partial_geometric_sum)
/// Helper: Proves all intermediate carries are bounded by 3
pub proof fn lemma_all_carries_bounded_by_3(limbs: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
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
    assert(3 * pow2(51) <= u64::MAX) by {
        lemma2_to64_rest();
    }
    lemma_bounded_shr_51((limbs[0] + 19) as u64);

    // Prove q1 < 3
    lemma_bounded_shr_51((limbs[1] + q0) as u64);

    // Prove q2 < 3
    lemma_bounded_shr_51((limbs[2] + q1) as u64);

    // Prove q3 < 3
    lemma_bounded_shr_51((limbs[3] + q2) as u64);

    // Prove q4 < 3
    lemma_bounded_shr_51((limbs[4] + q3) as u64);
}

/// Helper: Proves q can only be 0 or 1 (not 2)
/// Also establishes the division relationship for reuse
pub proof fn lemma_q_is_binary(limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        as_nat(limbs) < 2 * p(),  // From reduce()'s postcondition
        q == compute_q_spec(limbs),
        q < 3,
    ensures
        q == 0 || q == 1,
        q as nat == (as_nat(limbs) + 19) / pow2(255),  // Export for reuse
{
    lemma_carry_propagation_is_division(limbs, q);

    // Establish basic facts
    lemma2_to64();
    pow255_gt_19();
    lemma_pow2_adds(255, 1);  // Establish pow2(256) == pow2(255) * 2

    // Simplified reasoning:
    // Since p() = 2^255 - 19 < 2^255, we have:
    // as_nat(limbs) < 2*p() < 2*2^255
    // Therefore: as_nat(limbs) + 19 < 2*2^255
    assert(p() < pow2(255)) by {
        pow255_gt_19();
    }

    // By integer division: if x < 2 * d, then x / d < 2
    lemma_pow2_pos(255);
    lemma_div_strictly_bounded((as_nat(limbs) + 19) as int, pow2(255) as int, 2);

    // Since q = (as_nat(limbs) + 19) / 2^255, we have q < 2
}

/// Unified helper: Proves the biconditional relationship between as_nat and q
///
/// With the tight bound as_nat(limbs) < 2*p(), the value is either in [0, p) or [p, 2*p),
/// which maps directly to q=0 or q=1. This makes the biconditional proofs straightforward.
pub proof fn lemma_q_biconditional(limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
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
    lemma_pow2_pos(255);

    // The key insight: with as_nat(limbs) < 2*p() and p() < 2^255, we have two cases:
    // Case 1: as_nat(limbs) < p() ⟺ as_nat(limbs) + 19 < 2^255 ⟺ q = 0
    // Case 2: p() ≤ as_nat(limbs) < 2*p() ⟺ 2^255 ≤ as_nat(limbs) + 19 < 2*2^255 ⟺ q = 1

    // Forward direction: as_nat(limbs) < p() ==> q == 0
    if as_nat(limbs) < p() {
        lemma_div_strictly_bounded((as_nat(limbs) + 19) as int, pow2(255) as int, 1);
    }
    // Backward direction: q == 0 ==> as_nat(limbs) < p()

    if q == 0 {
        lemma_fundamental_div_mod((as_nat(limbs) + 19) as int, pow2(255) as int);
        lemma_mod_bound((as_nat(limbs) + 19) as int, pow2(255) as int);
    }
    // Forward direction: as_nat(limbs) >= p() ==> q == 1

    if as_nat(limbs) >= p() {
        // Since q is 0 or 1, and we know as_nat + 19 >= 2^255, q cannot be 0
        if q == 0 {
            lemma_fundamental_div_mod((as_nat(limbs) + 19) as int, pow2(255) as int);
            lemma_mod_bound((as_nat(limbs) + 19) as int, pow2(255) as int);
        }
    }
    // Backward direction: q == 1 ==> as_nat(limbs) >= p()

    if q == 1 {
        lemma_fundamental_div_mod((as_nat(limbs) + 19) as int, pow2(255) as int);
    }
}

/// Proves that q computed via successive carry propagation equals 1 iff h >= p, 0 otherwise
/// where h = as_nat(limbs) and limbs[i] < 2^52 for all i
///
/// The precondition `as_nat(limbs) < 2 * p()` is satisfied when limbs come from
/// `reduce()` output, which now ensures this property in its postcondition.
pub proof fn lemma_compute_q(limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        as_nat(limbs) < 2 * p(),  // From reduce()'s postcondition
        q == compute_q_spec(limbs),
    ensures
        q == 0 || q == 1,
        as_nat(limbs) >= p() <==> q == 1,
        as_nat(limbs) < p() <==> q == 0,
{
    // Step 1: Prove q < 3 (all carries bounded)
    lemma_all_carries_bounded_by_3(limbs);

    // Step 2: Prove q can only be 0 or 1 (not 2)
    // Note: This also establishes q as nat == (as_nat(limbs) + 19) / pow2(255)
    // internally by calling lemma_carry_propagation_is_division
    lemma_q_is_binary(limbs, q);

    // Step 3: Prove the biconditionals
    // With the tight bound as_nat < 2*p(), this is now straightforward
    lemma_q_biconditional(limbs, q);
}

} // verus!
