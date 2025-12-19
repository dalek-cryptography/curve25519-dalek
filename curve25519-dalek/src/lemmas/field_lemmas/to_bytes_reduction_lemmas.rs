#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::calc;
use vstd::prelude::*;

use super::compute_q_lemmas::*;
use super::load8_lemmas::*;
use super::pow2_51_lemmas::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

// ============================================================================
// LEMMA 2: Value preservation through modular reduction
// ============================================================================
/// Telescoping lemma for reduction: expands u64_5_as_nat through the carry propagation
/// This is analogous to lemma_radix51_telescoping_direct but for the reduction case
pub proof fn lemma_reduction_telescoping(
    input_limbs: [u64; 5],
    final_limbs: [u64; 5],
    q: u64,
    c0: int,
    c1: int,
    c2: int,
    c3: int,
    c4: int,
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
        u64_5_as_nat(input_limbs) as int + 19 * q as int == u64_5_as_nat(final_limbs) as int + c4
            * pow2(255) as int,
{
    // Establish power-of-2 relationships
    lemma_pow2_pos(51);
    lemma_pow2_adds(51, 51);
    lemma_pow2_adds(51, 102);
    lemma_pow2_adds(51, 153);
    lemma_pow2_adds(51, 204);

    // Expand u64_5_as_nat(input_limbs) + 19*q
    let lhs = u64_5_as_nat(input_limbs) as int + 19 * q as int;

    // Explicitly expand u64_5_as_nat using its definition
    assert(u64_5_as_nat(input_limbs) == (input_limbs[0] as nat) + pow2(51) * (input_limbs[1] as nat)
        + pow2(102) * (input_limbs[2] as nat) + pow2(153) * (input_limbs[3] as nat) + pow2(204) * (
    input_limbs[4] as nat));

    // Convert to int with commutativity
    assert(u64_5_as_nat(input_limbs) as int == input_limbs[0] as int + input_limbs[1] as int * pow2(
        51,
    ) as int + input_limbs[2] as int * pow2(102) as int + input_limbs[3] as int * pow2(153) as int
        + input_limbs[4] as int * pow2(204) as int) by {
        lemma_mul_is_commutative(pow2(51) as int, input_limbs[1] as int);
        lemma_mul_is_commutative(pow2(102) as int, input_limbs[2] as int);
        lemma_mul_is_commutative(pow2(153) as int, input_limbs[3] as int);
        lemma_mul_is_commutative(pow2(204) as int, input_limbs[4] as int);
    }

    assert(lhs == input_limbs[0] as int + input_limbs[1] as int * pow2(51) as int
        + input_limbs[2] as int * pow2(102) as int + input_limbs[3] as int * pow2(153) as int
        + input_limbs[4] as int * pow2(204) as int + 19 * q as int);

    // Substitute the division relationships (solve for input_limbs[i])

    // Expand each term using distributivity (same pattern as lemma_radix51_telescoping_direct)
    assert((c1 * pow2(51) as int + final_limbs[1] as int - c0) * pow2(51) as int == c1 * pow2(
        102,
    ) as int + final_limbs[1] as int * pow2(51) as int - c0 * pow2(51) as int) by {
        lemma_mul_is_distributive_sub_other_way(
            pow2(51) as int,
            c1 * pow2(51) as int + final_limbs[1] as int,
            c0,
        );
        lemma_mul_is_distributive_add_other_way(
            pow2(51) as int,
            c1 * pow2(51) as int,
            final_limbs[1] as int,
        );
        lemma_mul_is_associative(c1, pow2(51) as int, pow2(51) as int);
    }

    assert((c2 * pow2(51) as int + final_limbs[2] as int - c1) * pow2(102) as int == c2 * pow2(
        153,
    ) as int + final_limbs[2] as int * pow2(102) as int - c1 * pow2(102) as int) by {
        lemma_mul_is_distributive_sub_other_way(
            pow2(102) as int,
            c2 * pow2(51) as int + final_limbs[2] as int,
            c1,
        );
        lemma_mul_is_distributive_add_other_way(
            pow2(102) as int,
            c2 * pow2(51) as int,
            final_limbs[2] as int,
        );
        lemma_mul_is_associative(c2, pow2(51) as int, pow2(102) as int);
    }

    assert((c3 * pow2(51) as int + final_limbs[3] as int - c2) * pow2(153) as int == c3 * pow2(
        204,
    ) as int + final_limbs[3] as int * pow2(153) as int - c2 * pow2(153) as int) by {
        lemma_mul_is_distributive_sub_other_way(
            pow2(153) as int,
            c3 * pow2(51) as int + final_limbs[3] as int,
            c2,
        );
        lemma_mul_is_distributive_add_other_way(
            pow2(153) as int,
            c3 * pow2(51) as int,
            final_limbs[3] as int,
        );
        lemma_mul_is_associative(c3, pow2(51) as int, pow2(153) as int);
    }

    assert((c4 * pow2(51) as int + final_limbs[4] as int - c3) * pow2(204) as int == c4 * pow2(
        255,
    ) as int + final_limbs[4] as int * pow2(204) as int - c3 * pow2(204) as int) by {
        lemma_mul_is_distributive_sub_other_way(
            pow2(204) as int,
            c4 * pow2(51) as int + final_limbs[4] as int,
            c3,
        );
        lemma_mul_is_distributive_add_other_way(
            pow2(204) as int,
            c4 * pow2(51) as int,
            final_limbs[4] as int,
        );
        lemma_mul_is_associative(c4, pow2(51) as int, pow2(204) as int);
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
    let rhs = final_limbs[0] as int + final_limbs[1] as int * pow2(51) as int
        + final_limbs[2] as int * pow2(102) as int + final_limbs[3] as int * pow2(153) as int
        + final_limbs[4] as int * pow2(204) as int + c4 * pow2(255) as int;

    // Show that lhs == rhs through algebraic expansion
    assert(lhs == (c0 * pow2(51) as int + final_limbs[0] as int - 19 * q as int) + (c1 * pow2(
        51,
    ) as int + final_limbs[1] as int - c0) * pow2(51) as int + (c2 * pow2(51) as int
        + final_limbs[2] as int - c1) * pow2(102) as int + (c3 * pow2(51) as int
        + final_limbs[3] as int - c2) * pow2(153) as int + (c4 * pow2(51) as int
        + final_limbs[4] as int - c3) * pow2(204) as int + 19 * q as int);

    // Use the distributivity facts we proved above
    assert(lhs == (c0 * pow2(51) as int + final_limbs[0] as int - 19 * q as int) + (c1 * pow2(
        102,
    ) as int + final_limbs[1] as int * pow2(51) as int - c0 * pow2(51) as int) + (c2 * pow2(
        153,
    ) as int + final_limbs[2] as int * pow2(102) as int - c1 * pow2(102) as int) + (c3 * pow2(
        204,
    ) as int + final_limbs[3] as int * pow2(153) as int - c2 * pow2(153) as int) + (c4 * pow2(
        255,
    ) as int + final_limbs[4] as int * pow2(204) as int - c3 * pow2(204) as int) + 19 * q as int);

    // Group terms: the carries telescope
    // c0*2^51 - c0*2^51 = 0
    // c1*2^102 - c1*2^102 = 0
    // c2*2^153 - c2*2^153 = 0
    // c3*2^204 - c3*2^204 = 0
    // -19*q + 19*q = 0
    // What remains: final_limbs terms + c4*2^255

    assert(lhs == final_limbs[0] as int + final_limbs[1] as int * pow2(51) as int
        + final_limbs[2] as int * pow2(102) as int + final_limbs[3] as int * pow2(153) as int
        + final_limbs[4] as int * pow2(204) as int + c4 * pow2(255) as int);

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
    lemma_pow2_adds(51, 51);  // 2^102 = 2^51 * 2^51
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

    // Expand pow2(51) * sum using distributivity
    assert(pow2(51) * sum == pow2(51) * 1 + pow2(51) * pow2(51) + pow2(51) * pow2(102) + pow2(51)
        * pow2(153) + pow2(51) * pow2(204)) by {
        lemma_mul_is_distributive_add(pow2(51) as int, 1, pow2(51) as int);
        lemma_mul_is_distributive_add(pow2(51) as int, 1 + pow2(51) as int, pow2(102) as int);
        lemma_mul_is_distributive_add(
            pow2(51) as int,
            1 + pow2(51) + pow2(102) as int,
            pow2(153) as int,
        );
        lemma_mul_is_distributive_add(
            pow2(51) as int,
            1 + pow2(51) + pow2(102) + pow2(153) as int,
            pow2(204) as int,
        );
    }

    // Simplify using power-of-2 addition properties
    assert(pow2(51) * pow2(153) == pow2(204));
    assert(pow2(51) * pow2(204) == pow2(255));

    // Now compute lhs = (pow2(51) + pow2(102) + pow2(153) + pow2(204) + pow2(255)) - sum
    //                 = (pow2(51) + pow2(102) + pow2(153) + pow2(204) + pow2(255))
    //                   - (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204))

    // The middle terms cancel, leaving: pow2(255) - 1
}

/// Helper lemma: u64_5_as_nat bound for 51-bit limbs
/// If each limb < 2^51, then u64_5_as_nat < 2^255
pub proof fn lemma_as_nat_bound_from_51bit_limbs(limbs: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        u64_5_as_nat(limbs) < pow2(255),
{
    // Strategy: Prove that the maximum value (when all limbs = 2^51 - 1) equals 2^255 - 1
    // We'll prove this by showing the algebraic identity directly using bit manipulation
    lemma2_to64_rest();
    assert((1u64 << 51) as nat == pow2(51)) by (compute);

    // Establish power-of-2 relationships
    lemma_pow2_adds(51, 51);  // 2^102 = 2^51 * 2^51
    lemma_pow2_adds(51, 102);  // 2^153 = 2^51 * 2^102
    lemma_pow2_adds(51, 153);  // 2^204 = 2^51 * 2^153
    lemma_pow2_adds(51, 204);  // 2^255 = 2^51 * 2^204

    // Expand u64_5_as_nat definition
    assert(u64_5_as_nat(limbs) == limbs[0] as nat + pow2(51) * limbs[1] as nat + pow2(102)
        * limbs[2] as nat + pow2(153) * limbs[3] as nat + pow2(204) * limbs[4] as nat);

    // Each limb < 2^51, so limbs[i] <= 2^51 - 1
    lemma_pow2_pos(51);
    let max_limb = (pow2(51) - 1) as nat;

    // Prove upper bound for each term
    lemma_mul_upper_bound(pow2(51), limbs[1] as nat, max_limb);

    lemma_mul_upper_bound(pow2(102), limbs[2] as nat, max_limb);

    lemma_mul_upper_bound(pow2(153), limbs[3] as nat, max_limb);

    lemma_mul_upper_bound(pow2(204), limbs[4] as nat, max_limb);

    // Therefore, u64_5_as_nat(limbs) <= sum of maximum values
    // u64_5_as_nat(limbs) <= max_limb + pow2(51)*max_limb + pow2(102)*max_limb + pow2(153)*max_limb + pow2(204)*max_limb
    //                = max_limb * (1 + pow2(51) + pow2(102) + pow2(153) + pow2(204))

    // Since each term is maximized at max_limb = 2^51 - 1, we have:
    let max_val = max_limb + pow2(51) * max_limb + pow2(102) * max_limb + pow2(153) * max_limb
        + pow2(204) * max_limb;

    // Factor out max_limb using distributivity
    lemma_mul_is_distributive_add(max_limb as int, 1, pow2(51) as int);
    lemma_mul_is_distributive_add(max_limb as int, (1 + pow2(51)) as int, pow2(102) as int);
    lemma_mul_is_distributive_add(
        max_limb as int,
        (1 + pow2(51) + pow2(102)) as int,
        pow2(153) as int,
    );
    lemma_mul_is_distributive_add(
        max_limb as int,
        (1 + pow2(51) + pow2(102) + pow2(153)) as int,
        pow2(204) as int,
    );

    // Now use the geometric series identity: (2^51 - 1) * (1 + 2^51 + 2^102 + 2^153 + 2^204) = 2^255 - 1
    lemma_geometric_sum_5_terms();

    // Since u64_5_as_nat(limbs) <= max_val = 2^255 - 1 < 2^255, we're done
    assert(pow2(255) - 1 < pow2(255)) by {
        lemma_pow2_pos(255);
    }
}

/// Helper lemma: Proves that the carry propagation in reduction computes the division by 2^255
/// This is analogous to lemma_carry_propagation_is_division but for the reduction step
pub proof fn lemma_reduction_carry_propagation_is_division(input_limbs: [u64; 5], q: u64, c4: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
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
        c4 as int == (u64_5_as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int),
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

    // Prove that limbs are bounded (similar to lemma_all_carries_bounded_by_3)
    lemma2_to64_rest();

    // Convert the precondition limb bounds to pow2 form
    assert((1u64 << 52) == pow2(52)) by (compute);

    assert(19 * q < 20) by {}

    // Apply div-mod relationships
    l51_bit_mask_lt();
    lemma_u64_div_and_mod_51(c0, l0_masked, l0);
    lemma_u64_div_and_mod_51(c1, l1_masked, l1);
    lemma_u64_div_and_mod_51(c2, l2_masked, l2);
    lemma_u64_div_and_mod_51(c3, l3_masked, l3);
    lemma_u64_div_and_mod_51(c4, l4_masked, l4);

    // Now use the telescoping lemma
    let final_limbs = [l0_masked, l1_masked, l2_masked, l3_masked, l4_masked];

    // Verify preconditions for telescoping - need to prove the division-modulo relationships

    lemma_masked_lt_51(l0);
    lemma_masked_lt_51(l1);
    lemma_masked_lt_51(l2);
    lemma_masked_lt_51(l3);
    lemma_masked_lt_51(l4);

    lemma_reduction_telescoping(
        input_limbs,
        final_limbs,
        q,
        c0 as int,
        c1 as int,
        c2 as int,
        c3 as int,
        c4 as int,
    );

    // From telescoping: u64_5_as_nat(input_limbs) + 19*q == u64_5_as_nat(final_limbs) + c4*2^255
    // Therefore: c4 = (u64_5_as_nat(input_limbs) + 19*q - u64_5_as_nat(final_limbs)) / 2^255

    // Since final_limbs[i] < 2^51 for all i, u64_5_as_nat(final_limbs) < 2^255
    // This is a fundamental property of radix-2^51 representation with 5 limbs
    lemma_as_nat_bound_from_51bit_limbs(final_limbs);

    // From the telescoping identity:
    // u64_5_as_nat(input_limbs) + 19*q = u64_5_as_nat(final_limbs) + c4*2^255
    // Since 0 <= u64_5_as_nat(final_limbs) < 2^255, and this is the unique representation,
    // c4 = (u64_5_as_nat(input_limbs) + 19*q) / 2^255

    let dividend = u64_5_as_nat(input_limbs) as int + 19 * q as int;
    let divisor = pow2(255) as int;

    lemma_fundamental_div_mod(dividend, divisor);
    lemma_pow2_pos(255);

    // From telescoping: dividend = c4 * divisor + u64_5_as_nat(final_limbs)
    // where 0 <= u64_5_as_nat(final_limbs) < divisor (from the assume at line 1322)

    // Use the uniqueness lemma for division to prove: dividend / divisor == c4
    // We have:
    // - dividend = c4 * divisor + u64_5_as_nat(final_limbs)
    // - 0 <= u64_5_as_nat(final_limbs) < divisor
    // Therefore: dividend / divisor == c4

    let remainder = u64_5_as_nat(final_limbs) as int;

    lemma_div_multiples_vanish_fancy(c4 as int, u64_5_as_nat(final_limbs) as int, divisor);
}

/// Helper lemma: Show that the carry out of l4 equals q
pub proof fn lemma_carry_out_equals_q(input_limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
        q == 0 || q == 1,
        u64_5_as_nat(input_limbs) >= p() <==> q == 1,
        u64_5_as_nat(input_limbs) < 2 * p(),  // From reduce()'s postcondition

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
    // Strategy: Use the fact that the carry propagation computes (u64_5_as_nat(input_limbs) + 19*q) / 2^255

    // This is analogous to lemma_carry_propagation_is_division, but with input_limbs and 19*q instead of limbs and 19
    // The computation is:
    // Stage 0: (input_limbs[0] + 19*q) = c0*2^51 + r0
    // Stage 1: (input_limbs[1] + c0) = c1*2^51 + r1
    // ...
    // Stage 4: (input_limbs[4] + c3) = c4*2^51 + r4

    // By the same telescoping argument as in lemma_carry_propagation_is_division:
    // c4 = (u64_5_as_nat(input_limbs) + 19*q) / 2^255

    pow255_gt_19();
    lemma_pow2_pos(255);

    // Case analysis on q:
    if q == 0 {
        // When q == 0, we have u64_5_as_nat(input_limbs) < p() = 2^255 - 19
        // So: u64_5_as_nat(input_limbs) + 19*0 < 2^255
        // Therefore: (u64_5_as_nat(input_limbs) + 0) / 2^255 == 0
        // Invoke the division computation
        lemma_reduction_carry_propagation_is_division(input_limbs, q, c4);

        lemma_div_strictly_bounded(u64_5_as_nat(input_limbs) as int, pow2(255) as int, 1);
    } else {
        // q == 1
        // Simplified reasoning: c4 = q by computing the division
        //
        // From lemma_reduction_carry_propagation_is_division:
        //   c4 = ⌊(u64_5_as_nat(input_limbs) + 19*q) / 2^255⌋
        //
        // Substituting q = 1:
        //   c4 = ⌊(u64_5_as_nat(input_limbs) + 19) / 2^255⌋
        //
        // We prove this equals 1 using the bounds:
        //   Since q == 1, we have u64_5_as_nat(input_limbs) >= p() = 2^255 - 19
        //   So: u64_5_as_nat(input_limbs) + 19 >= 2^255
        //   Also: u64_5_as_nat(input_limbs) < 2*p() < 2*2^255
        //   So: u64_5_as_nat(input_limbs) + 19 < 2*2^255
        //   Therefore: 2^255 ≤ u64_5_as_nat(input_limbs) + 19 < 2*2^255
        //   Which gives: ⌊(u64_5_as_nat(input_limbs) + 19) / 2^255⌋ = 1
        //
        // Therefore: c4 = 1 = q
        // Invoke the division computation to establish c4 = (u64_5_as_nat + 19*q) / 2^255
        assert(c4 as int == (u64_5_as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int))
            by {
            lemma_reduction_carry_propagation_is_division(input_limbs, q, c4);
        }

        assert((u64_5_as_nat(input_limbs) as int + 19 * q as int) / (pow2(255) as int) == 1) by {
            // Prove (u64_5_as_nat(input_limbs) + 19) / 2^255 = 1 using bounds
            let val = u64_5_as_nat(input_limbs) as int + 19 * q as int;
            assert(19 == 19 * q as int) by {
                lemma_mul_basics_3(19);
            }
            let divisor = pow2(255) as int;

            // From q == 1, we have u64_5_as_nat(input_limbs) >= p()
            // So val >= 2^255
            assert(u64_5_as_nat(input_limbs) >= p());
            assert(val >= pow2(255));

            // From u64_5_as_nat(input_limbs) < 2*p() < 2*2^255
            // We have val < 2*2^255, so val / divisor < 2
            assert(val / divisor < 2) by {
                lemma_div_strictly_bounded(val, divisor, 2);
            }

            // From val >= divisor, we have val / divisor >= 1
            assert(val / divisor >= 1) by {
                assert(val / divisor >= val / val) by {
                    lemma_div_is_ordered_by_denominator(val, divisor, val)
                }
                assert(val / val == 1) by {
                    lemma_div_basics_3(val);
                }
            }
            // Therefore: 1 ≤ val / divisor < 2, so val / divisor == 1
            // Since c4 = val / divisor (with q=1), we have c4 = 1 = q
        }
    }
}

/// Proves that after adding 19*q and propagating carries while masking to 51 bits,
/// the result equals u64_5_as_nat(input_limbs) mod p
pub proof fn lemma_to_bytes_reduction(input_limbs: [u64; 5], final_limbs: [u64; 5], q: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
        q == 0 || q == 1,
        u64_5_as_nat(input_limbs) >= p() <==> q == 1,
        u64_5_as_nat(input_limbs) < 2 * p(),  // From reduce()'s postcondition
        final_limbs == reduce_with_q_spec(input_limbs, q),
    ensures
        forall|i: int| 0 <= i < 5 ==> final_limbs[i] < (1u64 << 51),
        u64_5_as_nat(final_limbs) == u64_5_as_nat(input_limbs) % p(),
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

    // Part 1: Prove that all final limbs are bounded by 2^51
    l51_bit_mask_lt();
    lemma_masked_lt_51(l0);
    lemma_masked_lt_51(l1);
    lemma_masked_lt_51(l2);
    lemma_masked_lt_51(l3);
    lemma_masked_lt_51(l4);

    // Part 2: Prove that u64_5_as_nat(final_limbs) == u64_5_as_nat(input_limbs) % p()
    // Strategy: Show that the carry propagation computes u64_5_as_nat(input_limbs) + 19*q - 2^255*q
    //           which equals u64_5_as_nat(input_limbs) - q*(2^255 - 19) = u64_5_as_nat(input_limbs) - q*p()

    // Use lemma_u64_div_and_mod_51 to relate the shift and mask operations to division and modulo
    lemma_u64_div_and_mod_51(l0 >> 51, l0 & mask51, l0);

    lemma_u64_div_and_mod_51(l1 >> 51, l1 & mask51, l1);

    lemma_u64_div_and_mod_51(l2 >> 51, l2 & mask51, l2);

    lemma_u64_div_and_mod_51(l3 >> 51, l3 & mask51, l3);

    lemma_u64_div_and_mod_51(l4 >> 51, l4 & mask51, l4);

    // Define the carries for readability
    let c0 = l0 >> 51;
    let c1 = l1 >> 51;
    let c2 = l2 >> 51;
    let c3 = l3 >> 51;
    let c4 = l4 >> 51;

    // Express l0, l1, l2, l3, l4 in terms of input_limbs
    // Note: Need to prove the casts don't affect the values (no overflow)
    assert(19 * q < 20) by {}
    assert((1u64 << 52) + 20 < u64::MAX) by (compute);

    // Similar reasoning for other limbs - the carries are small enough
    // l0 < 2^52 + 20, so l0 >> 51 <= 2
    // l1 = input_limbs[1] + (l0 >> 51) < 2^52 + 2 < u64::MAX
    lemma_u64_shr_le(l0, ((1u64 << 52) + 20) as u64, 51);
    assert((((1u64 << 52) + 20) as u64) >> 51 == 2) by (compute);

    lemma_u64_shr_le(l1, ((1u64 << 52) + 2) as u64, 51);
    assert((((1u64 << 52) + 2) as u64) >> 51 == 2) by (compute);

    lemma_u64_shr_le(l2, ((1u64 << 52) + 2) as u64, 51);

    lemma_u64_shr_le(l3, ((1u64 << 52) + 2) as u64, 51);

    // Now use the telescoping lemma to relate u64_5_as_nat(input_limbs) + 19*q to u64_5_as_nat(final_limbs) + c4*2^255
    // The division-mod relationships give us the preconditions needed:

    // All final_limbs are bounded by 2^51 (already proven above)
    lemma_reduction_telescoping(
        input_limbs,
        final_limbs,
        q,
        c0 as int,
        c1 as int,
        c2 as int,
        c3 as int,
        c4 as int,
    );

    // Prove that c4 == q
    lemma_carry_out_equals_q(input_limbs, q);

    // Therefore: u64_5_as_nat(input_limbs) + 19*q = u64_5_as_nat(final_limbs) + q*2^255
    // Rearranging: u64_5_as_nat(final_limbs) = u64_5_as_nat(input_limbs) + 19*q - q*2^255
    //                                    = u64_5_as_nat(input_limbs) - q*(2^255 - 19)
    //                                    = u64_5_as_nat(input_limbs) - q*p()

    pow255_gt_19();

    // Case analysis on q
    if q == 0 {
        // u64_5_as_nat(final_limbs) = u64_5_as_nat(input_limbs) - 0*p() = u64_5_as_nat(input_limbs)
        // Since q == 0, we have u64_5_as_nat(input_limbs) < p()
        // For values < p, x % p = x
        // Since u64_5_as_nat(input_limbs) < p(), we have u64_5_as_nat(input_limbs) % p() = u64_5_as_nat(input_limbs)
        lemma_pow2_pos(255);
        lemma_small_mod(u64_5_as_nat(input_limbs), p());

    } else {
        // q == 1
        // u64_5_as_nat(final_limbs) = u64_5_as_nat(input_limbs) - 1*p() = u64_5_as_nat(input_limbs) - p()
        // Need to prove: u64_5_as_nat(input_limbs) % p() = u64_5_as_nat(input_limbs) - p()
        // This holds when p <= u64_5_as_nat(input_limbs) < 2*p
        // We have u64_5_as_nat(input_limbs) >= p() (from q==1) and u64_5_as_nat(input_limbs) < 2*p() (from precondition)
        // For values in [p, 2*p), x % p = x - p
        lemma_fundamental_div_mod(u64_5_as_nat(input_limbs) as int, p() as int);
        lemma_pow2_pos(255);

        // Since p <= u64_5_as_nat < 2*p, the quotient is 1
        lemma_div_strictly_bounded(u64_5_as_nat(input_limbs) as int, p() as int, 2);

        // From div-mod: x = d * (x/d) + (x%d)
        // lemma_fundamental_div_mod establishes this with multiplication on the left
        let x = u64_5_as_nat(input_limbs) as int;
        let divisor = p() as int;
        let quotient = x / divisor;
        let remainder = x % divisor;

        // From lemma_fundamental_div_mod: x == divisor * quotient + remainder
        // Convert to: x == quotient * divisor + remainder
        assert(divisor * quotient == quotient * divisor) by {
            lemma_mul_is_commutative(divisor, quotient);
        }

        // We proved quotient == 1

        // Convert back to original terms
    }
}

/// Proves that the subtraction constants expand to 16 * p() in radix-2^51 form.
pub proof fn lemma_sub_constants_equal_16p()
    ensures
        (36028797018963664u64 as nat + pow2(51) * (36028797018963952u64 as nat) + pow2(102) * (
        36028797018963952u64 as nat) + pow2(153) * (36028797018963952u64 as nat) + pow2(204) * (
        36028797018963952u64 as nat)) == (16 as nat) * p(),
{
    lemma2_to64_rest();
    assert(pow2(51) == 0x8000000000000);

    assert(36028797018963664u64 as nat == 16 * (pow2(51) - 19)) by {
        assert(16 * (pow2(51) - 19) == 16 * (0x8000000000000 - 19)) by {
            assert(pow2(51) == 0x8000000000000);
        }
        assert(16 * (0x8000000000000 - 19) == 36028797018963664) by (compute);
    }

    assert(36028797018963952u64 as nat == 16 * (pow2(51) - 1)) by {
        assert(16 * (pow2(51) - 1) == 16 * (0x8000000000000 - 1)) by {
            assert(pow2(51) == 0x8000000000000);
        }
        assert(16 * (0x8000000000000 - 1) == 36028797018963952) by (compute);
    }

    calc! {
        (==)
        36028797018963664u64 as nat + pow2(51) * (36028797018963952u64 as nat) + pow2(102) * (
        36028797018963952u64 as nat) + pow2(153) * (36028797018963952u64 as nat) + pow2(204) * (
        36028797018963952u64 as nat); {
            // Substitute the constant definitions for clarity
        }
        (16 * (pow2(51) - 19) + pow2(51) * (16 * (pow2(51) - 1)) + pow2(102) * (16 * (pow2(51) - 1))
            + pow2(153) * (16 * (pow2(51) - 1)) + pow2(204) * (16 * (pow2(51) - 1))) as nat; {
            lemma_mul_is_distributive_add(
                16,
                pow2(51) - 19,
                pow2(51) * (pow2(51) - 1) + pow2(102) * (pow2(51) - 1) + pow2(153) * (pow2(51) - 1)
                    + pow2(204) * (pow2(51) - 1),
            );
        }
        (16 * ((pow2(51) - 19) + pow2(51) * (pow2(51) - 1) + pow2(102) * (pow2(51) - 1) + pow2(153)
            * (pow2(51) - 1) + pow2(204) * (pow2(51) - 1))) as nat; {
            lemma_p_radix_representation();
        }
        (16 * p()) as nat;
    }
}

/// Helper lemma establishing the radix-2^51 expansion of p().
pub proof fn lemma_p_radix_representation()
    ensures
        (pow2(51) - 19) + pow2(51) * (pow2(51) - 1) + pow2(102) * (pow2(51) - 1) + pow2(153) * (
        pow2(51) - 1) + pow2(204) * (pow2(51) - 1) == p(),
{
    let r1 = pow2(51);
    let r2 = pow2(102);
    let r3 = pow2(153);
    let r4 = pow2(204);
    let r5 = pow2(255);

    assert(pow2(51) * (pow2(51) - 1) == r2 - r1) by {
        calc! {
            (==)
            r1 * (r1 - 1); {
                lemma_mul_is_commutative(r1 as int, (r1 - 1) as int);
            }
            (r1 - 1) * r1; {
                lemma_mul_is_distributive_sub(r1 as int, r1 as int, 1);
            }
            r1 * r1 - r1 * 1; {
                lemma_pow2_adds(51, 51);
                lemma_mul_basics(r1 as int);
                assert(r1 * r1 == r2);
                assert(r1 * 1 == r1);
            }
            r2 - r1;
        }
    }

    assert(pow2(102) * (pow2(51) - 1) == r3 - r2) by {
        calc! {
            (==)
            r2 * (r1 - 1); {
                lemma_mul_is_distributive_sub(r2 as int, r1 as int, 1);
            }
            r2 * r1 - r2 * 1; {
                lemma_pow2_adds(102, 51);
                lemma_mul_is_commutative(r2 as int, r1 as int);
                lemma_mul_basics(r2 as int);
                assert(r2 * r1 == r3);
                assert(r2 * 1 == r2);
            }
            r3 - r2;
        }
    }

    assert(pow2(153) * (pow2(51) - 1) == r4 - r3) by {
        calc! {
            (==)
            r3 * (r1 - 1); {
                lemma_mul_is_distributive_sub(r3 as int, r1 as int, 1);
            }
            r3 * r1 - r3 * 1; {
                lemma_pow2_adds(153, 51);
                lemma_mul_is_commutative(r3 as int, r1 as int);
                lemma_mul_basics(r3 as int);
                assert(r3 * r1 == r4);
                assert(r3 * 1 == r3);
            }
            r4 - r3;
        }
    }

    assert(pow2(204) * (pow2(51) - 1) == r5 - r4) by {
        calc! {
            (==)
            r4 * (r1 - 1); {
                lemma_mul_is_distributive_sub(r4 as int, r1 as int, 1);
            }
            r4 * r1 - r4 * 1; {
                lemma_pow2_adds(204, 51);
                lemma_mul_is_commutative(r4 as int, r1 as int);
                lemma_mul_basics(r4 as int);
                assert(r4 * r1 == r5);
                assert(r4 * 1 == r4);
            }
            r5 - r4;
        }
    }

    calc! {
        (==)
        (pow2(51) - 19) + pow2(51) * (pow2(51) - 1) + pow2(102) * (pow2(51) - 1) + pow2(153) * (
        pow2(51) - 1) + pow2(204) * (pow2(51) - 1); {}
        (r1 - 19) + (r2 - r1) + (r3 - r2) + (r4 - r3) + (r5 - r4); {
            assert(pow2(51) * (pow2(51) - 1) == r2 - r1);
            assert(pow2(102) * (pow2(51) - 1) == r3 - r2);
            assert(pow2(153) * (pow2(51) - 1) == r4 - r3);
            assert(pow2(204) * (pow2(51) - 1) == r5 - r4);
        }
        r5 - 19;
    }

    assert(r5 - 19 == p()) by {
        assert(r5 == pow2(255));
        pow255_gt_19();
        assert(pow2(255) >= 19) by {
            assert(pow2(255) > 19);
        }
        assert(pow2(255) - 19 == p()) by {
            assert(pow2(255) - 19 == (pow2(255) - 19) as nat) by {
                assert(pow2(255) - 19 >= 0) by {
                    assert(pow2(255) >= 19);
                }
            }
            assert(p() == (pow2(255) - 19) as nat);
        }
        assert(r5 - 19 == pow2(255) - 19) by {
            assert(r5 == pow2(255));
        }
    }
}

} // verus!
