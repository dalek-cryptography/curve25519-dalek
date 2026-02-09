//! Lemmas for proving `lemma_part2_chain_quotient`
//!
//! This module contains the proof that after 4 calls to `part2`, we have:
//!   `intermediate = (T + N×L) / R`
//!
//! where intermediate = [r0, r1, r2, r3, r4].
//!
//! ## Proof Structure
//!
//! The proof uses the telescoping technique:
//!
//! 1. **Stage equations from part2**:
//!    - sum5 = r0 + carry5 × 2^52
//!    - sum6 = r1 + carry6 × 2^52
//!    - sum7 = r2 + carry7 × 2^52
//!    - sum8 = r3 + carry8 × 2^52 (where r4 = carry8)
//!
//! 2. **Telescoping**: Multiply by positional weights and sum.
//!    The intermediate carries cancel, leaving:
//!    sum5 + sum6×2^52 + sum7×2^104 + sum8×2^156
//!    = r0 + r1×2^52 + r2×2^104 + r3×2^156 + r4×2^208
//!
//! 3. **Connection**: The weighted sum of sums equals (T + N×L) / R
//!    because Part 1 zeroed out the low 260 bits.
//!
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;

use crate::backend::serial::u64::constants;
use crate::lemmas::scalar_lemmas::*;
use crate::specs::montgomery_reduce_specs::*;
use crate::specs::scalar52_specs::*;

use super::montgomery_reduce_part1_chain_lemmas::*;

verus! {

// =============================================================================
// Helper: Carry Cancellation Lemma
// =============================================================================
//
// This lemma proves the key carry cancellation property:
//   intermediate == carry4 + t_high + nl_high
//
// The proof shows that when expanding intermediate using stage equations
// and sum definitions, all intermediate carries (carry5, carry6, carry7) cancel.
/// Proves carry cancellation: intermediate = carry4 + t_high + nl_high
///
/// # Mathematical Argument
///
/// From stage equations: r_i = sum_{i+5} - carry_{i+5} × 2^52
/// From sum definitions: sum_{i+5} = carry_{i+4} + limbs[i+5] + products_{i+5}
///
/// When we expand intermediate = r0 + r1×2^52 + r2×2^104 + r3×2^156 + r4×2^208
/// and substitute the stage equations and sum definitions, the intermediate
/// carries cancel:
///   -carry5×2^52 + carry5×2^52 = 0
///   -carry6×2^104 + carry6×2^104 = 0
///   -carry7×2^156 + carry7×2^156 = 0
///
/// Leaving: carry4 + t_high + nl_high
proof fn lemma_part2_carry_cancellation(
    limbs: &[u128; 9],
    n0: u64,
    n1: u64,
    n2: u64,
    n3: u64,
    n4: u64,
    carry4: u128,
    sum5: u128,
    sum6: u128,
    sum7: u128,
    sum8: u128,
    carry5: u128,
    carry6: u128,
    carry7: u128,
    r0: u64,
    r1: u64,
    r2: u64,
    r3: u64,
    r4: u64,
)
    requires
// Sum definitions

        sum5 as nat == carry4 as nat + limbs[5] as nat + (n1 as nat) * (
        constants::L.limbs[4] as nat) + (n3 as nat) * (constants::L.limbs[2] as nat) + (n4 as nat)
            * (constants::L.limbs[1] as nat),
        sum6 as nat == carry5 as nat + limbs[6] as nat + (n2 as nat) * (
        constants::L.limbs[4] as nat) + (n4 as nat) * (constants::L.limbs[2] as nat),
        sum7 as nat == carry6 as nat + limbs[7] as nat + (n3 as nat) * (
        constants::L.limbs[4] as nat),
        sum8 as nat == carry7 as nat + limbs[8] as nat + (n4 as nat) * (
        constants::L.limbs[4] as nat),
        // Stage equations
        sum5 as nat == (r0 as nat) + (carry5 as nat) * pow2(52),
        sum6 as nat == (r1 as nat) + (carry6 as nat) * pow2(52),
        sum7 as nat == (r2 as nat) + (carry7 as nat) * pow2(52),
        sum8 as nat == (r3 as nat) + (r4 as nat) * pow2(52),
        // r bounds
        r0 < pow2(52),
        r1 < pow2(52),
        r2 < pow2(52),
        r3 < pow2(52),
    ensures
        five_u64_limbs_to_nat(r0, r1, r2, r3, r4) == (carry4 as nat) + t_high(limbs)
            + nl_high_contribution(n0, n1, n2, n3, n4),
{
    // =======================================================================
    // PROOF STRUCTURE
    // =======================================================================
    //
    // Goal: intermediate = carry4 + t_high + nl_high
    //
    // Subgoal 1: intermediate = expanded form (substitute stage equations)
    // Subgoal 2: expanded form = cancelled form (carries cancel)
    // Subgoal 3: cancelled form = target (regroup into t_high + nl_high)
    let intermediate = five_u64_limbs_to_nat(r0, r1, r2, r3, r4);
    let t_high_val = t_high(limbs);
    let nl_high = nl_high_contribution(n0, n1, n2, n3, n4);
    let target = (carry4 as nat) + t_high_val + nl_high;

    // Products at each position (N×L coefficients at positions 5-8)
    let products5 = (n1 as nat) * (constants::L.limbs[4] as nat) + (n3 as nat) * (
    constants::L.limbs[2] as nat) + (n4 as nat) * (constants::L.limbs[1] as nat);
    let products6 = (n2 as nat) * (constants::L.limbs[4] as nat) + (n4 as nat) * (
    constants::L.limbs[2] as nat);
    let products7 = (n3 as nat) * (constants::L.limbs[4] as nat);
    let products8 = (n4 as nat) * (constants::L.limbs[4] as nat);

    // Base values (limb + products, without carries)
    let base5 = (limbs[5] as nat) + products5;
    let base6 = (limbs[6] as nat) + products6;
    let base7 = (limbs[7] as nat) + products7;
    let base8 = (limbs[8] as nat) + products8;

    // Power-of-2 relationships
    lemma_pow2_adds(52, 52);  // pow2(104)
    lemma_pow2_adds(52, 104);  // pow2(156)
    lemma_pow2_adds(52, 156);  // pow2(208)

    // =======================================================================
    // Subgoal 1: intermediate = expanded form (substitute stage equations)
    // =======================================================================
    //
    // intermediate = r0 + r1×2^52 + r2×2^104 + r3×2^156 + r4×2^208
    //
    // From stage equations: r_i = sum_{i+5} - carry_{i+5} × 2^52
    // Expand: intermediate = (sum5 - carry5×2^52) + (sum6 - carry6×2^52)×2^52 + ...

    let expanded = (sum5 as nat) - (carry5 as nat) * pow2(52) + ((sum6 as nat) - (carry6 as nat)
        * pow2(52)) * pow2(52) + ((sum7 as nat) - (carry7 as nat) * pow2(52)) * pow2(104) + (
    sum8 as nat) * pow2(156);

    assert(intermediate == expanded) by {
        // r3×2^156 + r4×2^208 = sum8×2^156
        assert((r3 as nat) * pow2(156) + (r4 as nat) * pow2(208) == (sum8 as nat) * pow2(156)) by {
            lemma_mul_is_distributive_sub_other_way(
                pow2(156) as int,
                (sum8 as nat) as int,
                ((r4 as nat) * pow2(52)) as int,
            );
            assert((r4 as nat) * pow2(52) * pow2(156) == (r4 as nat) * pow2(208)) by {
                lemma_mul_is_associative((r4 as nat) as int, pow2(52) as int, pow2(156) as int);
            };
        };

        // Expand products: (sum - carry×2^52) × 2^k
        lemma_mul_is_distributive_sub_other_way(
            pow2(52) as int,
            (sum6 as nat) as int,
            ((carry6 as nat) * pow2(52)) as int,
        );
        lemma_mul_is_distributive_sub_other_way(
            pow2(104) as int,
            (sum7 as nat) as int,
            ((carry7 as nat) * pow2(52)) as int,
        );
        assert((carry6 as nat) * pow2(52) * pow2(52) == (carry6 as nat) * pow2(104)) by {
            lemma_mul_is_associative((carry6 as nat) as int, pow2(52) as int, pow2(52) as int);
        };
        assert((carry7 as nat) * pow2(52) * pow2(104) == (carry7 as nat) * pow2(156)) by {
            lemma_mul_is_associative((carry7 as nat) as int, pow2(52) as int, pow2(104) as int);
        };
    };

    // =======================================================================
    // Subgoal 2: expanded form = cancelled form (carries cancel)
    // =======================================================================
    //
    // Substitute sum definitions: sum_{i+5} = carry_{i+4} + base_{i+5}
    //
    // expanded = (carry4 + base5) - carry5×2^52
    //          + (carry5 + base6)×2^52 - carry6×2^104
    //          + (carry6 + base7)×2^104 - carry7×2^156
    //          + (carry7 + base8)×2^156
    //
    // After cancellation:
    //   -carry5×2^52 + carry5×2^52 = 0
    //   -carry6×2^104 + carry6×2^104 = 0
    //   -carry7×2^156 + carry7×2^156 = 0
    //
    // Result: carry4 + base5 + base6×2^52 + base7×2^104 + base8×2^156

    let cancelled = (carry4 as nat) + base5 + base6 * pow2(52) + base7 * pow2(104) + base8 * pow2(
        156,
    );

    assert(expanded == cancelled) by {
        // Verify sum decompositions
        assert((sum5 as nat) == (carry4 as nat) + base5);
        assert((sum6 as nat) == (carry5 as nat) + base6);
        assert((sum7 as nat) == (carry6 as nat) + base7);
        assert((sum8 as nat) == (carry7 as nat) + base8);

        // Expand each term
        let term5 = (carry4 as nat) + base5 - (carry5 as nat) * pow2(52);
        assert((sum5 as nat) - (carry5 as nat) * pow2(52) == term5);

        lemma_mul_is_distributive_sub_other_way(
            pow2(52) as int,
            ((carry5 as nat) + base6) as int,
            ((carry6 as nat) * pow2(52)) as int,
        );
        lemma_mul_is_distributive_add(pow2(52) as int, (carry5 as nat) as int, base6 as int);
        assert(((carry6 as nat) * pow2(52)) * pow2(52) == (carry6 as nat) * pow2(104)) by {
            lemma_mul_is_associative((carry6 as nat) as int, pow2(52) as int, pow2(52) as int);
        };
        let term6 = (carry5 as nat) * pow2(52) + base6 * pow2(52) - (carry6 as nat) * pow2(104);
        assert(((sum6 as nat) - (carry6 as nat) * pow2(52)) * pow2(52) == term6);

        lemma_mul_is_distributive_sub_other_way(
            pow2(104) as int,
            ((carry6 as nat) + base7) as int,
            ((carry7 as nat) * pow2(52)) as int,
        );
        lemma_mul_is_distributive_add(pow2(104) as int, (carry6 as nat) as int, base7 as int);
        assert(((carry7 as nat) * pow2(52)) * pow2(104) == (carry7 as nat) * pow2(156)) by {
            lemma_mul_is_associative((carry7 as nat) as int, pow2(52) as int, pow2(104) as int);
        };
        let term7 = (carry6 as nat) * pow2(104) + base7 * pow2(104) - (carry7 as nat) * pow2(156);
        assert(((sum7 as nat) - (carry7 as nat) * pow2(52)) * pow2(104) == term7);

        let term8 = (carry7 as nat) * pow2(156) + base8 * pow2(156);
        lemma_mul_is_distributive_add_other_way(
            pow2(156) as int,
            (carry7 as nat) as int,
            base8 as int,
        );
        assert((sum8 as nat) * pow2(156) == term8);

        // Sum terms and verify cancellation
        assert(expanded == term5 + term6 + term7 + term8);
        assert(term5 + term6 + term7 + term8 == cancelled);
    };

    // =======================================================================
    // Subgoal 3: cancelled form = target (regroup into t_high + nl_high)
    // =======================================================================
    //
    // cancelled = carry4 + (limbs[5] + products5)
    //           + (limbs[6] + products6)×2^52
    //           + (limbs[7] + products7)×2^104
    //           + (limbs[8] + products8)×2^156
    //
    // Distribute:
    //   = carry4 + (limbs[5] + limbs[6]×2^52 + limbs[7]×2^104 + limbs[8]×2^156)
    //           + (products5 + products6×2^52 + products7×2^104 + products8×2^156)
    //   = carry4 + t_high + nl_high

    assert(cancelled == target) by {
        assert(t_high_val == (limbs[5] as nat) + (limbs[6] as nat) * pow2(52) + (limbs[7] as nat)
            * pow2(104) + (limbs[8] as nat) * pow2(156));
        assert(nl_high == products5 + products6 * pow2(52) + products7 * pow2(104) + products8
            * pow2(156));

        // Expand base_i × 2^k
        assert(base6 * pow2(52) == (limbs[6] as nat) * pow2(52) + products6 * pow2(52)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(52) as int,
                (limbs[6] as nat) as int,
                products6 as int,
            );
        };
        assert(base7 * pow2(104) == (limbs[7] as nat) * pow2(104) + products7 * pow2(104)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(104) as int,
                (limbs[7] as nat) as int,
                products7 as int,
            );
        };
        assert(base8 * pow2(156) == (limbs[8] as nat) * pow2(156) + products8 * pow2(156)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(156) as int,
                (limbs[8] as nat) as int,
                products8 as int,
            );
        };
    };

    // Chain: intermediate == expanded == cancelled == target
    assert(intermediate == target);
}

// =============================================================================
// Main Quotient Lemma
// =============================================================================
/// After all 4 part2 calls, intermediate = (T + N×L) / R
///
/// This chains the individual part2 postconditions with the divisibility
/// result from Part 1 to establish that the intermediate value equals
/// the exact quotient of (T + N×L) divided by R.
///
/// # Mathematical Argument
///
/// 1. From Part 1: (T + N×L) ≡ 0 (mod R), so T + N×L = k × R for some k
/// 2. Part 2 computes k by extracting the high bits after division by R
/// 3. The sums at positions 5-8 represent (T + N×L) >> 260
/// 4. Telescoping shows: r0 + r1×2^52 + ... + r4×2^208 = k
/// 5. Therefore: intermediate = (T + N×L) / R
///
/// # Preconditions
///
/// - Part 1 divisibility must be established
/// - Stage equations from part2 postconditions
/// - Carry chain from part1's final carry (carry4) to part2's inputs
pub(crate) proof fn lemma_part2_chain_quotient(
    limbs: &[u128; 9],
    // N values from Part 1
    n0: u64,
    n1: u64,
    n2: u64,
    n3: u64,
    n4: u64,
    // Final carry from Part 1
    carry4: u128,
    // Part 2 sums
    sum5: u128,
    sum6: u128,
    sum7: u128,
    sum8: u128,
    // Part 2 carries
    carry5: u128,
    carry6: u128,
    carry7: u128,
    // Part 2 outputs
    r0: u64,
    r1: u64,
    r2: u64,
    r3: u64,
    r4: u64,
)
    requires
        montgomery_reduce_input_bounds(limbs),
        // N bounds (from part1 postconditions)
        n0 < pow2(52),
        n1 < pow2(52),
        n2 < pow2(52),
        n3 < pow2(52),
        n4 < pow2(52),
        // Part 1 divisibility result (T + N×L) ≡ 0 (mod 2^260)
        ({
            let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
                + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
            let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
            let l_low = constants::L.limbs[0] as nat + constants::L.limbs[1] as nat * pow2(52)
                + constants::L.limbs[2] as nat * pow2(104) + constants::L.limbs[3] as nat * pow2(
                156,
            ) + constants::L.limbs[4] as nat * pow2(208);
            (t_low + n * l_low) % pow2(260) == 0
        }),
        // Part 1 quotient result: t_low + nl_low_coeffs == carry4 * 2^260
        // This is the key fact from Part 1's telescoping that we need for the quotient calculation
        ({
            let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
                + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
            let l0_val = constants::L.limbs[0] as nat;
            let l1 = constants::L.limbs[1] as nat;
            let l2 = constants::L.limbs[2] as nat;
            let l4 = constants::L.limbs[4] as nat;
            let coeff0 = (n0 as nat) * l0_val;
            let coeff1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
            let coeff2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
            let coeff3 = (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;
            let coeff4 = (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat)
                * l0_val;
            let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156)
                + coeff4 * pow2(208);
            t_low + nl_low_coeffs == (carry4 as nat) * pow2(260)
        }),
        // Sum definitions (how part2 inputs are computed)
        sum5 as nat == carry4 as nat + limbs[5] as nat + (n1 as nat) * (
        constants::L.limbs[4] as nat) + (n3 as nat) * (constants::L.limbs[2] as nat) + (n4 as nat)
            * (constants::L.limbs[1] as nat),
        sum6 as nat == carry5 as nat + limbs[6] as nat + (n2 as nat) * (
        constants::L.limbs[4] as nat) + (n4 as nat) * (constants::L.limbs[2] as nat),
        sum7 as nat == carry6 as nat + limbs[7] as nat + (n3 as nat) * (
        constants::L.limbs[4] as nat),
        sum8 as nat == carry7 as nat + limbs[8] as nat + (n4 as nat) * (
        constants::L.limbs[4] as nat),
        // Part2 stage equations
        sum5 as nat == (r0 as nat) + (carry5 as nat) * pow2(52),
        sum6 as nat == (r1 as nat) + (carry6 as nat) * pow2(52),
        sum7 as nat == (r2 as nat) + (carry7 as nat) * pow2(52),
        sum8 as nat == (r3 as nat) + (r4 as nat) * pow2(52),
        // r bounds from part2 postconditions
        r0 < pow2(52),
        r1 < pow2(52),
        r2 < pow2(52),
        r3 < pow2(52),
    ensures
        ({
            let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
            let t = slice128_to_nat(limbs);
            let l = group_order();
            let intermediate = five_u64_limbs_to_nat(r0, r1, r2, r3, r4);
            // The key result: intermediate is the exact quotient
            intermediate * pow2(260) + 0 == t + n
                * l
            // Equivalently: intermediate == (t + n * l) / pow2(260)

        }),
{
    // =======================================================================
    // PROOF STRUCTURE (5 subgoals)
    // =======================================================================
    //
    // Goal: T + N×L = intermediate × 2^260
    //
    // Subgoal A: T = t_low + t_high × 2^260
    // Subgoal B: intermediate = carry4 + t_high + nl_high (carry cancellation)
    // Subgoal C: N×L = nl_low_coeffs + nl_high × 2^260
    // Subgoal D: t_low + nl_low_coeffs = carry4 × 2^260 (from Part 1)
    // Subgoal E: Chain A + C + D + B → goal
    // Setup: Define all key values
    let intermediate = five_u64_limbs_to_nat(r0, r1, r2, r3, r4);
    let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
    let t = slice128_to_nat(limbs);
    let l = group_order();

    // T decomposition components
    let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
        + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
    let t_high = limbs[5] as nat + limbs[6] as nat * pow2(52) + limbs[7] as nat * pow2(104)
        + limbs[8] as nat * pow2(156);

    // N×L decomposition components
    let nl_high = nl_high_contribution(n0, n1, n2, n3, n4);
    let l0_val = constants::L.limbs[0] as nat;
    let l1 = constants::L.limbs[1] as nat;
    let l2 = constants::L.limbs[2] as nat;
    let l4 = constants::L.limbs[4] as nat;  // L[3] = 0

    let coeff0 = (n0 as nat) * l0_val;
    let coeff1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
    let coeff2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
    let coeff3 = (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;
    let coeff4 = (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat) * l0_val;
    let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156)
        + coeff4 * pow2(208);

    // =======================================================================
    // Subgoal A: T = t_low + t_high × 2^260
    // =======================================================================
    assert(t == t_low + t_high * pow2(260)) by {
        // Expand slice128_to_nat to polynomial form
        super::super::scalar_lemmas::lemma_nine_limbs_equals_slice128_to_nat(limbs);

        // Power relationships for factoring
        lemma_pow2_adds(52, 260);
        lemma_pow2_adds(104, 260);
        lemma_pow2_adds(156, 260);

        // t_high × 2^260 expands to high limb terms
        assert(t_high * pow2(260) == (limbs[5] as nat) * pow2(260) + (limbs[6] as nat) * pow2(312)
            + (limbs[7] as nat) * pow2(364) + (limbs[8] as nat) * pow2(416)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                (limbs[5] as nat) as int,
                ((limbs[6] as nat) * pow2(52) + (limbs[7] as nat) * pow2(104) + (limbs[8] as nat)
                    * pow2(156)) as int,
            );
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                ((limbs[6] as nat) * pow2(52)) as int,
                ((limbs[7] as nat) * pow2(104) + (limbs[8] as nat) * pow2(156)) as int,
            );
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                ((limbs[7] as nat) * pow2(104)) as int,
                ((limbs[8] as nat) * pow2(156)) as int,
            );
            assert((limbs[6] as nat) * pow2(52) * pow2(260) == (limbs[6] as nat) * pow2(312)) by {
                lemma_mul_is_associative(
                    (limbs[6] as nat) as int,
                    pow2(52) as int,
                    pow2(260) as int,
                );
            };
            assert((limbs[7] as nat) * pow2(104) * pow2(260) == (limbs[7] as nat) * pow2(364)) by {
                lemma_mul_is_associative(
                    (limbs[7] as nat) as int,
                    pow2(104) as int,
                    pow2(260) as int,
                );
            };
            assert((limbs[8] as nat) * pow2(156) * pow2(260) == (limbs[8] as nat) * pow2(416)) by {
                lemma_mul_is_associative(
                    (limbs[8] as nat) as int,
                    pow2(156) as int,
                    pow2(260) as int,
                );
            };
        };
    };

    // =======================================================================
    // Subgoal B: intermediate = carry4 + t_high + nl_high (carry cancellation)
    // =======================================================================
    assert(intermediate == (carry4 as nat) + t_high + nl_high) by {
        lemma_part2_carry_cancellation(
            limbs,
            n0,
            n1,
            n2,
            n3,
            n4,
            carry4,
            sum5,
            sum6,
            sum7,
            sum8,
            carry5,
            carry6,
            carry7,
            r0,
            r1,
            r2,
            r3,
            r4,
        );
    };

    // =======================================================================
    // Subgoal C: N×L = nl_low_coeffs + nl_high × 2^260
    // =======================================================================
    assert(n * l == nl_low_coeffs + nl_high * pow2(260)) by {
        // Connect group_order() to limb polynomial
        lemma_l_equals_group_order();
        lemma_five_limbs_equals_to_nat(&constants::L.limbs);
        lemma_mul_is_commutative(pow2(52) as int, constants::L.limbs[1] as int);
        lemma_mul_is_commutative(pow2(104) as int, constants::L.limbs[2] as int);
        lemma_mul_is_commutative(pow2(156) as int, constants::L.limbs[3] as int);
        lemma_mul_is_commutative(pow2(208) as int, constants::L.limbs[4] as int);

        let l_poly = l0_val + l1 * pow2(52) + l2 * pow2(104) + 0 * pow2(156) + l4 * pow2(208);
        assert(l == l_poly);

        // Use polynomial multiplication decomposition lemma
        lemma_poly_mul_5x5_decomposition(
            n0 as nat,
            n1 as nat,
            n2 as nat,
            n3 as nat,
            n4 as nat,
            l0_val,
            l1,
            l2,
            0,
            l4,
        );

        let n_poly = (n0 as nat) + (n1 as nat) * pow2(52) + (n2 as nat) * pow2(104) + (n3 as nat)
            * pow2(156) + (n4 as nat) * pow2(208);
        assert(n == n_poly);
    };

    // =======================================================================
    // Subgoal D: t_low + nl_low_coeffs = carry4 × 2^260 (from Part 1 precondition)
    // =======================================================================
    assert(t_low + nl_low_coeffs == (carry4 as nat) * pow2(260));

    // =======================================================================
    // Subgoal E: Chain all subgoals to prove T + N×L = intermediate × 2^260
    // =======================================================================
    //
    // T + N×L = (t_low + t_high × 2^260) + (nl_low_coeffs + nl_high × 2^260)  [A + C]
    //         = (t_low + nl_low_coeffs) + (t_high + nl_high) × 2^260
    //         = carry4 × 2^260 + (t_high + nl_high) × 2^260                   [D]
    //         = (carry4 + t_high + nl_high) × 2^260
    //         = intermediate × 2^260                                          [B]

    assert(t + n * l == intermediate * pow2(260)) by {
        // Step 1: Combine T and N×L decompositions
        assert(t + n * l == (t_low + nl_low_coeffs) + (t_high + nl_high) * pow2(260)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                t_high as int,
                nl_high as int,
            );
        };

        // Step 2: Substitute Part 1 result and factor
        assert(t + n * l == ((carry4 as nat) + t_high + nl_high) * pow2(260)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                (carry4 as nat) as int,
                (t_high + nl_high) as int,
            );
        };

        // Step 3: Apply carry cancellation result
        // (carry4 + t_high + nl_high) == intermediate (from Subgoal B)
    };

    // Final postcondition
    assert(intermediate * pow2(260) + 0 == t + n * l);
}

} // verus!
