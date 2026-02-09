//! Lemmas for proving `lemma_part1_chain_divisibility`
//!
//! This module proves that after 5 calls to `part1`:
//!   `(T + N×L) ≡ 0 (mod 2^260)`
//!
//! ## Proof Structure
//!
//! 1. **`lemma_part1_telescoping_expansion`**: Weighted stage equations sum
//!    and intermediate carries cancel (telescope), leaving `c4 × 2^260`.
//!
//! 2. **`lemma_n_times_l_expansion`**: `(N × L_low) mod 2^260` equals
//!    the weighted sum of polynomial coefficients at positions 0-4.
//!
//! 3. **`lemma_poly_mul_5x5_decomposition`**: 5×5 polynomial multiplication
//!    decomposes into low (positions 0-4) and high (positions 5-8) parts.
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;

use crate::backend::serial::u64::constants;
use crate::specs::scalar52_specs::*;

verus! {

// =============================================================================
// Helper function for L[0] constant
// =============================================================================
/// Returns L[0] = constants::L.limbs[0] as nat
#[inline(always)]
pub(crate) open spec fn l0() -> nat {
    constants::L.limbs[0] as nat
}

// =============================================================================
// Core Polynomial Multiplication Decomposition
// =============================================================================
/// 5×5 polynomial multiplication decomposes into low (positions 0-4) and high (positions 5-8) parts.
///
/// # Mathematical Structure
///
/// Given two 5-term polynomials in radix 2^52:
///   A = a0 + a1×2^52 + a2×2^104 + a3×2^156 + a4×2^208
///   B = b0 + b1×2^52 + b2×2^104 + b3×2^156 + b4×2^208
///
/// Their product A×B has 9 coefficient positions (0-8), where position k
/// collects all cross-products aᵢ×bⱼ with i+j=k.
///
/// # Decomposition
///
/// low_coeffs  = coeff₀ + coeff₁×2^52 + coeff₂×2^104 + coeff₃×2^156 + coeff₄×2^208
/// high_coeffs = coeff₅ + coeff₆×2^52 + coeff₇×2^104 + coeff₈×2^156
///
/// A × B = low_coeffs + high_coeffs × 2^260
///
/// # Usage
///
/// This lemma is called from both `lemma_n_times_l_expansion` (Part 1) and
/// `lemma_part2_chain_quotient` (Part 2) to avoid duplicating the polynomial
/// multiplication proof.
pub(crate) proof fn lemma_poly_mul_5x5_decomposition(
    a0: nat,
    a1: nat,
    a2: nat,
    a3: nat,
    a4: nat,
    b0: nat,
    b1: nat,
    b2: nat,
    b3: nat,
    b4: nat,
)
    ensures
        ({
            let a = a0 + a1 * pow2(52) + a2 * pow2(104) + a3 * pow2(156) + a4 * pow2(208);
            let b = b0 + b1 * pow2(52) + b2 * pow2(104) + b3 * pow2(156) + b4 * pow2(208);

            // Position coefficients from polynomial multiplication
            let c0 = a0 * b0;
            let c1 = a0 * b1 + a1 * b0;
            let c2 = a0 * b2 + a1 * b1 + a2 * b0;
            let c3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0;
            let c4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0;
            let c5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1;
            let c6 = a2 * b4 + a3 * b3 + a4 * b2;
            let c7 = a3 * b4 + a4 * b3;
            let c8 = a4 * b4;

            let low_coeffs = c0 + c1 * pow2(52) + c2 * pow2(104) + c3 * pow2(156) + c4 * pow2(208);
            let high_coeffs = c5 + c6 * pow2(52) + c7 * pow2(104) + c8 * pow2(156);

            a * b == low_coeffs + high_coeffs * pow2(260)
        }),
{
    // =======================================================================
    // PROOF STRUCTURE (3 subgoals)
    // =======================================================================
    //
    // Goal: A × B = low_coeffs + high_coeffs × 2^260
    //
    // Subgoal A: A × B = full polynomial (all 9 coefficient positions)
    // Subgoal B: high positions (5-8) factor as high_coeffs × 2^260
    // Subgoal C: Combine to get final result
    // Setup: Power-of-2 relationships
    lemma_pow2_adds(52, 52);  // 2^104
    lemma_pow2_adds(52, 104);  // 2^156
    lemma_pow2_adds(52, 156);  // 2^208
    lemma_pow2_adds(52, 208);  // 2^260
    lemma_pow2_adds(104, 104);  // 2^208
    lemma_pow2_adds(104, 156);  // 2^260
    lemma_pow2_adds(156, 52);  // 2^208
    lemma_pow2_adds(156, 104);  // 2^260
    lemma_pow2_adds(208, 52);  // 2^260
    lemma_pow2_adds(260, 52);  // 2^312
    lemma_pow2_adds(260, 104);  // 2^364
    lemma_pow2_adds(260, 156);  // 2^416

    // Setup: Define polynomials and coefficients
    let a = a0 + a1 * pow2(52) + a2 * pow2(104) + a3 * pow2(156) + a4 * pow2(208);
    let b = b0 + b1 * pow2(52) + b2 * pow2(104) + b3 * pow2(156) + b4 * pow2(208);

    // Position coefficients (convolution: c_k = Σ_{i+j=k} a_i × b_j)
    let c0 = a0 * b0;
    let c1 = a0 * b1 + a1 * b0;
    let c2 = a0 * b2 + a1 * b1 + a2 * b0;
    let c3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0;
    let c4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0;
    let c5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1;
    let c6 = a2 * b4 + a3 * b3 + a4 * b2;
    let c7 = a3 * b4 + a4 * b3;
    let c8 = a4 * b4;

    let low_coeffs = c0 + c1 * pow2(52) + c2 * pow2(104) + c3 * pow2(156) + c4 * pow2(208);
    let high_coeffs = c5 + c6 * pow2(52) + c7 * pow2(104) + c8 * pow2(156);

    // Full 9-position polynomial
    let full = c0 + c1 * pow2(52) + c2 * pow2(104) + c3 * pow2(156) + c4 * pow2(208) + c5 * pow2(
        260,
    ) + c6 * pow2(312) + c7 * pow2(364) + c8 * pow2(416);

    // =======================================================================
    // Subgoal A: A × B = full polynomial (FOIL expansion)
    // =======================================================================
    assert(a * b == full) by {
        broadcast use group_mul_is_commutative_and_distributive;
        broadcast use lemma_mul_is_associative;
        // The broadcast axioms handle the 25-term FOIL expansion automatically

    };

    // =======================================================================
    // Subgoal B: high positions factor as high_coeffs × 2^260
    // =======================================================================
    //
    // c5×2^260 + c6×2^312 + c7×2^364 + c8×2^416
    // = c5×2^260 + c6×2^52×2^260 + c7×2^104×2^260 + c8×2^156×2^260
    // = (c5 + c6×2^52 + c7×2^104 + c8×2^156) × 2^260
    // = high_coeffs × 2^260

    assert(c5 * pow2(260) + c6 * pow2(312) + c7 * pow2(364) + c8 * pow2(416) == high_coeffs * pow2(
        260,
    )) by {
        // Distribute: (a + b + c + d) × k = a×k + b×k + c×k + d×k
        lemma_mul_is_distributive_add_other_way(
            pow2(260) as int,
            c5 as int,
            (c6 * pow2(52) + c7 * pow2(104) + c8 * pow2(156)) as int,
        );
        lemma_mul_is_distributive_add_other_way(
            pow2(260) as int,
            (c6 * pow2(52)) as int,
            (c7 * pow2(104) + c8 * pow2(156)) as int,
        );
        lemma_mul_is_distributive_add_other_way(
            pow2(260) as int,
            (c7 * pow2(104)) as int,
            (c8 * pow2(156)) as int,
        );

        // Power combinations: pow2(k) × pow2(260) = pow2(k+260)
        assert(pow2(52) * pow2(260) == pow2(312)) by {
            lemma_mul_is_commutative(pow2(52) as int, pow2(260) as int);
        };
        assert(pow2(104) * pow2(260) == pow2(364)) by {
            lemma_mul_is_commutative(pow2(104) as int, pow2(260) as int);
        };
        assert(pow2(156) * pow2(260) == pow2(416)) by {
            lemma_mul_is_commutative(pow2(156) as int, pow2(260) as int);
        };

        // Associativity: c_i × pow2(k) × pow2(260) = c_i × pow2(k+260)
        assert(c6 * pow2(52) * pow2(260) == c6 * pow2(312)) by {
            lemma_mul_is_associative(c6 as int, pow2(52) as int, pow2(260) as int);
        };
        assert(c7 * pow2(104) * pow2(260) == c7 * pow2(364)) by {
            lemma_mul_is_associative(c7 as int, pow2(104) as int, pow2(260) as int);
        };
        assert(c8 * pow2(156) * pow2(260) == c8 * pow2(416)) by {
            lemma_mul_is_associative(c8 as int, pow2(156) as int, pow2(260) as int);
        };
    };

    // =======================================================================
    // Subgoal C: Combine to get final result
    // =======================================================================
    // full = low_coeffs + (c5×2^260 + c6×2^312 + c7×2^364 + c8×2^416)
    //      = low_coeffs + high_coeffs × 2^260

    assert(a * b == low_coeffs + high_coeffs * pow2(260));
}

// =============================================================================
// Helper: Polynomial expansion of N × L_low
// =============================================================================
/// Decomposes N × L_low into low and high parts, showing the high part vanishes mod 2^260.
///
/// # What This Lemma Proves
///
/// Given 5-limb polynomials N and L_low (in base 2^52):
///
/// 1. **Full decomposition**: `N × L_low == low_part + high_part`
///    - `low_part` = coefficients at positions 0-4 (convolution terms < 2^260)
///    - `high_part` = coefficients at positions 5-8 (all multiples of 2^260)
///
/// 2. **Divisibility**: `high_part % pow2(260) == 0`
///
/// 3. **Modular equivalence**: `(N × L_low) % pow2(260) == low_part % pow2(260)`
///
/// # Why This Matters
///
/// In Montgomery reduction, we need `(T + N × L) % 2^260 == 0`. This lemma shows
/// that `N × L_low mod 2^260` depends only on the low-order coefficients (positions 0-4),
/// which are exactly the terms that appear in the stage equations.
///
/// # Polynomial Structure
///
/// ```text
/// N     = n0 + n1×2^52 + n2×2^104 + n3×2^156 + n4×2^208
/// L_low = l0 + l1×2^52 + l2×2^104 + 0×2^156 + l4×2^208   (l3 = 0)
/// ```
///
/// # Proof Structure
///
/// - **STEP 1**: Polynomial multiplication via `lemma_poly_mul_5x5_decomposition`
/// - **STEP 2**: Show `high_part` is a multiple of 2^260
/// - **STEP 3**: Apply modular arithmetic to conclude
pub(crate) proof fn lemma_n_times_l_expansion(
    n0: nat,
    n1: nat,
    n2: nat,
    n3: nat,
    n4: nat,
    l0: nat,
    l1: nat,
    l2: nat,
    l3: nat,
    l4: nat,
)
    requires
        l3 == 0,  // L[3] = 0 is a property of the group order

    ensures
// Modular equality: (N × L_low) mod 2^260 == low_part mod 2^260

        ({
            let n = n0 + n1 * pow2(52) + n2 * pow2(104) + n3 * pow2(156) + n4 * pow2(208);
            let l_low = l0 + l1 * pow2(52) + l2 * pow2(104) + l3 * pow2(156) + l4 * pow2(208);

            let coeff0 = n0 * l0;
            let coeff1 = n0 * l1 + n1 * l0;
            let coeff2 = n0 * l2 + n1 * l1 + n2 * l0;
            let coeff3 = n1 * l2 + n2 * l1 + n3 * l0;
            let coeff4 = n0 * l4 + n2 * l2 + n3 * l1 + n4 * l0;

            (n * l_low) % pow2(260) == (coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3
                * pow2(156) + coeff4 * pow2(208)) % pow2(260)
        }),
        // Full decomposition: N × L_low == low_part + high_part where high_part is a multiple of 2^260
        ({
            let n = n0 + n1 * pow2(52) + n2 * pow2(104) + n3 * pow2(156) + n4 * pow2(208);
            let l_low = l0 + l1 * pow2(52) + l2 * pow2(104) + l3 * pow2(156) + l4 * pow2(208);

            let coeff0 = n0 * l0;
            let coeff1 = n0 * l1 + n1 * l0;
            let coeff2 = n0 * l2 + n1 * l1 + n2 * l0;
            let coeff3 = n1 * l2 + n2 * l1 + n3 * l0;
            let coeff4 = n0 * l4 + n2 * l2 + n3 * l1 + n4 * l0;
            let low_part = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156)
                + coeff4 * pow2(208);

            let coeff5 = n1 * l4 + n3 * l2 + n4 * l1;
            let coeff6 = n2 * l4 + n4 * l2;
            let coeff7 = n3 * l4;
            let coeff8 = n4 * l4;
            let high_part = coeff5 * pow2(260) + coeff6 * pow2(312) + coeff7 * pow2(364) + coeff8
                * pow2(416);

            n * l_low == low_part + high_part && high_part % pow2(260) == 0
        }),
{
    // =======================================================================
    // PROOF STRUCTURE (3 subgoals)
    // =======================================================================
    //
    // Goal: (N × L_low) % 2^260 == low_part % 2^260
    //
    // Subgoal A: N × L_low = low_part + high_part (polynomial decomposition)
    // Subgoal B: high_part % 2^260 = 0 (high terms are multiples of 2^260)
    // Subgoal C: Modular equivalence follows from A and B
    // Setup: Power-of-2 relationships
    lemma_pow2_adds(52, 52);  // 2^104
    lemma_pow2_adds(52, 104);  // 2^156
    lemma_pow2_adds(52, 156);  // 2^208
    lemma_pow2_adds(52, 208);  // 2^260
    lemma_pow2_adds(104, 104);  // 2^208
    lemma_pow2_adds(104, 156);  // 2^260
    lemma_pow2_adds(156, 52);  // 2^208
    lemma_pow2_adds(156, 104);  // 2^260
    lemma_pow2_adds(208, 52);  // 2^260
    lemma_pow2_adds(52, 260);  // 2^312
    lemma_pow2_adds(104, 260);  // 2^364
    lemma_pow2_adds(156, 260);  // 2^416

    // Setup: Define polynomials and coefficients
    let n = n0 + n1 * pow2(52) + n2 * pow2(104) + n3 * pow2(156) + n4 * pow2(208);
    let l_low = l0 + l1 * pow2(52) + l2 * pow2(104) + l4 * pow2(208);  // l3=0

    // Low-order coefficients (positions 0-4)
    let coeff0 = n0 * l0;
    let coeff1 = n0 * l1 + n1 * l0;
    let coeff2 = n0 * l2 + n1 * l1 + n2 * l0;
    let coeff3 = n1 * l2 + n2 * l1 + n3 * l0;
    let coeff4 = n0 * l4 + n2 * l2 + n3 * l1 + n4 * l0;
    let low_part = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156) + coeff4
        * pow2(208);

    // High-order coefficients (positions 5-8, all multiples of 2^260)
    let coeff5 = n1 * l4 + n3 * l2 + n4 * l1;
    let coeff6 = n2 * l4 + n4 * l2;
    let coeff7 = n3 * l4;
    let coeff8 = n4 * l4;
    let high_part = coeff5 * pow2(260) + coeff6 * pow2(312) + coeff7 * pow2(364) + coeff8 * pow2(
        416,
    );

    // =======================================================================
    // Subgoal A: N × L_low = low_part + high_part (polynomial decomposition)
    // =======================================================================
    //
    // Use lemma_poly_mul_5x5_decomposition with l3 = 0 simplification.
    // General coefficients have n_i × l3 terms that vanish.

    assert(n * l_low == low_part + high_part) by {
        lemma_poly_mul_5x5_decomposition(n0, n1, n2, n3, n4, l0, l1, l2, l3, l4);

        // General coefficients (l3 terms vanish since l3 = 0)
        let gen_c0 = n0 * l0;
        let gen_c1 = n0 * l1 + n1 * l0;
        let gen_c2 = n0 * l2 + n1 * l1 + n2 * l0;
        let gen_c3 = n0 * l3 + n1 * l2 + n2 * l1 + n3 * l0;
        let gen_c4 = n0 * l4 + n1 * l3 + n2 * l2 + n3 * l1 + n4 * l0;
        let gen_c5 = n1 * l4 + n2 * l3 + n3 * l2 + n4 * l1;
        let gen_c6 = n2 * l4 + n3 * l3 + n4 * l2;
        let gen_c7 = n3 * l4 + n4 * l3;
        let gen_c8 = n4 * l4;

        let gen_low = gen_c0 + gen_c1 * pow2(52) + gen_c2 * pow2(104) + gen_c3 * pow2(156) + gen_c4
            * pow2(208);
        let gen_high = gen_c5 + gen_c6 * pow2(52) + gen_c7 * pow2(104) + gen_c8 * pow2(156);

        // Since l3 = 0: gen_c* == coeff* (all n_i × l3 terms vanish)
        assert(gen_c0 == coeff0 && gen_c1 == coeff1 && gen_c2 == coeff2);
        assert(gen_c3 == coeff3 && gen_c4 == coeff4);
        assert(gen_c5 == coeff5 && gen_c6 == coeff6 && gen_c7 == coeff7 && gen_c8 == coeff8);
        assert(gen_low == low_part);

        // gen_high × 2^260 = high_part
        assert(gen_high * pow2(260) == high_part) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                coeff5 as int,
                (coeff6 * pow2(52) + coeff7 * pow2(104) + coeff8 * pow2(156)) as int,
            );
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                (coeff6 * pow2(52)) as int,
                (coeff7 * pow2(104) + coeff8 * pow2(156)) as int,
            );
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                (coeff7 * pow2(104)) as int,
                (coeff8 * pow2(156)) as int,
            );
            lemma_mul_is_commutative(pow2(52) as int, pow2(260) as int);
            lemma_mul_is_commutative(pow2(104) as int, pow2(260) as int);
            lemma_mul_is_commutative(pow2(156) as int, pow2(260) as int);
            lemma_mul_is_associative(coeff6 as int, pow2(52) as int, pow2(260) as int);
            lemma_mul_is_associative(coeff7 as int, pow2(104) as int, pow2(260) as int);
            lemma_mul_is_associative(coeff8 as int, pow2(156) as int, pow2(260) as int);
        };
    };

    // =======================================================================
    // Subgoal B: high_part % 2^260 = 0 (high terms are multiples of 2^260)
    // =======================================================================
    //
    // high_part = c5×2^260 + c6×2^312 + c7×2^364 + c8×2^416
    //           = (c5 + c6×2^52 + c7×2^104 + c8×2^156) × 2^260
    // Any multiple of 2^260 is ≡ 0 (mod 2^260).

    lemma_pow2_pos(260);
    let gen_high = coeff5 + coeff6 * pow2(52) + coeff7 * pow2(104) + coeff8 * pow2(156);

    assert(high_part % pow2(260) == 0) by {
        // Show: high_part == gen_high × 2^260
        assert(gen_high * pow2(260) == high_part) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                coeff5 as int,
                (coeff6 * pow2(52) + coeff7 * pow2(104) + coeff8 * pow2(156)) as int,
            );
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                (coeff6 * pow2(52)) as int,
                (coeff7 * pow2(104) + coeff8 * pow2(156)) as int,
            );
            lemma_mul_is_distributive_add_other_way(
                pow2(260) as int,
                (coeff7 * pow2(104)) as int,
                (coeff8 * pow2(156)) as int,
            );
            lemma_mul_is_commutative(pow2(52) as int, pow2(260) as int);
            lemma_mul_is_commutative(pow2(104) as int, pow2(260) as int);
            lemma_mul_is_commutative(pow2(156) as int, pow2(260) as int);
            lemma_mul_is_associative(coeff6 as int, pow2(52) as int, pow2(260) as int);
            lemma_mul_is_associative(coeff7 as int, pow2(104) as int, pow2(260) as int);
            lemma_mul_is_associative(coeff8 as int, pow2(156) as int, pow2(260) as int);
        };

        // (k × 2^260) % 2^260 == 0
        lemma_mod_self_0(pow2(260) as int);
        lemma_mul_mod_noop_right(gen_high as int, pow2(260) as int, pow2(260) as int);
        lemma_mul_basics(gen_high as int);
        lemma_small_mod(0nat, pow2(260));
    };

    // =======================================================================
    // Subgoal C: Modular equivalence follows from A and B
    // =======================================================================
    //
    // From A: n × l_low == low_part + high_part
    // From B: high_part % 2^260 == 0
    //
    // (n × l_low) % 2^260 = (low_part + high_part) % 2^260
    //                     = (low_part % 2^260 + high_part % 2^260) % 2^260
    //                     = (low_part % 2^260 + 0) % 2^260
    //                     = low_part % 2^260

    lemma_add_mod_noop(low_part as int, high_part as int, pow2(260) as int);

    // Since high_part % pow2(260) == 0:
    // (low_part % pow2(260) + 0) % pow2(260) == low_part % pow2(260)
    assert((low_part + high_part) % pow2(260) == low_part % pow2(260)) by {
        assert((low_part % pow2(260) + 0) % pow2(260) == low_part % pow2(260)) by {
            lemma_mod_twice(low_part as int, pow2(260) as int);
        };
    };

    // Since n * l_low == low_part + high_part:
    assert((n * l_low) % pow2(260) == low_part % pow2(260));
}

// =============================================================================
// Helper: Telescoping expansion for part1 chain
// =============================================================================
/// Shows that when we sum the weighted stage equations, the intermediate
/// carries cancel (telescope).
///
/// # Stage Equations
///
/// Given the stage equations (where s_k is the LHS before adding n_k × l0):
/// - s0 + n0 × l0 = c0 × 2^52
/// - s1 + n1 × l0 = c1 × 2^52  (s1 includes c0)
/// - s2 + n2 × l0 = c2 × 2^52  (s2 includes c1)
/// - s3 + n3 × l0 = c3 × 2^52  (s3 includes c2)
/// - s4 + n4 × l0 = c4 × 2^52  (s4 includes c3)
///
/// # Telescoping
///
/// When we multiply each adjusted equation by 2^(52k) and sum:
/// - c0 appears as: +c0 × 2^52 (from eq 0) and -c0 × 2^52 (in weighted eq 1)
/// - Similarly for c1, c2, c3
/// - Only c4 × 2^260 remains
pub(crate) proof fn lemma_part1_telescoping_expansion(
    s0: nat,
    s1: nat,
    s2: nat,
    s3: nat,
    s4: nat,
    n0: nat,
    n1: nat,
    n2: nat,
    n3: nat,
    n4: nat,
    c0: nat,
    c1: nat,
    c2: nat,
    c3: nat,
    c4: nat,
    l0: nat,
)
    requires
        s0 + n0 * l0 == c0 * pow2(52),
        s1 + n1 * l0 == c1 * pow2(52),
        s2 + n2 * l0 == c2 * pow2(52),
        s3 + n3 * l0 == c3 * pow2(52),
        s4 + n4 * l0 == c4 * pow2(52),
    ensures
        (s0 + n0 * l0) + (s1 - c0 + n1 * l0) * pow2(52) + (s2 - c1 + n2 * l0) * pow2(104) + (s3 - c2
            + n3 * l0) * pow2(156) + (s4 - c3 + n4 * l0) * pow2(208) == c4 * pow2(260),
{
    // =======================================================================
    // PROOF STRUCTURE (2 subgoals)
    // =======================================================================
    //
    // Goal: Σ (s_k - c_{k-1} + n_k×l0) × 2^{52k} = c4 × 2^260
    //
    // Subgoal A: Each adjusted term expands to (c_k×2^52 - c_{k-1}) × 2^{52k}
    // Subgoal B: Sum telescopes (intermediate c_k terms cancel)
    // Setup: Power-of-2 relationships
    lemma_pow2_adds(52, 52);  // 2^104
    lemma_pow2_adds(52, 104);  // 2^156
    lemma_pow2_adds(52, 156);  // 2^208
    lemma_pow2_adds(52, 208);  // 2^260

    // =======================================================================
    // Subgoal A: Expand each weighted term
    // =======================================================================
    //
    // From stage equations: s_k + n_k×l0 = c_k×2^52
    // Adjusted form: (s_k - c_{k-1} + n_k×l0) = c_k×2^52 - c_{k-1}
    // Weighted: (c_k×2^52 - c_{k-1}) × 2^{52k} = c_k×2^{52(k+1)} - c_{k-1}×2^{52k}

    // Stage 0: no adjustment needed
    assert(s0 + n0 * l0 == c0 * pow2(52));

    // Stage 1: (c1×2^52 - c0) × 2^52 = c1×2^104 - c0×2^52
    assert((c1 * pow2(52) - c0) * pow2(52) == c1 * pow2(104) - c0 * pow2(52)) by {
        lemma_mul_is_distributive_sub_other_way(pow2(52) as int, (c1 * pow2(52)) as int, c0 as int);
        lemma_mul_is_associative(c1 as int, pow2(52) as int, pow2(52) as int);
    };

    // Stage 2: (c2×2^52 - c1) × 2^104 = c2×2^156 - c1×2^104
    assert((c2 * pow2(52) - c1) * pow2(104) == c2 * pow2(156) - c1 * pow2(104)) by {
        lemma_mul_is_distributive_sub_other_way(
            pow2(104) as int,
            (c2 * pow2(52)) as int,
            c1 as int,
        );
        lemma_mul_is_associative(c2 as int, pow2(52) as int, pow2(104) as int);
    };

    // Stage 3: (c3×2^52 - c2) × 2^156 = c3×2^208 - c2×2^156
    assert((c3 * pow2(52) - c2) * pow2(156) == c3 * pow2(208) - c2 * pow2(156)) by {
        lemma_mul_is_distributive_sub_other_way(
            pow2(156) as int,
            (c3 * pow2(52)) as int,
            c2 as int,
        );
        lemma_mul_is_associative(c3 as int, pow2(52) as int, pow2(156) as int);
    };

    // Stage 4: (c4×2^52 - c3) × 2^208 = c4×2^260 - c3×2^208
    assert((c4 * pow2(52) - c3) * pow2(208) == c4 * pow2(260) - c3 * pow2(208)) by {
        lemma_mul_is_distributive_sub_other_way(
            pow2(208) as int,
            (c4 * pow2(52)) as int,
            c3 as int,
        );
        lemma_mul_is_associative(c4 as int, pow2(52) as int, pow2(208) as int);
    };

    // Adjusted terms (from stage equations)
    assert(s1 - c0 + n1 * l0 == c1 * pow2(52) - c0);
    assert(s2 - c1 + n2 * l0 == c2 * pow2(52) - c1);
    assert(s3 - c2 + n3 * l0 == c3 * pow2(52) - c2);
    assert(s4 - c3 + n4 * l0 == c4 * pow2(52) - c3);

    // =======================================================================
    // Subgoal B: Sum telescopes to c4 × 2^260
    // =======================================================================
    //
    // Sum = c0×2^52
    //     + (c1×2^104 - c0×2^52)
    //     + (c2×2^156 - c1×2^104)
    //     + (c3×2^208 - c2×2^156)
    //     + (c4×2^260 - c3×2^208)
    //
    // Cancellation:
    //   +c0×2^52  - c0×2^52  = 0
    //   +c1×2^104 - c1×2^104 = 0
    //   +c2×2^156 - c2×2^156 = 0
    //   +c3×2^208 - c3×2^208 = 0
    //
    // Result: c4 × 2^260
}

// =============================================================================
// Main Lemma: Chaining part1 postconditions
// =============================================================================
/// After all 5 part1 calls, T + N×L ≡ 0 (mod 2^260)
///
/// Chains the individual part1 divisibility postconditions to establish
/// the global divisibility property needed for Montgomery reduction.
///
/// # Mathematical Argument
///
/// 1. Each part1 stage: `sum_k + n_k × L[0] = carry_k × 2^52`
/// 2. Telescoping: Weighted sum causes carries to cancel, leaving `c4 × 2^260`
/// 3. Quotient: `t_low + nl_low_coeffs = c4 × 2^260`
/// 4. Polynomial: `(N × L_low) mod 2^260 = nl_low_coeffs mod 2^260` (high terms vanish)
/// 5. Conclusion: `(t_low + N × L_low) mod 2^260 = 0`
///
/// # Proof Structure (5 steps)
///
/// - **STEP 1**: Apply telescoping lemma (carries cancel)
/// - **STEP 2**: Define weighted terms from telescoping structure
/// - **STEP 3**: Separate t_low from nl_low_coeffs using distributivity
/// - **STEP 4**: Establish quotient relationship and divisibility of nl_low_coeffs
/// - **STEP 5**: Connect to N × L_low via polynomial expansion
///
/// # Key Helper Lemmas
///
/// - `lemma_part1_telescoping_expansion`: Proves carry cancellation
/// - `lemma_n_times_l_expansion`: Proves polynomial decomposition
pub(crate) proof fn lemma_part1_chain_divisibility(
    limbs: &[u128; 9],
    n0: u64,
    n1: u64,
    n2: u64,
    n3: u64,
    n4: u64,
    carry0: u128,
    carry1: u128,
    carry2: u128,
    carry3: u128,
    carry4: u128,
)
    requires
// N limbs are 52-bit (from part1 computation: n_k = (sum & mask52) as u64)

        n0 < pow2(52),
        n1 < pow2(52),
        n2 < pow2(52),
        n3 < pow2(52),
        n4 < pow2(52),
        // Stage equations from part1 postconditions (in nat form)
        limbs[0] as nat + (n0 as nat) * l0() == (carry0 as nat) * pow2(52),
        (carry0 as nat + limbs[1] as nat + (n0 as nat) * (constants::L.limbs[1] as nat)) + (
        n1 as nat) * l0() == (carry1 as nat) * pow2(52),
        (carry1 as nat + limbs[2] as nat + (n0 as nat) * (constants::L.limbs[2] as nat) + (
        n1 as nat) * (constants::L.limbs[1] as nat)) + (n2 as nat) * l0() == (carry2 as nat) * pow2(
            52,
        ),
        (carry2 as nat + limbs[3] as nat + (n1 as nat) * (constants::L.limbs[2] as nat) + (
        n2 as nat) * (constants::L.limbs[1] as nat)) + (n3 as nat) * l0() == (carry3 as nat) * pow2(
            52,
        ),
        (carry3 as nat + limbs[4] as nat + (n0 as nat) * (constants::L.limbs[4] as nat) + (
        n2 as nat) * (constants::L.limbs[2] as nat) + (n3 as nat) * (constants::L.limbs[1] as nat))
            + (n4 as nat) * l0() == (carry4 as nat) * pow2(52),
    ensures
// Divisibility: (t_low + n * l_low) % 2^260 == 0

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
        // Quotient relationship: t_low + nl_low_coeffs == carry4 * 2^260
        // This is the exact form Part 2 needs
        ({
            let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
                + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
            let l0_val = constants::L.limbs[0] as nat;
            let l1 = constants::L.limbs[1] as nat;
            let l2 = constants::L.limbs[2] as nat;
            let l4 = constants::L.limbs[4] as nat;
            // Polynomial coefficients at positions 0-4
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
{
    // =======================================================================
    // PROOF STRUCTURE (4 subgoals)
    // =======================================================================
    //
    // Goal: (t_low + N × L_low) % 2^260 == 0
    //
    // Subgoal A: Telescoping sum equals c4 × 2^260 (carries cancel)
    // Subgoal B: t_low + nl_low_coeffs == c4 × 2^260 (quotient relationship)
    // Subgoal C: (N × L_low) % 2^260 == nl_low_coeffs % 2^260 (polynomial)
    // Subgoal D: Final divisibility from B and C
    // =======================================================================
    // Setup: Constants and key quantities
    // =======================================================================
    lemma_pow2_adds(52, 52);  // pow2(104)
    lemma_pow2_adds(52, 104);  // pow2(156)
    lemma_pow2_adds(52, 156);  // pow2(208)
    lemma_pow2_adds(52, 208);  // pow2(260)
    lemma_pow2_adds(52, 260);  // 2^312
    lemma_pow2_adds(104, 260);  // 2^364
    lemma_pow2_adds(156, 260);  // 2^416

    // L limb values (note: l3 == 0 for this group order)
    let l0_val = constants::L.limbs[0] as nat;
    let l1 = constants::L.limbs[1] as nat;
    let l2 = constants::L.limbs[2] as nat;
    let l3 = constants::L.limbs[3] as nat;  // = 0
    let l4 = constants::L.limbs[4] as nat;

    // Key quantities
    let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
        + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);

    let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
    let l_low = l0_val + l1 * pow2(52) + l2 * pow2(104) + l3 * pow2(156) + l4 * pow2(208);

    // N×L coefficients at positions 0-4 (from polynomial convolution)
    let coeff0 = (n0 as nat) * l0_val;
    let coeff1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
    let coeff2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
    let coeff3 = (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;
    let coeff4 = (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat) * l0_val;
    let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156)
        + coeff4 * pow2(208);

    // High-order coefficients (positions 5-8)
    let coeff5 = (n1 as nat) * l4 + (n3 as nat) * l2 + (n4 as nat) * l1;
    let coeff6 = (n2 as nat) * l4 + (n4 as nat) * l2;
    let coeff7 = (n3 as nat) * l4;
    let coeff8 = (n4 as nat) * l4;
    let high_part = coeff5 * pow2(260) + coeff6 * pow2(312) + coeff7 * pow2(364) + coeff8 * pow2(
        416,
    );

    // s_k values: LHS of each stage equation before adding n_k × l0
    let s0 = limbs[0] as nat;
    let s1 = carry0 as nat + limbs[1] as nat + (n0 as nat) * l1;
    let s2 = carry1 as nat + limbs[2] as nat + (n0 as nat) * l2 + (n1 as nat) * l1;
    let s3 = carry2 as nat + limbs[3] as nat + (n1 as nat) * l2 + (n2 as nat) * l1;
    let s4 = carry3 as nat + limbs[4] as nat + (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat)
        * l1;

    // =======================================================================
    // Subgoal A: Telescoping sum equals c4 × 2^260 (carries cancel)
    // =======================================================================
    //
    // Via lemma_part1_telescoping_expansion:
    //   Σ (s_k - c_{k-1} + n_k × l0) × 2^{52k} == c4 × 2^260

    lemma_part1_telescoping_expansion(
        s0,
        s1,
        s2,
        s3,
        s4,
        n0 as nat,
        n1 as nat,
        n2 as nat,
        n3 as nat,
        n4 as nat,
        carry0 as nat,
        carry1 as nat,
        carry2 as nat,
        carry3 as nat,
        carry4 as nat,
        l0_val,
    );

    // =======================================================================
    // Subgoal B: t_low + nl_low_coeffs == c4 × 2^260 (quotient relationship)
    // =======================================================================
    //
    // The telescoping sum equals t_low + nl_low_coeffs when we:
    // 1. Substitute s_k - c_{k-1} = limbs[k] + cross terms
    // 2. Use distributivity to separate limbs[k] from N×L coefficients

    let val = t_low + nl_low_coeffs;

    assert(val == (carry4 as nat) * pow2(260)) by {
        // Define weighted terms matching telescoping structure
        let term0 = s0 + (n0 as nat) * l0_val;
        let term1 = (s1 - (carry0 as nat) + (n1 as nat) * l0_val) * pow2(52);
        let term2 = (s2 - (carry1 as nat) + (n2 as nat) * l0_val) * pow2(104);
        let term3 = (s3 - (carry2 as nat) + (n3 as nat) * l0_val) * pow2(156);
        let term4 = (s4 - (carry3 as nat) + (n4 as nat) * l0_val) * pow2(208);

        // s_k - c_{k-1} simplifies to limbs[k] + cross terms
        assert(s1 - (carry0 as nat) == limbs[1] as nat + (n0 as nat) * l1);
        assert(s2 - (carry1 as nat) == limbs[2] as nat + (n0 as nat) * l2 + (n1 as nat) * l1);
        assert(s3 - (carry2 as nat) == limbs[3] as nat + (n1 as nat) * l2 + (n2 as nat) * l1);
        assert(s4 - (carry3 as nat) == limbs[4] as nat + (n0 as nat) * l4 + (n2 as nat) * l2 + (
        n3 as nat) * l1);

        // Separate limbs from N×L coefficients using distributivity
        assert(term1 == (limbs[1] as nat) * pow2(52) + coeff1 * pow2(52)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(52) as int,
                (limbs[1] as nat) as int,
                ((n0 as nat) * l1 + (n1 as nat) * l0_val) as int,
            );
        };
        assert(term2 == (limbs[2] as nat) * pow2(104) + coeff2 * pow2(104)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(104) as int,
                (limbs[2] as nat) as int,
                ((n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val) as int,
            );
        };
        assert(term3 == (limbs[3] as nat) * pow2(156) + coeff3 * pow2(156)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(156) as int,
                (limbs[3] as nat) as int,
                ((n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val) as int,
            );
        };
        assert(term4 == (limbs[4] as nat) * pow2(208) + coeff4 * pow2(208)) by {
            lemma_mul_is_distributive_add_other_way(
                pow2(208) as int,
                (limbs[4] as nat) as int,
                ((n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat)
                    * l0_val) as int,
            );
        };

        // Sum of terms equals t_low + nl_low_coeffs
        assert(term0 + term1 + term2 + term3 + term4 == t_low + nl_low_coeffs);
    };

    // =======================================================================
    // Subgoal C: (N × L_low) % 2^260 == nl_low_coeffs % 2^260 (polynomial)
    // =======================================================================
    //
    // Via lemma_n_times_l_expansion:
    //   N × L_low == nl_low_coeffs + high_part
    //   high_part % 2^260 == 0
    // Therefore: (N × L_low) % 2^260 == nl_low_coeffs % 2^260

    lemma_n_times_l_expansion(
        n0 as nat,
        n1 as nat,
        n2 as nat,
        n3 as nat,
        n4 as nat,
        l0_val,
        l1,
        l2,
        l3,
        l4,
    );

    assert((n * l_low) % pow2(260) == nl_low_coeffs % pow2(260));
    assert(n * l_low == nl_low_coeffs + high_part);
    assert(high_part % pow2(260) == 0);

    // =======================================================================
    // Subgoal D: Final divisibility from B and C
    // =======================================================================
    //
    // From B: val = t_low + nl_low_coeffs = c4 × 2^260
    //   ⟹ val % 2^260 == 0
    //
    // From C: N × L_low == nl_low_coeffs + high_part, high_part % 2^260 == 0
    //
    // Combine:
    //   t_low + N × L_low = t_low + nl_low_coeffs + high_part
    //                     = val + high_part
    //
    // Both val and high_part are divisible by 2^260, so their sum is too.

    assert(val % pow2(260) == 0) by {
        lemma_pow2_pos(260);
        lemma_mod_self_0(pow2(260) as int);
        lemma_mul_mod_noop_right((carry4 as nat) as int, pow2(260) as int, pow2(260) as int);
        lemma_mul_basics((carry4 as nat) as int);
        lemma_small_mod(0nat, pow2(260));
    };

    assert((t_low + n * l_low) % pow2(260) == 0) by {
        lemma_pow2_pos(260);
        assert(t_low + n * l_low == val + high_part);
        lemma_add_mod_noop(val as int, high_part as int, pow2(260) as int);
        lemma_small_mod(0nat, pow2(260));
    };
}

} // verus!
