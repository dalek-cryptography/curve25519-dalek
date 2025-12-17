//! Lemmas for Edwards point decompression
//!
//! This module contains proofs for the `decompress` operation on Ed25519 points.
//!
//! ## decompress Function
//!
//! ```text
//! fn decompress(&self: CompressedEdwardsY) -> Option<EdwardsPoint>
//! ```
//!
//! Decompresses a 32-byte compressed Edwards point into a full Edwards point.
//! - Calls step_1 to decode Y and compute candidate X
//! - Applies step_2 to adjust X sign based on the compressed sign bit
//! - Returns `Some(EdwardsPoint)` if Y is valid, else `None`
//! For step_1 lemmas (curve equation, validity), see `step1_lemmas.rs`.
//! For general curve equation lemmas (negation, extended coords), see `curve_equation_lemmas.rs`.
//!
//! ## Key Properties Proven
//!
//! 1. **Sign bit correctness**: After conditional_negate, the sign bit matches
//! 2. **Sign bit implications**: sign_bit=1 implies x≠0
//! 3. **Main decompress lemma**: Combines all properties for valid branch
#![allow(unused_imports)]
use crate::backend::serial::u64::constants;
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::edwards::EdwardsPoint;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
use crate::lemmas::edwards_lemmas::step1_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_ratio_lemmas::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// Sign Bit Lemmas
// =============================================================================
/// Lemma: After conditional_negate based on sign_bit, the result has the correct sign
///
/// ## Mathematical Proof
/// ```text
/// sqrt_ratio_i returns the non-negative root (LSB = 0)
/// conditional_negate flips the sign when sign_bit = 1
///
/// Case sign_bit = 0: result = x % p (even), LSB = 0 ✓
/// Case sign_bit = 1: result = -x = p - x
///                    Since p is odd and x is even: odd - even = odd
///                    So LSB = 1 ✓
/// ```
pub proof fn lemma_sign_bit_after_conditional_negate(x: nat, sign_bit: u8)
    requires
        (x % p()) % 2 == 0,  // x is non-negative root (LSB = 0)
        sign_bit == 0 || sign_bit == 1,
        sign_bit == 1 ==> x % p() != 0,  // if asking for odd, x ≠ 0

    ensures
        ({
            let result = if sign_bit == 1 {
                math_field_neg(x)
            } else {
                x % p()
            };
            (result % 2) as u8 == sign_bit
        }),
{
    let pval = p();
    let x_red = x % pval;
    let result = if sign_bit == 1 {
        math_field_neg(x)
    } else {
        x % pval
    };

    // Goal: LSB(result) = sign_bit
    assert((result % 2) as u8 == sign_bit) by {
        lemma_p_is_odd();  // p is odd

        if sign_bit == 0 {
            // Case: sign_bit = 0 → result = x % p (even)
            assert(result == x_red);
            assert(result % 2 == 0);
        } else {
            // Case: sign_bit = 1 → result = -x = p - x_red
            let neg_x = (pval - x_red) as nat;

            assert(result % 2 == 1) by {
                p_gt_2();

                assert(result == neg_x) by {
                    lemma_small_mod(neg_x, pval);
                };

                // (p - x_red) % 2 = (odd - even) % 2 = 1
                assert(neg_x % 2 == 1) by {
                    lemma_sub_mod_noop(pval as int, x_red as int, 2int);
                };
            };
        }
    };
}

// =============================================================================
// Sign Bit Correctness for Decompress
// =============================================================================
/// Top-level lemma for decompress sign bit using concrete field element
///
/// Connects to spec_field_element_sign_bit: ((x % p) % 2) as u8
pub proof fn lemma_decompress_field_element_sign_bit(
    x_before_negate: nat,
    x_after_negate: nat,
    sign_bit: u8,
)
    requires
        sign_bit == 0 || sign_bit == 1,
        (x_before_negate % p()) % 2 == 0,  // sqrt_ratio_i returns even
        sign_bit == 1 ==> x_before_negate % p() != 0,  // x ≠ 0 when negating
        x_after_negate == if sign_bit == 1 {
            math_field_neg(x_before_negate)
        } else {
            x_before_negate % p()
        },
    ensures
        ((x_after_negate % p()) % 2) as u8 == sign_bit,
{
    // (x_after % 2) as u8 == sign_bit
    assert((x_after_negate % 2) as u8 == sign_bit) by {
        lemma_sign_bit_after_conditional_negate(x_before_negate, sign_bit);
    }

    // x_after < p, so x_after % p = x_after
    assert(x_after_negate % p() == x_after_negate) by {
        assert(x_after_negate < p()) by {
            p_gt_2();
            if sign_bit == 1 {
                lemma_mod_bound((p() as int - (x_before_negate % p()) as int), p() as int);
            } else {
                lemma_mod_bound(x_before_negate as int, p() as int);
            }
        }
        lemma_small_mod(x_after_negate, p());
    }
}

// =============================================================================
// Sign Bit and Curve Interaction
// =============================================================================
/// Lemma: From compressed_y_has_valid_sign_bit, derive that sign_bit=1 implies x≠0
///
/// ## Mathematical Proof
///
/// The twisted Edwards curve equation is: -x² + y² = 1 + d·x²·y²
/// Rearranging: y² - 1 = x²(1 + d·y²)
///
/// If x = 0, then y² - 1 = 0, so y² = 1.
/// Contrapositive: If y² ≠ 1, then x ≠ 0.
///
/// From precondition: sign_bit = 1 ==> y² ≠ 1
/// From curve: y² ≠ 1 ==> x ≠ 0
/// Combined: sign_bit = 1 ==> x ≠ 0
pub proof fn lemma_sign_bit_one_implies_x_nonzero(bytes: &[u8; 32], x: nat, y: nat)
    requires
        compressed_y_has_valid_sign_bit(bytes),  // decompress precondition
        y == spec_field_element_from_bytes(bytes),  // Y from bytes
        math_on_edwards_curve(x, y),  // (x, y) on curve
        x < p(),  // X bounded

    ensures
// If sign bit is 1, x must be non-zero (since -0 = 0)

        (bytes[31] >> 7) == 1 ==> x % p() != 0,
{
    let sign_bit = bytes[31] >> 7;
    let y_sq = math_field_square(y);

    if sign_bit == 1 {
        // From compressed_y_has_valid_sign_bit: y² == 1 ==> sign_bit == 0
        // Contrapositive: sign_bit == 1 ==> y² != 1
        assert(y_sq != 1);

        // From curve equation and y² != 1, x must be non-zero (contrapositive)
        assert(x % p() != 0) by {
            // If x % p == 0, then by lemma_x_zero_implies_y_squared_one, y² == 1
            // But we have y² != 1, contradiction
            if x % p() == 0 {
                lemma_x_zero_implies_y_squared_one(x, y);
            }
        };
    }
}

// =============================================================================
// Main Decompress Lemma
// =============================================================================
/// Main lemma for decompress valid branch: proves all postconditions for Some(point).
/// It takes the mathematical values and the final point, proving the ensures clauses.
///
/// ## Parameters
/// - `repr_bytes`: The compressed representation bytes
/// - `x_orig`: The X value from step_1 (before conditional negate)
/// - `point`: The final EdwardsPoint from step_2
///
/// ## Proves
/// - is_valid_edwards_point(point)
/// - spec_field_element(&point.Y) == spec_field_element_from_bytes(repr_bytes)
/// - spec_field_element_sign_bit(&point.X) == (repr_bytes[31] >> 7)
pub proof fn lemma_decompress_valid_branch(repr_bytes: &[u8; 32], x_orig: nat, point: &EdwardsPoint)
    requires
        compressed_y_has_valid_sign_bit(repr_bytes),
        // step_1 postconditions
        spec_field_element(&point.Y) == spec_field_element_from_bytes(repr_bytes),
        math_on_edwards_curve(x_orig, spec_field_element(&point.Y)),
        // X is non-negative root (LSB = 0) and bounded
        (x_orig % p()) % 2 == 0,
        x_orig < p(),
        // step_2 postconditions
        spec_field_element(&point.X) == (if (repr_bytes[31] >> 7) == 1 {
            math_field_neg(x_orig)
        } else {
            x_orig
        }),
        spec_field_element(&point.Z) == 1,
        spec_field_element(&point.T) == math_field_mul(
            spec_field_element(&point.X),
            spec_field_element(&point.Y),
        ),
    ensures
        is_valid_edwards_point(*point),
        spec_field_element(&point.Y) == spec_field_element_from_bytes(repr_bytes),
        spec_field_element_sign_bit(&point.X) == (repr_bytes[31] >> 7),
{
    let x_final = spec_field_element(&point.X);
    let y_final = spec_field_element(&point.Y);
    let z_final = spec_field_element(&point.Z);
    let t_final = spec_field_element(&point.T);
    let sign_bit = repr_bytes[31] >> 7;

    // =========================================================================
    // Goal 1: is_valid_edwards_point(point)
    // =========================================================================
    assert(is_valid_edwards_point(*point)) by {
        // Establish that (x_final, y_final) is on curve
        assert(math_on_edwards_curve(x_final, y_final)) by {
            // X is conditionally negated; negation preserves curve membership
            if sign_bit == 1 {
                assert(x_final == math_field_neg(x_orig));
                lemma_negation_preserves_curve(x_orig, y_final);
            } else {
                assert(x_final == x_orig);
            }
        };

        // Z = 1, T = X * Y
        assert(z_final == 1);
        assert(t_final == math_field_mul(x_final, y_final));

        // Apply the validity lemma (from curve_equation_lemmas)
        lemma_affine_to_extended_valid(x_final, y_final, t_final);
    };

    // =========================================================================
    // Goal 2: Y coordinate preserved (directly from requires)
    // =========================================================================

    // =========================================================================
    // Goal 3: Sign bit correctness
    // =========================================================================
    assert(spec_field_element_sign_bit(&point.X) == (repr_bytes[31] >> 7)) by {
        let x_before = x_orig;
        let x_after = x_final;
        let repr_byte_31 = repr_bytes[31];

        // ((x_after % p) % 2) as u8 == sign_bit
        assert(((x_after % p()) % 2) as u8 == (repr_byte_31 >> 7)) by {
            let sign_bit = repr_byte_31 >> 7;

            // sign_bit ∈ {0, 1}
            assert(sign_bit == 0 || sign_bit == 1) by (bit_vector)
                requires
                    sign_bit == repr_byte_31 >> 7,
            ;

            // Precondition 1: sqrt_ratio_i returns non-negative root (LSB = 0)
            assert((x_before % p()) % 2 == 0);

            // Precondition 2: sign_bit == 1 ==> x != 0
            assert(sign_bit == 1 ==> x_before % p() != 0) by {
                lemma_sign_bit_one_implies_x_nonzero(repr_bytes, x_before, y_final);
            };

            // Precondition 3: x_after matches conditional expression
            assert(x_after == if sign_bit == 1 {
                math_field_neg(x_before)
            } else {
                x_before % p()
            }) by {
                lemma_small_mod(x_before, p());
            };

            lemma_decompress_field_element_sign_bit(x_before, x_after, sign_bit);
        };
    };
}

} // verus!
