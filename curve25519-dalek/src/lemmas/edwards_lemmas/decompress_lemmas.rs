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
#[cfg(verus_keep_ghost)]
use crate::specs::montgomery_specs::edwards_y_from_montgomery_u;
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
        x % 2 == 0,  // x is non-negative root (LSB = 0)
        x < p(),
        sign_bit == 0 || sign_bit == 1,
        sign_bit == 1 ==> x != 0,  // if asking for odd, x ≠ 0

    ensures
        ({
            let result = if sign_bit == 1 {
                field_neg(x)
            } else {
                x
            };
            (result % 2) as u8 == sign_bit
        }),
{
    let pval = p();
    let result = if sign_bit == 1 {
        field_neg(x)
    } else {
        x
    };

    // Goal: LSB(result) = sign_bit
    assert((result % 2) as u8 == sign_bit) by {
        lemma_p_is_odd();  // p is odd

        if sign_bit == 0 {
            // Case: sign_bit = 0 → result = x (even)
            assert(result % 2 == 0);
        } else {
            // Case: sign_bit = 1 → result = -x = p - x
            let neg_x = field_neg(x);

            assert(result % 2 == 1) by {
                p_gt_2();

                assert(neg_x == (pval - x) as nat) by {
                    assert(x == field_canonical(x)) by {
                        lemma_small_mod(x, pval);
                    }
                    // since SB == 1, x can't be zero
                    assert(0 <= pval - x < pval) by {
                        assert(x != 0);
                    }
                    assert((pval - x) as nat % pval == pval - x) by {
                        lemma_small_mod((pval - x) as nat, pval);
                    }
                };

                // (p - x) % 2 = (odd - even) % 2 = 1
                assert(neg_x % 2 == 1) by {
                    assert((pval - x) % 2 == ((pval % 2) - x % 2) % 2) by {
                        lemma_sub_mod_noop(pval as int, x as int, 2int);
                    }
                    assert(pval % 2 == 1);
                    assert(x % 2 == 0);
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
/// Connects to fe51_as_canonical_nat_sign_bit: ((x % p) % 2) as u8
pub proof fn lemma_decompress_field_element_sign_bit(
    x_before_negate: nat,
    x_after_negate: nat,
    sign_bit: u8,
)
    requires
        sign_bit == 0 || sign_bit == 1,
        x_before_negate % 2 == 0,  // sqrt_ratio_i returns even
        x_before_negate < p(),
        sign_bit == 1 ==> x_before_negate != 0,  // x ≠ 0 when negating
        x_after_negate == if sign_bit == 1 {
            field_neg(x_before_negate)
        } else {
            x_before_negate
        },
    ensures
        (x_after_negate % 2) as u8 == sign_bit,
{
    // (x_after % 2) as u8 == sign_bit
    assert((x_after_negate % 2) as u8 == sign_bit) by {
        lemma_sign_bit_after_conditional_negate(x_before_negate, sign_bit);
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
/// - fe51_as_canonical_nat(&point.Y) == field_element_from_bytes(repr_bytes)
/// - fe51_as_canonical_nat_sign_bit(&point.X) == (repr_bytes[31] >> 7)
pub proof fn lemma_decompress_valid_branch(repr_bytes: &[u8; 32], x_orig: nat, point: &EdwardsPoint)
    requires
// step_1 postconditions

        fe51_as_canonical_nat(&point.Y) == field_element_from_bytes(repr_bytes),
        math_on_edwards_curve(x_orig, fe51_as_canonical_nat(&point.Y)),
        // X is non-negative root (LSB = 0)
        x_orig % 2 == 0,
        // x_orig < p() is trivially true since x_orig = fe51_as_canonical_nat(&X)
        // which is defined as fe51_as_nat % p(). Required by internal lemma calls.
        x_orig < p(),
        // step_2 postconditions
        fe51_as_canonical_nat(&point.X) == (if (repr_bytes[31] >> 7) == 1 {
            field_neg(x_orig)
        } else {
            x_orig
        }),
        fe51_as_canonical_nat(&point.Z) == 1,
        fe51_as_canonical_nat(&point.T) == field_mul(
            fe51_as_canonical_nat(&point.X),
            fe51_as_canonical_nat(&point.Y),
        ),
    ensures
        is_valid_edwards_point(*point),
        fe51_as_canonical_nat(&point.Y) == field_element_from_bytes(repr_bytes),
        // Sign bit correctness when y² ≠ 1 (i.e., x ≠ 0).
        // When y² == 1, x = 0 and negation is the identity, so the sign bit
        // in the result is always 0 regardless of the compressed sign bit.
        field_square(field_element_from_bytes(repr_bytes)) != 1 ==> fe51_as_canonical_nat_sign_bit(
            &point.X,
        ) == (repr_bytes[31] >> 7),
{
    let x_final = fe51_as_canonical_nat(&point.X);
    let y_final = fe51_as_canonical_nat(&point.Y);
    let z_final = fe51_as_canonical_nat(&point.Z);
    let t_final = fe51_as_canonical_nat(&point.T);
    let sign_bit = repr_bytes[31] >> 7;

    // =========================================================================
    // Goal 1: is_valid_edwards_point(point)
    // =========================================================================
    assert(is_valid_edwards_point(*point)) by {
        // Establish that (x_final, y_final) is on curve
        assert(math_on_edwards_curve(x_final, y_final)) by {
            // X is conditionally negated; negation preserves curve membership
            if sign_bit == 1 {
                assert(x_final == field_neg(x_orig));
                lemma_negation_preserves_curve(x_orig, y_final);
            } else {
                assert(x_final == x_orig);
            }
        };

        // Z = 1, T = X * Y
        assert(z_final == 1);
        assert(t_final == field_mul(x_final, y_final));

        // Apply the validity lemma (from curve_equation_lemmas)
        lemma_affine_to_extended_valid(x_final, y_final, t_final);
    };

    // =========================================================================
    // Goal 2: Y coordinate preserved (directly from requires)
    // =========================================================================

    // =========================================================================
    // Goal 3: Sign bit correctness (conditional on y² ≠ 1)
    // =========================================================================
    let y_sq = field_square(y_final);
    if y_sq != 1 {
        assert(fe51_as_canonical_nat_sign_bit(&point.X) == (repr_bytes[31] >> 7)) by {
            let x_before = x_orig;
            let x_after = x_final;
            let repr_byte_31 = repr_bytes[31];

            assert((x_after % 2) as u8 == (repr_byte_31 >> 7)) by {
                let sign_bit = repr_byte_31 >> 7;

                assert(sign_bit == 0 || sign_bit == 1) by (bit_vector)
                    requires
                        sign_bit == repr_byte_31 >> 7,
                ;

                // When y² ≠ 1, x ≠ 0 (contrapositive of x=0 ⟹ y²=1)
                assert(sign_bit == 1 ==> x_before != 0) by {
                    if sign_bit == 1 && x_before == 0 {
                        lemma_x_zero_implies_y_squared_one(x_before, y_final);
                    }
                };

                assert(x_after == if sign_bit == 1 {
                    field_neg(x_before)
                } else {
                    x_before
                }) by {
                    lemma_small_mod(x_before, p());
                };

                lemma_decompress_field_element_sign_bit(x_before, x_after, sign_bit);
            };
        };
    }
}

// =============================================================================
// Decompression spec match and Montgomery→Edwards correctness
// =============================================================================
/// Lemma: Decompression from y and sign recovers the original point.
pub proof fn lemma_decompress_spec_matches_point(x: nat, y: nat, sign_bit: u8)
    requires
        math_on_edwards_curve(x, y),
        x < p(),
        y < p(),
        (x % 2) == (sign_bit as nat),
        sign_bit == 0 || sign_bit == 1,
    ensures
        spec_edwards_decompress_from_y_and_sign(y, sign_bit) == Some((x, y)),
{
    assert(math_is_valid_y_coordinate(y)) by {
        let d = fe51_as_canonical_nat(&EDWARDS_D);
        lemma_field_curve_point_implies_valid_y(d, x, y);
        reveal(math_is_valid_y_coordinate);
        let u = field_sub(field_square(y), 1);
        let v = field_add(field_mul(d, field_square(y)), 1);
        lemma_small_mod(u, p());
        lemma_small_mod(v, p());
        if u == 0 {
        } else {
            assert(v != 0);
            assert(field_mul(field_square(x), v) == u);
            assert(x < p());
        }
    };

    if field_square(y) == 1 {
        assert(x == 0) by {
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            axiom_d_plus_one_nonzero();
            lemma_field_y_sq_one_implies_x_zero(d, x, y);
        };
    }
    let x_chosen = choose|xc: nat|
        math_on_edwards_curve(xc, y) && xc < p() && (xc % 2) == (sign_bit as nat);
    assert(math_on_edwards_curve(x, y) && x < p() && (x % 2) == (sign_bit as nat));
    assert(x == x_chosen) by {
        lemma_unique_x_with_parity(x, x_chosen, y);
    };
}

/// Helper lemma: exact functional correctness for Montgomery→Edwards conversion.
pub proof fn lemma_to_edwards_correctness(x_exec: nat, y_nat: nat, sign_bit: u8, u_nat: nat)
    requires
        math_on_edwards_curve(x_exec, y_nat),
        x_exec < p(),
        y_nat < p(),
        sign_bit == 0 || sign_bit == 1,
        field_square(y_nat) != 1 ==> ((x_exec % 2) as u8 == sign_bit),
        y_nat == edwards_y_from_montgomery_u(u_nat),
        u_nat < p(),
        u_nat != field_sub(0, 1),
    ensures
        (x_exec, y_nat) == spec_montgomery_to_edwards_affine(u_nat, sign_bit),
{
    if field_square(y_nat) == 1 {
        assert(x_exec == 0) by {
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            axiom_d_plus_one_nonzero();
            lemma_field_y_sq_one_implies_x_zero(d, x_exec, y_nat);
        };
        assert(spec_edwards_decompress_from_y_and_sign(y_nat, 0u8) == Some((0nat, y_nat))) by {
            lemma_decompress_spec_matches_point(0nat, y_nat, 0u8);
        };
    } else {
        assert(spec_edwards_decompress_from_y_and_sign(y_nat, sign_bit) == Some((x_exec, y_nat)))
            by {
            lemma_decompress_spec_matches_point(x_exec, y_nat, sign_bit);
        };
    }
}

} // verus!
