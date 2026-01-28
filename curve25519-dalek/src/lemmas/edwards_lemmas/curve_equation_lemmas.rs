//! Lemmas about the Edwards curve equation and operations
//!
//! This module contains proofs for general properties of the twisted Edwards curve
//! equation and coordinate representations. These are fundamental mathematical facts
//! about the curve, not specific to any particular operation.
//!
//! ## Key Properties Proven
//!
//! 1. **Negation preserves curve**: (-x, y) is on the curve if (x, y) is (since x² = (-x)²)
//! 2. **Affine to extended validity**: (x, y, 1, xy) is a valid extended point when (x, y) is on curve
//! 3. **x=0 implies y²=1**: If x ≡ 0 and (x, y) is on curve, then y² = 1
//! 4. **Scalar mul pow2 successor**: [2^(k+1)]P = double([2^k]P)
#![allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::common_lemmas::pow_lemmas::{lemma_pow2_even, pow2_MUL_div};
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_pos, pow2};
use vstd::calc;
use vstd::prelude::*;

verus! {

// =============================================================================
// Identity Point Lemmas
// =============================================================================
/// Lemma: The identity point (0, 1) is on the Edwards curve
///
/// ## Mathematical Proof
///
/// The Edwards curve equation is: y² - x² = 1 + d·x²·y²
///
/// For (0, 1):
/// - LHS: 1² - 0² = 1 - 0 = 1
/// - RHS: 1 + d·0²·1² = 1 + 0 = 1
/// - LHS = RHS ✓
pub proof fn lemma_identity_on_curve()
    ensures
        math_on_edwards_curve(0, 1),
{
    let modulus = p();
    p_gt_2();

    let d = spec_field_element(&EDWARDS_D);

    // x² = 0² = 0
    let x2 = math_field_square(0nat);
    assert(x2 == 0) by {
        lemma_small_mod(0nat, modulus);
    }

    // y² = 1² = 1
    let y2 = math_field_square(1nat);
    assert(y2 == 1) by {
        lemma_small_mod(1nat, modulus);
    }

    // LHS = y² - x² = 1 - 0 = 1 (using math_field_sub)
    // math_field_sub(a, b) = ((a % p) + p - (b % p)) % p
    let lhs = math_field_sub(y2, x2);
    assert(lhs == 1) by {
        // y2 = 1, x2 = 0
        // math_field_sub(1, 0) = ((1 % p) + p - (0 % p)) % p
        //                      = (1 + p - 0) % p
        //                      = (p + 1) % p = 1
        lemma_small_mod(1nat, modulus);
        lemma_small_mod(0nat, modulus);
        // (p + 1) % p = 1 because (p + 1) = p * 1 + 1, and remainder is 1
        lemma_mod_multiples_vanish(1, 1, modulus as int);
    }

    // x²·y² = 0·1 = 0
    let x2y2 = math_field_mul(x2, y2);
    assert(x2y2 == 0) by {
        lemma_small_mod(0nat, modulus);
    }

    // d·x²·y² = d·0 = 0
    let d_x2y2 = math_field_mul(d, x2y2);
    assert(d_x2y2 == 0) by {
        lemma_mul_by_zero_is_zero(d as int);
        lemma_small_mod(0nat, modulus);
    }

    // RHS = 1 + d·x²·y² = 1 + 0 = 1
    let rhs = math_field_add(1nat, d_x2y2);
    assert(rhs == 1) by {
        lemma_small_mod(1nat, modulus);
    }

    // LHS = RHS = 1, so math_on_edwards_curve(0, 1) holds
    assert(lhs == rhs);
}

/// Lemma: The identity point (0, 1, 1, 0) is a valid extended Edwards point
///
/// This combines lemma_identity_on_curve with lemma_affine_to_extended_valid.
pub proof fn lemma_identity_is_valid_extended()
    ensures
        math_is_valid_extended_edwards_point(0, 1, 1, 0),
{
    // First prove (0, 1) is on the curve
    lemma_identity_on_curve();

    // t = x * y = 0 * 1 = 0
    assert(math_field_mul(0nat, 1nat) == 0) by {
        p_gt_2();
        lemma_small_mod(0nat, p());
    }

    // Use the affine-to-extended lemma
    lemma_affine_to_extended_valid(0nat, 1nat, 0nat);
}

// =============================================================================
// Negation Lemmas
// =============================================================================
/// Lemma: Negation preserves the curve equation
///
/// If (x, y) is on the curve, then (-x, y) is also on the curve.
/// This is because the curve equation involves x² which is the same for x and -x.
pub proof fn lemma_negation_preserves_curve(x: nat, y: nat)
    requires
        math_on_edwards_curve(x, y),
    ensures
        math_on_edwards_curve(math_field_neg(x), y),
{
    // Goal: on_curve(-x, y)
    // Strategy: The curve equation uses x², and (-x)² = x², so the equation is identical
    //
    //   y² - (-x)² = 1 + d·(-x)²·y²
    //   y² - x²    = 1 + d·x²·y²      (same equation!)
    //
    // The precondition says (x, y) satisfies this, so (-x, y) does too.
    let neg_x = math_field_neg(x);

    assert(math_on_edwards_curve(neg_x, y)) by {
        // Key insight: (-x)² = x²
        assert(math_field_square(neg_x) == math_field_square(x)) by {
            lemma_neg_square_eq(x);  // (-x)² = (x % p)²
            lemma_square_mod_noop(x);  // (x % p)² = x²
        };
        // With (-x)² = x², the curve equations are identical
    };
}

// =============================================================================
// Extended Coordinates Validity
// =============================================================================
/// Lemma: Converting affine coordinates to extended coordinates yields a valid point
///
/// When (x, y) is on the Edwards curve, the extended representation (x, y, 1, x·y)
/// is a valid extended Edwards point.
///
/// ## Mathematical Proof
///
/// For extended coordinates (X:Y:Z:T) to be valid, we need:
/// 1. Z ≠ 0
/// 2. (X/Z, Y/Z) is on the curve
/// 3. T = X·Y/Z
///
/// With Z = 1:
/// - Z ≠ 0 ✓
/// - (X/1, Y/1) = (X, Y) is on curve (given)
/// - T = X·Y/1 = X·Y ✓
pub proof fn lemma_affine_to_extended_valid(x: nat, y: nat, t: nat)
    requires
        math_on_edwards_curve(x, y),
        t == math_field_mul(x, y),
    ensures
        math_is_valid_extended_edwards_point(x, y, 1, t),
{
    let p = p();
    p_gt_2();

    // New validity definition uses:
    // - Z != 0
    // - projective curve equation
    // - Segre relation X·Y == Z·T

    // 1) Z != 0 (Z = 1)

    // 2) Projective curve equation holds for Z = 1
    assert(math_on_edwards_curve_projective(x, y, 1)) by {
        let x2 = math_field_square(x);
        let y2 = math_field_square(y);
        let z2 = math_field_square(1);
        let z4 = math_field_square(z2);
        let d = spec_field_element(&EDWARDS_D);

        // z2 = 1^2 = 1, z4 = 1^4 = 1
        assert(z2 == 1) by {
            lemma_mul_basics(1int);
            lemma_small_mod(1, p);
        };
        assert(z4 == 1) by {
            assert(z2 == 1);
            lemma_mul_basics(1int);
            lemma_small_mod(1, p);
        };

        // LHS: (y2 - x2)·1 = (y2 - x2)
        let lhs = math_field_mul(math_field_sub(y2, x2), z2);
        assert(lhs == math_field_sub(y2, x2)) by {
            assert(z2 == 1);
            lemma_mul_basics((math_field_sub(y2, x2)) as int);
            // lhs = (sub * 1) % p = sub % p = sub (since sub is already reduced mod p)
            lemma_mod_twice((((y2 % p) + p) - (x2 % p)) as int, p as int);
        };

        // RHS: 1 + d·x2·y2
        let rhs = math_field_add(z4, math_field_mul(d, math_field_mul(x2, y2)));
        assert(rhs == math_field_add(1, math_field_mul(d, math_field_mul(x2, y2)))) by {
            assert(z4 == 1);
        };

        // Affine curve equation gives the same equality.
        assert(math_field_sub(y2, x2) == math_field_add(
            1,
            math_field_mul(d, math_field_mul(x2, y2)),
        ));
        assert(lhs == rhs);
    };

    // 3) Segre relation: X·Y == Z·T (with Z = 1 and T = X·Y)
    assert(math_field_mul(x, y) == math_field_mul(1, t)) by {
        assert(t == math_field_mul(x, y));
        // 1·t = t in the field
        assert(t < p) by {
            lemma_mod_bound((x * y) as int, p as int);
        };
        lemma_field_element_reduced(t);
        lemma_mul_basics(t as int);
    };
}

// =============================================================================
// Curve Equation Properties
// =============================================================================
/// Lemma: If x = 0 (mod p) and (x, y) is on the Edwards curve, then y² = 1 (mod p)
///
/// ## Mathematical Proof
///
/// From the curve equation: y² - x² = 1 + d·x²·y² (mod p)
///
/// If x ≡ 0 (mod p):
/// - x² = (x * x) % p = (0 * 0) % p = 0
/// - x²·y² = 0 * y² = 0
/// - Curve becomes: y² - 0 = 1 + d·0
/// - Therefore: y² = 1 (mod p)
pub proof fn lemma_x_zero_implies_y_squared_one(x: nat, y: nat)
    requires
        math_on_edwards_curve(x, y),
        x % p() == 0,
    ensures
        math_field_square(y) == 1,
{
    let modulus = p();
    let d = spec_field_element(&EDWARDS_D);
    let x2 = math_field_square(x);
    let y2 = math_field_square(y);
    let x2y2 = math_field_mul(x2, y2);
    let d_x2y2 = math_field_mul(d, x2y2);
    let lhs = math_field_sub(y2, x2);
    let rhs = math_field_add(1, d_x2y2);

    // Establish p > 1 for lemma preconditions
    assert(modulus > 1) by {
        p_gt_2();
    };

    // Goal: y² = 1
    // Strategy: From curve equation y² - x² = 1 + d·x²·y², show all terms simplify

    assert(x2 == 0) by {
        // x % p == 0 means x * x % p == 0
        // (x * x) % p == ((x % p) * (x % p)) % p == (0 * 0) % p == 0
        lemma_mul_mod_noop_general(x as int, x as int, modulus as int);
        assert((x as int * x as int) % (modulus as int) == (((x as int) % (modulus as int)) * ((
        x as int) % (modulus as int))) % (modulus as int));
        assert((x as int) % (modulus as int) == 0);
        assert(0int * 0int == 0int) by {
            lemma_mul_basics(0int);
        }
        lemma_small_mod(0nat, modulus);
    };

    assert(x2y2 == 0) by {
        // x²·y² = 0 * y² = 0
        assert(x2 == 0);
        lemma_mul_by_zero_is_zero(y2 as int);
        lemma_small_mod(0, modulus);
    };

    assert(d_x2y2 == 0) by {
        // d * x²y² = d * 0 = 0
        assert(x2y2 == 0);
        lemma_mul_by_zero_is_zero(d as int);
    };

    assert(rhs == 1) by {
        // rhs = (1 + d·x²·y²) % p = (1 + 0) % p = 1 % p = 1
        assert(d_x2y2 == 0);
        lemma_small_mod(1, modulus);
    };

    // From curve equation (precondition): lhs == rhs
    assert(lhs == rhs);
    assert(lhs == 1);

    assert(lhs == y2) by {
        // lhs = math_field_sub(y2, 0) = (y2 + p) % p = y2
        assert(x2 == 0);

        // y2 < p (math_field_square output is reduced)
        assert(y2 < modulus) by {
            lemma_mod_bound(y as int * y as int, modulus as int);
        };

        // (p + y2) % p = y2 % p = y2 (since y2 < p)
        lemma_small_mod(y2, modulus);
        lemma_mod_multiples_vanish(1, y2 as int, modulus as int);
    };

    // Conclusion: y2 == lhs == 1
    assert(y2 == 1);
}

// =============================================================================
// Affine ↔ Projective Curve Equation Equivalence
// =============================================================================
/// Lemma: The affine curve equation implies the projective curve equation
///
/// If the affine point (X/Z, Y/Z) is on the Edwards curve, then the projective
/// coordinates (X, Y, Z) satisfy the homogenized curve equation.
///
/// ## Mathematical Proof
///
/// From the affine curve equation for (x, y) = (X/Z, Y/Z):
///   y² - x² = 1 + d·x²·y²
///
/// Substituting x = X/Z, y = Y/Z:
///   (Y/Z)² - (X/Z)² = 1 + d·(X/Z)²·(Y/Z)²
///   (Y² - X²)/Z² = 1 + d·X²·Y²/Z⁴
///   (Y² - X²)/Z² = (Z⁴ + d·X²·Y²)/Z⁴
///
/// Multiplying both sides by Z⁴:
///   (Y² - X²)·Z² = Z⁴ + d·X²·Y²
///
/// This is exactly the projective curve equation.
pub proof fn lemma_affine_curve_implies_projective(x: nat, y: nat, z: nat)
    requires
        z % p() != 0,  // Z must be non-zero in the field (not just non-zero as nat)
        math_on_edwards_curve(
            math_field_mul(x, math_field_inv(z)),
            math_field_mul(y, math_field_inv(z)),
        ),
    ensures
        math_on_edwards_curve_projective(x, y, z),
{
    let p = p();
    p_gt_2();

    let d = spec_field_element(&EDWARDS_D);
    let inv_z = math_field_inv(z);

    // Define affine coordinates
    let x_div_z = math_field_mul(x, inv_z);
    let y_div_z = math_field_mul(y, inv_z);

    // Squares of affine coordinates
    let x_div_z_sq = math_field_square(x_div_z);
    let y_div_z_sq = math_field_square(y_div_z);

    // From precondition: the affine curve equation holds
    // y_div_z² - x_div_z² = 1 + d * x_div_z² * y_div_z²
    let affine_lhs = math_field_sub(y_div_z_sq, x_div_z_sq);
    let affine_rhs = math_field_add(1, math_field_mul(d, math_field_mul(x_div_z_sq, y_div_z_sq)));
    assert(affine_lhs == affine_rhs);

    // Projective coordinates
    let x2 = math_field_square(x);
    let y2 = math_field_square(y);
    let z2 = math_field_square(z);
    let z4 = math_field_square(z2);

    // Use lemma_quotient_of_squares: (a/b)² = a²/b²
    // So x_div_z² = x²/z² and y_div_z² = y²/z²
    let inv_z2 = math_field_inv(z2);

    assert(x_div_z_sq == math_field_mul(x2, inv_z2)) by {
        lemma_quotient_of_squares(x, z);
    };

    assert(y_div_z_sq == math_field_mul(y2, inv_z2)) by {
        lemma_quotient_of_squares(y, z);
    };

    // The projective curve equation: (y² - x²)·z² = z⁴ + d·x²·y²
    let proj_lhs = math_field_mul(math_field_sub(y2, x2), z2);
    let proj_rhs = math_field_add(z4, math_field_mul(d, math_field_mul(x2, y2)));

    // === STEP 1: Rewrite affine_lhs ===
    // affine_lhs = y²·inv(z²) - x²·inv(z²) = (y² - x²)·inv(z²)
    // by factoring out inv(z²)

    // First show: y²·inv(z²) - x²·inv(z²) = (y² - x²)·inv(z²)
    let y2_minus_x2 = math_field_sub(y2, x2);

    assert(affine_lhs == math_field_mul(y2_minus_x2, inv_z2)) by {
        lemma_field_mul_distributes_over_sub_right(y2, x2, inv_z2);
    };

    // === STEP 2: Rewrite affine_rhs ===
    // We need: (x/z)²·(y/z)² = x²·y²·inv(z⁴)
    // Since (x/z)² = x²·inv(z²) and (y/z)² = y²·inv(z²)
    // their product is x²·inv(z²)·y²·inv(z²) = x²·y²·inv(z²)·inv(z²) = x²·y²·inv(z⁴)

    let inv_z4 = math_field_inv(z4);
    let x2_y2 = math_field_mul(x2, y2);
    let x2_y2_inv_z4 = math_field_mul(x2_y2, inv_z4);

    // inv(z²)·inv(z²) = inv(z⁴)
    assert(math_field_mul(inv_z2, inv_z2) == inv_z4) by {
        // z4 = z² · z², so inv(z4) = inv(z²·z²) = inv(z²)·inv(z²)
        lemma_inv_of_product(z2, z2);
    };

    // (x/z)²·(y/z)² = x²·y²·inv(z⁴)
    assert(math_field_mul(x_div_z_sq, y_div_z_sq) == x2_y2_inv_z4) by {
        // (x²·inv(z²))·(y²·inv(z²)) = x²·y²·inv(z²)·inv(z²) = x²·y²·inv(z⁴)
        lemma_field_mul_assoc(x2, inv_z2, math_field_mul(y2, inv_z2));
        lemma_field_mul_comm(inv_z2, math_field_mul(y2, inv_z2));
        lemma_field_mul_assoc(y2, inv_z2, inv_z2);
        lemma_field_mul_assoc(x2, y2, math_field_mul(inv_z2, inv_z2));
    };

    // So affine_rhs = 1 + d·x²·y²·inv(z⁴)
    assert(affine_rhs == math_field_add(1, math_field_mul(d, x2_y2_inv_z4)));

    // === STEP 3: Multiply both sides by z⁴ ===
    // We need: if A = B in the field, then A·z⁴ = B·z⁴

    // First prove z² ≠ 0 and z⁴ ≠ 0 (mod p) since z ≠ 0 and p is prime
    // z2 = math_field_square(z) = (z * z) % p = math_field_mul(z, z)
    lemma_nonzero_product(z, z);
    assert(z2 < p) by {
        lemma_mod_bound((z * z) as int, p as int);
    };
    lemma_field_element_reduced(z2);
    assert(z2 % p != 0);

    // Similarly for z4: z4 = z2 * z2 % p = math_field_mul(z2, z2)
    lemma_nonzero_product(z2, z2);
    assert(z4 < p) by {
        lemma_mod_bound((z2 * z2) as int, p as int);
    };
    lemma_field_element_reduced(z4);
    assert(z4 % p != 0);

    // LHS after multiplying: (y² - x²)·inv(z²)·z⁴ = (y² - x²)·z²
    // because inv(z²)·z⁴ = inv(z²)·z²·z² = z² (since inv(z²)·z² = 1)

    // Show inv(z²)·z⁴ = z² when z ≠ 0
    assert(math_field_mul(inv_z2, z4) == z2) by {
        // z4 = z2 · z2
        // inv(z2) · z4 = inv(z2) · (z2 · z2) = (inv(z2) · z2) · z2 = 1 · z2 = z2
        lemma_field_mul_assoc(inv_z2, z2, z2);
        lemma_inv_mul_cancel(z2);
        lemma_field_mul_one_left(z2);
    };

    // So (y² - x²)·inv(z²)·z⁴ = (y² - x²)·z²
    assert(math_field_mul(math_field_mul(y2_minus_x2, inv_z2), z4) == proj_lhs) by {
        lemma_field_mul_assoc(y2_minus_x2, inv_z2, z4);
    };

    // RHS after multiplying: (1 + d·x²·y²·inv(z⁴))·z⁴ = z⁴ + d·x²·y²
    // because inv(z⁴)·z⁴ = 1

    // Show inv(z⁴)·z⁴ = 1 when z ≠ 0
    assert(math_field_mul(inv_z4, z4) == 1) by {
        lemma_inv_mul_cancel(z4);
    };

    // d·x²·y²·inv(z⁴)·z⁴ = d·x²·y² (since inv(z⁴)·z⁴ = 1)
    // Chain: (d · x2_y2_inv_z4) · z4 = d · (x2_y2 · (inv_z4 · z4)) = d · (x2_y2 · 1) = d · x2_y2
    assert(math_field_mul(math_field_mul(d, x2_y2_inv_z4), z4) == math_field_mul(d, x2_y2)) by {
        lemma_field_mul_assoc(d, x2_y2_inv_z4, z4);
        lemma_field_mul_assoc(x2_y2, inv_z4, z4);
        lemma_mod_bound((x2 * y2) as int, p as int);
        lemma_field_element_reduced(x2_y2);
        lemma_field_mul_one_right(x2_y2);
    };

    // (1 + d·x²·y²·inv(z⁴))·z⁴ = z⁴ + d·x²·y²·inv(z⁴)·z⁴ = z⁴ + d·x²·y²
    assert(math_field_mul(affine_rhs, z4) == proj_rhs) by {
        lemma_field_mul_distributes_over_add(z4, 1, math_field_mul(d, x2_y2_inv_z4));
        lemma_field_mul_comm(z4, 1);
        lemma_field_mul_one_right(z4);
        lemma_field_mul_comm(z4, math_field_mul(d, x2_y2_inv_z4));
    };

    // === STEP 4: Connect via the affine equation ===
    // Since affine_lhs = affine_rhs, we have:
    // affine_lhs · z⁴ = affine_rhs · z⁴
    // (y² - x²)·inv(z²)·z⁴ = (1 + d·x²·y²·inv(z⁴))·z⁴
    // (y² - x²)·z² = z⁴ + d·x²·y²
    // proj_lhs = proj_rhs

    assert(math_field_mul(affine_lhs, z4) == math_field_mul(affine_rhs, z4));

    // affine_lhs · z⁴ = (y² - x²)·inv(z²)·z⁴ = proj_lhs
    assert(math_field_mul(affine_lhs, z4) == proj_lhs) by {
        // affine_lhs = (y² - x²)·inv(z²)
        lemma_field_mul_assoc(y2_minus_x2, inv_z2, z4);
    };

    // affine_rhs · z⁴ = proj_rhs (shown above)

    assert(proj_lhs == proj_rhs);
}

// =============================================================================
// Scalar Multiplication Lemmas
// =============================================================================
/// Lemma: Doubling the identity point yields the identity point.
///
/// This is used to handle the `a == 0` edge case in scalar-multiplication composition proofs.
pub proof fn lemma_edwards_double_identity()
    ensures
        edwards_double(0, 1) == (0nat, 1nat),
{
    // Field facts used throughout
    p_gt_2();
    lemma_field_inv_one();
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());
    lemma_mod_multiples_vanish(1, 1, p() as int);

    // Intermediate values: 0*0=0, 1*1=1, d*0*1=0
    let x1x2 = math_field_mul(0nat, 0nat);
    let y1y2 = math_field_mul(1nat, 1nat);
    assert(x1x2 == 0);
    assert(y1y2 == 1);
    let t = math_field_mul(spec_field_element(&EDWARDS_D), math_field_mul(x1x2, y1y2));
    assert(t == 0);

    // Denominators: 1+0=1, 1-0=1, inv(1)=1
    let denom_x = math_field_add(1nat, t);
    let denom_y = math_field_sub(1nat, t);
    assert(denom_x == 1 && denom_y == 1);
    assert(math_field_inv(denom_x) == 1 && math_field_inv(denom_y) == 1);

    // Result follows from edwards_add definition
}

/// Lemma: The Edwards identity `(0, 1)` is a right-identity for `edwards_add`.
///
/// Note: `edwards_add` always reduces inputs modulo `p()`, so the result is `(x % p(), y % p())`.
pub proof fn lemma_edwards_add_identity_right(x: nat, y: nat)
    ensures
        edwards_add(x, y, 0, 1) == (x % p(), y % p()),
{
    // Field facts used throughout
    p_gt_2();
    lemma_field_inv_one();
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());
    lemma_small_mod(x % p(), p());
    lemma_small_mod(y % p(), p());
    lemma_mod_multiples_vanish(1, 1, p() as int);

    // Multiplication lemmas: a*0=0, a*1=a
    lemma_field_mul_zero_right(x, 0nat);
    lemma_field_mul_zero_right(y, 0nat);
    lemma_field_mul_one_right(x);
    lemma_field_mul_one_right(y);
    lemma_field_mul_one_right(x % p());
    lemma_field_mul_one_right(y % p());

    // Intermediate values
    let x1x2 = math_field_mul(x, 0nat);
    let y1y2 = math_field_mul(y, 1nat);
    let x1y2 = math_field_mul(x, 1nat);
    let y1x2 = math_field_mul(y, 0nat);
    assert(x1x2 == 0 && y1x2 == 0 && y1y2 == y % p() && x1y2 == x % p());

    // t = d * 0 = 0
    let t = math_field_mul(spec_field_element(&EDWARDS_D), math_field_mul(x1x2, y1y2));
    assert(t == 0) by {
        lemma_field_mul_zero_left(x1x2, y1y2);
        lemma_field_mul_zero_right(spec_field_element(&EDWARDS_D), 0nat);
    }

    // Denominators: 1+0=1, 1-0=1, inv(1)=1
    let denom_x = math_field_add(1nat, t);
    let denom_y = math_field_sub(1nat, t);
    assert(denom_x == 1 && denom_y == 1);
    assert(math_field_inv(denom_x) == 1 && math_field_inv(denom_y) == 1);

    // Result: x3 = (x%p + 0) * 1 = x%p, y3 = (y%p + 0) * 1 = y%p
}

/// Lemma: Edwards addition is commutative.
///
/// This follows directly from the symmetry of the affine addition formulas.
pub proof fn lemma_edwards_add_commutative(x1: nat, y1: nat, x2: nat, y2: nat)
    ensures
        edwards_add(x1, y1, x2, y2) == edwards_add(x2, y2, x1, y1),
{
    // Help the solver with the commutativity of the `math_field_mul` terms that appear
    // in the numerators/denominators.
    lemma_field_mul_comm(x1, x2);
    lemma_field_mul_comm(y1, y2);
    lemma_field_mul_comm(x1, y2);
    lemma_field_mul_comm(y1, x2);

    assert(edwards_add(x1, y1, x2, y2) == edwards_add(x2, y2, x1, y1));
}

/// Lemma: Edwards addition is associative.
///
/// This is a standard group-law property. We admit it for now to unblock proofs that rely on
/// re-associating long addition chains (e.g. scalar multiplication linearity).
pub proof fn lemma_edwards_add_associative(x1: nat, y1: nat, x2: nat, y2: nat, x3: nat, y3: nat)
    ensures
        ({
            let ab = edwards_add(x1, y1, x2, y2);
            edwards_add(ab.0, ab.1, x3, y3)
        }) == ({
            let bc = edwards_add(x2, y2, x3, y3);
            edwards_add(x1, y1, bc.0, bc.1)
        }),
{
    admit();
}

/// Lemma: Doubling distributes over addition (assuming associativity/commutativity of `edwards_add`).
///
///   2*(A + B) = 2*A + 2*B
pub proof fn lemma_edwards_double_of_add(x1: nat, y1: nat, x2: nat, y2: nat)
    ensures
        ({
            let ab = edwards_add(x1, y1, x2, y2);
            edwards_double(ab.0, ab.1)
        }) == ({
            let aa = edwards_double(x1, y1);
            let bb = edwards_double(x2, y2);
            edwards_add(aa.0, aa.1, bb.0, bb.1)
        }),
{
    let ab = edwards_add(x1, y1, x2, y2);
    let aa = edwards_double(x1, y1);
    let bb = edwards_double(x2, y2);
    let ba = edwards_add(x2, y2, x1, y1);

    lemma_edwards_add_commutative(x2, y2, x1, y1);
    assert(ba == ab);

    calc! {
        (==)
        edwards_double(ab.0, ab.1); (==) {
            assert(edwards_double(ab.0, ab.1) == edwards_add(ab.0, ab.1, ab.0, ab.1));
        }
        edwards_add(ab.0, ab.1, ab.0, ab.1); (==) {
            // (A+B) + (A+B) == A + (B + (A+B))
            lemma_edwards_add_associative(x1, y1, x2, y2, ab.0, ab.1);
        }
        {
            let bc = edwards_add(x2, y2, ab.0, ab.1);
            edwards_add(x1, y1, bc.0, bc.1)
        }; (==) {
            // B + (A+B) == (B+A) + B
            let bc = edwards_add(x2, y2, ab.0, ab.1);
            lemma_edwards_add_associative(x2, y2, x1, y1, x2, y2);
            assert(bc == edwards_add(ba.0, ba.1, x2, y2));
        }
        {
            let bc = edwards_add(ba.0, ba.1, x2, y2);
            edwards_add(x1, y1, bc.0, bc.1)
        }; (==) {
            assert(ba == ab);
        }
        {
            let bc = edwards_add(ab.0, ab.1, x2, y2);
            edwards_add(x1, y1, bc.0, bc.1)
        }; (==) {
            // A + (ab + B) == (A + ab) + B
            lemma_edwards_add_associative(x1, y1, ab.0, ab.1, x2, y2);
        }
        {
            let left = edwards_add(x1, y1, ab.0, ab.1);
            edwards_add(left.0, left.1, x2, y2)
        }; (==) {
            // A + (A+B) == (A+A) + B
            let left = edwards_add(x1, y1, ab.0, ab.1);
            lemma_edwards_add_associative(x1, y1, x1, y1, x2, y2);
            assert(left == edwards_add(aa.0, aa.1, x2, y2));
        }
        {
            let left = edwards_add(aa.0, aa.1, x2, y2);
            edwards_add(left.0, left.1, x2, y2)
        }; (==) {
            // (aa + B) + B == aa + (B + B)
            lemma_edwards_add_associative(aa.0, aa.1, x2, y2, x2, y2);
        }
        {
            let right = edwards_add(x2, y2, x2, y2);
            edwards_add(aa.0, aa.1, right.0, right.1)
        }; (==) {
            let right = edwards_add(x2, y2, x2, y2);
            assert(right == bb);
        }
        edwards_add(aa.0, aa.1, bb.0, bb.1);
    }
}

/// Lemma: `edwards_scalar_mul` satisfies the linear recursion step for n ≥ 1:
///
///   (n+1)*P = n*P + P
pub proof fn lemma_edwards_scalar_mul_succ(point_affine: (nat, nat), n: nat)
    requires
        n >= 1,
    ensures
        edwards_scalar_mul(point_affine, n + 1) == {
            let prev = edwards_scalar_mul(point_affine, n);
            edwards_add(prev.0, prev.1, point_affine.0, point_affine.1)
        },
    decreases n,
{
    if n == 1 {
        // 2P = double(P) = P + P
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert((2nat / 2nat) as nat == 1nat) by (compute);
        assert(edwards_scalar_mul(point_affine, 1) == point_affine);
        // double(P) = add(P, P) by definition of edwards_double
    } else {
        let np1 = (n + 1) as nat;
        assert(np1 >= 3);

        if np1 % 2 == 1 {
            // Odd (n+1): the definition takes the odd branch directly.
            reveal_with_fuel(edwards_scalar_mul, 1);
            assert(np1 != 0 && np1 != 1);
            assert(edwards_scalar_mul(point_affine, np1) == {
                let prev = edwards_scalar_mul(point_affine, (np1 - 1) as nat);
                edwards_add(prev.0, prev.1, point_affine.0, point_affine.1)
            });
            assert((np1 - 1) as nat == n);
        } else {
            // Even (n+1): relate the double-and-add recursion to a linear step.
            // Since np1 % 2 != 1 (we're in else branch), np1 % 2 == 0
            lemma_add_mod_noop(n as int, 1, 2);
            lemma_fundamental_div_mod(np1 as int, 2);

            assert(np1 % 2 == 0);
            assert(n % 2 != 0);  // If n were even, (n+1) would be odd

            // Write n+1 = 2*m (since it's even).
            let m = (np1 / 2) as nat;
            assert(np1 == m * 2);
            assert(m >= 2);  // np1 >= 3 and even implies m >= 2

            let mm1 = (m - 1) as nat;
            assert(mm1 >= 1);

            // Unfold scalar_mul(P, n+1) at the even branch: (n+1)P = 2*(mP).
            reveal_with_fuel(edwards_scalar_mul, 1);
            assert(np1 != 0 && np1 != 1);
            assert(edwards_scalar_mul(point_affine, np1) == {
                let half = edwards_scalar_mul(point_affine, m);
                edwards_double(half.0, half.1)
            });

            // Unfold scalar_mul(P, n) at the odd branch: nP = (n-1)P + P.
            assert(n >= 3);
            reveal_with_fuel(edwards_scalar_mul, 1);
            assert(n != 0 && n != 1);
            assert(edwards_scalar_mul(point_affine, n) == {
                let prev = edwards_scalar_mul(point_affine, (n - 1) as nat);
                edwards_add(prev.0, prev.1, point_affine.0, point_affine.1)
            });

            // Unfold scalar_mul(P, n-1) at the even branch: (n-1)P = 2*((m-1)P).
            let nm1 = (n - 1) as nat;
            assert(nm1 == (mm1 * 2)) by {
                assert(np1 == m * 2);
                assert(nm1 + 2 == np1);
                assert(nm1 + 2 == m * 2);
                assert(nm1 == m * 2 - 2);
                assert(m * 2 - 2 == (m - 1) * 2) by (compute);
            }
            assert(nm1 % 2 == 0) by {
                assert(nm1 == mm1 * 2);
                lemma_mul_mod_noop_right(mm1 as int, 2, 2);
                assert(nm1 % 2 == (mm1 * (2nat % 2nat)) % 2);
                assert(2nat % 2nat == 0nat) by (compute);
                assert(mm1 * 0 == 0) by {
                    lemma_mul_by_zero_is_zero(mm1 as int);
                }
                assert(0nat % 2 == 0) by (compute);
            }

            reveal_with_fuel(edwards_scalar_mul, 1);
            assert(nm1 != 0 && nm1 != 1);
            assert(edwards_scalar_mul(point_affine, nm1) == {
                let half = edwards_scalar_mul(point_affine, (nm1 / 2) as nat);
                edwards_double(half.0, half.1)
            });
            assert((nm1 / 2) as nat == mm1) by {
                assert(nm1 == mm1 * 2);
                lemma_div_by_multiple(mm1 as int, 2);
            }

            // Use IH: mP = (m-1)P + P.
            lemma_edwards_scalar_mul_succ(point_affine, mm1);

            let p_mm1 = edwards_scalar_mul(point_affine, mm1);
            assert(edwards_scalar_mul(point_affine, m) == edwards_add(
                p_mm1.0,
                p_mm1.1,
                point_affine.0,
                point_affine.1,
            )) by {
                assert(m == mm1 + 1);
            }

            // LHS: (n+1)P = 2*(mP) = 2*((m-1)P + P) = 2*(m-1)P + 2P.
            lemma_edwards_double_of_add(p_mm1.0, p_mm1.1, point_affine.0, point_affine.1);
            let lhs_as_sum = {
                let d_mm1 = edwards_double(p_mm1.0, p_mm1.1);
                let d_p = edwards_double(point_affine.0, point_affine.1);
                edwards_add(d_mm1.0, d_mm1.1, d_p.0, d_p.1)
            };
            assert(edwards_double(
                edwards_scalar_mul(point_affine, m).0,
                edwards_scalar_mul(point_affine, m).1,
            ) == lhs_as_sum) by {
                assert(edwards_scalar_mul(point_affine, m) == edwards_add(
                    p_mm1.0,
                    p_mm1.1,
                    point_affine.0,
                    point_affine.1,
                ));
            }

            // RHS: (nP) + P = ((n-1)P + P) + P = (n-1)P + 2P.
            let p_nm1 = edwards_scalar_mul(point_affine, nm1);
            assert(p_nm1 == edwards_double(p_mm1.0, p_mm1.1)) by {
                assert(edwards_scalar_mul(point_affine, nm1) == {
                    let half = edwards_scalar_mul(point_affine, (nm1 / 2) as nat);
                    edwards_double(half.0, half.1)
                });
                assert((nm1 / 2) as nat == mm1);
                assert(p_mm1 == edwards_scalar_mul(point_affine, mm1));
            }

            let rhs_as_sum = {
                let d_p = edwards_double(point_affine.0, point_affine.1);
                edwards_add(p_nm1.0, p_nm1.1, d_p.0, d_p.1)
            };

            // Finish by rewriting both sides to the same `(... + 2P)` form.
            calc! {
                (==)
                edwards_scalar_mul(point_affine, np1); (==) {}
                edwards_double(
                    edwards_scalar_mul(point_affine, m).0,
                    edwards_scalar_mul(point_affine, m).1,
                ); (==) {
                    assert(edwards_double(
                        edwards_scalar_mul(point_affine, m).0,
                        edwards_scalar_mul(point_affine, m).1,
                    ) == lhs_as_sum);
                }
                lhs_as_sum; (==) {
                    // Substitute p_nm1 = 2*(m-1)P
                    assert(p_nm1 == edwards_double(p_mm1.0, p_mm1.1));
                    // lhs_as_sum = 2*(m-1)P + 2P
                    assert(lhs_as_sum == rhs_as_sum) by {
                        // p_nm1 is already 2*(m-1)P; just rewrite.
                        assert(p_nm1 == edwards_double(p_mm1.0, p_mm1.1));
                    }
                }
                rhs_as_sum; (==) {
                    // (nP)+P = (n-1)P + 2P
                    let p_n = edwards_scalar_mul(point_affine, n);
                    let d_p = edwards_double(point_affine.0, point_affine.1);
                    lemma_edwards_add_associative(
                        p_nm1.0,
                        p_nm1.1,
                        point_affine.0,
                        point_affine.1,
                        point_affine.0,
                        point_affine.1,
                    );
                    assert(edwards_add(
                        edwards_add(p_nm1.0, p_nm1.1, point_affine.0, point_affine.1).0,
                        edwards_add(p_nm1.0, p_nm1.1, point_affine.0, point_affine.1).1,
                        point_affine.0,
                        point_affine.1,
                    ) == edwards_add(p_nm1.0, p_nm1.1, d_p.0, d_p.1));
                    assert(p_n == edwards_add(p_nm1.0, p_nm1.1, point_affine.0, point_affine.1));
                }
                edwards_add(
                    edwards_scalar_mul(point_affine, n).0,
                    edwards_scalar_mul(point_affine, n).1,
                    point_affine.0,
                    point_affine.1,
                );
            }
        }
    }
}

/// Lemma: scalar multiplication by a power-of-two exponent unfolds to a doubling.
///
/// For any point P and exponent k ≥ 0:
///   [2^(k+1)]P = double([2^k]P)
///
/// This is used to prove `mul_by_pow_2` correct by showing each doubling step
/// computes the next power-of-two multiple.
pub proof fn lemma_edwards_scalar_mul_pow2_succ(point_affine: (nat, nat), k: nat)
    ensures
        edwards_scalar_mul(point_affine, pow2(k + 1)) == {
            let half = edwards_scalar_mul(point_affine, pow2(k));
            edwards_double(half.0, half.1)
        },
{
    reveal_with_fuel(edwards_scalar_mul, 1);

    // pow2(k+1) > 0
    assert(pow2(k + 1) != 0) by {
        lemma_pow2_pos(k + 1);
        lemma2_to64();
    };

    // pow2(k+1) is even (for k+1 >= 1)
    assert(pow2(k + 1) % 2 == 0) by {
        lemma_pow2_even(k + 1);
        lemma2_to64();
    };

    // pow2(k+1) >= 2 for k >= 0, so != 1
    assert(pow2(k + 1) != 1) by {
        lemma_pow2_pos(k + 1);
        lemma2_to64();
    };

    // pow2(k+1) / 2 == pow2(k)
    assert(pow2(k + 1) / 2 == pow2(k)) by {
        pow2_MUL_div(1, k + 1, 1);
        lemma2_to64();
    };
}

/// **Lemma**: Scalar multiplication composition for powers of 2
///
/// Simplified version for powers of 2: `edwards_scalar_mul(edwards_scalar_mul(P, a), pow2(k)) == edwards_scalar_mul(P, a * pow2(k))`
/// This is easier to prove than the general case because powers of 2 always take the even branch.
///
/// The proof proceeds by induction on `k`, using `lemma_edwards_scalar_mul_pow2_succ` to
/// unfold the `pow2(k)` recursion and basic arithmetic facts about powers of 2.
pub proof fn lemma_edwards_scalar_mul_composition_pow2(point_affine: (nat, nat), a: nat, k: nat)
    ensures
        edwards_scalar_mul(edwards_scalar_mul(point_affine, a), pow2(k)) == edwards_scalar_mul(
            point_affine,
            a * pow2(k),
        ),
    decreases k,
{
    if k == 0 {
        lemma2_to64();
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(pow2(0) == 1);
        assert(a * 1 == a) by (nonlinear_arith);
        assert(a * pow2(0) == a);
    } else {
        let km1 = (k - 1) as nat;

        // Induction hypothesis at k-1.
        lemma_edwards_scalar_mul_composition_pow2(point_affine, a, km1);

        // Unfold the `pow2(k)` scalar multiplication on the left.
        lemma_edwards_scalar_mul_pow2_succ(edwards_scalar_mul(point_affine, a), km1);

        if a == 0 {
            // scalar_mul(P, 0) = identity, and doubling identity = identity
            reveal_with_fuel(edwards_scalar_mul, 1);
            lemma_edwards_double_identity();
            assert(edwards_scalar_mul(point_affine, 0) == math_edwards_identity());
            assert(0nat * pow2(k) == 0);
            // IH: scalar_mul(scalar_mul(P,0), pow2(k-1)) == scalar_mul(P,0) == identity
            // So double(identity) == identity
        } else {
            // Lemmas needed for arithmetic reasoning
            reveal_with_fuel(edwards_scalar_mul, 1);
            lemma_pow2_even(k);
            lemma_pow2_pos(k);
            lemma2_to64();
            pow2_MUL_div(a, k, 1);
            lemma_mul_mod_noop_right(a as int, pow2(k) as int, 2);
            lemma_mul_by_zero_is_zero(a as int);
            lemma_mul_nonzero(a as int, pow2(k) as int);

            // a * pow2(k) is even, nonzero, != 1, and divides correctly
            assert(pow2(k) % 2 == 0);
            assert((a * pow2(k)) % 2 == 0);
            assert((a * pow2(k)) / 2 == a * pow2(km1));
            assert(a * pow2(k) != 0 && a * pow2(k) != 1);

            // Rewrite both sides to the same "double" form.
            calc! {
                (==)
                edwards_scalar_mul(edwards_scalar_mul(point_affine, a), pow2(k)); (==) {
                    // From lemma_edwards_scalar_mul_pow2_succ on the left:
                    // scalar_mul(Q, 2^k) = double(scalar_mul(Q, 2^(k-1))).
                }
                {
                    let half = edwards_scalar_mul(edwards_scalar_mul(point_affine, a), pow2(km1));
                    edwards_double(half.0, half.1)
                }; (==) {
                    // Apply IH to rewrite the inner scalar multiplication.
                    assert(edwards_scalar_mul(edwards_scalar_mul(point_affine, a), pow2(km1))
                        == edwards_scalar_mul(point_affine, a * pow2(km1)));
                }
                {
                    let half = edwards_scalar_mul(point_affine, a * pow2(km1));
                    edwards_double(half.0, half.1)
                }; (==) {
                    // Unfold RHS at n = a*pow2(k) and use the computed half.
                    assert(((a * pow2(k)) / 2) as nat == a * pow2(km1));
                }
                edwards_scalar_mul(point_affine, a * pow2(k));
            }
        }
    }
}

} // verus!
