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
use crate::backend::serial::curve_models::{
    AffineNielsPoint, ProjectiveNielsPoint, ProjectivePoint,
};
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::common_lemmas::pow_lemmas::{lemma_pow2_even, pow2_MUL_div};
#[cfg(verus_keep_ghost)]
use crate::lemmas::field_lemmas::add_lemmas::lemma_fe51_limbs_bounded_weaken;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::field_lemmas::negate_lemmas::{lemma_neg, lemma_neg_no_underflow, proof_negate};
#[cfg(verus_keep_ghost)]
use crate::lemmas::field_lemmas::u64_5_as_nat_lemmas::lemma_fe51_unit_is_one;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use crate::specs::montgomery_specs::edwards_y_from_montgomery_u;
use crate::specs::primality_specs::*;
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
        is_on_edwards_curve(0, 1),
{
    let modulus = p();
    p_gt_2();

    let d = fe51_as_canonical_nat(&EDWARDS_D);

    // x² = 0² = 0
    let x2 = field_square(0nat);
    assert(x2 == 0) by {
        lemma_small_mod(0nat, modulus);
    }

    // y² = 1² = 1
    let y2 = field_square(1nat);
    assert(y2 == 1) by {
        lemma_small_mod(1nat, modulus);
    }

    // LHS = y² - x² = 1 - 0 = 1 (using field_sub)
    // field_sub(a, b) = ((a % p) + p - (b % p)) % p
    let lhs = field_sub(y2, x2);
    assert(lhs == 1) by {
        // y2 = 1, x2 = 0
        // field_sub(1, 0) = ((1 % p) + p - (0 % p)) % p
        //                      = (1 + p - 0) % p
        //                      = (p + 1) % p = 1
        lemma_small_mod(1nat, modulus);
        lemma_small_mod(0nat, modulus);
        // (p + 1) % p = 1 because (p + 1) = p * 1 + 1, and remainder is 1
        lemma_mod_multiples_vanish(1, 1, modulus as int);
    }

    // x²·y² = 0·1 = 0
    let x2y2 = field_mul(x2, y2);
    assert(x2y2 == 0) by {
        lemma_small_mod(0nat, modulus);
    }

    // d·x²·y² = d·0 = 0
    let d_x2y2 = field_mul(d, x2y2);
    assert(d_x2y2 == 0) by {
        lemma_mul_by_zero_is_zero(d as int);
        lemma_small_mod(0nat, modulus);
    }

    // RHS = 1 + d·x²·y² = 1 + 0 = 1
    let rhs = field_add(1nat, d_x2y2);
    assert(rhs == 1) by {
        lemma_small_mod(1nat, modulus);
    }

    // LHS = RHS = 1, so is_on_edwards_curve(0, 1) holds
    assert(lhs == rhs);
}

/// Lemma: The identity point (0, 1, 1, 0) is a valid extended Edwards point
///
/// This combines lemma_identity_on_curve with lemma_affine_to_extended_valid.
pub proof fn lemma_identity_is_valid_extended()
    ensures
        is_valid_extended_edwards_point(0, 1, 1, 0),
{
    // First prove (0, 1) is on the curve
    lemma_identity_on_curve();

    // t = x * y = 0 * 1 = 0
    assert(field_mul(0nat, 1nat) == 0) by {
        p_gt_2();
        lemma_small_mod(0nat, p());
    }

    // Use the affine-to-extended lemma
    lemma_affine_to_extended_valid(0nat, 1nat, 0nat);
}

/// The identity projective point (X=0, Y=1, Z=1) is valid, has bounded limbs,
/// and its affine coordinates are the identity (0, 1).
pub proof fn lemma_identity_projective_point_properties()
    ensures
        is_valid_projective_point(identity_projective_point_edwards()),
        fe51_limbs_bounded(&identity_projective_point_edwards().X, 52),
        fe51_limbs_bounded(&identity_projective_point_edwards().Y, 52),
        fe51_limbs_bounded(&identity_projective_point_edwards().Z, 52),
        sum_of_limbs_bounded(
            &identity_projective_point_edwards().X,
            &identity_projective_point_edwards().Y,
            u64::MAX,
        ),
        projective_point_as_affine_edwards(identity_projective_point_edwards())
            == edwards_identity(),
{
    let id = identity_projective_point_edwards();
    p_gt_2();

    assert(0u64 < (1u64 << 52u64) && 1u64 < (1u64 << 52u64)) by (bit_vector);

    // fe51_as_nat for all-zero limbs (X) is 0, for [1,0,0,0,0] limbs (Y, Z) is 1
    assert(fe51_as_nat(&id.X) == 0nat && fe51_as_nat(&id.Y) == 1nat && fe51_as_nat(&id.Z) == 1nat)
        by {
        reveal(pow2);
        lemma_mul_by_zero_is_zero(pow2(51) as int);
        lemma_mul_by_zero_is_zero(pow2(102) as int);
        lemma_mul_by_zero_is_zero(pow2(153) as int);
        lemma_mul_by_zero_is_zero(pow2(204) as int);
    };

    assert(fe51_as_canonical_nat(&id.X) == 0 && fe51_as_canonical_nat(&id.Y) == 1
        && fe51_as_canonical_nat(&id.Z) == 1) by {
        lemma_small_mod(0nat, p());
        lemma_small_mod(1nat, p());
    };

    // Projective curve equation: -0² + 1² = 1² + d·0²·1²
    // Z3 needs individual field operation results as stepping stones
    lemma_small_mod(0nat, p());
    lemma_small_mod(1nat, p());
    assert(field_square(0nat) == 0 && field_square(1nat) == 1);
    assert(field_sub(1nat, 0nat) == 1) by {
        lemma_mod_multiples_vanish(1, 1, p() as int);
    };
    assert(field_mul(1nat, 1nat) == 1);
    assert(field_mul(fe51_as_canonical_nat(&EDWARDS_D), 0nat) == 0) by {
        lemma_mul_by_zero_is_zero(fe51_as_canonical_nat(&EDWARDS_D) as int);
    };
    assert(is_on_edwards_curve_projective(0, 1, 1));

    lemma_field_inv_one();
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
        is_on_edwards_curve(x, y),
    ensures
        is_on_edwards_curve(field_neg(x), y),
{
    // Goal: on_curve(-x, y)
    // Strategy: The curve equation uses x², and (-x)² = x², so the equation is identical
    //
    //   y² - (-x)² = 1 + d·(-x)²·y²
    //   y² - x²    = 1 + d·x²·y²      (same equation!)
    //
    // The precondition says (x, y) satisfies this, so (-x, y) does too.
    let neg_x = field_neg(x);

    assert(is_on_edwards_curve(neg_x, y)) by {
        // Key insight: (-x)² = x²
        assert(field_square(neg_x) == field_square(x)) by {
            lemma_neg_square_eq(x);  // (-x)² = (x % p)²
            lemma_square_mod_noop(x);  // (x % p)² = x²
        };
        // With (-x)² = x², the curve equations are identical
    };
}

/// Lemma: Negation preserves extended Edwards point validity
///
/// If (X, Y, Z, T) is a valid extended Edwards point, then (-X, Y, Z, -T) is also valid.
/// This is because:
/// 1. Z ≠ 0 is unchanged
/// 2. The projective curve equation uses X² and (-X)² = X²
/// 3. The Segre relation: (-X)·Y = -(X·Y) = -(Z·T) = Z·(-T)
pub proof fn lemma_negation_preserves_extended_validity(x: nat, y: nat, z: nat, t: nat)
    requires
        is_valid_extended_edwards_point(x, y, z, t),
    ensures
        is_valid_extended_edwards_point(field_neg(x), y, z, field_neg(t)),
{
    let p = p();
    p_gt_2();
    let neg_x = field_neg(x);
    let neg_t = field_neg(t);

    // From precondition: z != 0, curve equation holds, x*y = z*t

    // 1) Z ≠ 0 is unchanged (z remains the same)

    // 2) Projective curve equation: uses X², and (-X)² = X²
    assert(is_on_edwards_curve_projective(neg_x, y, z)) by {
        // Key insight: (-x)² = x²
        assert(field_square(neg_x) == field_square(x)) by {
            lemma_neg_square_eq(x);
            lemma_square_mod_noop(x);
        };
        // With (-x)² = x², the projective curve equation is unchanged
    };

    // 3) Segre relation: (-X)·Y = Z·(-T)
    // Need to prove: field_mul(neg_x, y) == field_mul(z, neg_t)
    assert(field_mul(neg_x, y) == field_mul(z, neg_t)) by {
        // From precondition: x*y = z*t
        let xy = field_mul(x, y);
        let zt = field_mul(z, t);
        assert(xy == zt);

        // (-x)*y = -(x*y)
        assert(field_mul(neg_x, y) == field_neg(xy)) by {
            lemma_field_mul_neg(y, x);  // y * neg(x) = neg(y * x)
            lemma_field_mul_comm(neg_x, y);
            lemma_field_mul_comm(y, x);
        };

        // z*(-t) = -(z*t)
        assert(field_mul(z, neg_t) == field_neg(zt)) by {
            lemma_field_mul_neg(z, t);
        };

        // neg(x*y) = neg(z*t) since x*y = z*t
        assert(field_neg(xy) == field_neg(zt));
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
        is_on_edwards_curve(x, y),
        t == field_mul(x, y),
    ensures
        is_valid_extended_edwards_point(x, y, 1, t),
{
    let p = p();
    p_gt_2();

    // New validity definition uses:
    // - Z % p != 0 (field-nonzero)
    // - projective curve equation
    // - Segre relation X·Y == Z·T

    // 1) Z = 1, so 1 % p != 0 (since p > 2)
    assert(1nat % p != 0) by {
        lemma_small_mod(1nat, p);
    }

    // 2) Projective curve equation holds for Z = 1
    assert(is_on_edwards_curve_projective(x, y, 1)) by {
        let x2 = field_square(x);
        let y2 = field_square(y);
        let z2 = field_square(1);
        let z4 = field_square(z2);
        let d = fe51_as_canonical_nat(&EDWARDS_D);

        // z2 = 1^2 = 1, z4 = 1^4 = 1
        assert(z2 == 1) by {
            lemma_mul_basics(1int);
            lemma_small_mod(1, p);
        };
        assert(z4 == 1) by {
            lemma_mul_basics(1int);
            lemma_small_mod(1, p);
        };

        // LHS: (y2 - x2)·1 = (y2 - x2)
        let lhs = field_mul(field_sub(y2, x2), z2);
        assert(lhs == field_sub(y2, x2)) by {
            lemma_mul_basics((field_sub(y2, x2)) as int);
            lemma_mod_twice((((y2 % p) + p) - (x2 % p)) as int, p as int);
        };

        // RHS: 1 + d·x2·y2 (z4 == 1)
        let rhs = field_add(z4, field_mul(d, field_mul(x2, y2)));
        assert(rhs == field_add(1, field_mul(d, field_mul(x2, y2))));

        // Affine curve equation gives the same equality.
        assert(field_sub(y2, x2) == field_add(1, field_mul(d, field_mul(x2, y2))));
        assert(lhs == rhs);
    };

    // 3) Segre relation: X·Y == Z·T (with Z = 1 and T = X·Y)
    assert(field_mul(x, y) == field_mul(1, t)) by {
        assert(t == field_mul(x, y));
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
        is_on_edwards_curve(x, y),
        x == 0,
    ensures
        field_square(y) == 1,
{
    let modulus = p();
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let x2 = field_square(x);
    let y2 = field_square(y);
    let x2y2 = field_mul(x2, y2);
    let d_x2y2 = field_mul(d, x2y2);
    let lhs = field_sub(y2, x2);
    let rhs = field_add(1, d_x2y2);

    // Establish p > 1 for lemma preconditions
    assert(modulus > 1) by {
        p_gt_2();
    };

    // Goal: y² = 1
    // Strategy: From curve equation y² - x² = 1 + d·x²·y², show all terms simplify

    assert(x2 == 0) by {
        lemma_mul_basics_2(0);
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
        // lhs = field_sub(y2, 0) = (y2 + p) % p = y2
        assert(x2 == 0);

        // y2 < p (field_square output is reduced)
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
/// Special case of `lemma_affine_curve_implies_projective` when Z = 1.
/// With Z = 1 the affine and projective equations coincide, so the proof
/// only needs field_inv(1) = 1 and field_mul(a, 1) = a.
pub proof fn lemma_z_one_affine_implies_projective(x: nat, y: nat)
    requires
        is_on_edwards_curve(x, y),
        x < p(),
        y < p(),
    ensures
        is_on_edwards_curve_projective(x, y, 1nat),
{
    p_gt_2();
    assert(1nat % p() != 0) by {
        lemma_small_mod(1nat, p());
    };
    lemma_field_inv_one();
    lemma_field_mul_one_right(x);
    lemma_field_mul_one_right(y);
    lemma_small_mod(x, p());
    lemma_small_mod(y, p());
    lemma_affine_curve_implies_projective(x, y, 1nat);
}

/// This is exactly the projective curve equation.
pub proof fn lemma_affine_curve_implies_projective(x: nat, y: nat, z: nat)
    requires
        z % p() != 0,  // Z must be non-zero in the field (not just non-zero as nat)
        is_on_edwards_curve(field_mul(x, field_inv(z)), field_mul(y, field_inv(z))),
    ensures
        is_on_edwards_curve_projective(x, y, z),
{
    let p = p();
    p_gt_2();

    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let inv_z = field_inv(z);

    // Define affine coordinates
    let x_div_z = field_mul(x, inv_z);
    let y_div_z = field_mul(y, inv_z);

    // Squares of affine coordinates
    let x_div_z_sq = field_square(x_div_z);
    let y_div_z_sq = field_square(y_div_z);

    // From precondition: the affine curve equation holds
    // y_div_z² - x_div_z² = 1 + d * x_div_z² * y_div_z²
    let affine_lhs = field_sub(y_div_z_sq, x_div_z_sq);
    let affine_rhs = field_add(1, field_mul(d, field_mul(x_div_z_sq, y_div_z_sq)));
    assert(affine_lhs == affine_rhs);

    // Projective coordinates
    let x2 = field_square(x);
    let y2 = field_square(y);
    let z2 = field_square(z);
    let z4 = field_square(z2);

    // Use lemma_quotient_of_squares: (a/b)² = a²/b²
    // So x_div_z² = x²/z² and y_div_z² = y²/z²
    let inv_z2 = field_inv(z2);

    assert(x_div_z_sq == field_mul(x2, inv_z2)) by {
        lemma_quotient_of_squares(x, z);
    };

    assert(y_div_z_sq == field_mul(y2, inv_z2)) by {
        lemma_quotient_of_squares(y, z);
    };

    // The projective curve equation: (y² - x²)·z² = z⁴ + d·x²·y²
    let proj_lhs = field_mul(field_sub(y2, x2), z2);
    let proj_rhs = field_add(z4, field_mul(d, field_mul(x2, y2)));

    // === STEP 1: Rewrite affine_lhs ===
    // affine_lhs = y²·inv(z²) - x²·inv(z²) = (y² - x²)·inv(z²)
    // by factoring out inv(z²)

    // First show: y²·inv(z²) - x²·inv(z²) = (y² - x²)·inv(z²)
    let y2_minus_x2 = field_sub(y2, x2);

    assert(affine_lhs == field_mul(y2_minus_x2, inv_z2)) by {
        lemma_field_mul_distributes_over_sub_right(y2, x2, inv_z2);
    };

    // === STEP 2: Rewrite affine_rhs ===
    // We need: (x/z)²·(y/z)² = x²·y²·inv(z⁴)
    // Since (x/z)² = x²·inv(z²) and (y/z)² = y²·inv(z²)
    // their product is x²·inv(z²)·y²·inv(z²) = x²·y²·inv(z²)·inv(z²) = x²·y²·inv(z⁴)

    let inv_z4 = field_inv(z4);
    let x2_y2 = field_mul(x2, y2);
    let x2_y2_inv_z4 = field_mul(x2_y2, inv_z4);

    // inv(z²)·inv(z²) = inv(z⁴)
    assert(field_mul(inv_z2, inv_z2) == inv_z4) by {
        // z4 = z² · z², so inv(z4) = inv(z²·z²) = inv(z²)·inv(z²)
        lemma_inv_of_product(z2, z2);
    };

    // (x/z)²·(y/z)² = x²·y²·inv(z⁴)
    assert(field_mul(x_div_z_sq, y_div_z_sq) == x2_y2_inv_z4) by {
        // (x²·inv(z²))·(y²·inv(z²)) = x²·y²·inv(z²)·inv(z²) = x²·y²·inv(z⁴)
        lemma_field_mul_assoc(x2, inv_z2, field_mul(y2, inv_z2));
        lemma_field_mul_comm(inv_z2, field_mul(y2, inv_z2));
        lemma_field_mul_assoc(y2, inv_z2, inv_z2);
        lemma_field_mul_assoc(x2, y2, field_mul(inv_z2, inv_z2));
    };

    // So affine_rhs = 1 + d·x²·y²·inv(z⁴)
    assert(affine_rhs == field_add(1, field_mul(d, x2_y2_inv_z4)));

    // === STEP 3: Multiply both sides by z⁴ ===
    // We need: if A = B in the field, then A·z⁴ = B·z⁴

    // First prove z² ≠ 0 and z⁴ ≠ 0 (mod p) since z ≠ 0 and p is prime
    // z2 = field_square(z) = (z * z) % p = field_mul(z, z)
    lemma_nonzero_product(z, z);
    assert(z2 < p) by {
        lemma_mod_bound((z * z) as int, p as int);
    };
    lemma_field_element_reduced(z2);
    assert(z2 % p != 0);

    // Similarly for z4: z4 = z2 * z2 % p = field_mul(z2, z2)
    lemma_nonzero_product(z2, z2);
    assert(z4 < p) by {
        lemma_mod_bound((z2 * z2) as int, p as int);
    };
    lemma_field_element_reduced(z4);
    assert(z4 % p != 0);

    // LHS after multiplying: (y² - x²)·inv(z²)·z⁴ = (y² - x²)·z²
    // because inv(z²)·z⁴ = inv(z²)·z²·z² = z² (since inv(z²)·z² = 1)

    // Show inv(z²)·z⁴ = z² when z ≠ 0
    assert(field_mul(inv_z2, z4) == z2) by {
        // z4 = z2 · z2
        // inv(z2) · z4 = inv(z2) · (z2 · z2) = (inv(z2) · z2) · z2 = 1 · z2 = z2
        lemma_field_mul_assoc(inv_z2, z2, z2);
        lemma_inv_mul_cancel(z2);
        lemma_field_mul_one_left(z2);
    };

    // So (y² - x²)·inv(z²)·z⁴ = (y² - x²)·z²
    assert(field_mul(field_mul(y2_minus_x2, inv_z2), z4) == proj_lhs) by {
        lemma_field_mul_assoc(y2_minus_x2, inv_z2, z4);
    };

    // RHS after multiplying: (1 + d·x²·y²·inv(z⁴))·z⁴ = z⁴ + d·x²·y²
    // because inv(z⁴)·z⁴ = 1

    // Show inv(z⁴)·z⁴ = 1 when z ≠ 0
    assert(field_mul(inv_z4, z4) == 1) by {
        lemma_inv_mul_cancel(z4);
    };

    // d·x²·y²·inv(z⁴)·z⁴ = d·x²·y² (since inv(z⁴)·z⁴ = 1)
    // Chain: (d · x2_y2_inv_z4) · z4 = d · (x2_y2 · (inv_z4 · z4)) = d · (x2_y2 · 1) = d · x2_y2
    assert(field_mul(field_mul(d, x2_y2_inv_z4), z4) == field_mul(d, x2_y2)) by {
        lemma_field_mul_assoc(d, x2_y2_inv_z4, z4);
        lemma_field_mul_assoc(x2_y2, inv_z4, z4);
        lemma_mod_bound((x2 * y2) as int, p as int);
        lemma_field_element_reduced(x2_y2);
        lemma_field_mul_one_right(x2_y2);
    };

    // (1 + d·x²·y²·inv(z⁴))·z⁴ = z⁴ + d·x²·y²·inv(z⁴)·z⁴ = z⁴ + d·x²·y²
    assert(field_mul(affine_rhs, z4) == proj_rhs) by {
        // Commutativity: field_mul(affine_rhs, z4) == field_mul(z4, affine_rhs)
        lemma_field_mul_comm(affine_rhs, z4);
        // Distribution: field_mul(z4, 1 + D) == field_mul(z4, 1) + field_mul(z4, D)
        lemma_field_mul_distributes_over_add(z4, 1, field_mul(d, x2_y2_inv_z4));
        // field_mul(z4, 1) == z4
        lemma_field_mul_one_right(z4);
        lemma_small_mod(z4, p);
        // field_mul(z4, D) == field_mul(D, z4) == field_mul(d, x2_y2)
        lemma_field_mul_comm(z4, field_mul(d, x2_y2_inv_z4));
    };

    // === STEP 4: Connect via the affine equation ===
    // Since affine_lhs = affine_rhs, we have:
    // affine_lhs · z⁴ = affine_rhs · z⁴
    // (y² - x²)·inv(z²)·z⁴ = (1 + d·x²·y²·inv(z⁴))·z⁴
    // (y² - x²)·z² = z⁴ + d·x²·y²
    // proj_lhs = proj_rhs

    assert(field_mul(affine_lhs, z4) == field_mul(affine_rhs, z4));

    // affine_lhs · z⁴ = (y² - x²)·inv(z²)·z⁴ = proj_lhs
    assert(field_mul(affine_lhs, z4) == proj_lhs) by {
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
    let x1x2 = field_mul(0nat, 0nat);
    let y1y2 = field_mul(1nat, 1nat);
    assert(x1x2 == 0);
    assert(y1y2 == 1);
    let t = field_mul(fe51_as_canonical_nat(&EDWARDS_D), field_mul(x1x2, y1y2));
    assert(t == 0) by {
        assert(field_mul(fe51_as_canonical_nat(&EDWARDS_D), 0) == 0) by {
            lemma_mul_basics_2(fe51_as_canonical_nat(&EDWARDS_D) as int);
        }
    }

    // Denominators: 1+0=1, 1-0=1, inv(1)=1
    let denom_x = field_add(1nat, t);
    let denom_y = field_sub(1nat, t);
    assert(denom_x == 1 && denom_y == 1);
    assert(field_inv(denom_x) == 1 && field_inv(denom_y) == 1);

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
    let x1x2 = field_mul(x, 0nat);
    let y1y2 = field_mul(y, 1nat);
    let x1y2 = field_mul(x, 1nat);
    let y1x2 = field_mul(y, 0nat);
    assert(x1x2 == 0 && y1x2 == 0 && y1y2 == y % p() && x1y2 == x % p());

    // t = d * 0 = 0
    let t = field_mul(fe51_as_canonical_nat(&EDWARDS_D), field_mul(x1x2, y1y2));
    assert(t == 0) by {
        lemma_field_mul_zero_left(x1x2, y1y2);
        lemma_field_mul_zero_right(fe51_as_canonical_nat(&EDWARDS_D), 0nat);
    }

    // Denominators: 1+0=1, 1-0=1, inv(1)=1
    let denom_x = field_add(1nat, t);
    let denom_y = field_sub(1nat, t);
    assert(denom_x == 1 && denom_y == 1);
    assert(field_inv(denom_x) == 1 && field_inv(denom_y) == 1);

    // Result: x3 = (x%p + 0) * 1 = x%p, y3 = (y%p + 0) * 1 = y%p
}

/// Lemma: Edwards addition is commutative.
///
/// This follows directly from the symmetry of the affine addition formulas.
pub proof fn lemma_edwards_add_commutative(x1: nat, y1: nat, x2: nat, y2: nat)
    ensures
        edwards_add(x1, y1, x2, y2) == edwards_add(x2, y2, x1, y1),
{
    // Help the solver with the commutativity of the `field_mul` terms that appear
    // in the numerators/denominators.
    lemma_field_mul_comm(x1, x2);
    lemma_field_mul_comm(y1, y2);
    lemma_field_mul_comm(x1, y2);
    lemma_field_mul_comm(y1, x2);

    assert(edwards_add(x1, y1, x2, y2) == edwards_add(x2, y2, x1, y1));
}

/// Axiom: Edwards addition is associative.
///
/// This is a standard group-law property.
pub proof fn axiom_edwards_add_associative(x1: nat, y1: nat, x2: nat, y2: nat, x3: nat, y3: nat)
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
            axiom_edwards_add_associative(x1, y1, x2, y2, ab.0, ab.1);
        }
        {
            let bc = edwards_add(x2, y2, ab.0, ab.1);
            edwards_add(x1, y1, bc.0, bc.1)
        }; (==) {
            // B + (A+B) == (B+A) + B
            let bc = edwards_add(x2, y2, ab.0, ab.1);
            axiom_edwards_add_associative(x2, y2, x1, y1, x2, y2);
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
            axiom_edwards_add_associative(x1, y1, ab.0, ab.1, x2, y2);
        }
        {
            let left = edwards_add(x1, y1, ab.0, ab.1);
            edwards_add(left.0, left.1, x2, y2)
        }; (==) {
            // A + (A+B) == (A+A) + B
            let left = edwards_add(x1, y1, ab.0, ab.1);
            axiom_edwards_add_associative(x1, y1, x1, y1, x2, y2);
            assert(left == edwards_add(aa.0, aa.1, x2, y2));
        }
        {
            let left = edwards_add(aa.0, aa.1, x2, y2);
            edwards_add(left.0, left.1, x2, y2)
        }; (==) {
            // (aa + B) + B == aa + (B + B)
            axiom_edwards_add_associative(aa.0, aa.1, x2, y2, x2, y2);
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

/// Four-way swap: (A+B) + (C+D) = (A+C) + (B+D).
///
/// Follows from associativity and commutativity:
///   (A+B)+(C+D) = A+(B+(C+D)) = A+((B+C)+D) = A+((C+B)+D) = A+(C+(B+D)) = (A+C)+(B+D)
pub proof fn lemma_edwards_add_four_way_swap(
    a: (nat, nat),
    b: (nat, nat),
    c: (nat, nat),
    d: (nat, nat),
)
    ensures
        ({
            let ab = edwards_add(a.0, a.1, b.0, b.1);
            let cd = edwards_add(c.0, c.1, d.0, d.1);
            edwards_add(ab.0, ab.1, cd.0, cd.1)
        }) == ({
            let ac = edwards_add(a.0, a.1, c.0, c.1);
            let bd = edwards_add(b.0, b.1, d.0, d.1);
            edwards_add(ac.0, ac.1, bd.0, bd.1)
        }),
{
    let cd = edwards_add(c.0, c.1, d.0, d.1);
    let bd = edwards_add(b.0, b.1, d.0, d.1);
    axiom_edwards_add_associative(a.0, a.1, b.0, b.1, cd.0, cd.1);
    axiom_edwards_add_associative(b.0, b.1, c.0, c.1, d.0, d.1);
    lemma_edwards_add_commutative(b.0, b.1, c.0, c.1);
    axiom_edwards_add_associative(c.0, c.1, b.0, b.1, d.0, d.1);
    axiom_edwards_add_associative(a.0, a.1, c.0, c.1, bd.0, bd.1);
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
        assert((2nat / 2nat) as nat == 1nat);
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
                assert(m * 2 - 2 == (m - 1) * 2) by {
                    lemma_mul_is_distributive_sub_other_way(2, m as int, 1);
                }

            }
            // nm1 == mm1 * 2, so nm1 % 2 == 0
            assert(nm1 % 2 == 0) by {
                lemma_mul_mod_noop_right(mm1 as int, 2, 2);
                lemma_mul_by_zero_is_zero(mm1 as int);
            }

            reveal_with_fuel(edwards_scalar_mul, 1);
            assert(nm1 != 0 && nm1 != 1);
            assert(edwards_scalar_mul(point_affine, nm1) == {
                let half = edwards_scalar_mul(point_affine, (nm1 / 2) as nat);
                edwards_double(half.0, half.1)
            });
            assert((nm1 / 2) as nat == mm1) by {
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
                    axiom_edwards_add_associative(
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

/// Four successive doublings equal multiplication by 16.
pub proof fn lemma_four_doublings_is_mul_16(
    a0: (nat, nat),
    a1: (nat, nat),
    a2: (nat, nat),
    a3: (nat, nat),
    a4: (nat, nat),
)
    requires
        a1 == edwards_double(a0.0, a0.1),
        a2 == edwards_double(a1.0, a1.1),
        a3 == edwards_double(a2.0, a2.1),
        a4 == edwards_double(a3.0, a3.1),
    ensures
        a4 == edwards_scalar_mul(a0, 16),
{
    lemma2_to64();
    assert(edwards_scalar_mul(a0, 2) == a1) by {
        reveal_with_fuel(edwards_scalar_mul, 1);
        lemma_edwards_scalar_mul_pow2_succ(a0, 0);
    }
    assert(edwards_scalar_mul(a0, 4) == a2) by {
        lemma_edwards_scalar_mul_pow2_succ(a0, 1);
    }
    assert(edwards_scalar_mul(a0, 8) == a3) by {
        lemma_edwards_scalar_mul_pow2_succ(a0, 2);
    }
    assert(edwards_scalar_mul(a0, 16) == a4) by {
        lemma_edwards_scalar_mul_pow2_succ(a0, 3);
    }
}

pub proof fn lemma_edwards_add_identity_left(x: nat, y: nat)
    ensures
        edwards_add(0, 1, x, y) == (x % p(), y % p()),
{
    lemma_edwards_add_commutative(0, 1, x, y);
    lemma_edwards_add_identity_right(x, y);
}

// =============================================================================
// Axioms: Signed scalar multiplication linearity (group law)
// =============================================================================
/// Axiom: Scalar multiplication distributes over point negation.
/// [n](-P) = -([n]P)
pub proof fn axiom_scalar_mul_distributes_over_neg(P: (nat, nat), n: nat)
    ensures
        edwards_scalar_mul(edwards_neg(P), n) == edwards_neg(edwards_scalar_mul(P, n)),
{
    admit();
}

/// Axiom: Negation distributes over addition (group homomorphism property).
/// (-P) + (-Q) = -(P + Q)
pub proof fn axiom_neg_distributes_over_add(P: (nat, nat), Q: (nat, nat))
    ensures
        edwards_add(edwards_neg(P).0, edwards_neg(P).1, edwards_neg(Q).0, edwards_neg(Q).1)
            == edwards_neg(edwards_add(P.0, P.1, Q.0, Q.1)),
{
    admit();
}

/// Axiom: Adding a point and its negation gives identity.
/// P + (-P) = O (identity)
pub proof fn axiom_add_neg_is_identity(P: (nat, nat))
    ensures
        edwards_add(P.0, P.1, edwards_neg(P).0, edwards_neg(P).1) == edwards_identity(),
{
    admit();
}

/// Negation flips the sign of signed scalar multiplication:
///   edwards_neg(edwards_scalar_mul_signed(P, n)) == edwards_scalar_mul_signed(P, -n)
///
/// Requires canonical P so that scalar_mul outputs are also canonical,
/// which is needed for the n < 0 case (field_neg involution).
pub proof fn lemma_neg_of_signed_scalar_mul(P: (nat, nat), n: int)
    requires
        P.0 < p(),
        P.1 < p(),
    ensures
        edwards_neg(edwards_scalar_mul_signed(P, n)) == edwards_scalar_mul_signed(P, -n),
{
    reveal(edwards_scalar_mul_signed);
    if n > 0 {
        // LHS: neg(scalar_mul(P, n as nat)) = (field_neg(x), y)
        // RHS: signed(P, -n) with -n < 0 => (field_neg(x'), y') where (x',y') = scalar_mul(P, n as nat)
        assert((-(-n)) as nat == n as nat);
    } else if n == 0 {
        // LHS: neg(scalar_mul(P, 0)) = neg(identity) = (field_neg(0), 1)
        // RHS: scalar_mul(P, 0) = (0, 1)
        reveal_with_fuel(edwards_scalar_mul, 1);
        p_gt_2();
        lemma_small_mod(0nat, p());
        // field_neg(0) = (p - 0%p) % p = p % p = 0
        lemma_mod_self_0(p() as int);
    } else {
        // n < 0: LHS = neg(neg(scalar_mul(P, |n|))) = (field_neg(field_neg(x)), y)
        //         RHS = scalar_mul(P, |n|) = (x, y)
        let (x, _y) = edwards_scalar_mul(P, (-n) as nat);
        lemma_edwards_scalar_mul_canonical(P, (-n) as nat);
        lemma_field_neg_neg(x);
        lemma_small_mod(x, p());
    }
}

/// Axiom: [a]P + [b]P = [a+b]P for signed scalars a, b.
///
/// This is the group law for scalar multiplication linearity (group homomorphism property).
pub proof fn axiom_edwards_scalar_mul_signed_additive(P: (nat, nat), a: int, b: int)
    ensures
        ({
            let pa = edwards_scalar_mul_signed(P, a);
            let pb = edwards_scalar_mul_signed(P, b);
            edwards_add(pa.0, pa.1, pb.0, pb.1)
        }) == edwards_scalar_mul_signed(P, a + b),
{
    admit();
}

/// Lemma: [b]([a]P) = [a*b]P for signed a, unsigned b.
/// Proved using the unsigned composition lemma and axiom_scalar_mul_distributes_over_neg.
pub proof fn lemma_edwards_scalar_mul_signed_composition(P: (nat, nat), a: int, b: nat)
    ensures
        edwards_scalar_mul(edwards_scalar_mul_signed(P, a), b) == edwards_scalar_mul_signed(
            P,
            a * (b as int),
        ),
{
    reveal(edwards_scalar_mul_signed);
    if a >= 0 {
        // a >= 0: both sides use unsigned scalar_mul
        let an = a as nat;
        lemma_edwards_scalar_mul_composition(P, an, b);
        assert(a * (b as int) >= 0) by {
            lemma_mul_nonnegative(a, b as int);
        }
        assert((a * (b as int)) as nat == an * b) by {
            lemma_mul_is_commutative(a, b as int);
        }
    } else {
        // a < 0: LHS = [b](-[|a|]P), RHS = -[|a|*b]P
        let abs_a = (-a) as nat;
        let (x, y) = edwards_scalar_mul(P, abs_a);

        // LHS: [b]((neg_x, y)) where (x, y) = [|a|]P
        // By axiom: [b](-Q) = -([b]Q)
        axiom_scalar_mul_distributes_over_neg(edwards_scalar_mul(P, abs_a), b);

        // [b]([|a|]P) = [|a|*b]P by unsigned composition
        lemma_edwards_scalar_mul_composition(P, abs_a, b);

        // a * b <= 0 since a < 0 and b >= 0
        // So RHS = -[|a*b|]P = -[|a|*b]P (or identity if b = 0)
        if b == 0 {
            // Special case: both sides are identity
            reveal_with_fuel(edwards_scalar_mul, 1);
            assert(a * (b as int) == 0) by {
                lemma_mul_by_zero_is_zero(a);
            }
        } else {
            // a < 0 and b > 0, so a * b < 0
            assert(a * (b as int) < 0) by {
                lemma_mul_strictly_positive(-a, b as int);
                lemma_mul_unary_negation(a, b as int);
            }
            assert((-(a * (b as int))) as nat == abs_a * b) by {
                lemma_mul_unary_negation(a, b as int);
            }
        }
    }
}

/// Lemma: Scalar multiplication is additive in the scalar for positive scalars:
///
///   [m]P + [n]P = [m+n]P, for m,n ≥ 1.
pub proof fn lemma_edwards_scalar_mul_additive(point_affine: (nat, nat), m: nat, n: nat)
    requires
        m >= 1,
        n >= 1,
    ensures
        ({
            let pm = edwards_scalar_mul(point_affine, m);
            let pn = edwards_scalar_mul(point_affine, n);
            edwards_add(pm.0, pm.1, pn.0, pn.1)
        }) == edwards_scalar_mul(point_affine, m + n),
    decreases n,
{
    if n == 1 {
        lemma_edwards_scalar_mul_succ(point_affine, m);
        assert(edwards_scalar_mul(point_affine, m + 1) == {
            let pm = edwards_scalar_mul(point_affine, m);
            edwards_add(pm.0, pm.1, point_affine.0, point_affine.1)
        });
        assert(edwards_scalar_mul(point_affine, 1) == point_affine) by {
            reveal_with_fuel(edwards_scalar_mul, 1);
        }
    } else {
        let nm1 = (n - 1) as nat;
        assert(nm1 >= 1);

        let pm = edwards_scalar_mul(point_affine, m);
        let pnm1 = edwards_scalar_mul(point_affine, nm1);
        let pn = edwards_scalar_mul(point_affine, n);
        let pm_plus_nm1 = edwards_scalar_mul(point_affine, m + nm1);

        // pn == [n-1]P + P by successor lemma (n == nm1 + 1)
        assert(pn == edwards_add(pnm1.0, pnm1.1, point_affine.0, point_affine.1)) by {
            lemma_edwards_scalar_mul_succ(point_affine, nm1);
        }

        // By associativity: [m]P + ([n-1]P + P) == ([m]P + [n-1]P) + P
        assert(edwards_add(
            pm.0,
            pm.1,
            edwards_add(pnm1.0, pnm1.1, point_affine.0, point_affine.1).0,
            edwards_add(pnm1.0, pnm1.1, point_affine.0, point_affine.1).1,
        ) == {
            let left = edwards_add(pm.0, pm.1, pnm1.0, pnm1.1);
            edwards_add(left.0, left.1, point_affine.0, point_affine.1)
        }) by {
            axiom_edwards_add_associative(
                pm.0,
                pm.1,
                pnm1.0,
                pnm1.1,
                point_affine.0,
                point_affine.1,
            );
        }

        // By IH: [m]P + [n-1]P == [m+n-1]P
        assert(edwards_add(pm.0, pm.1, pnm1.0, pnm1.1) == pm_plus_nm1) by {
            lemma_edwards_scalar_mul_additive(point_affine, m, nm1);
        }

        // By successor: [m+n-1]P + P == [m+n]P
        assert(edwards_add(pm_plus_nm1.0, pm_plus_nm1.1, point_affine.0, point_affine.1)
            == edwards_scalar_mul(point_affine, m + n)) by {
            lemma_edwards_scalar_mul_succ(point_affine, m + nm1);
        }
    }
}

/// Proves that `edwards_scalar_mul(edwards_scalar_mul(P, a), b) == edwards_scalar_mul(P, a * b)`
///
/// This is the scalar multiplication composition lemma: applying scalar multiplication twice
/// composes multiplicatively. The proof uses `lemma_edwards_scalar_mul_additive` for the odd-b
/// case, which in turn relies on `axiom_edwards_add_associative`.
pub proof fn lemma_edwards_scalar_mul_composition(point_affine: (nat, nat), a: nat, b: nat)
    ensures
        edwards_scalar_mul(edwards_scalar_mul(point_affine, a), b) == edwards_scalar_mul(
            point_affine,
            a * b,
        ),
    decreases b,
{
    // The proof proceeds by induction on b:
    // - The `b % 2 == 0` case unfolds to doubling and uses the induction hypothesis.
    // - The `b % 2 == 1` case uses `lemma_edwards_scalar_mul_additive` to rewrite
    //   [b]Q = [b-1]Q + Q, then applies the IH.
    if a == 0 {
        // Special case: [b]([0]P) == [0]P for all b.
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(edwards_scalar_mul(point_affine, 0) == edwards_identity());
        assert(a * b == 0);

        if b == 0 {
            // Both sides are scalar_mul(_, 0) == identity.
        } else if b == 1 {
            // scalar_mul(identity, 1) == identity.
            assert(edwards_scalar_mul(edwards_identity(), 1) == edwards_identity());
        } else if b % 2 == 0 {
            let hb = (b / 2) as nat;
            lemma_edwards_scalar_mul_composition(point_affine, 0, hb);

            // Unfold the left at even b: [b]I = double([b/2]I).
            assert(edwards_scalar_mul(edwards_scalar_mul(point_affine, 0), b) == {
                let half = edwards_scalar_mul(edwards_scalar_mul(point_affine, 0), hb);
                edwards_double(half.0, half.1)
            });

            // IH gives [b/2]I == I.
            let half = edwards_scalar_mul(edwards_scalar_mul(point_affine, 0), hb);
            assert(half == edwards_identity());

            // double(I) == I
            assert(edwards_double(half.0, half.1) == edwards_identity()) by {
                lemma_edwards_double_identity();
            }
        } else {
            // Odd b (>1): [b]I = [b-1]I + I, but [b-1]I = I, so this is I + I = I.
            let bm1 = (b - 1) as nat;
            lemma_edwards_scalar_mul_composition(point_affine, 0, bm1);

            let prev = edwards_scalar_mul(edwards_scalar_mul(point_affine, 0), bm1);
            assert(prev == edwards_identity());

            // I + I == I (identity added to itself is identity)
            assert(edwards_add(0, 1, 0, 1) == edwards_identity()) by {
                lemma_edwards_double_identity();
            }
        }
    } else if b == 0 {
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(a * b == 0);
    } else if b == 1 {
        // [1]([a]P) == [a]P and [a*1]P == [a]P
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(a * b == a);
    } else if b % 2 == 0 {
        let hb = (b / 2) as nat;
        lemma_edwards_scalar_mul_composition(point_affine, a, hb);

        // Unfold LHS at even b.
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(edwards_scalar_mul(edwards_scalar_mul(point_affine, a), b) == {
            let half = edwards_scalar_mul(edwards_scalar_mul(point_affine, a), hb);
            edwards_double(half.0, half.1)
        });

        // Unfold RHS at n = a*b, which is even since b is even.
        assert((a * b) % 2 == 0) by {
            lemma_mul_mod_noop_right(a as int, b as int, 2);
            assert((a * b) % 2 == (a * (b % 2)) % 2);
            assert(b % 2 == 0);
            assert(a * (b % 2) == 0) by {
                lemma_mul_by_zero_is_zero(a as int);
            }
            assert(0nat % 2 == 0);
        }

        // Compute (a*b)/2 = a*(b/2) (valid since b is even).
        assert((a * b) / 2 == a * hb) by {
            // b = (b/2)*2 + b%2, and b%2=0, so b == hb * 2
            lemma_fundamental_div_mod(b as int, 2);
            lemma_mul_is_associative(a as int, hb as int, 2);
            lemma_div_by_multiple((a * hb) as int, 2);
        }

        assert(a * b != 0) by {
            lemma_mul_nonzero(a as int, b as int);
        }
        // a * b is even (since b is even), so a * b != 1
        assert(a * b != 1);

        assert(edwards_scalar_mul(point_affine, a * b) == {
            let half = edwards_scalar_mul(point_affine, ((a * b) / 2) as nat);
            edwards_double(half.0, half.1)
        });

        // Put it together using the IH.
        calc! {
            (==)
            edwards_scalar_mul(edwards_scalar_mul(point_affine, a), b); (==) {
                // Unfolded above.
            }
            {
                let half = edwards_scalar_mul(edwards_scalar_mul(point_affine, a), hb);
                edwards_double(half.0, half.1)
            }; (==) {
                assert(edwards_scalar_mul(edwards_scalar_mul(point_affine, a), hb)
                    == edwards_scalar_mul(point_affine, a * hb));
            }
            {
                let half = edwards_scalar_mul(point_affine, a * hb);
                edwards_double(half.0, half.1)
            }; (==) {
                assert(((a * b) / 2) as nat == a * hb);
            }
            edwards_scalar_mul(point_affine, a * b);
        }
    } else {
        // Odd b (>1): use linearity of scalar multiplication in the scalar.
        let bm1 = (b - 1) as nat;
        lemma_edwards_scalar_mul_composition(point_affine, a, bm1);

        let pa = edwards_scalar_mul(point_affine, a);
        let prev = edwards_scalar_mul(pa, bm1);

        // Unfold LHS at odd b: [b]([a]P) = [b-1]([a]P) + [a]P.
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(b != 0 && b != 1);
        assert(b % 2 != 0);
        assert(edwards_scalar_mul(pa, b) == edwards_add(prev.0, prev.1, pa.0, pa.1));

        // Induction hypothesis: [b-1]([a]P) = [a*(b-1)]P.
        assert(prev == edwards_scalar_mul(point_affine, a * bm1)) by {
            assert(edwards_scalar_mul(edwards_scalar_mul(point_affine, a), bm1)
                == edwards_scalar_mul(point_affine, a * bm1));
        }

        // Scalar-mul additivity for positive scalars: [a*(b-1)]P + [a]P = [a*b]P.
        assert(a >= 1);
        assert(bm1 >= 1);
        assert(a * bm1 >= 1) by {
            lemma_mul_nonzero(a as int, bm1 as int);
        }

        // b == bm1 + 1, so a * bm1 + a == a * (bm1 + 1) == a * b
        assert(a * bm1 + a == a * b) by {
            lemma_mul_is_distributive_add(a as int, bm1 as int, 1);
            lemma_mul_basics(a as int);
        }

        calc! {
            (==)
            edwards_scalar_mul(edwards_scalar_mul(point_affine, a), b); (==) {
                assert(edwards_scalar_mul(edwards_scalar_mul(point_affine, a), b)
                    == edwards_scalar_mul(pa, b));
            }
            edwards_scalar_mul(pa, b); (==) {}
            edwards_add(prev.0, prev.1, pa.0, pa.1); (==) {
                assert(prev == edwards_scalar_mul(point_affine, a * bm1));
            }
            edwards_add(
                edwards_scalar_mul(point_affine, a * bm1).0,
                edwards_scalar_mul(point_affine, a * bm1).1,
                edwards_scalar_mul(point_affine, a).0,
                edwards_scalar_mul(point_affine, a).1,
            ); (==) {
                // [a*(b-1)]P + [a]P = [a*(b-1) + a]P by scalar-mul additivity
                lemma_edwards_scalar_mul_additive(point_affine, a * bm1, a);
            }
            edwards_scalar_mul(point_affine, a * bm1 + a); (==) {
                assert(a * bm1 + a == a * b);
            }
            edwards_scalar_mul(point_affine, a * b);
        }
    }
}

/// Lemma: P + O = P (group identity law) for reduced points.
/// The identity point is (0, 1) in affine coordinates.
pub proof fn lemma_edwards_add_identity_right_canonical(P: (nat, nat))
    requires
        P.0 < p(),
        P.1 < p(),
    ensures
        edwards_add(P.0, P.1, 0, 1) == P,
{
    lemma_edwards_add_identity_right(P.0, P.1);
    lemma_small_mod(P.0, p());
    lemma_small_mod(P.1, p());
}

/// Lemma: edwards_scalar_mul always produces reduced coordinates (< p()).
/// This follows from the fact that edwards_add/edwards_double use field_* operations
/// which always return results mod p().
pub proof fn lemma_edwards_scalar_mul_canonical(point_affine: (nat, nat), n: nat)
    requires
        point_affine.0 < p(),
        point_affine.1 < p(),
    ensures
        edwards_scalar_mul(point_affine, n).0 < p(),
        edwards_scalar_mul(point_affine, n).1 < p(),
    decreases n,
{
    p_gt_2();
    if n == 0 {
        reveal_with_fuel(edwards_scalar_mul, 1);
        // identity is (0, 1), both < p()
    } else if n == 1 {
        reveal_with_fuel(edwards_scalar_mul, 1);
        // result is point_affine, which is reduced by precondition
    } else if n % 2 == 0 {
        reveal_with_fuel(edwards_scalar_mul, 1);
        let half = edwards_scalar_mul(point_affine, (n / 2) as nat);
        lemma_edwards_scalar_mul_canonical(point_affine, (n / 2) as nat);
        // edwards_double returns field_mul results which are < p()
        lemma_edwards_add_canonical(half.0, half.1, half.0, half.1);
    } else {
        reveal_with_fuel(edwards_scalar_mul, 1);
        let prev = edwards_scalar_mul(point_affine, (n - 1) as nat);
        lemma_edwards_scalar_mul_canonical(point_affine, (n - 1) as nat);
        // edwards_add returns field_mul results which are < p()
        lemma_edwards_add_canonical(prev.0, prev.1, point_affine.0, point_affine.1);
    }
}

/// Lemma: edwards_scalar_mul_signed always returns canonical coordinates (< p()).
/// This follows from the definition: either edwards_scalar_mul (induction) or neg + edwards_scalar_mul.
pub proof fn lemma_edwards_scalar_mul_signed_canonical(point_affine: (nat, nat), n: int)
    requires
        point_affine.0 < p(),
        point_affine.1 < p(),
    ensures
        edwards_scalar_mul_signed(point_affine, n).0 < p(),
        edwards_scalar_mul_signed(point_affine, n).1 < p(),
{
    reveal(edwards_scalar_mul_signed);
    if n >= 0 {
        lemma_edwards_scalar_mul_canonical(point_affine, n as nat);
    } else {
        lemma_edwards_scalar_mul_canonical(point_affine, (-n) as nat);
        // neg(x) = (p - x%p) % p, so < p
        p_gt_2();
        let (x, y) = edwards_scalar_mul(point_affine, (-n) as nat);
        lemma_mod_bound((p() - (x % p())) as int, p() as int);
    }
}

/// Lemma: edwards_add always produces reduced coordinates (< p()).
pub proof fn lemma_edwards_add_canonical(x1: nat, y1: nat, x2: nat, y2: nat)
    ensures
        edwards_add(x1, y1, x2, y2).0 < p(),
        edwards_add(x1, y1, x2, y2).1 < p(),
{
    // edwards_add computes x3 = field_mul(...) and y3 = field_mul(...)
    // field_mul(a, b) = (a * b) % p(), so result is always < p()
    p_gt_2();
    lemma_mod_bound(
        field_add(field_mul(x1, y2), field_mul(y1, x2)) as int * field_inv(
            field_add(
                1,
                field_mul(
                    fe51_as_canonical_nat(&EDWARDS_D),
                    field_mul(field_mul(x1, x2), field_mul(y1, y2)),
                ),
            ),
        ) as int,
        p() as int,
    );
    lemma_mod_bound(
        field_add(field_mul(y1, y2), field_mul(x1, x2)) as int * field_inv(
            field_sub(
                1,
                field_mul(
                    fe51_as_canonical_nat(&EDWARDS_D),
                    field_mul(field_mul(x1, x2), field_mul(y1, y2)),
                ),
            ),
        ) as int,
        p() as int,
    );
}

// =============================================================================
// AffineNiels Point Conversion Lemmas
// =============================================================================
/// Lemma: identity_affine_niels decodes to the identity point (0, 1).
///
/// The identity in AffineNiels representation has y_plus_x = y_minus_x = 1,
/// which decodes to x = (1-1)/2 = 0 and y = (1+1)/2 = 1.
pub proof fn lemma_identity_affine_niels_is_identity()
    ensures
        affine_niels_point_as_affine_edwards(identity_affine_niels()) == edwards_identity(),
{
    let id = identity_affine_niels();
    let y_plus_x = fe51_as_canonical_nat(&id.y_plus_x);
    let y_minus_x = fe51_as_canonical_nat(&id.y_minus_x);

    assert(y_plus_x == 1) by {
        lemma_fe51_unit_is_one(&id.y_plus_x);
    }
    assert(y_minus_x == 1) by {
        lemma_fe51_unit_is_one(&id.y_minus_x);
    }

    // x = (y_plus_x - y_minus_x) * inv(2) = (1 - 1) * inv(2) = 0 * inv(2) = 0
    let diff = field_sub(y_plus_x, y_minus_x);
    assert(diff == 0) by {
        // field_sub(1, 1) = (((1 % p) + p) - (1 % p)) % p = (1 + p - 1) % p = p % p = 0
        p_gt_2();
        lemma_small_mod(1nat, p());
        lemma_mod_self_0(p() as int);
    }
    let x = field_mul(diff, field_inv(2));
    assert(x == 0) by {
        // diff == 0, so diff % p() == 0
        p_gt_2();
        lemma_small_mod(0nat, p());
        assert(diff % p() == 0);
        lemma_field_mul_zero_left(diff, field_inv(2));
    }

    // y = (y_plus_x + y_minus_x) * inv(2) = (1 + 1) * inv(2) = 2 * inv(2) = 1
    let sum = field_add(y_plus_x, y_minus_x);
    assert(sum == 2) by {
        // field_add(1, 1) = (1 + 1) % p = 2 (since 2 < p)
        p_gt_2();
        lemma_small_mod(2nat, p());
    }
    let y = field_mul(sum, field_inv(2));
    assert(y == 1) by {
        // 2 * inv(2) = 1 by field_inv_property
        p_gt_2();
        assert(2nat % p() != 0) by {
            lemma_small_mod(2nat, p());
        }
        field_inv_property(2nat);
        lemma_field_mul_comm(2nat, field_inv(2));
    }
}

/// Lemma: the identity AffineNielsPoint is valid (corresponds to a valid EdwardsPoint).
pub proof fn lemma_identity_affine_niels_valid()
    ensures
        is_valid_affine_niels_point(identity_affine_niels()),
{
    let id = identity_affine_niels();
    let zero_fe = FieldElement51 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
    let one_fe = FieldElement51 { limbs: [1u64, 0u64, 0u64, 0u64, 0u64] };

    // Witness: identity EdwardsPoint (X=0, Y=1, Z=1, T=0)
    let witness = crate::edwards::EdwardsPoint { X: zero_fe, Y: one_fe, Z: one_fe, T: zero_fe };

    assert(p() > 2) by {
        p_gt_2();
    }
    assert(1u64 < (1u64 << 52u64)) by (bit_vector);
    assert(fe51_limbs_bounded(&zero_fe, 52u64));
    assert(fe51_limbs_bounded(&one_fe, 52u64));
    assert(sum_of_limbs_bounded(&one_fe, &zero_fe, u64::MAX)) by {
        assert forall|i: int| 0 <= i < 5 implies one_fe.limbs[i] + zero_fe.limbs[i] < u64::MAX by {}
    }

    // Witness is a valid EdwardsPoint
    lemma_unfold_edwards(witness);
    assert(fe51_as_canonical_nat(&zero_fe) == 0) by {
        lemma_small_mod(0nat, p());
    }
    assert(fe51_as_canonical_nat(&one_fe) == 1) by {
        lemma_small_mod(1nat, p());
    }
    assert(is_valid_edwards_point(witness)) by {
        lemma_identity_is_valid_extended();
    }

    // Affine coordinates: z_inv = field_inv(1) = 1, x = 0, y = 1
    assert(field_inv(1nat) == 1) by {
        lemma_field_inv_one();
    }
    assert(field_mul(0nat, 1nat) == 0) by {
        lemma_field_mul_zero_left(0nat, 1nat);
    }
    assert(field_mul(1nat, 1nat) == 1) by {
        lemma_field_mul_one_right(1nat);
        lemma_small_mod(1nat, p());
    }

    // Correspondence field by field
    assert(fe51_as_canonical_nat(&id.y_plus_x) == 1) by {
        lemma_fe51_unit_is_one(&id.y_plus_x);
    }
    assert(fe51_as_canonical_nat(&id.y_minus_x) == 1) by {
        lemma_fe51_unit_is_one(&id.y_minus_x);
    }
    assert(fe51_as_canonical_nat(&id.xy2d) == 0) by {
        lemma_small_mod(0nat, p());
    }

    assert(field_add(1nat, 0nat) == 1) by {
        lemma_small_mod(1nat, p());
    }
    assert(field_sub(1nat, 0nat) == 1) by {
        p_gt_2();
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1, 1, p() as int);
    }
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    assert(field_mul(field_mul(field_mul(0nat, 1nat), 2nat), d) == 0) by {
        lemma_field_mul_zero_left(0nat, 1nat);
        lemma_field_mul_zero_left(0nat, 2nat);
        lemma_field_mul_zero_left(0nat, d);
    }

    assert(affine_niels_corresponds_to_edwards(id, witness));
}

/// Lemma: negating a valid AffineNielsPoint preserves validity.
pub proof fn lemma_negate_affine_niels_preserves_validity(pt: AffineNielsPoint)
    requires
        is_valid_affine_niels_point(pt),
        fe51_limbs_bounded(&pt.y_plus_x, 54),
        fe51_limbs_bounded(&pt.y_minus_x, 54),
        fe51_limbs_bounded(&pt.xy2d, 54),
    ensures
        is_valid_affine_niels_point(negate_affine_niels(pt)),
{
    let neg = negate_affine_niels(pt);
    assert(p() > 2) by {
        p_gt_2();
    }

    // Extract witness from is_valid_affine_niels_point(pt).
    // The strengthened existential gives us limb bounds and sum_of_limbs directly.
    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && edwards_point_limbs_bounded(ep) && sum_of_limbs_bounded(
            &edwards_y(ep),
            &edwards_x(ep),
            u64::MAX,
        ) && #[trigger] affine_niels_corresponds_to_edwards(pt, ep);
    lemma_unfold_edwards(ep);

    let xp = fe51_as_canonical_nat(&ep.X);
    let yp = fe51_as_canonical_nat(&ep.Y);
    let zp = fe51_as_canonical_nat(&ep.Z);
    let tp = fe51_as_canonical_nat(&ep.T);
    let z_inv = field_inv(zp);
    let x = field_mul(xp, z_inv);
    let y = field_mul(yp, z_inv);

    // Negate X and T limbs; 52-bounded => 54-bounded for negate precondition
    let neg_x_limbs = spec_negate(ep.X.limbs);
    let neg_t_limbs = spec_negate(ep.T.limbs);
    let ep_x_fe = FieldElement51 { limbs: ep.X.limbs };
    let ep_t_fe = FieldElement51 { limbs: ep.T.limbs };
    lemma_fe51_limbs_bounded_weaken(&ep_x_fe, 52, 54);
    lemma_fe51_limbs_bounded_weaken(&ep_t_fe, 52, 54);
    lemma_neg_no_underflow(ep.X.limbs);
    lemma_neg_no_underflow(ep.T.limbs);
    proof_negate(ep.X.limbs);
    proof_negate(ep.T.limbs);

    let neg_x_fe = FieldElement51 { limbs: neg_x_limbs };
    let neg_t_fe = FieldElement51 { limbs: neg_t_limbs };
    assert(fe51_limbs_bounded(&neg_x_fe, 52u64)) by {
        assert forall|i: int| 0 <= i < 5 implies #[trigger] neg_x_fe.limbs[i] < (1u64 << 52u64) by {
            assert(spec_negate(ep.X.limbs)[i] < (1u64 << 52u64));
        }
    }
    assert(fe51_limbs_bounded(&neg_t_fe, 52u64)) by {
        assert forall|i: int| 0 <= i < 5 implies #[trigger] neg_t_fe.limbs[i] < (1u64 << 52u64) by {
            assert(spec_negate(ep.T.limbs)[i] < (1u64 << 52u64));
        }
    }
    assert(sum_of_limbs_bounded(&ep.Y, &neg_x_fe, u64::MAX)) by {
        assert forall|i: int| 0 <= i < 5 implies (#[trigger] ep.Y.limbs[i]) + neg_x_fe.limbs[i]
            < u64::MAX by {
            assert((1u64 << 52u64) + (1u64 << 52u64) < u64::MAX) by (bit_vector);
        }
    }

    // Connect spec_negate to field_neg at nat level
    lemma_neg(&ep_x_fe);
    lemma_neg(&ep_t_fe);
    let neg_xp = fe51_as_canonical_nat(&neg_x_fe);
    let neg_tp = fe51_as_canonical_nat(&neg_t_fe);
    assert(neg_xp == field_neg(xp));
    assert(neg_tp == field_neg(tp));

    // Negated point is on the curve: (-X)^2 = X^2
    assert(field_square(neg_xp) == field_square(xp)) by {
        lemma_neg_square_eq(xp);
        lemma_square_mod_noop(xp);
    }
    // Segre relation: field_mul(neg_X, Y) == field_mul(Z, neg_T)
    assert(is_valid_extended_edwards_point(neg_xp, yp, zp, neg_tp)) by {
        lemma_field_neg_mul_left(xp, yp);
        lemma_field_mul_comm(zp, neg_tp);
        lemma_field_neg_mul_left(tp, zp);
        lemma_field_mul_comm(tp, zp);
    }

    // Construct the negated EdwardsPoint witness
    let neg_ep = crate::edwards::EdwardsPoint { X: neg_x_fe, Y: ep.Y, Z: ep.Z, T: neg_t_fe };
    lemma_unfold_edwards(neg_ep);
    assert(is_valid_edwards_point(neg_ep));

    // Affine coordinates for negated witness
    let neg_x_affine = field_mul(neg_xp, z_inv);
    let neg_y_affine = field_mul(yp, z_inv);
    assert(neg_x_affine == field_neg(x)) by {
        lemma_field_neg_mul_left(xp, z_inv);
    }
    assert(neg_y_affine == y);
    let d = fe51_as_canonical_nat(&EDWARDS_D);

    // Condition 1: neg.y_plus_x = pt.y_minus_x encodes field_add(y, neg(x)) = field_sub(y, x)
    assert(fe51_as_canonical_nat(&neg.y_plus_x) == field_add(neg_y_affine, neg_x_affine)) by {
        lemma_field_sub_eq_add_neg(y, x);
    }

    // Condition 2: neg.y_minus_x = pt.y_plus_x encodes field_sub(y, neg(x)) = field_add(y, x)
    assert(fe51_as_canonical_nat(&neg.y_minus_x) == field_sub(neg_y_affine, neg_x_affine)) by {
        lemma_field_sub_eq_add_neg(y, field_neg(x));
        lemma_field_neg_neg(x);
        lemma_field_add_comm(y, x % p());
        lemma_field_add_canonical_left(x, y);
        lemma_field_add_comm(x, y);
    }

    // Condition 3: neg.xy2d = negate(pt.xy2d) encodes field_mul(field_mul(field_mul(neg_x, y), 2), d)
    let pt_xy2d_fe = FieldElement51 { limbs: pt.xy2d.limbs };
    lemma_neg_no_underflow(pt.xy2d.limbs);
    proof_negate(pt.xy2d.limbs);
    lemma_neg(&pt_xy2d_fe);
    let pt_xy2d_val = fe51_as_canonical_nat(&pt.xy2d);
    let neg_xy2d_fe = FieldElement51 { limbs: spec_negate(pt.xy2d.limbs) };
    let neg_xy2d_val = fe51_as_canonical_nat(&neg_xy2d_fe);
    assert(neg_xy2d_val == field_neg(pt_xy2d_val));
    assert(pt_xy2d_val == field_mul(field_mul(field_mul(x, y), 2), d));
    assert(neg_xy2d_val == field_mul(field_mul(field_mul(neg_x_affine, neg_y_affine), 2), d)) by {
        lemma_field_neg_mul_left(field_mul(field_mul(x, y), 2), d);
        lemma_field_neg_mul_left(field_mul(x, y), 2);
        lemma_field_neg_mul_left(x, y);
    }

    assert(edwards_point_limbs_bounded(neg_ep));
    lemma_unfold_edwards(neg_ep);
    assert(sum_of_limbs_bounded(&neg_ep.Y, &neg_ep.X, u64::MAX));
    assert(sum_of_limbs_bounded(&edwards_y(neg_ep), &edwards_x(neg_ep), u64::MAX));
    assert(affine_niels_corresponds_to_edwards(neg, neg_ep));
}

/// Lemma: negating an AffineNielsPoint negates the x-coordinate.
///
/// AffineNiels negation swaps y_plus_x and y_minus_x, which results in
/// negating the x-coordinate while preserving the y-coordinate.
pub proof fn lemma_negate_affine_niels_is_edwards_neg(pt: AffineNielsPoint)
    ensures
        affine_niels_point_as_affine_edwards(negate_affine_niels(pt)) == edwards_neg(
            affine_niels_point_as_affine_edwards(pt),
        ),
{
    // negate_affine_niels swaps y_plus_x and y_minus_x:
    //   neg.y_plus_x = pt.y_minus_x
    //   neg.y_minus_x = pt.y_plus_x
    let y_plus_x = fe51_as_canonical_nat(&pt.y_plus_x);
    let y_minus_x = fe51_as_canonical_nat(&pt.y_minus_x);
    let inv2 = field_inv(2);

    // Original point coords:
    let x = field_mul(field_sub(y_plus_x, y_minus_x), inv2);
    let y = field_mul(field_add(y_plus_x, y_minus_x), inv2);

    // Negated point coords (after swapping y_plus_x and y_minus_x):
    let x_neg = field_mul(field_sub(y_minus_x, y_plus_x), inv2);
    let y_neg = field_mul(field_add(y_minus_x, y_plus_x), inv2);

    // y' = y because field addition is commutative: (a + b) % p == (b + a) % p
    assert(y_neg == y) by {
        assert((y_minus_x + y_plus_x) == (y_plus_x + y_minus_x));
    }

    assert(x_neg == field_neg(x)) by {
        lemma_swap_sub_negates_mul(y_plus_x, y_minus_x, inv2);
    }
}

/// Lemma: identity_projective_niels decodes to the identity point (0, 1).
///
/// The identity in ProjectiveNiels has Y_plus_X = Y_minus_X = Z = 1, T2d = 0,
/// which decodes to x = (1-1)/2 / 1 = 0 and y = (1+1)/2 / 1 = 1.
pub proof fn lemma_identity_projective_niels_is_identity()
    ensures
        projective_niels_point_as_affine_edwards(identity_projective_niels()) == edwards_identity(),
{
    let id = identity_projective_niels();
    let y_plus_x = fe51_as_canonical_nat(&id.Y_plus_X);
    let y_minus_x = fe51_as_canonical_nat(&id.Y_minus_X);
    let z = fe51_as_canonical_nat(&id.Z);

    assert(y_plus_x == 1) by {
        lemma_fe51_unit_is_one(&id.Y_plus_X);
    }
    assert(y_minus_x == 1) by {
        lemma_fe51_unit_is_one(&id.Y_minus_X);
    }
    assert(z == 1) by {
        lemma_fe51_unit_is_one(&id.Z);
    }

    // x_proj = (1 - 1) / 2 = 0
    let diff = field_sub(y_plus_x, y_minus_x);
    assert(diff == 0) by {
        p_gt_2();
        lemma_small_mod(1nat, p());
        lemma_mod_self_0(p() as int);
    }
    let inv2 = field_inv(2);
    let x_proj = field_mul(diff, inv2);
    assert(x_proj == 0) by {
        p_gt_2();
        lemma_small_mod(0nat, p());
        lemma_field_mul_zero_left(diff, inv2);
    }

    // y_proj = (1 + 1) / 2 = 1
    let sum = field_add(y_plus_x, y_minus_x);
    assert(sum == 2) by {
        p_gt_2();
        lemma_small_mod(2nat, p());
    }
    let y_proj = field_mul(sum, inv2);
    assert(y_proj == 1) by {
        p_gt_2();
        assert(2nat % p() != 0) by {
            lemma_small_mod(2nat, p());
        }
        field_inv_property(2nat);
        lemma_field_mul_comm(2nat, field_inv(2));
    }

    // x = x_proj * z_inv = 0 * inv(1) = 0
    let z_inv = field_inv(z);
    assert(field_mul(x_proj, z_inv) == 0) by {
        p_gt_2();
        lemma_small_mod(0nat, p());
        lemma_field_mul_zero_left(x_proj, z_inv);
    }

    // y = y_proj * z_inv = 1 * inv(1) = 1
    // field_inv_property(1): field_mul(field_canonical(1), inv(1)) == 1
    // field_canonical(1) = 1 % p = 1 (since p > 2)
    p_gt_2();
    assert(1nat % p() != 0) by {
        lemma_small_mod(1nat, p());
    }
    field_inv_property(1nat);
    assert(field_canonical(1nat) == 1nat) by {
        lemma_small_mod(1nat, p());
    }
    // Now field_mul(1, field_inv(1)) == 1
    // Since y_proj == 1 and z_inv == field_inv(1), field_mul(y_proj, z_inv) == 1
}

/// Lemma: negating a ProjectiveNielsPoint negates the x-coordinate.
///
/// ProjectiveNiels negation swaps Y_plus_X and Y_minus_X (and negates T2d, keeps Z).
/// This swaps (Y+X) and (Y-X), negating the recovered x-coordinate while preserving y.
pub proof fn lemma_negate_projective_niels_is_edwards_neg(
    pt: crate::backend::serial::curve_models::ProjectiveNielsPoint,
)
    ensures
        projective_niels_point_as_affine_edwards(negate_projective_niels(pt)) == edwards_neg(
            projective_niels_point_as_affine_edwards(pt),
        ),
{
    let y_plus_x = fe51_as_canonical_nat(&pt.Y_plus_X);
    let y_minus_x = fe51_as_canonical_nat(&pt.Y_minus_X);
    let z = fe51_as_canonical_nat(&pt.Z);
    let inv2 = field_inv(2);
    let z_inv = field_inv(z);

    // Original point coords
    let x_proj = field_mul(field_sub(y_plus_x, y_minus_x), inv2);
    let y_proj = field_mul(field_add(y_plus_x, y_minus_x), inv2);
    let x = field_mul(x_proj, z_inv);
    let y = field_mul(y_proj, z_inv);

    // Negated point: swaps Y_plus_X and Y_minus_X, Z unchanged
    let x_proj_neg = field_mul(field_sub(y_minus_x, y_plus_x), inv2);
    let y_proj_neg = field_mul(field_add(y_minus_x, y_plus_x), inv2);
    let x_neg = field_mul(x_proj_neg, z_inv);
    let y_neg = field_mul(y_proj_neg, z_inv);

    // y' = y: field_add is commutative
    assert(y_proj_neg == y_proj) by {
        assert((y_minus_x + y_plus_x) == (y_plus_x + y_minus_x));
    }
    assert(y_neg == y);

    assert(x_proj_neg == field_neg(x_proj)) by {
        lemma_swap_sub_negates_mul(y_plus_x, y_minus_x, inv2);
    }
    assert(x_neg == field_neg(x)) by {
        lemma_field_mul_neg(z_inv, x_proj);
        lemma_field_mul_comm(field_neg(x_proj), z_inv);
        lemma_field_mul_comm(x_proj, z_inv);
    }
}

/// Lemma: the identity ProjectiveNielsPoint is valid (corresponds to a valid EdwardsPoint).
pub proof fn lemma_identity_projective_niels_valid()
    ensures
        is_valid_projective_niels_point(identity_projective_niels()),
{
    let id = identity_projective_niels();
    let zero_fe = FieldElement51 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
    let one_fe = FieldElement51 { limbs: [1u64, 0u64, 0u64, 0u64, 0u64] };

    // Witness: identity EdwardsPoint (X=0, Y=1, Z=1, T=0)
    let witness = crate::edwards::EdwardsPoint { X: zero_fe, Y: one_fe, Z: one_fe, T: zero_fe };

    assert(p() > 2) by {
        p_gt_2();
    }
    assert(1u64 < (1u64 << 52u64)) by (bit_vector);
    assert(fe51_limbs_bounded(&zero_fe, 52u64));
    assert(fe51_limbs_bounded(&one_fe, 52u64));

    // Witness is a valid EdwardsPoint
    lemma_unfold_edwards(witness);
    assert(fe51_as_canonical_nat(&zero_fe) == 0) by {
        lemma_small_mod(0nat, p());
    }
    assert(fe51_as_canonical_nat(&one_fe) == 1) by {
        lemma_small_mod(1nat, p());
    }
    assert(is_valid_edwards_point(witness)) by {
        lemma_identity_is_valid_extended();
    }
    assert(edwards_point_limbs_bounded(witness));

    // Correspondence field by field
    assert(fe51_as_canonical_nat(&id.Y_plus_X) == 1) by {
        lemma_fe51_unit_is_one(&id.Y_plus_X);
    }
    assert(fe51_as_canonical_nat(&id.Y_minus_X) == 1) by {
        lemma_fe51_unit_is_one(&id.Y_minus_X);
    }
    assert(fe51_as_canonical_nat(&id.Z) == 1) by {
        lemma_fe51_unit_is_one(&id.Z);
    }
    assert(fe51_as_canonical_nat(&id.T2d) == 0) by {
        lemma_small_mod(0nat, p());
    }

    assert(field_add(1nat, 0nat) == 1) by {
        lemma_small_mod(1nat, p());
    }
    assert(field_sub(1nat, 0nat) == 1) by {
        p_gt_2();
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1, 1, p() as int);
    }
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    assert(field_mul(field_mul(2, d), 0nat) == 0) by {
        lemma_field_mul_comm(field_mul(2, d), 0nat);
        lemma_field_mul_zero_left(0nat, field_mul(2, d));
        lemma_small_mod(0nat, p());
    }

    assert(projective_niels_corresponds_to_edwards(id, witness));
}

/// Lemma: negating a valid ProjectiveNielsPoint preserves validity.
pub proof fn lemma_negate_projective_niels_preserves_validity(pt: ProjectiveNielsPoint)
    requires
        is_valid_projective_niels_point(pt),
        fe51_limbs_bounded(&pt.Y_plus_X, 54),
        fe51_limbs_bounded(&pt.Y_minus_X, 54),
        fe51_limbs_bounded(&pt.Z, 54),
        fe51_limbs_bounded(&pt.T2d, 54),
    ensures
        is_valid_projective_niels_point(negate_projective_niels(pt)),
{
    let neg = negate_projective_niels(pt);
    assert(p() > 2) by {
        p_gt_2();
    }

    // Extract witness from is_valid_projective_niels_point(pt)
    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && edwards_point_limbs_bounded(ep)
            && #[trigger] projective_niels_corresponds_to_edwards(pt, ep);
    lemma_unfold_edwards(ep);

    let xp = fe51_as_canonical_nat(&ep.X);
    let yp = fe51_as_canonical_nat(&ep.Y);
    let zp = fe51_as_canonical_nat(&ep.Z);
    let tp = fe51_as_canonical_nat(&ep.T);

    // Negate X and T limbs; 52-bounded => 54-bounded for negate precondition
    let ep_x_fe = FieldElement51 { limbs: ep.X.limbs };
    let ep_t_fe = FieldElement51 { limbs: ep.T.limbs };
    lemma_fe51_limbs_bounded_weaken(&ep_x_fe, 52, 54);
    lemma_fe51_limbs_bounded_weaken(&ep_t_fe, 52, 54);
    lemma_neg_no_underflow(ep.X.limbs);
    lemma_neg_no_underflow(ep.T.limbs);
    proof_negate(ep.X.limbs);
    proof_negate(ep.T.limbs);

    let neg_x_limbs = spec_negate(ep.X.limbs);
    let neg_t_limbs = spec_negate(ep.T.limbs);
    let neg_x_fe = FieldElement51 { limbs: neg_x_limbs };
    let neg_t_fe = FieldElement51 { limbs: neg_t_limbs };
    assert(fe51_limbs_bounded(&neg_x_fe, 52u64)) by {
        assert forall|i: int| 0 <= i < 5 implies #[trigger] neg_x_fe.limbs[i] < (1u64 << 52u64) by {
            assert(spec_negate(ep.X.limbs)[i] < (1u64 << 52u64));
        }
    }
    assert(fe51_limbs_bounded(&neg_t_fe, 52u64)) by {
        assert forall|i: int| 0 <= i < 5 implies #[trigger] neg_t_fe.limbs[i] < (1u64 << 52u64) by {
            assert(spec_negate(ep.T.limbs)[i] < (1u64 << 52u64));
        }
    }

    // Connect spec_negate to field_neg at nat level
    lemma_neg(&ep_x_fe);
    lemma_neg(&ep_t_fe);
    let neg_xp = fe51_as_canonical_nat(&neg_x_fe);
    let neg_tp = fe51_as_canonical_nat(&neg_t_fe);
    assert(neg_xp == field_neg(xp));
    assert(neg_tp == field_neg(tp));

    // Negated point is on the curve: (-X)^2 = X^2
    assert(field_square(neg_xp) == field_square(xp)) by {
        lemma_neg_square_eq(xp);
        lemma_square_mod_noop(xp);
    }
    // Segre relation: field_mul(neg_X, Y) == field_mul(Z, neg_T)
    assert(is_valid_extended_edwards_point(neg_xp, yp, zp, neg_tp)) by {
        lemma_field_neg_mul_left(xp, yp);
        lemma_field_mul_comm(zp, neg_tp);
        lemma_field_neg_mul_left(tp, zp);
        lemma_field_mul_comm(tp, zp);
    }

    // Construct the negated EdwardsPoint witness
    let neg_ep = crate::edwards::EdwardsPoint { X: neg_x_fe, Y: ep.Y, Z: ep.Z, T: neg_t_fe };
    lemma_unfold_edwards(neg_ep);
    assert(is_valid_edwards_point(neg_ep));
    assert(edwards_point_limbs_bounded(neg_ep));

    // Condition 1: neg.Y_plus_X == field_add(yp, neg_xp)
    // neg.Y_plus_X = pt.Y_minus_X (swapped), and pt.Y_minus_X == field_sub(yp, xp)
    assert(fe51_as_canonical_nat(&neg.Y_plus_X) == field_add(yp, neg_xp)) by {
        lemma_field_sub_eq_add_neg(yp, xp);
    }

    // Condition 2: neg.Y_minus_X == field_sub(yp, neg_xp)
    // neg.Y_minus_X = pt.Y_plus_X (swapped), and pt.Y_plus_X == field_add(yp, xp)
    assert(fe51_as_canonical_nat(&neg.Y_minus_X) == field_sub(yp, neg_xp)) by {
        lemma_field_sub_eq_add_neg(yp, field_neg(xp));
        lemma_field_neg_neg(xp);
        lemma_field_add_canonical_left(xp, yp);
        lemma_field_add_comm(xp, yp);
    }

    // Condition 3: neg.Z == zp (unchanged)

    // Condition 4: neg.T2d == field_mul(field_mul(2, d), neg_tp)
    let pt_t2d_fe = FieldElement51 { limbs: pt.T2d.limbs };
    lemma_neg_no_underflow(pt.T2d.limbs);
    proof_negate(pt.T2d.limbs);
    lemma_neg(&pt_t2d_fe);
    let pt_t2d_val = fe51_as_canonical_nat(&pt.T2d);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    assert(pt_t2d_val == field_mul(field_mul(2, d), tp));
    let neg_t2d_fe = FieldElement51 { limbs: spec_negate(pt.T2d.limbs) };
    let neg_t2d_val = fe51_as_canonical_nat(&neg_t2d_fe);
    assert(neg_t2d_val == field_neg(pt_t2d_val));
    assert(neg_t2d_val == field_mul(field_mul(2, d), neg_tp)) by {
        lemma_field_mul_neg(field_mul(2, d), tp);
        lemma_field_mul_comm(field_mul(2, d), field_neg(tp));
        lemma_field_mul_comm(field_mul(2, d), tp);
    }

    assert(projective_niels_corresponds_to_edwards(neg, neg_ep));
}

/// Helper: Recover x and y from the Niels encoding (y+x, y-x) via halving.
///
/// Given y_plus_x == field_add(y, x) and y_minus_x == field_sub(y, x):
///   - (y_plus_x - y_minus_x) / 2 == x % p()
///   - (y_plus_x + y_minus_x) / 2 == y % p()
proof fn lemma_recover_xy_from_niels_encoding(y_plus_x: nat, y_minus_x: nat, x: nat, y: nat)
    requires
        y_plus_x == field_add(y, x),
        y_minus_x == field_sub(y, x),
    ensures
        field_mul(field_sub(y_plus_x, y_minus_x), field_inv(2)) == x % p(),
        field_mul(field_add(y_plus_x, y_minus_x), field_inv(2)) == y % p(),
{
    // (y+x) - (y-x) = 2x
    assert(field_sub(y_plus_x, y_minus_x) == field_mul(2, x)) by {
        lemma_field_add_sub_recover_double(y, x);
    };
    // (2x) * inv(2) = x (mod p)
    assert(field_mul(field_sub(y_plus_x, y_minus_x), field_inv(2)) == x % p()) by {
        lemma_field_halve_double(x);
    };

    // (y+x) + (y-x) = 2y
    assert(field_add(y_plus_x, y_minus_x) == field_mul(2, y)) by {
        lemma_field_add_add_recover_double(y, x);
    };
    // (2y) * inv(2) = y (mod p)
    assert(field_mul(field_add(y_plus_x, y_minus_x), field_inv(2)) == y % p()) by {
        lemma_field_halve_double(y);
    };
}

/// Lemma: When a ProjectiveNielsPoint corresponds to an EdwardsPoint,
/// their affine representations are equal.
///
/// ## Mathematical Proof
///
/// Given `projective_niels_corresponds_to_edwards(niels, point)`:
/// - y_plus_x == Y + X
/// - y_minus_x == Y - X
/// - niels_z == Z
///
/// From `projective_niels_point_as_affine_edwards`:
/// - x_proj = (y_plus_x - y_minus_x) / 2 = ((Y+X) - (Y-X)) / 2 = 2X / 2 = X
/// - y_proj = (y_plus_x + y_minus_x) / 2 = ((Y+X) + (Y-X)) / 2 = 2Y / 2 = Y
/// - x_affine = x_proj / z = X / Z
/// - y_affine = y_proj / z = Y / Z
///
/// This equals `edwards_point_as_affine(point) = (X/Z, Y/Z)`.
pub proof fn lemma_projective_niels_affine_equals_edwards_affine(
    niels: crate::backend::serial::curve_models::ProjectiveNielsPoint,
    point: crate::edwards::EdwardsPoint,
)
    requires
        projective_niels_corresponds_to_edwards(niels, point),
        is_valid_edwards_point(point),
    ensures
        projective_niels_point_as_affine_edwards(niels) == edwards_point_as_affine(point),
{
    lemma_unfold_edwards(point);
    let x = fe51_as_canonical_nat(&point.X);
    let y = fe51_as_canonical_nat(&point.Y);
    let z = fe51_as_canonical_nat(&point.Z);

    let y_plus_x = fe51_as_canonical_nat(&niels.Y_plus_X);
    let y_minus_x = fe51_as_canonical_nat(&niels.Y_minus_X);
    let niels_z = fe51_as_canonical_nat(&niels.Z);

    assert(y_plus_x == field_add(y, x));
    assert(y_minus_x == field_sub(y, x));
    assert(niels_z == z);

    let inv2 = field_inv(2);
    let x_proj = field_mul(field_sub(y_plus_x, y_minus_x), inv2);
    let y_proj = field_mul(field_add(y_plus_x, y_minus_x), inv2);

    lemma_recover_xy_from_niels_encoding(y_plus_x, y_minus_x, x, y);

    // x < p and y < p since fe51_as_canonical_nat returns val % p
    assert(x < p()) by {
        p_gt_2();
        lemma_mod_bound(fe51_as_nat(&point.X) as int, p() as int);
    }
    assert(y < p()) by {
        p_gt_2();
        lemma_mod_bound(fe51_as_nat(&point.Y) as int, p() as int);
    }

    assert(x_proj == x) by {
        lemma_small_mod(x, p());
    }
    assert(y_proj == y) by {
        lemma_small_mod(y, p());
    }
}

// =============================================================================
// Axioms and lemmas for decompression and cofactor clearing
// =============================================================================
/// Lemma: On Ed25519, the x-coordinate is uniquely determined by y and parity.
///
/// The curve equation determines x² uniquely from y. Over F_p with p odd,
/// a nonzero square has exactly two roots with opposite parities, so the
/// parity constraint selects at most one. When x² = 0, x = 0 is unique.
///
/// Proof sketch:
///   1. Both (x1,y) and (x2,y) on curve => x1²·v = u = x2²·v where
///      u = y²-1 and v = d·y²+1.
///   2. If v ≠ 0: cancel v to get x1² = x2².
///      If v = 0: then u = 0 so x1² = x2² = 0.
///   3. x1²-x2² = (x1-x2)(x1+x2) = 0 in F_p.
///   4. F_p has no zero-divisors, so x1 = x2 or x1 = -x2 (mod p).
///   5. x1 = -x2 with x1,x2 < p means x2 = p-x1 (when x1≠0), but p odd
///      makes their parities opposite, contradicting x1%2 == x2%2.
pub proof fn lemma_unique_x_with_parity(x1: nat, x2: nat, y: nat)
    requires
        is_on_edwards_curve(x1, y),
        is_on_edwards_curve(x2, y),
        x1 < p(),
        x2 < p(),
        y < p(),
        x1 % 2 == x2 % 2,
    ensures
        x1 == x2,
{
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let x1sq = field_square(x1);
    let x2sq = field_square(x2);
    let y2 = field_square(y);
    let u = field_sub(y2, 1);
    let v = field_add(field_mul(d, y2), 1);
    p_gt_2();
    axiom_p_is_prime();

    // Both on the curve => x1²·v = u and x2²·v = u (field lemma)
    assert(field_mul(x1sq, v) == u) by {
        lemma_field_curve_eq_x2v_eq_u(d, x1, y);
    };
    assert(field_mul(x2sq, v) == u) by {
        lemma_field_curve_eq_x2v_eq_u(d, x2, y);
    };
    assert(field_mul(x1sq, v) == field_mul(x2sq, v));

    // Show x1² = x2²: either cancel v (if v ≠ 0) or derive contradiction (v = 0 impossible)
    if v % p() != 0 {
        assert(x1sq == x2sq) by {
            lemma_field_mul_comm(x1sq, v);
            lemma_field_mul_comm(x2sq, v);
            lemma_field_mul_left_cancel(v, x1sq, x2sq);
            assert(x1sq < p()) by {
                lemma_mod_bound((x1 * x1) as int, p() as int);
            };
            assert(x2sq < p()) by {
                lemma_mod_bound((x2 * x2) as int, p() as int);
            };
            lemma_small_mod(x1sq, p());
            lemma_small_mod(x2sq, p());
        };
    } else {
        // v % p == 0 => field_mul(x1sq, v) = 0 = u => y² = 1 => v = d+1 ≠ 0, contradiction
        assert(u == 0) by {
            lemma_field_mul_zero_right(x1sq, v);
        };
        assert(y2 < p()) by {
            lemma_mod_bound((y * y) as int, p() as int);
        };
        lemma_small_mod(y2, p());
        lemma_small_mod(1nat, p());
        // u = field_sub(y2, 1) = ((y2+p)-1) % p = 0
        // y2 + p - 1 is in [p-1, 2p-2] since y2 < p.
        // (y2+p-1) % p == 0 and p-1 <= y2+p-1 < 2p implies y2+p-1 == p, so y2 == 1.
        let su: int = (y2 + p() - 1) as int;
        let pu: int = p() as int;
        assert(su % pu == 0int);
        lemma_fundamental_div_mod(su, pu);
        assert(y2 == 1) by (nonlinear_arith)
            requires
                su == pu * (su / pu) + su % pu,
                su % pu == 0int,
                su == y2 as int + pu - 1,
                0 <= y2 as int,
                (y2 as int) < pu,
                pu > 1int,
        ;
        // field_mul(d, 1) = (d*1) % p = d % p
        assert(field_mul(d, y2) == d % p()) by {
            lemma_field_mul_one_right(d);
        };
        assert(v == field_add(d, 1)) by {
            lemma_field_add_canonical_left(d, 1);
        };
        crate::lemmas::field_lemmas::constants_lemmas::lemma_d_plus_one_nonzero();
        lemma_small_mod(v, p());
        assert(false);
    }

    assert(x1sq == x2sq);

    // x1² - x2² = (x1-x2)(x1+x2) = 0 in F_p
    assert(field_sub(x1sq, x2sq) == 0) by {
        lemma_field_sub_self(x1sq);
    };
    assert(field_mul(field_sub(x1, x2), field_add(x1, x2)) == 0) by {
        lemma_field_diff_of_squares(x1, x2);
    };

    if field_sub(x1, x2) % p() == 0 {
        // x1 ≡ x2 (mod p), both < p => x1 = x2
        assert(field_sub(x1, x2) < p()) by {
            lemma_mod_bound(((x1 % p() + p()) as int - (x2 % p()) as int) as int, p() as int);
        };
        lemma_small_mod(field_sub(x1, x2), p());
        assert(field_sub(x1, x2) == 0);
        assert(x1 == x2) by {
            lemma_small_mod(x1, p());
            lemma_small_mod(x2, p());
            lemma_field_add_sub_cancel(x1, x2);
            assert(field_add(0nat, x2) == x1);
        };
    } else {
        // x1+x2 ≡ 0 (mod p) by Euclid's lemma (no zero-divisors)
        let a = field_sub(x1, x2);
        let b = field_add(x1, x2);
        assert(a < p()) by {
            lemma_mod_bound(((x1 % p() + p()) as int - (x2 % p()) as int) as int, p() as int);
        };
        assert(b < p()) by {
            lemma_mod_bound((x1 + x2) as int, p() as int);
        };
        assert((a * b) % p() == 0) by {
            lemma_small_mod(a, p());
            lemma_small_mod(b, p());
            lemma_mul_mod_noop_left(a as int, b as int, p() as int);
            lemma_mul_mod_noop_right((a % p()) as int, b as int, p() as int);
        };
        assert((x1 + x2) % p() == 0) by {
            lemma_small_mod(a, p());
            lemma_small_mod(b, p());
            lemma_euclid_prime(a, b, p());
            lemma_small_mod(x1, p());
            lemma_small_mod(x2, p());
        };

        if x1 == 0 && x2 == 0 {
            assert(x1 == x2);
        } else {
            let s: int = (x1 + x2) as int;
            let pp: int = p() as int;
            lemma_fundamental_div_mod(s, pp);
            assert(x1 + x2 == p()) by (nonlinear_arith)
                requires
                    s == pp * (s / pp) + s % pp,
                    s % pp == 0int,
                    s == x1 as int + x2 as int,
                    pp == p() as int,
                    (x1 as int) >= 0,
                    (x2 as int) >= 0,
                    (x1 as int) < pp,
                    (x2 as int) < pp,
                    !(x1 as int == 0 && x2 as int == 0),
                    pp > 0,
            ;
            lemma_p_is_odd();
            assert(x1 % 2 != x2 % 2) by {
                assert((x1 + x2) % 2 == 1);
            };
            assert(false);
        }
    }
}

/// Lemma: A valid extended Edwards point lies on the affine curve.
///
/// If (X, Y, Z, T) is a valid extended Edwards point (Z ≠ 0 mod p, projective curve
/// equation holds, Segre relation X·Y = Z·T), then the affine coordinates (X/Z, Y/Z)
/// satisfy the Edwards curve equation -x² + y² = 1 + d·x²·y².
///
/// This is the converse of `lemma_affine_curve_implies_projective`.
///
/// Proof strategy: multiply the projective equation (y²-x²)·z² = z⁴ + d·x²·y² by
/// inv(z⁴) and simplify both sides to recover the affine equation.
pub proof fn lemma_valid_extended_point_affine_on_curve(x: nat, y: nat, z: nat, t: nat)
    requires
        is_valid_extended_edwards_point(x, y, z, t),
    ensures
        is_on_edwards_curve(field_mul(x, field_inv(z)), field_mul(y, field_inv(z))),
{
    let p = p();
    assert(p > 2) by {
        p_gt_2();
    };

    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let inv_z = field_inv(z);

    // Define affine coordinates: x/z, y/z
    let x_div_z = field_mul(x, inv_z);
    let y_div_z = field_mul(y, inv_z);

    // Squares of affine coordinates
    let x_div_z_sq = field_square(x_div_z);
    let y_div_z_sq = field_square(y_div_z);

    // Projective values
    let x2 = field_square(x);
    let y2 = field_square(y);
    let z2 = field_square(z);
    let z4 = field_square(z2);
    let inv_z2 = field_inv(z2);
    let inv_z4 = field_inv(z4);

    // From precondition: projective curve equation
    // proj_lhs = (y² - x²)·z²
    // proj_rhs = z⁴ + d·x²·y²
    let y2_minus_x2 = field_sub(y2, x2);
    let x2_y2 = field_mul(x2, y2);
    let proj_lhs = field_mul(y2_minus_x2, z2);
    let proj_rhs = field_add(z4, field_mul(d, x2_y2));
    assert(proj_lhs == proj_rhs);  // from is_on_edwards_curve_projective

    // === Establish z², z⁴ are nonzero in the field ===
    assert(z2 != 0 && z2 % p != 0) by {
        lemma_nonzero_product(z, z);
        assert(z2 < p) by {
            lemma_mod_bound((z * z) as int, p as int);
        };
        lemma_field_element_reduced(z2);
    };

    assert(z4 != 0 && z4 % p != 0) by {
        lemma_nonzero_product(z2, z2);
        assert(z4 < p) by {
            lemma_mod_bound((z2 * z2) as int, p as int);
        };
        lemma_field_element_reduced(z4);
    };

    // === STEP 1: Quotient of squares ===
    // (x/z)² = x²/z² = x²·inv(z²)
    assert(x_div_z_sq == field_mul(x2, inv_z2)) by {
        lemma_quotient_of_squares(x, z);
    };
    // (y/z)² = y²/z² = y²·inv(z²)
    assert(y_div_z_sq == field_mul(y2, inv_z2)) by {
        lemma_quotient_of_squares(y, z);
    };

    // === STEP 2: Affine LHS = (y/z)² - (x/z)² = (y²-x²)·inv(z²) ===
    let affine_lhs = field_sub(y_div_z_sq, x_div_z_sq);
    assert(affine_lhs == field_mul(y2_minus_x2, inv_z2)) by {
        lemma_field_mul_distributes_over_sub_right(y2, x2, inv_z2);
    };

    // === STEP 3: Affine RHS = 1 + d·(x/z)²·(y/z)² ===
    // First: inv(z²)·inv(z²) = inv(z⁴)
    assert(field_mul(inv_z2, inv_z2) == inv_z4) by {
        lemma_inv_of_product(z2, z2);
    };

    // (x/z)²·(y/z)² = x²·inv(z²)·y²·inv(z²) = x²·y²·inv(z⁴)
    let x2_y2_inv_z4 = field_mul(x2_y2, inv_z4);
    assert(field_mul(x_div_z_sq, y_div_z_sq) == x2_y2_inv_z4) by {
        lemma_field_mul_assoc(x2, inv_z2, field_mul(y2, inv_z2));
        lemma_field_mul_comm(inv_z2, field_mul(y2, inv_z2));
        lemma_field_mul_assoc(y2, inv_z2, inv_z2);
        lemma_field_mul_assoc(x2, y2, field_mul(inv_z2, inv_z2));
    };

    let affine_rhs = field_add(1, field_mul(d, field_mul(x_div_z_sq, y_div_z_sq)));
    assert(affine_rhs == field_add(1, field_mul(d, x2_y2_inv_z4)));

    // === STEP 4: Multiply projective equation by inv(z⁴) ===
    // proj_lhs == proj_rhs, so proj_lhs · inv(z⁴) == proj_rhs · inv(z⁴)

    // --- LHS: proj_lhs · inv(z⁴) = (y²-x²)·z²·inv(z⁴) = (y²-x²)·inv(z²) = affine_lhs ---
    // z²·inv(z⁴) = z²·inv(z²)·inv(z²) = inv(z²)
    // z2 · inv_z4 = inv_z2 (cancel one factor of z²)
    assert(field_mul(z2, inv_z4) == inv_z2) by {
        // inv_z4 = inv_z2 · inv_z2
        assert(inv_z4 == field_mul(inv_z2, inv_z2)) by {
            lemma_inv_of_product(z2, z2);
        };
        // z2 · (inv_z2 · inv_z2) = (z2 · inv_z2) · inv_z2
        lemma_field_mul_assoc(z2, inv_z2, inv_z2);
        // z2 · inv_z2 = 1
        assert(field_mul(z2, inv_z2) == 1) by {
            lemma_field_mul_comm(z2, inv_z2);
            lemma_inv_mul_cancel(z2);
        };
        // 1 · inv_z2 = inv_z2
        assert(field_mul(1, inv_z2) == inv_z2 % p) by {
            lemma_field_mul_one_left(inv_z2);
        };
        assert(inv_z2 < p) by {
            field_inv_property(z2);
        };
        assert(inv_z2 == inv_z2 % p) by {
            lemma_field_element_reduced(inv_z2);
        };
    };
    assert(field_mul(proj_lhs, inv_z4) == affine_lhs) by {
        lemma_field_mul_assoc(y2_minus_x2, z2, inv_z4);
    };

    // --- RHS: proj_rhs · inv(z⁴) = (z⁴ + d·x²y²)·inv(z⁴) = 1 + d·x²y²·inv(z⁴) = affine_rhs ---
    // inv(z⁴)·z⁴ = 1
    assert(field_mul(inv_z4, z4) == 1) by {
        lemma_inv_mul_cancel(z4);
    };
    // inv(z⁴)·(d·x²y²) = d·(x²y²·inv(z⁴)) = d·x2_y2_inv_z4
    assert(field_mul(inv_z4, field_mul(d, x2_y2)) == field_mul(d, x2_y2_inv_z4)) by {
        lemma_field_mul_assoc(inv_z4, d, x2_y2);
        lemma_field_mul_comm(inv_z4, d);
        lemma_field_mul_assoc(d, inv_z4, x2_y2);
        lemma_field_mul_comm(inv_z4, x2_y2);
    };
    // Distribute: (z⁴ + d·x²y²)·inv(z⁴) = z⁴·inv(z⁴) + d·x²y²·inv(z⁴) = 1 + d·x2_y2_inv_z4
    assert(field_mul(proj_rhs, inv_z4) == affine_rhs) by {
        lemma_field_mul_comm(proj_rhs, inv_z4);
        lemma_field_mul_distributes_over_add(inv_z4, z4, field_mul(d, x2_y2));
        lemma_small_mod(1nat, p);
    };

    // === STEP 5: Conclude affine_lhs == affine_rhs ===
    assert(affine_lhs == affine_rhs);
}

/// Lemma: When an AffineNielsPoint corresponds to an EdwardsPoint,
/// their affine representations are equal.
///
/// ## Mathematical Proof
///
/// Given `affine_niels_corresponds_to_edwards(niels, point)` with affine x = X/Z, y = Y/Z:
/// - y_plus_x == y + x
/// - y_minus_x == y - x
///
/// From `affine_niels_point_as_affine_edwards`:
/// - x_niels = (y_plus_x - y_minus_x) / 2 = ((y+x) - (y-x)) / 2 = 2x / 2 = x
/// - y_niels = (y_plus_x + y_minus_x) / 2 = ((y+x) + (y-x)) / 2 = 2y / 2 = y
///
/// This equals `edwards_point_as_affine(point) = (X/Z, Y/Z) = (x, y)`.
///
/// Note: Unlike the ProjectiveNiels case, AffineNiels stores affine sums (y+x, y-x)
/// rather than projective sums (Y+X, Y-X), so no division by Z is needed here.
pub proof fn lemma_affine_niels_affine_equals_edwards_affine(
    niels: crate::backend::serial::curve_models::AffineNielsPoint,
    point: crate::edwards::EdwardsPoint,
)
    requires
        affine_niels_corresponds_to_edwards(niels, point),
        is_valid_edwards_point(point),
    ensures
        affine_niels_point_as_affine_edwards(niels) == edwards_point_as_affine(point),
{
    lemma_unfold_edwards(point);
    let x_proj = fe51_as_canonical_nat(&point.X);
    let y_proj = fe51_as_canonical_nat(&point.Y);
    let z_proj = fe51_as_canonical_nat(&point.Z);

    let z_inv = field_inv(z_proj);
    let x = field_mul(x_proj, z_inv);
    let y = field_mul(y_proj, z_inv);

    let y_plus_x = fe51_as_canonical_nat(&niels.y_plus_x);
    let y_minus_x = fe51_as_canonical_nat(&niels.y_minus_x);

    assert(y_plus_x == field_add(y, x));
    assert(y_minus_x == field_sub(y, x));

    let inv2 = field_inv(2);
    let x_niels = field_mul(field_sub(y_plus_x, y_minus_x), inv2);
    let y_niels = field_mul(field_add(y_plus_x, y_minus_x), inv2);

    lemma_recover_xy_from_niels_encoding(y_plus_x, y_minus_x, x, y);

    // x < p and y < p (field elements), so x%p = x and y%p = y
    assert(x < p()) by {
        p_gt_2();
        lemma_mod_bound(fe51_as_nat(&point.X) as int, p() as int);
        lemma_mod_bound((x_proj * z_inv) as int, p() as int);
    };
    assert(y < p()) by {
        p_gt_2();
        lemma_mod_bound(fe51_as_nat(&point.Y) as int, p() as int);
        lemma_mod_bound((y_proj * z_inv) as int, p() as int);
    };

    assert(x_niels == x) by {
        lemma_small_mod(x, p());
    };
    assert(y_niels == y) by {
        lemma_small_mod(y, p());
    };
}

/// Axiom: addition on the twisted Edwards curve is complete (always defined) and closed
/// (the result stays on the curve).
///
/// Given two affine points (x₁, y₁) and (x₂, y₂) on -x² + y² = 1 + d·x²y²,
/// let t = d·x₁x₂·y₁y₂. Then:
/// 1. **Completeness**: 1 + t ≠ 0 and 1 − t ≠ 0, so the addition denominators
///    in `edwards_add` are invertible.
/// 2. **Closure**: the resulting point `edwards_add(x₁, y₁, x₂, y₂)` satisfies the
///    curve equation.
///
/// This holds because d is non-square in GF(p) for Ed25519.
///
/// Reference: Bernstein, Birkner, Joye, Lange, Peters,
/// "Twisted Edwards Curves", AFRICACRYPT 2008, Theorem 3.3.
/// <https://eprint.iacr.org/2008/013>
pub proof fn axiom_edwards_add_complete(x1: nat, y1: nat, x2: nat, y2: nat)
    requires
        is_on_edwards_curve(x1, y1),
        is_on_edwards_curve(x2, y2),
    ensures
        ({
            let d = fe51_as_canonical_nat(&EDWARDS_D);
            let t = field_mul(d, field_mul(field_mul(x1, x2), field_mul(y1, y2)));
            field_add(1, t) != 0 && field_sub(1, t) != 0
        }),
        is_on_edwards_curve(edwards_add(x1, y1, x2, y2).0, edwards_add(x1, y1, x2, y2).1),
{
    admit();
}

/// The concrete addition formulas and `edwards_add` compute the same point.
///
/// There are two representations of Edwards addition:
/// - **`edwards_add`** (abstract): affine formula x₃ = (x₁y₂+y₁x₂)/(1+d·x₁x₂y₁y₂),
///   y₃ = (y₁y₂+x₁x₂)/(1−d·x₁x₂y₁y₂)
/// - **P¹×P¹ formulas** (concrete): produce (X:Y:Z:T) where each coordinate is
///   scaled by 2, e.g. X = 2·(x₁y₂+y₁x₂), Z = 2·(1+d·x₁x₂y₁y₂)
///
/// This lemma shows the two agree: the common factor of 2 cancels in the
/// projective ratios X/Z and Y/T, recovering exactly `edwards_add`. It also
/// ensures Z ≠ 0, T ≠ 0, and the result lies on the curve (via
/// `axiom_edwards_add_complete`).
pub proof fn lemma_completed_point_ratios(
    x1: nat,
    y1: nat,
    x2: nat,
    y2: nat,
    result_x: nat,
    result_y: nat,
    result_z: nat,
    result_t: nat,
)
    requires
// (x₁, y₁) on curve

        is_on_edwards_curve(x1, y1),
        // (x₂, y₂) on curve
        is_on_edwards_curve(x2, y2),
        // X = 2·(x₁y₂ + y₁x₂)
        result_x == field_mul(2, field_add(field_mul(x1, y2), field_mul(y1, x2))),
        // Y = 2·(y₁y₂ + x₁x₂)
        result_y == field_mul(2, field_add(field_mul(y1, y2), field_mul(x1, x2))),
        // Z = 2·(1 + d·x₁x₂·y₁y₂)
        result_z == field_mul(
            2,
            field_add(
                1,
                field_mul(
                    fe51_as_canonical_nat(&EDWARDS_D),
                    field_mul(field_mul(x1, x2), field_mul(y1, y2)),
                ),
            ),
        ),
        // T = 2·(1 − d·x₁x₂·y₁y₂)
        result_t == field_mul(
            2,
            field_sub(
                1,
                field_mul(
                    fe51_as_canonical_nat(&EDWARDS_D),
                    field_mul(field_mul(x1, x2), field_mul(y1, y2)),
                ),
            ),
        ),
    ensures
// Z ≠ 0

        result_z != 0,
        // T ≠ 0
        result_t != 0,
        // X/Z = edwards_add(x₁, y₁, x₂, y₂).x
        field_mul(result_x, field_inv(result_z)) == edwards_add(x1, y1, x2, y2).0,
        // Y/T = edwards_add(x₁, y₁, x₂, y₂).y
        field_mul(result_y, field_inv(result_t)) == edwards_add(x1, y1, x2, y2).1,
        // (X/Z, Y/T) on curve
        is_on_edwards_curve(
            field_mul(result_x, field_inv(result_z)),
            field_mul(result_y, field_inv(result_t)),
        ),
{
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let x1y2 = field_mul(x1, y2);
    let y1x2 = field_mul(y1, x2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);
    let t = field_mul(d, field_mul(x1x2, y1y2));
    let denom_x = field_add(1, t);
    let denom_y = field_sub(1, t);
    let num_x = field_add(x1y2, y1x2);
    let num_y = field_add(y1y2, x1x2);
    let two: nat = 2;

    // Denominators non-zero and result on curve
    assert(denom_x != 0 && denom_y != 0 && is_on_edwards_curve(
        field_mul(num_x, field_inv(denom_x)),
        field_mul(num_y, field_inv(denom_y)),
    )) by {
        axiom_edwards_add_complete(x1, y1, x2, y2);
    };
    assert(p() > 2) by {
        p_gt_2();
    };

    assert(two % p() != 0) by {
        lemma_small_mod(two, p());
    };
    assert(denom_x % p() != 0) by {
        lemma_small_mod(denom_x, p());
    };
    assert(denom_y % p() != 0) by {
        lemma_small_mod(denom_y, p());
    };

    // result_z = mul(2, denom_x) ≠ 0, result_t = mul(2, denom_y) ≠ 0
    assert(field_mul(two, denom_x) == field_mul(denom_x, two)) by {
        lemma_field_mul_comm(two, denom_x);
    }
    assert(field_mul(denom_x, two) != 0) by {
        lemma_nonzero_product(denom_x, two);
    }
    assert(field_mul(two, denom_y) == field_mul(denom_y, two)) by {
        lemma_field_mul_comm(two, denom_y);
    }
    assert(field_mul(denom_y, two) != 0) by {
        lemma_nonzero_product(denom_y, two);
    }

    // Cancel common factor of 2: mul(2,num)/mul(2,denom) = num/denom
    assert(field_mul(two, num_x) == field_mul(num_x, two)) by {
        lemma_field_mul_comm(two, num_x);
    }
    assert(field_mul(field_mul(num_x, two), field_inv(field_mul(denom_x, two))) == field_mul(
        num_x,
        field_inv(denom_x),
    )) by {
        lemma_cancel_common_factor(num_x, denom_x, two);
    }
    assert(field_mul(two, num_y) == field_mul(num_y, two)) by {
        lemma_field_mul_comm(two, num_y);
    }
    assert(field_mul(field_mul(num_y, two), field_inv(field_mul(denom_y, two))) == field_mul(
        num_y,
        field_inv(denom_y),
    )) by {
        lemma_cancel_common_factor(num_y, denom_y, two);
    }
}

/// Axiom: For field elements Y, Z with Z ≠ 0: (Z+Y)/(Z-Y) == (1+y)/(1-y) where y = Y/Z.
///
/// Used by `to_montgomery` to compute the Edwards-to-Montgomery map u = (1+y)/(1-y)
/// directly from the projective Y, Z coordinates as (Z+Y)/(Z-Y).
///
/// TODO: prove this from field algebra (cross-multiply and simplify).
pub proof fn axiom_edwards_to_montgomery_correspondence(y: nat, z: nat)
    requires
        z % p() != 0,  // Non-identity point (Z ≠ 0)

    ensures
        ({
            let y_affine = field_mul(y, field_inv(z));
            let one_plus_y = field_add(1, y_affine);
            let one_minus_y = field_sub(1, y_affine);
            let projective_result = field_mul(field_add(z, y), field_inv(field_sub(z, y)));
            let affine_result = field_mul(one_plus_y, field_inv(one_minus_y));
            projective_result == affine_result
        }),
{
    admit();
}

/// Lemma: When Z = 1 in a well-formed EdwardsPoint, the affine coordinates
/// equal (X, Y) directly, the point lies on the Edwards curve, and both
/// coordinates are in [0, p).
pub(crate) proof fn lemma_edwards_affine_when_z_is_one(point: crate::edwards::EdwardsPoint)
    requires
        is_well_formed_edwards_point(point),
        fe51_as_canonical_nat(&edwards_z(point)) == 1,
    ensures
        edwards_point_as_affine(point) == (
            fe51_as_canonical_nat(&edwards_x(point)),
            fe51_as_canonical_nat(&edwards_y(point)),
        ),
        is_on_edwards_curve(
            fe51_as_canonical_nat(&edwards_x(point)),
            fe51_as_canonical_nat(&edwards_y(point)),
        ),
        fe51_as_canonical_nat(&edwards_x(point)) < p(),
        fe51_as_canonical_nat(&edwards_y(point)) < p(),
{
    lemma_unfold_edwards(point);
    let x = fe51_as_canonical_nat(&point.X);
    let y = fe51_as_canonical_nat(&point.Y);

    assert(x < p() && y < p()) by {
        p_gt_2();
        lemma_mod_bound(u64_5_as_nat(point.X.limbs) as int, p() as int);
        lemma_mod_bound(u64_5_as_nat(point.Y.limbs) as int, p() as int);
    };

    assert(field_inv(1) == 1) by {
        lemma_field_inv_one();
    };
    assert(field_mul(x, 1) == x % p()) by {
        lemma_field_mul_one_right(x);
    };
    assert(field_mul(y, 1) == y % p()) by {
        lemma_field_mul_one_right(y);
    };
    assert(x % p() == x && y % p() == y) by {
        lemma_small_mod(x, p());
        lemma_small_mod(y, p());
    };

    let x2 = field_square(x);
    let y2 = field_square(y);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    let sub = field_sub(y2, x2);
    assert(field_mul(sub, 1) == sub % p() && sub % p() == sub) by {
        lemma_field_mul_one_right(sub);
        lemma_mod_bound(sub as int, p() as int);
        lemma_small_mod(sub, p());
    };
    assert(field_square(1nat) == 1) by {
        lemma_field_mul_one_right(1nat);
        lemma_small_mod(1nat, p());
    };
}

/// Lemma: projective curve equation implies affine curve equation
///
/// This is the natural inverse of `lemma_affine_curve_implies_projective`.
/// Given that (X:Y:Z) satisfies the projective curve equation and Z != 0,
/// the affine point (X/Z, Y/Z) lies on the Edwards curve.
///
/// Proof strategy: construct a ghost T satisfying the Segre relation X*Y = Z*T,
/// then delegate to `lemma_valid_extended_point_affine_on_curve`.
pub proof fn lemma_projective_implies_affine_on_curve(x: nat, y: nat, z: nat)
    requires
        z % p() != 0,
        is_on_edwards_curve_projective(x, y, z),
    ensures
        is_on_edwards_curve(field_mul(x, field_inv(z)), field_mul(y, field_inv(z))),
{
    let p = p();
    p_gt_2();

    let z_inv = field_inv(z);
    let xy = field_mul(x, y);
    let ghost_t = field_mul(xy, z_inv);

    // Prove Segre: field_mul(x, y) == field_mul(z, ghost_t)
    // Step 1: ghost_t = field_mul(z_inv, xy) by commutativity
    assert(ghost_t == field_mul(z_inv, xy)) by {
        lemma_field_mul_comm(xy, z_inv);
    };
    // Step 2: field_mul(z, field_mul(z_inv, xy)) = field_mul(field_mul(z, z_inv), xy)
    assert(field_mul(z, field_mul(z_inv, xy)) == field_mul(field_mul(z, z_inv), xy)) by {
        lemma_field_mul_assoc(z, z_inv, xy);
    };
    // Step 3: field_mul(z, z_inv) == 1
    assert(field_mul(z, z_inv) == 1) by {
        field_inv_property(z);
        // field_inv_property gives field_mul(field_canonical(z), z_inv) == 1
        // field_mul(z, z_inv) == field_mul(field_canonical(z), z_inv) by mod absorption
        lemma_mul_mod_noop_left(z as int, z_inv as int, p as int);
    };
    // Step 4: field_mul(1, xy) == xy
    assert(field_mul(1nat, xy) == xy) by {
        lemma_field_mul_one_left(xy);
        lemma_mod_bound((x * y) as int, p as int);
        lemma_small_mod(xy, p);
    };
    assert(field_mul(z, ghost_t) == xy);

    assert(is_valid_extended_edwards_point(x, y, z, ghost_t));
    assert(is_on_edwards_curve(field_mul(x, field_inv(z)), field_mul(y, field_inv(z)))) by {
        lemma_valid_extended_point_affine_on_curve(x, y, z, ghost_t);
    };
}

// =============================================================================
// Scalar multiplication distributivity (group homomorphism)
// =============================================================================
/// Axiom: Scalar multiplication distributes over Edwards addition.
///
/// [n]*(A + B) = [n]*A + [n]*B
///
/// This is a fundamental property of abelian groups: the "multiplication by n"
/// endomorphism is a group homomorphism.
pub proof fn axiom_edwards_scalar_mul_distributive(a: (nat, nat), b: (nat, nat), n: nat)
    ensures
        edwards_scalar_mul(edwards_add(a.0, a.1, b.0, b.1), n) == ({
            let na = edwards_scalar_mul(a, n);
            let nb = edwards_scalar_mul(b, n);
            edwards_add(na.0, na.1, nb.0, nb.1)
        }),
{
    admit();
}

// =============================================================================
// Scalar mul / double helpers
// =============================================================================
/// [n]*O = O for all n.
pub proof fn lemma_edwards_scalar_mul_identity(n: nat)
    ensures
        edwards_scalar_mul(edwards_identity(), n) == edwards_identity(),
    decreases n,
{
    let id = edwards_identity();
    if n == 0 {
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else if n == 1 {
        reveal_with_fuel(edwards_scalar_mul, 2);
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(id);
    } else {
        lemma_edwards_scalar_mul_identity((n - 1) as nat);
        lemma_edwards_scalar_mul_succ(id, (n - 1) as nat);
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(id);
    }
}

/// double(P) = [2]*P.
pub proof fn lemma_double_is_scalar_mul_2(P: (nat, nat))
    ensures
        edwards_double(P.0, P.1) == edwards_scalar_mul(P, 2),
{
    reveal_with_fuel(edwards_scalar_mul, 3);
}

/// double(A + B) = double(A) + double(B).
pub proof fn lemma_double_distributes(a: (nat, nat), b: (nat, nat))
    ensures
        ({
            let ab = edwards_add(a.0, a.1, b.0, b.1);
            edwards_double(ab.0, ab.1)
        }) == ({
            let da = edwards_double(a.0, a.1);
            let db = edwards_double(b.0, b.1);
            edwards_add(da.0, da.1, db.0, db.1)
        }),
{
    let ab = edwards_add(a.0, a.1, b.0, b.1);
    lemma_double_is_scalar_mul_2(ab);
    lemma_double_is_scalar_mul_2(a);
    lemma_double_is_scalar_mul_2(b);
    axiom_edwards_scalar_mul_distributive(a, b, 2);
}

/// double(O) = O.
pub proof fn lemma_double_identity()
    ensures
        edwards_double(0nat, 1nat) == edwards_identity(),
{
    lemma_double_is_scalar_mul_2(edwards_identity());
    lemma_edwards_scalar_mul_identity(2);
}

} // verus!
