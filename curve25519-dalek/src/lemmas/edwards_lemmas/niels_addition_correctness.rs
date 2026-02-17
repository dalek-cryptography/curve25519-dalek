//! Correctness of Niels-based addition formulas for twisted Edwards curves.
//!
//! Proves that the projective addition formulas used in
//! `EdwardsPoint +/- ProjectiveNielsPoint` and `EdwardsPoint +/- AffineNielsPoint`
//! correctly compute the Edwards group law and produce valid CompletedPoints.
//!
//! Given extended point P1 = (X1:Y1:Z1:T1) and a Niels point encoding P2,
//! the exec code computes a CompletedPoint via the formulas from
//! Hisil-Wong-Carter-Dawson 2008, Table 3 (<https://eprint.iacr.org/2008/522>):
//!
//!   PP = (Y1+X1)(Y2+X2),  MM = (Y1-X1)(Y2-X2)
//!   result.X = PP - MM,  result.Y = PP + MM
//!   result.Z = 2·Z1·Z2 + T1·(2d)·T2,  result.T = 2·Z1·Z2 - T1·(2d)·T2
//!
//! Each lemma proves that the resulting CompletedPoint, when projected to
//! affine coordinates, equals edwards_add (or edwards_sub) of (x1, y1, x2, y2)
//! where xi = Xi/Zi.
//!
//! Proof strategy (shared by all 4 variants):
//!   1. FOIL: expand PP +/- MM into sums of cross-products
//!   2. Factor: pull out z1z2 = Z1·Z2 (or just Z1 for affine Niels)
//!   3. Segre: use T = X·Y/Z to rewrite T1·T2 as (x1y1·x2y2)·z1z2
//!   4. Denominator: factor result.Z, result.T into z1z2·2(1+t), z1z2·2(1-t)
//!   5. Cancel: divide out z1z2 to get affine ratios matching edwards_add
//!   6. Connect: link Niels affine coords to Edwards affine coords
//!
//! Sub variants reduce to add via edwards_sub(x1,y1,x2,y2) = edwards_add(x1,y1,-x2,y2).
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// =============================================================================
// Helper lemmas to reduce repetition across the 4 main proof lemmas
// =============================================================================
/// Helper: Given projective A = a·Z_A and B = b·Z_B, prove
/// A·B = (a·b)·(Z_A·Z_B).
///
/// Used to factor Yi·Xj = (yi·xj)·(Zi·Zj) from projective coordinates.
proof fn lemma_projective_product_factor(a_proj: nat, z_a: nat, b_proj: nat, z_b: nat)
    requires
        z_a % p() != 0,
        z_b % p() != 0,
        a_proj < p(),
        b_proj < p(),
    ensures
        ({
            let a = field_mul(a_proj, field_inv(z_a));
            let b = field_mul(b_proj, field_inv(z_b));
            field_mul(a_proj, b_proj) == field_mul(field_mul(a, b), field_mul(z_a, z_b))
        }),
{
    let a = field_mul(a_proj, field_inv(z_a));
    let b = field_mul(b_proj, field_inv(z_b));
    assert(field_mul(a_proj, b_proj) == field_mul(field_mul(a, b), field_mul(z_a, z_b))) by {
        lemma_four_factor_rearrange(a, z_a, b, z_b);
        lemma_div_mul_cancel(a_proj, z_a);
        lemma_div_mul_cancel(b_proj, z_b);
        lemma_field_element_reduced(a_proj);
        lemma_field_element_reduced(b_proj);
    };
}

/// Helper: Given projective A = a·Z (with only one Z factor), prove
/// A·b = (a·b)·Z for affine b.
///
/// Used for AffineNiels case where only one coordinate is projective.
proof fn lemma_projective_affine_product_factor(a_proj: nat, z: nat, b: nat)
    requires
        z % p() != 0,
        a_proj < p(),
    ensures
        ({
            let a = field_mul(a_proj, field_inv(z));
            field_mul(a_proj, b) == field_mul(field_mul(a, b), z)
        }),
{
    let a = field_mul(a_proj, field_inv(z));
    assert(field_mul(a_proj, b) == field_mul(field_mul(a, b), z)) by {
        lemma_div_mul_cancel(a_proj, z);
        lemma_field_element_reduced(a_proj);
        lemma_field_mul_assoc(a, z, b);
        lemma_field_mul_comm(z, b);
        lemma_field_mul_assoc(a, b, z);
    };
}

/// Helper: Cancel a common Z factor from both X/Z and Y/T ratios of a
/// CompletedPoint, and prove the result is nonzero.
///
/// Given result_x = z·aff_rx, result_y = z·aff_ry, etc.,
/// proves that x/z = aff_rx/aff_rz and y/t = aff_ry/aff_rt.
proof fn lemma_cancel_z_from_ratios(aff_rx: nat, aff_ry: nat, aff_rz: nat, aff_rt: nat, z: nat)
    requires
        z % p() != 0,
        z != 0,
        aff_rz % p() != 0,
        aff_rt % p() != 0,
    ensures
// X/Z cancellation

        field_mul(field_mul(z, aff_rx), field_inv(field_mul(z, aff_rz))) == field_mul(
            aff_rx,
            field_inv(aff_rz),
        ),
        // Y/T cancellation
        field_mul(field_mul(z, aff_ry), field_inv(field_mul(z, aff_rt))) == field_mul(
            aff_ry,
            field_inv(aff_rt),
        ),
        // Nonzero results
        field_mul(z, aff_rz) != 0,
        field_mul(z, aff_rt) != 0,
{
    // Cancel z from X/Z ratio
    assert(field_mul(field_mul(z, aff_rx), field_inv(field_mul(z, aff_rz))) == field_mul(
        aff_rx,
        field_inv(aff_rz),
    )) by {
        lemma_cancel_common_factor(aff_rx, aff_rz, z);
        lemma_field_mul_comm(z, aff_rx);
        lemma_field_mul_comm(z, aff_rz);
    };

    // Cancel z from Y/T ratio
    assert(field_mul(field_mul(z, aff_ry), field_inv(field_mul(z, aff_rt))) == field_mul(
        aff_ry,
        field_inv(aff_rt),
    )) by {
        lemma_cancel_common_factor(aff_ry, aff_rt, z);
        lemma_field_mul_comm(z, aff_ry);
        lemma_field_mul_comm(z, aff_rt);
    };

    // Nonzero
    assert(field_mul(z, aff_rz) != 0) by {
        lemma_nonzero_product(aff_rz, z);
    };
    assert(field_mul(z, aff_rt) != 0) by {
        lemma_nonzero_product(aff_rt, z);
    };
}

/// Helper: Derive T = (x·y)·Z from the Segre invariant X·Y = Z·T.
///
/// Given projective coords X, Y, Z, T with X·Y = Z·T and Z ≠ 0,
/// and affine x = X/Z, y = Y/Z, proves that T ≡ (x·y)·Z (mod p).
proof fn lemma_segre_t_derivation(proj_x: nat, proj_y: nat, proj_z: nat, proj_t: nat)
    requires
        proj_z % p() != 0,
        proj_x < p(),
        proj_y < p(),
        proj_t < p(),
        // Segre invariant
        field_mul(proj_x, proj_y) == field_mul(proj_z, proj_t),
    ensures
        ({
            let x = field_mul(proj_x, field_inv(proj_z));
            let y = field_mul(proj_y, field_inv(proj_z));
            let xy = field_mul(x, y);
            proj_t == field_mul(xy, proj_z) % p()
        }),
{
    let x = field_mul(proj_x, field_inv(proj_z));
    let y = field_mul(proj_y, field_inv(proj_z));
    let xy = field_mul(x, y);

    // X·Y = (xy)·Z² via four-factor rearrange
    assert(field_mul(proj_x, proj_y) == field_mul(xy, field_mul(proj_z, proj_z))) by {
        lemma_four_factor_rearrange(x, proj_z, y, proj_z);
        lemma_div_mul_cancel(proj_x, proj_z);
        lemma_div_mul_cancel(proj_y, proj_z);
        lemma_field_element_reduced(proj_x);
        lemma_field_element_reduced(proj_y);
    };

    // From Segre: Z·T = (xy)·Z², so T = (xy)·Z (cancel Z)
    assert(proj_t == field_mul(xy, proj_z) % p()) by {
        lemma_field_mul_assoc(xy, proj_z, proj_z);
        lemma_field_mul_comm(field_mul(xy, proj_z), proj_z);
        lemma_field_mul_left_cancel(proj_z, proj_t, field_mul(xy, proj_z));
        lemma_field_element_reduced(proj_t);
    };
}

/// Helper: Reduce subtraction to addition via negation.
///
/// Given affine (x1,y1), (x2,y2) on the curve and t = d·x1x2·y1y2,
/// proves the substitution identities needed for edwards_sub = edwards_add(x1,y1,-x2,y2):
/// - neg(x2) is on the curve
/// - sub(x1y2, y1x2) = add(x1y2, y1·neg(x2))
/// - sub(y1y2, x1x2) = add(y1y2, x1·neg(x2))
/// - t' = d·x1·neg(x2)·y1·y2 = neg(t)
/// - sub(1, t') = add(1, t) and add(1, t') = sub(1, t)
proof fn lemma_sub_via_negation(
    x1: nat,
    y1: nat,
    x2: nat,
    y2: nat,
    x1y2: nat,
    y1x2: nat,
    y1y2: nat,
    x1x2: nat,
    d: nat,
    t: nat,
)
    requires
        math_on_edwards_curve(x2, y2),
        x1y2 == field_mul(x1, y2),
        y1x2 == field_mul(y1, x2),
        y1y2 == field_mul(y1, y2),
        x1x2 == field_mul(x1, x2),
        d == fe51_as_canonical_nat(&EDWARDS_D),
        t == field_mul(d, field_mul(x1x2, y1y2)),
    ensures
        ({
            let neg_x2 = field_neg(x2);
            let t_prime = field_mul(d, field_mul(field_mul(x1, neg_x2), field_mul(y1, y2)));
            &&& math_on_edwards_curve(neg_x2, y2)
            &&& field_sub(x1y2, y1x2) == field_add(x1y2, field_mul(y1, neg_x2))
            &&& field_sub(y1y2, x1x2) == field_add(y1y2, field_mul(x1, neg_x2))
            &&& t_prime == field_neg(t)
            &&& field_sub(1nat, t_prime) == field_add(1nat, t)
            &&& field_add(1nat, t_prime) == field_sub(1nat, t)
        }),
{
    let neg_x2 = field_neg(x2);
    let t_prime = field_mul(d, field_mul(field_mul(x1, neg_x2), field_mul(y1, y2)));

    // neg(x2) is on the curve
    assert(math_on_edwards_curve(neg_x2, y2)) by {
        lemma_negation_preserves_curve(x2, y2);
    };

    // sub(x1y2, y1x2) = add(x1y2, y1·neg(x2))
    assert(field_sub(x1y2, y1x2) == field_add(x1y2, field_mul(y1, neg_x2))) by {
        lemma_field_mul_neg(y1, x2);
        lemma_field_sub_eq_add_neg(x1y2, y1x2);
    };

    // sub(y1y2, x1x2) = add(y1y2, x1·neg(x2))
    assert(field_sub(y1y2, x1x2) == field_add(y1y2, field_mul(x1, neg_x2))) by {
        lemma_field_mul_neg(x1, x2);
        lemma_field_sub_eq_add_neg(y1y2, x1x2);
    };

    // t' = d·x1·neg(x2)·y1·y2 = neg(t)
    assert(t_prime == field_neg(t)) by {
        lemma_field_mul_neg(x1, x2);
        lemma_field_mul_comm(field_neg(x1x2), y1y2);
        lemma_field_mul_neg(y1y2, x1x2);
        lemma_field_mul_comm(y1y2, x1x2);
        lemma_field_mul_neg(d, field_mul(x1x2, y1y2));
    };

    // Denominators swap under negation
    assert(field_sub(1nat, t_prime) == field_add(1nat, t)) by {
        lemma_field_sub_eq_add_neg(1nat, t_prime);
        lemma_neg_neg(t);
        let p = p();
        p_gt_2();
        lemma_add_mod_noop(1nat as int, (t % p) as int, p as int);
        lemma_add_mod_noop(1nat as int, t as int, p as int);
        lemma_mod_twice(t as int, p as int);
    };
    assert(field_add(1nat, t_prime) == field_sub(1nat, t)) by {
        lemma_field_sub_eq_add_neg(1nat, t);
    };
}

/// EdwardsPoint(X1,Y1,Z1,T1) + ProjectiveNielsPoint → CompletedPoint.
/// The Niels point encodes an EdwardsPoint(X2,Y2,Z2,T2) as (Y2+X2, Y2-X2, Z2, 2d·T2).
///
/// Requires: self_point and other are valid; result fields match the
///   Hisil et al. addition formulas (PP-MM, PP+MM, 2ZZ+TT2d, 2ZZ-TT2d).
///
/// Ensures: is_valid_completed_point(result) ∧
///   completed_point_as_affine_edwards(result) == edwards_add(self_affine, other_affine)
pub proof fn lemma_add_projective_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::ProjectiveNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pp_val: nat,
    mm_val: nat,
    tt2d_val: nat,
    zz_val: nat,
)
    requires
// P₁ is well-formed and valid

        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        // P₂ (as ProjectiveNiels) is valid
        is_valid_projective_niels_point(other),
        // PP = (Y₁+X₁)·(Y₂+X₂)
        pp_val == field_mul(
            field_add(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.Y_plus_X),
        ),
        // MM = (Y₁−X₁)·(Y₂−X₂)
        mm_val == field_mul(
            field_sub(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.Y_minus_X),
        ),
        // TT2d = T₁·(2d·T₂)
        tt2d_val == field_mul(
            fe51_as_canonical_nat(&self_point.T),
            fe51_as_canonical_nat(&other.T2d),
        ),
        // ZZ = Z₁·Z₂
        zz_val == field_mul(fe51_as_canonical_nat(&self_point.Z), fe51_as_canonical_nat(&other.Z)),
        // result.X = PP − MM
        fe51_as_canonical_nat(&result.X) == field_sub(pp_val, mm_val),
        // result.Y = PP + MM
        fe51_as_canonical_nat(&result.Y) == field_add(pp_val, mm_val),
        // result.Z = 2·ZZ + TT2d
        fe51_as_canonical_nat(&result.Z) == field_add(field_add(zz_val, zz_val), tt2d_val),
        // result.T = 2·ZZ − TT2d
        fe51_as_canonical_nat(&result.T) == field_sub(field_add(zz_val, zz_val), tt2d_val),
    ensures
// The CompletedPoint is valid (Z ≠ 0, T ≠ 0)

        is_valid_completed_point(result),
        // Its affine projection equals edwards_add(P₁, P₂)
        completed_point_as_affine_edwards(result) == {
            let self_affine = edwards_point_as_affine(self_point);
            let other_affine = projective_niels_point_as_affine_edwards(other);
            edwards_add(self_affine.0, self_affine.1, other_affine.0, other_affine.1)
        },
{
    let sX = fe51_as_canonical_nat(&self_point.X);
    let sY = fe51_as_canonical_nat(&self_point.Y);
    let sZ = fe51_as_canonical_nat(&self_point.Z);
    let sT = fe51_as_canonical_nat(&self_point.T);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    assert(p() > 2) by {
        p_gt_2();
    };

    assert(sZ % p() != 0);  // from is_valid_edwards_point → math_is_valid_extended_edwards_point

    // Extract witness from is_valid_projective_niels_point
    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && #[trigger] projective_niels_corresponds_to_edwards(other, ep);
    let X2 = fe51_as_canonical_nat(&ep.X);
    let Y2 = fe51_as_canonical_nat(&ep.Y);
    let Z2 = fe51_as_canonical_nat(&ep.Z);
    let T2 = fe51_as_canonical_nat(&ep.T);

    assert(Z2 % p() != 0);  // from is_valid_edwards_point(ep)

    // Segre invariant: Xi·Yi = Zi·Ti
    assert(field_mul(sX, sY) == field_mul(sZ, sT));
    assert(field_mul(X2, Y2) == field_mul(Z2, T2));

    // Niels correspondence: (Y+X, Y-X, Z, 2dT)
    assert(fe51_as_canonical_nat(&other.Y_plus_X) == field_add(Y2, X2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.Y_minus_X) == field_sub(Y2, X2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.Z) == Z2) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.T2d) == field_mul(field_mul(2, d), T2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };

    // Affine coordinates: xi = Xi/Zi, yi = Yi/Zi
    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));
    let x2 = field_mul(X2, field_inv(Z2));
    let y2 = field_mul(Y2, field_inv(Z2));

    assert(math_on_edwards_curve(x1, y1)) by {
        lemma_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    };
    assert(math_on_edwards_curve(x2, y2)) by {
        lemma_valid_extended_point_affine_on_curve(X2, Y2, Z2, T2);
    };

    // STEP 1: FOIL on PP and MM
    let result_x = field_sub(pp_val, mm_val);
    let result_y = field_add(pp_val, mm_val);
    // PP - MM = 2(Y1·X2 + X1·Y2)
    assert(result_x == field_mul(2, field_add(field_mul(sY, X2), field_mul(sX, Y2)))) by {
        lemma_pp_minus_mm(sY, sX, Y2, X2);
    };
    // PP + MM = 2(Y1·Y2 + X1·X2)
    assert(result_y == field_mul(2, field_add(field_mul(sY, Y2), field_mul(sX, X2)))) by {
        lemma_pp_plus_mm(sY, sX, Y2, X2);
    };

    // STEP 2: Yi·Xj = (yi·xj)·z1z2 since Yi = yi·Zi
    let z1z2 = field_mul(sZ, Z2);
    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    assert(field_mul(sY, X2) == field_mul(y1x2, z1z2)) by {
        lemma_projective_product_factor(sY, sZ, X2, Z2);
    };
    assert(field_mul(sX, Y2) == field_mul(x1y2, z1z2)) by {
        lemma_projective_product_factor(sX, sZ, Y2, Z2);
    };
    assert(field_mul(sY, Y2) == field_mul(y1y2, z1z2)) by {
        lemma_projective_product_factor(sY, sZ, Y2, Z2);
    };
    assert(field_mul(sX, X2) == field_mul(x1x2, z1z2)) by {
        lemma_projective_product_factor(sX, sZ, X2, Z2);
    };

    // Y1·X2 + X1·Y2 = z1z2·(y1x2 + x1y2)
    assert(field_add(field_mul(sY, X2), field_mul(sX, Y2)) == field_mul(
        z1z2,
        field_add(y1x2, x1y2),
    )) by {
        lemma_reverse_distribute_add(y1x2, x1y2, z1z2);
        lemma_field_mul_comm(field_add(y1x2, x1y2), z1z2);
    };

    // Y1·Y2 + X1·X2 = z1z2·(y1y2 + x1x2)
    assert(field_add(field_mul(sY, Y2), field_mul(sX, X2)) == field_mul(
        z1z2,
        field_add(y1y2, x1x2),
    )) by {
        lemma_reverse_distribute_add(y1y2, x1x2, z1z2);
        lemma_field_mul_comm(field_add(y1y2, x1x2), z1z2);
    };

    let num_x = field_add(y1x2, x1y2);  // x1y2 + y1x2
    let num_y = field_add(y1y2, x1x2);  // y1y2 + x1x2

    // STEP 3: TT2d = T1·(2d·T2), rewrite via Segre T = (x·y)·Z
    let x1y1 = field_mul(x1, y1);
    let x2y2 = field_mul(x2, y2);

    // T1 = (x1y1)·Z1, T2 = (x2y2)·Z2 via Segre invariant
    assert(sT == field_mul(x1y1, sZ) % p()) by {
        lemma_segre_t_derivation(sX, sY, sZ, sT);
    };
    assert(T2 == field_mul(x2y2, Z2) % p()) by {
        lemma_segre_t_derivation(X2, Y2, Z2, T2);
    };

    // T1·T2 = (x1y1·Z1)·(x2y2·Z2) = (x1y1·x2y2)·z1z2
    assert(field_mul(sT, T2) == field_mul(field_mul(x1y1, x2y2), z1z2)) by {
        lemma_field_element_reduced(sT);
        lemma_field_element_reduced(T2);
        lemma_mul_mod_noop_right(sT as int, T2 as int, p() as int);
        lemma_mul_mod_noop_left(sT as int, T2 as int, p() as int);
        lemma_mul_mod_noop_left((field_mul(x1y1, sZ)) as int, T2 as int, p() as int);
        lemma_mul_mod_noop_right(
            (field_mul(x1y1, sZ)) as int,
            (field_mul(x2y2, Z2)) as int,
            p() as int,
        );
        lemma_four_factor_rearrange(x1y1, sZ, x2y2, Z2);
    };

    let t = field_mul(d, field_mul(x1x2, y1y2));  // t = d·x1·x2·y1·y2

    // (x1·y1)·(x2·y2) = (x1·x2)·(y1·y2)  (rearrange)
    assert(field_mul(x1y1, x2y2) == field_mul(x1x2, y1y2)) by {
        lemma_four_factor_rearrange(x1, y1, x2, y2);
    };

    // TT2d = T1·(2d·T2) = (T1·T2)·2d
    assert(tt2d_val == field_mul(field_mul(sT, T2), field_mul(2, d))) by {
        lemma_field_mul_comm(field_mul(2, d), T2);
        lemma_field_mul_assoc(sT, T2, field_mul(2, d));
    };

    let x1x2y1y2 = field_mul(x1x2, y1y2);
    assert(field_mul(field_mul(x1x2y1y2, z1z2), field_mul(2, d)) == field_mul(
        z1z2,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        lemma_field_mul_comm(x1x2y1y2, z1z2);
        lemma_field_mul_assoc(z1z2, x1x2y1y2, field_mul(2, d));
    };

    // x1x2y1y2·2d = 2·(d·x1x2y1y2) = 2t
    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    assert(tt2d_val == field_mul(z1z2, field_mul(2, t)));  // TT2d = z1z2·2t

    // STEP 4: Factor result.Z and result.T into z1z2·2(1+t) and z1z2·2(1-t)
    let zz2 = field_add(zz_val, zz_val);
    assert(zz2 == field_mul(2, z1z2)) by {  // ZZ + ZZ = 2·z1z2
        lemma_add_self_eq_double(zz_val);
    };

    let result_z = field_add(zz2, tt2d_val);
    let result_t = field_sub(zz2, tt2d_val);

    assert(field_mul(2, z1z2) == field_mul(z1z2, 2)) by {
        lemma_field_mul_comm(2nat, z1z2);
    };

    // result.Z = 2·z1z2 + z1z2·2t = z1z2·(2 + 2t) = z1z2·2(1+t)
    assert(result_z == field_mul(z1z2, field_add(2, field_mul(2, t)))) by {
        lemma_reverse_distribute_add(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_add(2, field_mul(2, t)), z1z2);
    };

    assert(field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t))) by {
        lemma_field_mul_distributes_over_add(2, 1, t);
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    assert(result_z == field_mul(z1z2, field_mul(2, field_add(1, t))));

    // result.T = 2·z1z2 - z1z2·2t = z1z2·(2 - 2t) = z1z2·2(1-t)
    assert(field_mul(z1z2, field_mul(2, t)) == field_mul(field_mul(2, t), z1z2)) by {
        lemma_field_mul_comm(z1z2, field_mul(2, t));
    };
    assert(result_t == field_mul(z1z2, field_sub(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_sub(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_sub(2nat, field_mul(2, t)), z1z2);
    };

    assert(field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t))) by {
        lemma_field_mul_comm(2nat, field_sub(1, t));
        lemma_field_mul_distributes_over_sub_right(1, t, 2);
        lemma_field_mul_one_left(2nat);
        lemma_small_mod(2nat, p());
        lemma_field_mul_comm(t, 2nat);
    };
    assert(result_t == field_mul(z1z2, field_mul(2, field_sub(1, t))));

    // result.X = 2·z1z2·num_x = z1z2·2·num_x
    assert(result_x == field_mul(z1z2, field_mul(2, num_x))) by {
        lemma_field_mul_assoc(2, z1z2, num_x);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_x);
    };

    // result.Y = z1z2·2·num_y
    assert(result_y == field_mul(z1z2, field_mul(2, num_y))) by {
        lemma_field_mul_assoc(2, z1z2, num_y);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_y);
    };

    // STEP 5: Cancel z1z2; result = z1z2·(aff_rX : aff_rY : aff_rZ : aff_rT)
    let aff_rx = field_mul(2, field_add(x1y2, y1x2));
    let aff_ry = field_mul(2, field_add(y1y2, x1x2));
    let aff_rz = field_mul(2, field_add(1, t));
    let aff_rt = field_mul(2, field_sub(1, t));

    assert(num_x == field_add(x1y2, y1x2)) by {
        let pp = p();
        lemma_add_mod_noop(y1x2 as int, x1y2 as int, pp as int);
        lemma_add_mod_noop(x1y2 as int, y1x2 as int, pp as int);
    };

    assert(result_x == field_mul(z1z2, aff_rx));
    assert(result_y == field_mul(z1z2, aff_ry));
    assert(result_z == field_mul(z1z2, aff_rz));
    assert(result_t == field_mul(z1z2, aff_rt));

    assert(aff_rz != 0 && aff_rt != 0 && math_on_edwards_curve(
        field_mul(aff_rx, field_inv(aff_rz)),
        field_mul(aff_ry, field_inv(aff_rt)),
    ) && field_mul(aff_rx, field_inv(aff_rz)) == edwards_add(x1, y1, x2, y2).0 && field_mul(
        aff_ry,
        field_inv(aff_rt),
    ) == edwards_add(x1, y1, x2, y2).1) by {
        lemma_completed_point_ratios(x1, y1, x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);
    };

    // STEP 6: Cancel z1z2 from all ratios
    assert(z1z2 != 0) by {
        lemma_field_element_reduced(sZ);
        lemma_field_element_reduced(Z2);
        lemma_nonzero_product(sZ, Z2);
    };
    assert(z1z2 % p() != 0) by {
        lemma_mod_bound((sZ * Z2) as int, p() as int);
        lemma_field_element_reduced(z1z2);
    };
    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    assert(field_mul(z1z2, aff_rz) != 0 && field_mul(z1z2, aff_rt) != 0) by {
        lemma_cancel_z_from_ratios(aff_rx, aff_ry, aff_rz, aff_rt, z1z2);
    };
    assert(field_mul(field_mul(z1z2, aff_rx), field_inv(field_mul(z1z2, aff_rz))) == field_mul(
        aff_rx,
        field_inv(aff_rz),
    ) && field_mul(field_mul(z1z2, aff_ry), field_inv(field_mul(z1z2, aff_rt))) == field_mul(
        aff_ry,
        field_inv(aff_rt),
    )) by {
        lemma_cancel_z_from_ratios(aff_rx, aff_ry, aff_rz, aff_rt, z1z2);
    };

    // STEP 7: Connect to edwards_add via projective_niels correspondence
    assert(projective_niels_point_as_affine_edwards(other) == edwards_point_as_affine(ep)) by {
        lemma_projective_niels_affine_equals_edwards_affine(other, ep);
    };
}

/// EdwardsPoint(X1,Y1,Z1,T1) - ProjectiveNielsPoint → CompletedPoint.
/// The Niels point encodes an EdwardsPoint(X2,Y2,Z2,T2) as (Y2+X2, Y2-X2, Z2, 2d·T2).
///
/// Requires: self_point and other are valid; result fields match the
///   sub formulas (PM-MP, PM+MP, 2ZZ-TT2d, 2ZZ+TT2d).
///
/// Ensures: is_valid_completed_point(result) ∧
///   completed_point_as_affine_edwards(result) == edwards_sub(self_affine, other_affine)
pub proof fn lemma_sub_projective_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::ProjectiveNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pm_val: nat,
    mp_val: nat,
    tt2d_val: nat,
    zz_val: nat,
)
    requires
// P₁ is well-formed and valid

        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        // P₂ (as ProjectiveNiels) is valid
        is_valid_projective_niels_point(other),
        // PM = (Y₁+X₁)·(Y₂−X₂)  [note: swapped vs add]
        pm_val == field_mul(
            field_add(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.Y_minus_X),
        ),
        // MP = (Y₁−X₁)·(Y₂+X₂)  [note: swapped vs add]
        mp_val == field_mul(
            field_sub(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.Y_plus_X),
        ),
        // TT2d = T₁·(2d·T₂)
        tt2d_val == field_mul(
            fe51_as_canonical_nat(&self_point.T),
            fe51_as_canonical_nat(&other.T2d),
        ),
        // ZZ = Z₁·Z₂
        zz_val == field_mul(fe51_as_canonical_nat(&self_point.Z), fe51_as_canonical_nat(&other.Z)),
        // result.X = PM − MP
        fe51_as_canonical_nat(&result.X) == field_sub(pm_val, mp_val),
        // result.Y = PM + MP
        fe51_as_canonical_nat(&result.Y) == field_add(pm_val, mp_val),
        // result.Z = 2·ZZ − TT2d  [note: minus vs add]
        fe51_as_canonical_nat(&result.Z) == field_sub(field_add(zz_val, zz_val), tt2d_val),
        // result.T = 2·ZZ + TT2d  [note: plus vs add]
        fe51_as_canonical_nat(&result.T) == field_add(field_add(zz_val, zz_val), tt2d_val),
    ensures
// The CompletedPoint is valid (Z ≠ 0, T ≠ 0)

        is_valid_completed_point(result),
        // Its affine projection equals edwards_sub(P₁, P₂)
        completed_point_as_affine_edwards(result) == {
            let self_affine = edwards_point_as_affine(self_point);
            let other_affine = projective_niels_point_as_affine_edwards(other);
            edwards_sub(self_affine.0, self_affine.1, other_affine.0, other_affine.1)
        },
{
    let sX = fe51_as_canonical_nat(&self_point.X);
    let sY = fe51_as_canonical_nat(&self_point.Y);
    let sZ = fe51_as_canonical_nat(&self_point.Z);
    let sT = fe51_as_canonical_nat(&self_point.T);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    assert(p() > 2) by {
        p_gt_2();
    };

    assert(sZ % p() != 0);  // from is_valid_edwards_point → math_is_valid_extended_edwards_point

    // Extract witness from is_valid_projective_niels_point
    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && #[trigger] projective_niels_corresponds_to_edwards(other, ep);
    let X2 = fe51_as_canonical_nat(&ep.X);
    let Y2 = fe51_as_canonical_nat(&ep.Y);
    let Z2 = fe51_as_canonical_nat(&ep.Z);
    let T2 = fe51_as_canonical_nat(&ep.T);

    assert(Z2 % p() != 0);  // from is_valid_edwards_point(ep)

    // Segre invariant
    assert(field_mul(sX, sY) == field_mul(sZ, sT));
    assert(field_mul(X2, Y2) == field_mul(Z2, T2));

    // Niels correspondence: (Y+X, Y-X, Z, 2dT)
    assert(fe51_as_canonical_nat(&other.Y_plus_X) == field_add(Y2, X2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.Y_minus_X) == field_sub(Y2, X2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.Z) == Z2) by {
        reveal(projective_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.T2d) == field_mul(field_mul(2, d), T2)) by {
        reveal(projective_niels_corresponds_to_edwards);
    };

    // Affine coordinates: xi = Xi/Zi, yi = Yi/Zi
    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));
    let x2 = field_mul(X2, field_inv(Z2));
    let y2 = field_mul(Y2, field_inv(Z2));

    assert(math_on_edwards_curve(x1, y1)) by {
        lemma_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    };
    assert(math_on_edwards_curve(x2, y2)) by {
        lemma_valid_extended_point_affine_on_curve(X2, Y2, Z2, T2);
    };

    // STEP 1: Mixed FOIL on PM and MP (swapped from add)
    let result_x = field_sub(pm_val, mp_val);
    let result_y = field_add(pm_val, mp_val);

    // PM - MP = 2(X1·Y2 - Y1·X2)
    assert(result_x == field_mul(2, field_sub(field_mul(sX, Y2), field_mul(sY, X2)))) by {
        lemma_pm_minus_mp(sY, sX, Y2, X2);
    };
    // PM + MP = 2(Y1·Y2 - X1·X2)
    assert(result_y == field_mul(2, field_sub(field_mul(sY, Y2), field_mul(sX, X2)))) by {
        lemma_pm_plus_mp(sY, sX, Y2, X2);
    };

    // STEP 2: Yi·Xj = (yi·xj)·z1z2
    let z1z2 = field_mul(sZ, Z2);
    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    assert(field_mul(sY, X2) == field_mul(y1x2, z1z2)) by {
        lemma_projective_product_factor(sY, sZ, X2, Z2);
    };
    assert(field_mul(sX, Y2) == field_mul(x1y2, z1z2)) by {
        lemma_projective_product_factor(sX, sZ, Y2, Z2);
    };
    assert(field_mul(sY, Y2) == field_mul(y1y2, z1z2)) by {
        lemma_projective_product_factor(sY, sZ, Y2, Z2);
    };
    assert(field_mul(sX, X2) == field_mul(x1x2, z1z2)) by {
        lemma_projective_product_factor(sX, sZ, X2, Z2);
    };

    assert(field_sub(field_mul(sX, Y2), field_mul(sY, X2)) == field_mul(
        z1z2,
        field_sub(x1y2, y1x2),
    )) by {
        lemma_reverse_distribute_sub(x1y2, y1x2, z1z2);
        lemma_field_mul_comm(field_sub(x1y2, y1x2), z1z2);
    };

    assert(field_sub(field_mul(sY, Y2), field_mul(sX, X2)) == field_mul(
        z1z2,
        field_sub(y1y2, x1x2),
    )) by {
        lemma_reverse_distribute_sub(y1y2, x1x2, z1z2);
        lemma_field_mul_comm(field_sub(y1y2, x1x2), z1z2);
    };

    let num_x = field_sub(x1y2, y1x2);  // x1y2 - y1x2
    let num_y = field_sub(y1y2, x1x2);  // y1y2 - x1x2

    // STEP 3: TT2d = z1z2·2t  (same derivation as add variant)
    let x1y1 = field_mul(x1, y1);
    let x2y2 = field_mul(x2, y2);

    // T1 = (x1y1)·Z1, T2 = (x2y2)·Z2 via Segre invariant
    assert(sT == field_mul(x1y1, sZ) % p()) by {
        lemma_segre_t_derivation(sX, sY, sZ, sT);
    };
    assert(T2 == field_mul(x2y2, Z2) % p()) by {
        lemma_segre_t_derivation(X2, Y2, Z2, T2);
    };

    // T1·T2 = (x1y1·x2y2)·z1z2
    assert(field_mul(sT, T2) == field_mul(field_mul(x1y1, x2y2), z1z2)) by {
        lemma_field_element_reduced(sT);
        lemma_field_element_reduced(T2);
        lemma_mul_mod_noop_right(sT as int, T2 as int, p() as int);
        lemma_mul_mod_noop_left(sT as int, T2 as int, p() as int);
        lemma_mul_mod_noop_left((field_mul(x1y1, sZ)) as int, T2 as int, p() as int);
        lemma_mul_mod_noop_right(
            (field_mul(x1y1, sZ)) as int,
            (field_mul(x2y2, Z2)) as int,
            p() as int,
        );
        lemma_four_factor_rearrange(x1y1, sZ, x2y2, Z2);
    };

    let t = field_mul(d, field_mul(x1x2, y1y2));

    assert(field_mul(x1y1, x2y2) == field_mul(x1x2, y1y2)) by {
        lemma_four_factor_rearrange(x1, y1, x2, y2);
    };

    assert(tt2d_val == field_mul(field_mul(sT, T2), field_mul(2, d))) by {
        lemma_field_mul_comm(field_mul(2, d), T2);
        lemma_field_mul_assoc(sT, T2, field_mul(2, d));
    };

    let x1x2y1y2 = field_mul(x1x2, y1y2);
    assert(field_mul(field_mul(x1x2y1y2, z1z2), field_mul(2, d)) == field_mul(
        z1z2,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        lemma_field_mul_comm(x1x2y1y2, z1z2);
        lemma_field_mul_assoc(z1z2, x1x2y1y2, field_mul(2, d));
    };

    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    assert(tt2d_val == field_mul(z1z2, field_mul(2, t)));

    // STEP 4: Denominator factoring (Z/T swapped from add: sub uses 2Z-TT2d, 2Z+TT2d)
    let zz2 = field_add(zz_val, zz_val);
    assert(zz2 == field_mul(2, z1z2)) by {
        lemma_add_self_eq_double(zz_val);
    };

    let result_z = field_sub(zz2, tt2d_val);
    let result_t = field_add(zz2, tt2d_val);

    assert(field_mul(2, z1z2) == field_mul(z1z2, 2)) by {
        lemma_field_mul_comm(2nat, z1z2);
    };

    // result.Z = 2·z1z2 - z1z2·2t = z1z2·2(1-t)
    assert(field_mul(z1z2, field_mul(2, t)) == field_mul(field_mul(2, t), z1z2)) by {
        lemma_field_mul_comm(z1z2, field_mul(2, t));
    };
    assert(result_z == field_mul(z1z2, field_sub(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_sub(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_sub(2nat, field_mul(2, t)), z1z2);
    };

    assert(field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t))) by {
        lemma_field_mul_comm(2nat, field_sub(1, t));
        lemma_field_mul_distributes_over_sub_right(1, t, 2);
        lemma_field_mul_one_left(2nat);
        lemma_small_mod(2nat, p());
        lemma_field_mul_comm(t, 2nat);
    };
    assert(result_z == field_mul(z1z2, field_mul(2, field_sub(1, t))));

    // result.T = 2·z1z2 + z1z2·2t = z1z2·2(1+t)
    assert(result_t == field_mul(z1z2, field_add(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_add(2nat, field_mul(2, t), z1z2);
        lemma_field_mul_comm(field_add(2nat, field_mul(2, t)), z1z2);
    };

    assert(field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t))) by {
        lemma_field_mul_distributes_over_add(2, 1, t);
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    assert(result_t == field_mul(z1z2, field_mul(2, field_add(1, t))));

    assert(result_x == field_mul(z1z2, field_mul(2, num_x))) by {
        lemma_field_mul_assoc(2, z1z2, num_x);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_x);
    };

    assert(result_y == field_mul(z1z2, field_mul(2, num_y))) by {
        lemma_field_mul_assoc(2, z1z2, num_y);
        lemma_field_mul_comm(2nat, z1z2);
        lemma_field_mul_assoc(z1z2, 2, num_y);
    };

    // STEP 5: Reduce sub to add via neg: edwards_sub(x1,y1,x2,y2) = edwards_add(x1,y1,-x2,y2)
    let neg_x2 = field_neg(x2);
    let t_prime = field_mul(d, field_mul(field_mul(x1, neg_x2), field_mul(y1, y2)));
    assert(math_on_edwards_curve(neg_x2, y2) && field_sub(x1y2, y1x2) == field_add(
        x1y2,
        field_mul(y1, neg_x2),
    ) && field_sub(y1y2, x1x2) == field_add(y1y2, field_mul(x1, neg_x2)) && t_prime == field_neg(t)
        && field_sub(1nat, t_prime) == field_add(1nat, t) && field_add(1nat, t_prime) == field_sub(
        1nat,
        t,
    )) by {
        lemma_sub_via_negation(x1, y1, x2, y2, x1y2, y1x2, y1y2, x1x2, d, t);
    };

    // Affine result of edwards_add(x1, y1, -x2, y2)
    let aff_rx = field_mul(2, field_add(field_mul(x1, y2), field_mul(y1, neg_x2)));
    let aff_ry = field_mul(2, field_add(field_mul(y1, y2), field_mul(x1, neg_x2)));
    let aff_rz = field_mul(2, field_add(1, t_prime));
    let aff_rt = field_mul(2, field_sub(1, t_prime));

    assert(aff_rx == field_mul(2, num_x));
    assert(aff_ry == field_mul(2, num_y));
    assert(aff_rz == field_mul(2, field_sub(1, t)));
    assert(aff_rt == field_mul(2, field_add(1, t)));

    assert(result_x == field_mul(z1z2, aff_rx));
    assert(result_y == field_mul(z1z2, aff_ry));
    assert(result_z == field_mul(z1z2, aff_rz));
    assert(result_t == field_mul(z1z2, aff_rt));

    assert(aff_rz != 0 && aff_rt != 0 && math_on_edwards_curve(
        field_mul(aff_rx, field_inv(aff_rz)),
        field_mul(aff_ry, field_inv(aff_rt)),
    ) && field_mul(aff_rx, field_inv(aff_rz)) == edwards_add(x1, y1, neg_x2, y2).0 && field_mul(
        aff_ry,
        field_inv(aff_rt),
    ) == edwards_add(x1, y1, neg_x2, y2).1) by {
        lemma_completed_point_ratios(x1, y1, neg_x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);
    };

    // STEP 6: Cancel z1z2 from all ratios
    assert(z1z2 != 0) by {
        lemma_field_element_reduced(sZ);
        lemma_field_element_reduced(Z2);
        lemma_nonzero_product(sZ, Z2);
    };
    assert(z1z2 % p() != 0) by {
        lemma_mod_bound((sZ * Z2) as int, p() as int);
        lemma_field_element_reduced(z1z2);
    };
    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    assert(field_mul(z1z2, aff_rz) != 0 && field_mul(z1z2, aff_rt) != 0) by {
        lemma_cancel_z_from_ratios(aff_rx, aff_ry, aff_rz, aff_rt, z1z2);
    };
    assert(field_mul(field_mul(z1z2, aff_rx), field_inv(field_mul(z1z2, aff_rz))) == field_mul(
        aff_rx,
        field_inv(aff_rz),
    ) && field_mul(field_mul(z1z2, aff_ry), field_inv(field_mul(z1z2, aff_rt))) == field_mul(
        aff_ry,
        field_inv(aff_rt),
    )) by {
        lemma_cancel_z_from_ratios(aff_rx, aff_ry, aff_rz, aff_rt, z1z2);
    };

    // STEP 7: Connect to edwards_sub via projective_niels correspondence
    assert(projective_niels_point_as_affine_edwards(other) == edwards_point_as_affine(ep)) by {
        lemma_projective_niels_affine_equals_edwards_affine(other, ep);
    };
}

/// EdwardsPoint(X1,Y1,Z1,T1) + AffineNielsPoint → CompletedPoint.
/// The Niels point encodes affine (x2, y2) as (y2+x2, y2-x2, 2d·x2·y2).
///
/// Requires: self_point and other are valid; result fields match the
///   addition formulas (PP-MM, PP+MM, 2Z1+Txy2d, 2Z1-Txy2d).
///
/// Ensures: is_valid_completed_point(result) ∧
///   completed_point_as_affine_edwards(result) == edwards_add(self_affine, other_affine)
/// Same as ProjectiveNiels but factors out Z1 instead of Z1·Z2 (affine Niels has Z₂ = 1).
pub proof fn lemma_add_affine_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::AffineNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pp_val: nat,
    mm_val: nat,
    txy2d_val: nat,
    z2_val: nat,
)
    requires
// P₁ is well-formed and valid

        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        // P₂ (as AffineNiels) is valid
        is_valid_affine_niels_point(other),
        // PP = (Y₁+X₁)·(y₂+x₂)
        pp_val == field_mul(
            field_add(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.y_plus_x),
        ),
        // MM = (Y₁−X₁)·(y₂−x₂)
        mm_val == field_mul(
            field_sub(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.y_minus_x),
        ),
        // Txy2d = T₁·(2d·x₂y₂)
        txy2d_val == field_mul(
            fe51_as_canonical_nat(&self_point.T),
            fe51_as_canonical_nat(&other.xy2d),
        ),
        // 2Z₁ = Z₁ + Z₁
        z2_val == field_add(
            fe51_as_canonical_nat(&self_point.Z),
            fe51_as_canonical_nat(&self_point.Z),
        ),
        // result.X = PP − MM
        fe51_as_canonical_nat(&result.X) == field_sub(pp_val, mm_val),
        // result.Y = PP + MM
        fe51_as_canonical_nat(&result.Y) == field_add(pp_val, mm_val),
        // result.Z = 2Z₁ + Txy2d
        fe51_as_canonical_nat(&result.Z) == field_add(z2_val, txy2d_val),
        // result.T = 2Z₁ − Txy2d
        fe51_as_canonical_nat(&result.T) == field_sub(z2_val, txy2d_val),
    ensures
// The CompletedPoint is valid (Z ≠ 0, T ≠ 0)

        is_valid_completed_point(result),
        // Its affine projection equals edwards_add(P₁, P₂)
        completed_point_as_affine_edwards(result) == {
            let self_affine = edwards_point_as_affine(self_point);
            let other_affine = affine_niels_point_as_affine_edwards(other);
            edwards_add(self_affine.0, self_affine.1, other_affine.0, other_affine.1)
        },
{
    let sX = fe51_as_canonical_nat(&self_point.X);
    let sY = fe51_as_canonical_nat(&self_point.Y);
    let sZ = fe51_as_canonical_nat(&self_point.Z);
    let sT = fe51_as_canonical_nat(&self_point.T);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    assert(p() > 2) by {
        p_gt_2();
    };

    assert(sZ % p() != 0);  // from is_valid_edwards_point → math_is_valid_extended_edwards_point

    // Extract witness from is_valid_affine_niels_point
    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && #[trigger] affine_niels_corresponds_to_edwards(other, ep);
    let X2 = fe51_as_canonical_nat(&ep.X);
    let Y2 = fe51_as_canonical_nat(&ep.Y);
    let Z2 = fe51_as_canonical_nat(&ep.Z);

    let z2_inv = field_inv(Z2);
    let x2 = field_mul(X2, z2_inv);
    let y2 = field_mul(Y2, z2_inv);

    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));

    assert(math_on_edwards_curve(x1, y1)) by {
        lemma_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    };
    assert(math_on_edwards_curve(x2, y2)) by {
        lemma_valid_extended_point_affine_on_curve(X2, Y2, Z2, fe51_as_canonical_nat(&ep.T));
    };

    // Affine Niels correspondence: (y+x, y-x, 2dxy)  (already affine, no Z)
    assert(fe51_as_canonical_nat(&other.y_plus_x) == field_add(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.y_minus_x) == field_sub(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.xy2d) == field_mul(field_mul(field_mul(x2, y2), 2), d)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };

    // STEP 1: FOIL on PP and MM
    let result_x = field_sub(pp_val, mm_val);
    let result_y = field_add(pp_val, mm_val);

    // PP - MM = 2(Y1·x2 + X1·y2)  (note: x2, y2 are affine)
    assert(result_x == field_mul(2, field_add(field_mul(sY, x2), field_mul(sX, y2)))) by {
        lemma_pp_minus_mm(sY, sX, y2, x2);
    };
    // PP + MM = 2(Y1·y2 + X1·x2)
    assert(result_y == field_mul(2, field_add(field_mul(sY, y2), field_mul(sX, x2)))) by {
        lemma_pp_plus_mm(sY, sX, y2, x2);
    };

    // STEP 2: Y1·x2 = (y1·x2)·Z1 since Y1 = y1·Z1 (only factor Z1, x2 already affine)
    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    assert(field_mul(sY, x2) == field_mul(y1x2, sZ)) by {
        lemma_projective_affine_product_factor(sY, sZ, x2);
    };
    assert(field_mul(sX, y2) == field_mul(x1y2, sZ)) by {
        lemma_projective_affine_product_factor(sX, sZ, y2);
    };
    assert(field_mul(sY, y2) == field_mul(y1y2, sZ)) by {
        lemma_projective_affine_product_factor(sY, sZ, y2);
    };
    assert(field_mul(sX, x2) == field_mul(x1x2, sZ)) by {
        lemma_projective_affine_product_factor(sX, sZ, x2);
    };

    assert(field_add(field_mul(sY, x2), field_mul(sX, y2)) == field_mul(sZ, field_add(y1x2, x1y2)))
        by {
        lemma_reverse_distribute_add(y1x2, x1y2, sZ);
        lemma_field_mul_comm(field_add(y1x2, x1y2), sZ);
    };

    assert(field_add(field_mul(sY, y2), field_mul(sX, x2)) == field_mul(sZ, field_add(y1y2, x1x2)))
        by {
        lemma_reverse_distribute_add(y1y2, x1x2, sZ);
        lemma_field_mul_comm(field_add(y1y2, x1x2), sZ);
    };

    let num_x = field_add(y1x2, x1y2);
    let num_y = field_add(y1y2, x1x2);

    // result.X = 2·sZ·num_x = sZ·2·num_x
    assert(result_x == field_mul(sZ, field_mul(2, num_x))) by {
        lemma_field_mul_assoc(2, sZ, num_x);
        lemma_field_mul_comm(2nat, sZ);
        lemma_field_mul_assoc(sZ, 2, num_x);
    };

    // result.Y = sZ·2·num_y
    assert(result_y == field_mul(sZ, field_mul(2, num_y))) by {
        lemma_field_mul_assoc(2, sZ, num_y);
        lemma_field_mul_comm(2nat, sZ);
        lemma_field_mul_assoc(sZ, 2, num_y);
    };

    // STEP 3: Txy2d = T1·xy2d, rewrite T1 via Segre: T1 = (x1y1)·Z1
    let x1y1 = field_mul(x1, y1);
    let x2y2 = field_mul(x2, y2);

    // T1 = (x1y1)·Z1 via Segre invariant
    assert(sT == field_mul(x1y1, sZ) % p()) by {
        lemma_segre_t_derivation(sX, sY, sZ, sT);
    };

    let xy2d_spec = field_mul(field_mul(x2y2, 2), d);

    assert(field_mul(sT, xy2d_spec) == field_mul(field_mul(x1y1, sZ), xy2d_spec)) by {
        lemma_field_element_reduced(sT);
        lemma_mul_mod_noop_left(sT as int, xy2d_spec as int, p() as int);
        lemma_mul_mod_noop_left((field_mul(x1y1, sZ)) as int, xy2d_spec as int, p() as int);
    };

    assert(xy2d_spec == field_mul(x2y2, field_mul(2, d))) by {
        lemma_field_mul_assoc(x2y2, 2, d);
    };

    assert(field_mul(field_mul(x1y1, sZ), field_mul(x2y2, field_mul(2, d))) == field_mul(
        field_mul(x1y1, x2y2),
        field_mul(sZ, field_mul(2, d)),
    )) by {
        lemma_four_factor_rearrange(x1y1, sZ, x2y2, field_mul(2, d));
    };

    assert(field_mul(x1y1, x2y2) == field_mul(x1x2, y1y2)) by {
        lemma_four_factor_rearrange(x1, y1, x2, y2);
    };

    let t = field_mul(d, field_mul(x1x2, y1y2));
    let x1x2y1y2 = field_mul(x1x2, y1y2);

    assert(field_mul(x1x2y1y2, field_mul(sZ, field_mul(2, d))) == field_mul(
        sZ,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        lemma_field_mul_assoc(x1x2y1y2, sZ, field_mul(2, d));
        lemma_field_mul_comm(x1x2y1y2, sZ);
        lemma_field_mul_assoc(sZ, x1x2y1y2, field_mul(2, d));
    };

    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    assert(txy2d_val == field_mul(sZ, field_mul(2, t)));  // Txy2d = sZ·2t

    // STEP 4: result.Z = 2Z1 + sZ·2t = sZ·2(1+t),  result.T = 2Z1 - sZ·2t = sZ·2(1-t)
    assert(z2_val == field_mul(2, sZ)) by {
        lemma_add_self_eq_double(sZ);
    };

    let result_z = field_add(z2_val, txy2d_val);
    let result_t = field_sub(z2_val, txy2d_val);

    assert(field_mul(2, sZ) == field_mul(sZ, 2)) by {
        lemma_field_mul_comm(2nat, sZ);
    };

    assert(result_z == field_mul(sZ, field_add(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_add(2nat, field_mul(2, t), sZ);
        lemma_field_mul_comm(field_add(2nat, field_mul(2, t)), sZ);
    };

    assert(field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t))) by {
        lemma_field_mul_distributes_over_add(2, 1, t);
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    assert(result_z == field_mul(sZ, field_mul(2, field_add(1, t))));

    assert(field_mul(sZ, field_mul(2, t)) == field_mul(field_mul(2, t), sZ)) by {
        lemma_field_mul_comm(sZ, field_mul(2, t));
    };
    assert(result_t == field_mul(sZ, field_sub(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_sub(2nat, field_mul(2, t), sZ);
        lemma_field_mul_comm(field_sub(2nat, field_mul(2, t)), sZ);
    };

    assert(field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t))) by {
        lemma_field_mul_comm(2nat, field_sub(1, t));
        lemma_field_mul_distributes_over_sub_right(1, t, 2);
        lemma_field_mul_one_left(2nat);
        lemma_small_mod(2nat, p());
        lemma_field_mul_comm(t, 2nat);
    };
    assert(result_t == field_mul(sZ, field_mul(2, field_sub(1, t))));

    // STEP 5: Cancel sZ; result = sZ·(aff_rX : aff_rY : aff_rZ : aff_rT)
    let aff_rx = field_mul(2, field_add(x1y2, y1x2));
    let aff_ry = field_mul(2, field_add(y1y2, x1x2));
    let aff_rz = field_mul(2, field_add(1, t));
    let aff_rt = field_mul(2, field_sub(1, t));

    assert(num_x == field_add(x1y2, y1x2)) by {
        let pp = p();
        lemma_add_mod_noop(y1x2 as int, x1y2 as int, pp as int);
        lemma_add_mod_noop(x1y2 as int, y1x2 as int, pp as int);
    };

    assert(result_x == field_mul(sZ, aff_rx));
    assert(result_y == field_mul(sZ, aff_ry));
    assert(result_z == field_mul(sZ, aff_rz));
    assert(result_t == field_mul(sZ, aff_rt));

    assert(aff_rz != 0 && aff_rt != 0 && math_on_edwards_curve(
        field_mul(aff_rx, field_inv(aff_rz)),
        field_mul(aff_ry, field_inv(aff_rt)),
    ) && field_mul(aff_rx, field_inv(aff_rz)) == edwards_add(x1, y1, x2, y2).0 && field_mul(
        aff_ry,
        field_inv(aff_rt),
    ) == edwards_add(x1, y1, x2, y2).1) by {
        lemma_completed_point_ratios(x1, y1, x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);
    };

    assert(sZ != 0) by {
        assert(sZ % p() != 0);  // from is_valid_edwards_point → math_is_valid_extended_edwards_point
        if sZ == 0 {
            lemma_small_mod(0nat, p());
            assert((0nat % p()) == 0);
            assert(sZ % p() == 0);
            assert(false);
        }
    };
    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    assert(field_mul(sZ, aff_rz) != 0 && field_mul(sZ, aff_rt) != 0) by {
        lemma_cancel_z_from_ratios(aff_rx, aff_ry, aff_rz, aff_rt, sZ);
    };
    assert(field_mul(field_mul(sZ, aff_rx), field_inv(field_mul(sZ, aff_rz))) == field_mul(
        aff_rx,
        field_inv(aff_rz),
    ) && field_mul(field_mul(sZ, aff_ry), field_inv(field_mul(sZ, aff_rt))) == field_mul(
        aff_ry,
        field_inv(aff_rt),
    )) by {
        lemma_cancel_z_from_ratios(aff_rx, aff_ry, aff_rz, aff_rt, sZ);
    };

    // STEP 6: Connect to edwards_add via affine_niels correspondence
    assert(affine_niels_point_as_affine_edwards(other) == edwards_point_as_affine(ep)) by {
        lemma_affine_niels_affine_equals_edwards_affine(other, ep);
    };
}

/// EdwardsPoint(X1,Y1,Z1,T1) - AffineNielsPoint → CompletedPoint.
/// The Niels point encodes affine (x2, y2) as (y2+x2, y2-x2, 2d·x2·y2).
///
/// Requires: self_point and other are valid; result fields match the
///   sub formulas (PM-MP, PM+MP, 2Z1-Txy2d, 2Z1+Txy2d).
///
/// Ensures: is_valid_completed_point(result) ∧
///   completed_point_as_affine_edwards(result) == edwards_sub(self_affine, other_affine)
pub proof fn lemma_sub_affine_niels_completed_valid(
    self_point: crate::edwards::EdwardsPoint,
    other: crate::backend::serial::curve_models::AffineNielsPoint,
    result: crate::backend::serial::curve_models::CompletedPoint,
    pm_val: nat,
    mp_val: nat,
    txy2d_val: nat,
    z2_val: nat,
)
    requires
// P₁ is well-formed and valid

        is_well_formed_edwards_point(self_point),
        is_valid_edwards_point(self_point),
        // P₂ (as AffineNiels) is valid
        is_valid_affine_niels_point(other),
        // PM = (Y₁+X₁)·(y₂−x₂)  [note: swapped vs add]
        pm_val == field_mul(
            field_add(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.y_minus_x),
        ),
        // MP = (Y₁−X₁)·(y₂+x₂)  [note: swapped vs add]
        mp_val == field_mul(
            field_sub(fe51_as_canonical_nat(&self_point.Y), fe51_as_canonical_nat(&self_point.X)),
            fe51_as_canonical_nat(&other.y_plus_x),
        ),
        // Txy2d = T₁·(2d·x₂y₂)
        txy2d_val == field_mul(
            fe51_as_canonical_nat(&self_point.T),
            fe51_as_canonical_nat(&other.xy2d),
        ),
        // 2Z₁ = Z₁ + Z₁
        z2_val == field_add(
            fe51_as_canonical_nat(&self_point.Z),
            fe51_as_canonical_nat(&self_point.Z),
        ),
        // result.X = PM − MP
        fe51_as_canonical_nat(&result.X) == field_sub(pm_val, mp_val),
        // result.Y = PM + MP
        fe51_as_canonical_nat(&result.Y) == field_add(pm_val, mp_val),
        // result.Z = 2Z₁ − Txy2d  [note: minus vs add]
        fe51_as_canonical_nat(&result.Z) == field_sub(z2_val, txy2d_val),
        // result.T = 2Z₁ + Txy2d  [note: plus vs add]
        fe51_as_canonical_nat(&result.T) == field_add(z2_val, txy2d_val),
    ensures
// The CompletedPoint is valid (Z ≠ 0, T ≠ 0)

        is_valid_completed_point(result),
        // Its affine projection equals edwards_sub(P₁, P₂)
        completed_point_as_affine_edwards(result) == {
            let self_affine = edwards_point_as_affine(self_point);
            let other_affine = affine_niels_point_as_affine_edwards(other);
            edwards_sub(self_affine.0, self_affine.1, other_affine.0, other_affine.1)
        },
{
    let sX = fe51_as_canonical_nat(&self_point.X);
    let sY = fe51_as_canonical_nat(&self_point.Y);
    let sZ = fe51_as_canonical_nat(&self_point.Z);
    let sT = fe51_as_canonical_nat(&self_point.T);
    let d = fe51_as_canonical_nat(&EDWARDS_D);
    assert(p() > 2) by {
        p_gt_2();
    };

    assert(sZ % p() != 0);  // from is_valid_edwards_point → math_is_valid_extended_edwards_point

    let ep = choose|ep: crate::edwards::EdwardsPoint|
        is_valid_edwards_point(ep) && #[trigger] affine_niels_corresponds_to_edwards(other, ep);
    let X2 = fe51_as_canonical_nat(&ep.X);
    let Y2 = fe51_as_canonical_nat(&ep.Y);
    let Z2 = fe51_as_canonical_nat(&ep.Z);

    let z2_inv = field_inv(Z2);
    let x2 = field_mul(X2, z2_inv);
    let y2 = field_mul(Y2, z2_inv);

    let x1 = field_mul(sX, field_inv(sZ));
    let y1 = field_mul(sY, field_inv(sZ));

    assert(math_on_edwards_curve(x1, y1)) by {
        lemma_valid_extended_point_affine_on_curve(sX, sY, sZ, sT);
    };
    assert(math_on_edwards_curve(x2, y2)) by {
        lemma_valid_extended_point_affine_on_curve(X2, Y2, Z2, fe51_as_canonical_nat(&ep.T));
    };

    // Niels correspondence
    assert(fe51_as_canonical_nat(&other.y_plus_x) == field_add(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.y_minus_x) == field_sub(y2, x2)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };
    assert(fe51_as_canonical_nat(&other.xy2d) == field_mul(field_mul(field_mul(x2, y2), 2), d)) by {
        reveal(affine_niels_corresponds_to_edwards);
    };

    // STEP 1: Mixed FOIL on PM and MP (swapped Y+X / Y-X)
    let result_x = field_sub(pm_val, mp_val);
    let result_y = field_add(pm_val, mp_val);

    // PM - MP = 2(X1·y2 - Y1·x2)
    assert(result_x == field_mul(2, field_sub(field_mul(sX, y2), field_mul(sY, x2)))) by {
        lemma_pm_minus_mp(sY, sX, y2, x2);
    };
    // PM + MP = 2(Y1·y2 - X1·x2)
    assert(result_y == field_mul(2, field_sub(field_mul(sY, y2), field_mul(sX, x2)))) by {
        lemma_pm_plus_mp(sY, sX, y2, x2);
    };

    // STEP 2: Y1·x2 = (y1·x2)·Z1 since Y1 = y1·Z1 (factor out Z1 only)
    let y1x2 = field_mul(y1, x2);
    let x1y2 = field_mul(x1, y2);
    let y1y2 = field_mul(y1, y2);
    let x1x2 = field_mul(x1, x2);

    assert(field_mul(sY, x2) == field_mul(y1x2, sZ)) by {
        lemma_projective_affine_product_factor(sY, sZ, x2);
    };
    assert(field_mul(sX, y2) == field_mul(x1y2, sZ)) by {
        lemma_projective_affine_product_factor(sX, sZ, y2);
    };
    assert(field_mul(sY, y2) == field_mul(y1y2, sZ)) by {
        lemma_projective_affine_product_factor(sY, sZ, y2);
    };
    assert(field_mul(sX, x2) == field_mul(x1x2, sZ)) by {
        lemma_projective_affine_product_factor(sX, sZ, x2);
    };

    assert(field_sub(field_mul(sX, y2), field_mul(sY, x2)) == field_mul(sZ, field_sub(x1y2, y1x2)))
        by {
        lemma_reverse_distribute_sub(x1y2, y1x2, sZ);
        lemma_field_mul_comm(field_sub(x1y2, y1x2), sZ);
    };

    assert(field_sub(field_mul(sY, y2), field_mul(sX, x2)) == field_mul(sZ, field_sub(y1y2, x1x2)))
        by {
        lemma_reverse_distribute_sub(y1y2, x1x2, sZ);
        lemma_field_mul_comm(field_sub(y1y2, x1x2), sZ);
    };

    let num_x = field_sub(x1y2, y1x2);  // x1y2 - y1x2
    let num_y = field_sub(y1y2, x1x2);  // y1y2 - x1x2

    // result.X = sZ·2·num_x
    assert(result_x == field_mul(sZ, field_mul(2, num_x))) by {
        lemma_field_mul_assoc(2, sZ, num_x);
        lemma_field_mul_comm(2nat, sZ);
        lemma_field_mul_assoc(sZ, 2, num_x);
    };

    // result.Y = sZ·2·num_y
    assert(result_y == field_mul(sZ, field_mul(2, num_y))) by {
        lemma_field_mul_assoc(2, sZ, num_y);
        lemma_field_mul_comm(2nat, sZ);
        lemma_field_mul_assoc(sZ, 2, num_y);
    };

    // STEP 3: Txy2d = sZ·2t  (same derivation as add affine variant)
    let x1y1 = field_mul(x1, y1);
    let x2y2 = field_mul(x2, y2);

    // T1 = (x1y1)·Z1 via Segre invariant
    assert(sT == field_mul(x1y1, sZ) % p()) by {
        lemma_segre_t_derivation(sX, sY, sZ, sT);
    };

    let xy2d_spec = field_mul(field_mul(x2y2, 2), d);

    assert(field_mul(sT, xy2d_spec) == field_mul(field_mul(x1y1, sZ), xy2d_spec)) by {
        lemma_field_element_reduced(sT);
        lemma_mul_mod_noop_left(sT as int, xy2d_spec as int, p() as int);
        lemma_mul_mod_noop_left((field_mul(x1y1, sZ)) as int, xy2d_spec as int, p() as int);
    };

    assert(xy2d_spec == field_mul(x2y2, field_mul(2, d))) by {
        lemma_field_mul_assoc(x2y2, 2, d);
    };

    assert(field_mul(field_mul(x1y1, sZ), field_mul(x2y2, field_mul(2, d))) == field_mul(
        field_mul(x1y1, x2y2),
        field_mul(sZ, field_mul(2, d)),
    )) by {
        lemma_four_factor_rearrange(x1y1, sZ, x2y2, field_mul(2, d));
    };

    assert(field_mul(x1y1, x2y2) == field_mul(x1x2, y1y2)) by {
        lemma_four_factor_rearrange(x1, y1, x2, y2);
    };

    let t = field_mul(d, field_mul(x1x2, y1y2));
    let x1x2y1y2 = field_mul(x1x2, y1y2);

    assert(field_mul(x1x2y1y2, field_mul(sZ, field_mul(2, d))) == field_mul(
        sZ,
        field_mul(x1x2y1y2, field_mul(2, d)),
    )) by {
        lemma_field_mul_assoc(x1x2y1y2, sZ, field_mul(2, d));
        lemma_field_mul_comm(x1x2y1y2, sZ);
        lemma_field_mul_assoc(sZ, x1x2y1y2, field_mul(2, d));
    };

    assert(field_mul(x1x2y1y2, field_mul(2, d)) == field_mul(2, t)) by {
        lemma_field_mul_comm(x1x2y1y2, field_mul(2, d));
        lemma_field_mul_assoc(2, d, x1x2y1y2);
    };

    assert(txy2d_val == field_mul(sZ, field_mul(2, t)));

    // STEP 4: result.Z = 2Z1 - sZ·2t = sZ·2(1-t),  result.T = 2Z1 + sZ·2t = sZ·2(1+t)
    assert(z2_val == field_mul(2, sZ)) by {
        lemma_add_self_eq_double(sZ);
    };

    let result_z = field_sub(z2_val, txy2d_val);
    let result_t = field_add(z2_val, txy2d_val);

    assert(field_mul(2, sZ) == field_mul(sZ, 2)) by {
        lemma_field_mul_comm(2nat, sZ);
    };

    assert(field_mul(sZ, field_mul(2, t)) == field_mul(field_mul(2, t), sZ)) by {
        lemma_field_mul_comm(sZ, field_mul(2, t));
    };
    assert(result_z == field_mul(sZ, field_sub(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_sub(2nat, field_mul(2, t), sZ);
        lemma_field_mul_comm(field_sub(2nat, field_mul(2, t)), sZ);
    };

    assert(field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t))) by {
        lemma_field_mul_comm(2nat, field_sub(1, t));
        lemma_field_mul_distributes_over_sub_right(1, t, 2);
        lemma_field_mul_one_left(2nat);
        lemma_small_mod(2nat, p());
        lemma_field_mul_comm(t, 2nat);
    };
    assert(result_z == field_mul(sZ, field_mul(2, field_sub(1, t))));

    assert(result_t == field_mul(sZ, field_add(2nat, field_mul(2, t)))) by {
        lemma_reverse_distribute_add(2nat, field_mul(2, t), sZ);
        lemma_field_mul_comm(field_add(2nat, field_mul(2, t)), sZ);
    };

    assert(field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t))) by {
        lemma_field_mul_distributes_over_add(2, 1, t);
        lemma_field_mul_one_right(2nat);
        lemma_small_mod(2nat, p());
    };
    assert(result_t == field_mul(sZ, field_mul(2, field_add(1, t))));

    // STEP 5: Reduce sub to add via neg: edwards_sub(x1,y1,x2,y2) = edwards_add(x1,y1,-x2,y2)
    let neg_x2 = field_neg(x2);
    let t_prime = field_mul(d, field_mul(field_mul(x1, neg_x2), field_mul(y1, y2)));
    assert(math_on_edwards_curve(neg_x2, y2) && field_sub(x1y2, y1x2) == field_add(
        x1y2,
        field_mul(y1, neg_x2),
    ) && field_sub(y1y2, x1x2) == field_add(y1y2, field_mul(x1, neg_x2)) && t_prime == field_neg(t)
        && field_sub(1nat, t_prime) == field_add(1nat, t) && field_add(1nat, t_prime) == field_sub(
        1nat,
        t,
    )) by {
        lemma_sub_via_negation(x1, y1, x2, y2, x1y2, y1x2, y1y2, x1x2, d, t);
    };

    let aff_rx = field_mul(2, field_add(field_mul(x1, y2), field_mul(y1, neg_x2)));
    let aff_ry = field_mul(2, field_add(field_mul(y1, y2), field_mul(x1, neg_x2)));
    let aff_rz = field_mul(2, field_add(1, t_prime));
    let aff_rt = field_mul(2, field_sub(1, t_prime));

    assert(aff_rx == field_mul(2, num_x));
    assert(aff_ry == field_mul(2, num_y));
    assert(aff_rz == field_mul(2, field_sub(1, t)));
    assert(aff_rt == field_mul(2, field_add(1, t)));

    assert(result_x == field_mul(sZ, aff_rx));
    assert(result_y == field_mul(sZ, aff_ry));
    assert(result_z == field_mul(sZ, aff_rz));
    assert(result_t == field_mul(sZ, aff_rt));

    assert(aff_rz != 0 && aff_rt != 0 && math_on_edwards_curve(
        field_mul(aff_rx, field_inv(aff_rz)),
        field_mul(aff_ry, field_inv(aff_rt)),
    ) && field_mul(aff_rx, field_inv(aff_rz)) == edwards_add(x1, y1, neg_x2, y2).0 && field_mul(
        aff_ry,
        field_inv(aff_rt),
    ) == edwards_add(x1, y1, neg_x2, y2).1) by {
        lemma_completed_point_ratios(x1, y1, neg_x2, y2, aff_rx, aff_ry, aff_rz, aff_rt);
    };

    assert(sZ != 0) by {
        assert(sZ % p() != 0);  // from is_valid_edwards_point → math_is_valid_extended_edwards_point
        if sZ == 0 {
            lemma_small_mod(0nat, p());
            assert((0nat % p()) == 0);
            assert(sZ % p() == 0);
            assert(false);
        }
    };
    assert(aff_rz % p() != 0) by {
        lemma_field_element_reduced(aff_rz);
    };
    assert(aff_rt % p() != 0) by {
        lemma_field_element_reduced(aff_rt);
    };
    assert(field_mul(sZ, aff_rz) != 0 && field_mul(sZ, aff_rt) != 0) by {
        lemma_cancel_z_from_ratios(aff_rx, aff_ry, aff_rz, aff_rt, sZ);
    };
    assert(field_mul(field_mul(sZ, aff_rx), field_inv(field_mul(sZ, aff_rz))) == field_mul(
        aff_rx,
        field_inv(aff_rz),
    ) && field_mul(field_mul(sZ, aff_ry), field_inv(field_mul(sZ, aff_rt))) == field_mul(
        aff_ry,
        field_inv(aff_rt),
    )) by {
        lemma_cancel_z_from_ratios(aff_rx, aff_ry, aff_rz, aff_rt, sZ);
    };

    // STEP 7: Connect to edwards_sub via affine_niels correspondence
    assert(affine_niels_point_as_affine_edwards(other) == edwards_point_as_affine(ep)) by {
        lemma_affine_niels_affine_equals_edwards_affine(other, ep);
    };
}

} // verus!
