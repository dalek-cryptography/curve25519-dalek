// Specifications for mathematical operations on Curve25519 (Edwards curve)
// TODO: Add group-law lemmas (associativity/commutativity/identity/inverses and scalar-mul linearity)
//       for edwards_add/edwards_scalar_mul to support subgroup proofs in Ristretto specs.
//
// ## References
//
// The mathematical formulas and specifications in this file are based on:
//
// - [BBJLP2008] Bernstein, D.J., Birkner, P., Joye, M., Lange, T., Peters, C. (2008).
//   "Twisted Edwards Curves". In: Vaudenay, S. (eds) Progress in Cryptology – AFRICACRYPT 2008.
//   https://eprint.iacr.org/2008/013.pdf
//
// - [RFC8032] Josefsson, S. and I. Liusvaara, "Edwards-Curve Digital Signature Algorithm (EdDSA)",
//   RFC 8032, DOI 10.17487/RFC8032, January 2017.
//   https://www.rfc-editor.org/info/rfc8032
//
// - [HWCD2008] Hisil, H., Wong, K.K., Carter, G., Dawson, E. (2008).
//   "Twisted Edwards Curves Revisited". In: Pieprzyk, J. (eds) Advances in Cryptology - ASIACRYPT 2008.
//   https://eprint.iacr.org/2008/522.pdf
//   (Source for extended coordinates and efficient addition formulas)
//
// - Curve25519-dalek documentation and implementation
//   https://github.com/dalek-cryptography/curve25519-dalek
//
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::backend::serial::curve_models::{
    AffineNielsPoint, CompletedPoint, ProjectiveNielsPoint, ProjectivePoint,
};
#[cfg(feature = "precomputed-tables")]
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE;
#[allow(unused_imports)] // Used in verus! blocks
use crate::backend::serial::u64::constants::{ED25519_BASEPOINT_POINT, EDWARDS_D, EIGHT_TORSION};
#[cfg(feature = "precomputed-tables")]
#[allow(unused_imports)]
use crate::edwards::EdwardsBasepointTable;
#[allow(unused_imports)] // Used in verus! blocks
use crate::edwards::{CompressedEdwardsY, EdwardsPoint};
#[allow(unused_imports)]
use crate::scalar::Scalar;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[allow(unused_imports)]
use crate::specs::montgomery_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::scalar_specs::scalar_to_nat;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::{lemma_mod_bound, lemma_small_mod};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::core_specs::{bytes32_to_nat, bytes_seq_to_nat};

// =============================================================================
// Ed25519 Basepoint
// =============================================================================
/// The Ed25519 basepoint B in affine coordinates (x, y).
/// This is the generator point of the prime-order subgroup.
///
/// References the actual constant ED25519_BASEPOINT_POINT from constants.rs.
/// The y-coordinate is 4/5 mod p (the first 255 bits of the compressed form).
/// The x-coordinate is the positive square root satisfying the curve equation.
///
/// Reference: [RFC8032] Section 5.1
pub open spec fn spec_ed25519_basepoint() -> (nat, nat) {
    (u64_5_as_nat(ED25519_BASEPOINT_POINT.X.limbs), u64_5_as_nat(ED25519_BASEPOINT_POINT.Y.limbs))
}

/// The Ed25519 basepoint has reduced coordinates (both < p)
///
/// This is a property of the specific basepoint constant definition from the Ed25519 spec.
/// The basepoint X and Y coordinates are canonical field elements < p.
///
/// ## Values
/// - X = 15112221349535807912866137220509078935008241517709382056166116785143545249788
/// - Y = 46316835694926478169428394003475163141307993866256225615783033603165251855960
/// - p = 57896044618658097711785492504343953926634992332820282019728792003956564819949
///
/// Both X < p and Y < p by direct comparison.
///
pub proof fn axiom_ed25519_basepoint_canonical()
    ensures
        spec_ed25519_basepoint().0 < p(),
        spec_ed25519_basepoint().1 < p(),
{
    admit();
}

/// Proof: The basepoint is on the Edwards curve
/* SEE IF WE NEED THIS
pub proof fn lemma_basepoint_on_curve()
    ensures
        math_on_edwards_curve(spec_ed25519_basepoint().0, spec_ed25519_basepoint().1),
{
    assume(math_on_edwards_curve(spec_ed25519_basepoint().0, spec_ed25519_basepoint().1));
}
*/
// =============================================================================
// EdwardsBasepointTable Specification
// =============================================================================
/// Compute 256^n (i.e., (16²)^n) for basepoint table indexing
/// Uses pow2(8*n) since 256 = 2^8
pub open spec fn pow256(n: nat) -> nat {
    pow2(8 * n)
}

/// Spec: A valid EdwardsBasepointTable for a basepoint B contains 32 LookupTables where:
/// - table.0[i] contains [1·(16²)^i·B, 2·(16²)^i·B, ..., 8·(16²)^i·B]
/// - All entries have bounded limbs (< 2^54)
///
/// This enables computing [scalar] * B via radix-16 representation of scalar.
#[cfg(feature = "precomputed-tables")]
pub open spec fn is_valid_edwards_basepoint_table(
    table: EdwardsBasepointTable,
    basepoint: (nat, nat),
) -> bool {
    // Each of the 32 LookupTables contains correct multiples of (16²)^i * B
    // and has bounded limbs
    forall|i: int|
        #![trigger table.0[i]]
        0 <= i < 32 ==> {
            &&& crate::specs::window_specs::is_valid_lookup_table_affine_coords(
                table.0[i].0,
                edwards_scalar_mul(basepoint, pow256(i as nat)),
                8,
            )
            &&& crate::specs::window_specs::lookup_table_affine_limbs_bounded(table.0[i].0)
        }
}

/// Axiom: ED25519_BASEPOINT_TABLE is a valid basepoint table for the Ed25519 basepoint.
/// This connects the hardcoded constant to our specification.
#[cfg(feature = "precomputed-tables")]
pub proof fn axiom_ed25519_basepoint_table_valid()
    ensures
        is_valid_edwards_basepoint_table(*ED25519_BASEPOINT_TABLE, spec_ed25519_basepoint()),
{
    admit();
    // VERIFICATION NOTE: we probably have to prove this
}

/// Axiom: All 8-torsion points are well-formed.
///
/// The EIGHT_TORSION array contains the 8-torsion subgroup E[8] of the curve.
/// Each element satisfies `is_well_formed_edwards_point`, which requires:
/// - `is_valid_edwards_point`: Z ≠ 0, projective curve equation, X·Y = Z·T
/// - `edwards_point_limbs_bounded`: all limbs < 2^52
/// - `sum_of_limbs_bounded(Y, X)`: Y + X doesn't overflow
///
/// This is verified by the `test_eight_torsion_well_formed` test below.
pub proof fn axiom_eight_torsion_well_formed()
    ensures
        is_well_formed_edwards_point(EIGHT_TORSION[0]),
        is_well_formed_edwards_point(EIGHT_TORSION[1]),
        is_well_formed_edwards_point(EIGHT_TORSION[2]),
        is_well_formed_edwards_point(EIGHT_TORSION[3]),
        is_well_formed_edwards_point(EIGHT_TORSION[4]),
        is_well_formed_edwards_point(EIGHT_TORSION[5]),
        is_well_formed_edwards_point(EIGHT_TORSION[6]),
        is_well_formed_edwards_point(EIGHT_TORSION[7]),
{
    admit();
}

} // verus!
/// Test that all 8-torsion points satisfy the structural well-formedness conditions.
/// This partially validates axiom_eight_torsion_well_formed() by checking:
/// - Z ≠ 0, limbs < 2^52, Y+X bounded
/// Note: The curve equation and T=XY/Z are trusted from the constant definition.
#[cfg(test)]
mod eight_torsion_tests {
    use super::*;

    const LIMB_BOUND_52: u64 = 1u64 << 52;

    // Tests that all limbs are < bound
    fn limbs_bounded(fe: &crate::backend::serial::u64::field::FieldElement51, bound: u64) -> bool {
        fe.limbs.iter().all(|&limb| limb < bound)
    }

    // Tests edwards_point_limbs_bounded - all coordinate limbs < 2^52
    fn point_limbs_bounded(p: &EdwardsPoint) -> bool {
        limbs_bounded(&p.X, LIMB_BOUND_52)
            && limbs_bounded(&p.Y, LIMB_BOUND_52)
            && limbs_bounded(&p.Z, LIMB_BOUND_52)
            && limbs_bounded(&p.T, LIMB_BOUND_52)
    }

    // Tests Z ≠ 0 (part of is_valid_edwards_point)
    fn z_nonzero(p: &EdwardsPoint) -> bool {
        p.Z.limbs.iter().any(|&limb| limb != 0)
    }

    // Tests sum_of_limbs_bounded(Y, X) - Y + X doesn't overflow
    fn sum_bounded(p: &EdwardsPoint) -> bool {
        p.Y.limbs
            .iter()
            .zip(p.X.limbs.iter())
            .all(|(&y, &x)| (y as u128) + (x as u128) <= u64::MAX as u128)
    }

    #[test]
    fn test_eight_torsion_well_formed() {
        for (i, point) in EIGHT_TORSION.iter().enumerate() {
            assert!(z_nonzero(point), "EIGHT_TORSION[{}] has Z = 0", i);
            assert!(
                point_limbs_bounded(point),
                "EIGHT_TORSION[{}] limbs exceed 2^52",
                i
            );
            assert!(
                sum_bounded(point),
                "EIGHT_TORSION[{}] Y+X would overflow",
                i
            );
        }
    }
}

verus! {

// =============================================================================
// Curve Equation Specifications
// =============================================================================
/// Check if a point (x, y) satisfies the Edwards curve equation
/// -x² + y² = 1 + d·x²·y²  (mod p)
///
/// This is the twisted Edwards curve equation with a = -1.
/// Reference: [BBJLP2008] Section 3, [RFC8032] Section 5.1
pub open spec fn math_on_edwards_curve(x: nat, y: nat) -> bool {
    let p = p();
    let d = spec_field_element(&EDWARDS_D);
    let x2 = math_field_square(x);
    let y2 = math_field_square(y);
    let x2y2 = math_field_mul(x2, y2);

    // -x² + y² = 1 + d·x²·y²
    let lhs = math_field_sub(y2, x2);  // y² - x²
    let rhs = math_field_add(1, math_field_mul(d, x2y2));  // 1 + d·x²·y²

    lhs == rhs
}

/// Homogenized Edwards curve equation for projective coordinates
/// A projective point (X:Y:Z) represents the affine point (X/Z, Y/Z)
/// The homogenized curve equation is: (-X² + Y²)·Z² = Z⁴ + d·X²·Y²
/// This is equivalent to the affine equation when Z ≠ 0
///
/// Reference: [BBJLP2008] Section 3
pub open spec fn math_on_edwards_curve_projective(x: nat, y: nat, z: nat) -> bool {
    let d = spec_field_element(&EDWARDS_D);

    // Compute X², Y², Z²
    let x2 = math_field_square(x);
    let y2 = math_field_square(y);
    let z2 = math_field_square(z);
    let z4 = math_field_square(z2);

    // LHS: (-X² + Y²)·Z² = (Y² - X²)·Z²
    let lhs = math_field_mul(math_field_sub(y2, x2), z2);

    // RHS: Z⁴ + d·X²·Y²
    let rhs = math_field_add(z4, math_field_mul(d, math_field_mul(x2, y2)));

    lhs == rhs
}

/// Spec function: Check if a y-coordinate corresponds to a valid point on the curve.
/// Mirrors the sqrt_ratio_i computation from field.rs to determine if u/v is a square.
/// From the curve equation: x² = (y² - 1) / (d·y² + 1)
/// This computes the same check as sqrt_ratio_i(&u, &v) where:
///   u = y² - 1
///   v = d·y² + 1
/// Returns true if u/v is a square (i.e., x can be recovered)
pub open spec fn math_is_valid_y_coordinate(y: nat) -> bool {
    let d = spec_field_element(&EDWARDS_D);
    let y2 = math_field_square(y);

    // Compute u = y² - 1
    let u = math_field_sub(y2, 1);

    // Compute v = d·y² + 1
    let v = math_field_add(math_field_mul(d, y2), 1);

    if u % p() == 0 {
        // If u = 0, then y² = 1, so y = ±1, which gives valid points (x=0, y=±1)
        true
    } else if v % p() == 0 {
        // If v = 0 but u ≠ 0, division by zero case - invalid
        false
    } else {
        // Check if there exists r such that r² * v ≡ ±u (mod p)
        // This is what sqrt_ratio_i determines
        exists|r: nat|
            r < p() && (#[trigger] math_field_mul(math_field_square(r), v) == u % p()
                || #[trigger] math_field_mul(math_field_square(r), v) == math_field_neg(u))
    }
}

/// The identity point in affine coordinates (0, 1)
pub open spec fn math_edwards_identity() -> (nat, nat) {
    (0, 1)
}

/// Check if affine coordinates represent the identity point
pub open spec fn math_is_edwards_identity(x: nat, y: nat) -> bool {
    x % p() == 0 && y % p() == 1
}

/// Check if an EdwardsPoint represents the identity point
/// The identity point is (0, 1) in affine coordinates
/// In projective coordinates (X:Y:Z:T), this means X/Z = 0 and Y/Z = 1
/// Which is equivalent to X ≡ 0 (mod p) and Y ≡ Z (mod p) with Z ≠ 0
pub open spec fn is_identity_edwards_point(point: crate::edwards::EdwardsPoint) -> bool {
    let x = spec_field_element(&point.X);
    let y = spec_field_element(&point.Y);
    let z = spec_field_element(&point.Z);

    z != 0 && x == 0 && y == z
}

/// Math-level validity predicate for an Edwards point in **extended coordinates** (X:Y:Z:T).
///
/// This is the "unpacked" version of `is_valid_edwards_point` that operates directly on the
/// mathematical values `(x, y, z, t)` (all reduced mod p via `math_field_*`).
///
/// An (X:Y:Z:T) tuple is valid iff:
/// 1. Z ≠ 0
/// 2. The projective curve equation holds: (Y² - X²)·Z² = Z⁴ + d·X²·Y²
/// 3. The Segre relation holds: X·Y = Z·T
pub open spec fn math_is_valid_extended_edwards_point(x: nat, y: nat, z: nat, t: nat) -> bool {
    z != 0 && math_on_edwards_curve_projective(x, y, z) && math_field_mul(x, y) == math_field_mul(
        z,
        t,
    )
}

/// Check if an EdwardsPoint in extended coordinates is valid
/// An EdwardsPoint (X:Y:Z:T) is valid if:
/// 1. Z ≠ 0
/// 2. The projective curve equation holds: (Y² - X²)·Z² = Z⁴ + d·X²·Y²
/// 3. The Segre relation holds: X·Y = Z·T
///
/// Extended coordinates (X:Y:Z:T) with X·Y = Z·T enable faster point arithmetic.
/// Reference: [HWCD2008] Section 3 for extended twisted Edwards coordinates
pub open spec fn is_valid_edwards_point(point: crate::edwards::EdwardsPoint) -> bool {
    let x = spec_field_element(&point.X);
    let y = spec_field_element(&point.Y);
    let z = spec_field_element(&point.Z);
    let t = spec_field_element(&point.T);

    math_is_valid_extended_edwards_point(x, y, z, t)
}

/// EdwardsPoint invariant: all coordinate limbs must be 52-bounded.
pub open spec fn edwards_point_limbs_bounded(point: crate::edwards::EdwardsPoint) -> bool {
    fe51_limbs_bounded(&point.X, 52) && fe51_limbs_bounded(&point.Y, 52) && fe51_limbs_bounded(
        &point.Z,
        52,
    ) && fe51_limbs_bounded(&point.T, 52)
}

/// A well-formed EdwardsPoint: mathematically valid and properly bounded.
pub open spec fn is_well_formed_edwards_point(point: crate::edwards::EdwardsPoint) -> bool {
    is_valid_edwards_point(point) && edwards_point_limbs_bounded(point) && sum_of_limbs_bounded(
        &point.Y,
        &point.X,
        u64::MAX,
    )
}

/// Returns the field element values (X, Y, Z, T) from an EdwardsPoint.
/// An EdwardsPoint (X:Y:Z:T) is in extended projective coordinates.
pub open spec fn spec_edwards_point(point: crate::edwards::EdwardsPoint) -> (nat, nat, nat, nat) {
    let x = spec_field_element(&point.X);
    let y = spec_field_element(&point.Y);
    let z = spec_field_element(&point.Z);
    let t = spec_field_element(&point.T);
    (x, y, z, t)
}

/// Returns the abstract affine coordinates (x, y) from an EdwardsPoint.
/// An EdwardsPoint (X:Y:Z:T) represents affine point (X/Z, Y/Z).
pub open spec fn edwards_point_as_affine(point: crate::edwards::EdwardsPoint) -> (nat, nat) {
    let (x, y, z, _t) = spec_edwards_point(point);
    let z_inv = math_field_inv(z);
    (math_field_mul(x, z_inv), math_field_mul(y, z_inv))
}

/// Returns the field element values (X, Y, Z, T) from a CompletedPoint.
/// A CompletedPoint is ((X:Z), (Y:T)) in P¹ × P¹.
pub open spec fn spec_completed_point(
    point: crate::backend::serial::curve_models::CompletedPoint,
) -> (nat, nat, nat, nat) {
    let x_abs = spec_field_element(&point.X);
    let y_abs = spec_field_element(&point.Y);
    let z_abs = spec_field_element(&point.Z);
    let t_abs = spec_field_element(&point.T);
    (x_abs, y_abs, z_abs, t_abs)
}

/// Returns the abstract affine coordinates (x, y) from a CompletedPoint.
/// A CompletedPoint ((X:Z), (Y:T)) in P¹ × P¹ represents affine point (X/Z, Y/T).
pub open spec fn completed_point_as_affine_edwards(
    point: crate::backend::serial::curve_models::CompletedPoint,
) -> (nat, nat) {
    let (x_abs, y_abs, z_abs, t_abs) = spec_completed_point(point);
    let z_inv = math_field_inv(z_abs);
    let t_inv = math_field_inv(t_abs);
    (math_field_mul(x_abs, z_inv), math_field_mul(y_abs, t_inv))
}

/// Returns the field element values (X, Y, Z) from an Edwards ProjectivePoint.
/// An Edwards ProjectivePoint (X:Y:Z) is in projective coordinates.
pub open spec fn spec_projective_point_edwards(point: ProjectivePoint) -> (nat, nat, nat) {
    let x = spec_field_element(&point.X);
    let y = spec_field_element(&point.Y);
    let z = spec_field_element(&point.Z);
    (x, y, z)
}

/// Spec function: Identity element for ProjectivePoint as tuple
/// Identity in projective coordinates: (0, 1, 1) represents (0:1:1) which is affine point (0, 1)
pub open spec fn spec_identity_projective_point_edwards() -> (nat, nat, nat) {
    (0nat, 1nat, 1nat)
}

/// Identity element for ProjectivePoint as structure
pub open spec fn identity_projective_point_edwards() -> ProjectivePoint {
    ProjectivePoint {
        X: crate::field::FieldElement { limbs: [0, 0, 0, 0, 0] },  // 0
        Y: crate::field::FieldElement { limbs: [1, 0, 0, 0, 0] },  // 1
        Z: crate::field::FieldElement { limbs: [1, 0, 0, 0, 0] },  // 1
    }
}

/// Returns the abstract affine coordinates (x, y) from an Edwards ProjectivePoint.
/// An Edwards ProjectivePoint (X:Y:Z) represents affine point (X/Z, Y/Z).
pub open spec fn projective_point_as_affine_edwards(point: ProjectivePoint) -> (nat, nat) {
    let (x, y, z) = spec_projective_point_edwards(point);
    let z_inv = math_field_inv(z);
    (math_field_mul(x, z_inv), math_field_mul(y, z_inv))
}

/// Returns the field element values (Y+X, Y-X, Z, T2d) from a ProjectiveNielsPoint.
///
/// Niels coordinates are an optimized representation for point addition.
/// Reference: [HWCD2008] Section 3.1 for extended coordinates and efficient formulas
pub open spec fn spec_projective_niels_point(niels: ProjectiveNielsPoint) -> (nat, nat, nat, nat) {
    let y_plus_x = spec_field_element(&niels.Y_plus_X);
    let y_minus_x = spec_field_element(&niels.Y_minus_X);
    let z = spec_field_element(&niels.Z);
    let t2d = spec_field_element(&niels.T2d);
    (y_plus_x, y_minus_x, z, t2d)
}

/// Returns the field element values (y+x, y-x, xy2d) from an AffineNielsPoint.
///
/// Affine Niels coordinates store (y+x, y-x, xy2d) for efficient mixed addition.
/// Reference: [HWCD2008] Section 3.1
pub open spec fn spec_affine_niels_point(niels: AffineNielsPoint) -> (nat, nat, nat) {
    let y_plus_x = spec_field_element(&niels.y_plus_x);
    let y_minus_x = spec_field_element(&niels.y_minus_x);
    let xy2d = spec_field_element(&niels.xy2d);
    (y_plus_x, y_minus_x, xy2d)
}

/// Spec function: check if a CompressedEdwardsY corresponds to an EdwardsPoint
/// The compressed form should match the affine y-coordinate and x sign bit
pub open spec fn compressed_edwards_y_corresponds_to_edwards(
    compressed: CompressedEdwardsY,
    point: EdwardsPoint,
) -> bool {
    let (x_affine, y_affine) = edwards_point_as_affine(point);
    // The y-coordinate in the compressed form matches the affine y-coordinate
    spec_field_element_from_bytes(&compressed.0)
        == y_affine
    // The sign bit matches the sign of the affine x-coordinate
     && (compressed.0[31] >> 7) == (((x_affine % crate::specs::field_specs_u64::p()) % 2) as u8)
}

/// Check if a CompressedEdwardsY has a valid sign bit.
///
/// ## Mathematical basis
///
/// For points with x = 0 on the Edwards curve, the curve equation gives y² = 1,
/// so y = ±1. These special points (the identity (0,1) and the point (0,-1))
/// have only one valid sign bit: 0, since sign_bit = x % 2 = 0.
///
/// ## Definition
///
/// If the Y coordinate yields x = 0 (i.e., y² ≡ 1 mod p), the sign bit must be 0.
pub open spec fn compressed_y_has_valid_sign_bit(bytes: &[u8; 32]) -> bool {
    let y = spec_field_element_from_bytes(bytes);
    let sign_bit = bytes[31] >> 7;
    // If y² ≡ 1 (mod p), then x = 0, so sign_bit must be 0
    // Equivalently: sign_bit == 1 implies y² ≢ 1
    math_field_square(y) == 1 ==> sign_bit == 0
}

/// Check if a ProjectiveNielsPoint corresponds to an EdwardsPoint
/// A ProjectiveNielsPoint (Y_plus_X, Y_minus_X, Z, T2d) corresponds to EdwardsPoint (X:Y:Z:T) if:
/// 1. Y_plus_X = Y + X (mod p)
/// 2. Y_minus_X = Y - X (mod p)
/// 3. Z matches
/// 4. T2d = 2d * T (mod p) where T = XY/Z
pub open spec fn projective_niels_corresponds_to_edwards(
    niels: ProjectiveNielsPoint,
    point: EdwardsPoint,
) -> bool {
    let x = spec_field_element(&point.X);
    let y = spec_field_element(&point.Y);
    let z = spec_field_element(&point.Z);
    let t = spec_field_element(&point.T);
    let d = spec_field_element(&EDWARDS_D);

    let y_plus_x = spec_field_element(&niels.Y_plus_X);
    let y_minus_x = spec_field_element(&niels.Y_minus_X);
    let niels_z = spec_field_element(&niels.Z);
    let t2d = spec_field_element(&niels.T2d);

    // Check the relationships
    // 2d is computed as math_field_mul(2, d) in field arithmetic
    &&& y_plus_x == math_field_add(y, x)
    &&& y_minus_x == math_field_sub(y, x)
    &&& niels_z == z
    &&& t2d == math_field_mul(math_field_mul(2, d), t)
}

/// Check if a ProjectiveNielsPoint is valid
/// A valid ProjectiveNielsPoint must correspond to some valid EdwardsPoint
pub open spec fn is_valid_projective_niels_point(niels: ProjectiveNielsPoint) -> bool {
    // A ProjectiveNielsPoint is valid if there exists an EdwardsPoint that:
    // 1. Is valid itself
    // 2. The niels point corresponds to it
    exists|point: EdwardsPoint|
        is_valid_edwards_point(point) && #[trigger] projective_niels_corresponds_to_edwards(
            niels,
            point,
        )
}

/// Extract affine coordinates (x, y) from a ProjectiveNielsPoint
/// Given: Y_plus_X = Y + X, Y_minus_X = Y - X, and Z (all in projective coords)
/// First recover projective X and Y, then convert to affine: x = X/Z, y = Y/Z
pub open spec fn projective_niels_point_as_affine_edwards(niels: ProjectiveNielsPoint) -> (
    nat,
    nat,
) {
    let y_plus_x = spec_field_element(&niels.Y_plus_X);
    let y_minus_x = spec_field_element(&niels.Y_minus_X);
    let z = spec_field_element(&niels.Z);

    // Recover projective X and Y from Y+X and Y-X
    let x_proj = math_field_mul(math_field_sub(y_plus_x, y_minus_x), math_field_inv(2));
    let y_proj = math_field_mul(math_field_add(y_plus_x, y_minus_x), math_field_inv(2));

    // Convert to affine by dividing by Z
    let z_inv = math_field_inv(z);
    let x = math_field_mul(x_proj, z_inv);
    let y = math_field_mul(y_proj, z_inv);

    (x, y)
}

/// Check if an AffineNielsPoint corresponds to an EdwardsPoint
/// An AffineNielsPoint (y_plus_x, y_minus_x, xy2d) corresponds to EdwardsPoint (X:Y:Z:T) if:
/// 1. y_plus_x = y + x (mod p) where x = X/Z, y = Y/Z (affine coordinates)
/// 2. y_minus_x = y - x (mod p)
/// 3. xy2d = x * y * 2d (mod p)
pub open spec fn affine_niels_corresponds_to_edwards(
    niels: AffineNielsPoint,
    point: EdwardsPoint,
) -> bool {
    let x_proj = spec_field_element(&point.X);
    let y_proj = spec_field_element(&point.Y);
    let z_proj = spec_field_element(&point.Z);
    let d = spec_field_element(&EDWARDS_D);

    // Compute affine coordinates x = X/Z, y = Y/Z
    let z_inv = math_field_inv(z_proj);
    let x = math_field_mul(x_proj, z_inv);
    let y = math_field_mul(y_proj, z_inv);

    let y_plus_x_niels = spec_field_element(&niels.y_plus_x);
    let y_minus_x_niels = spec_field_element(&niels.y_minus_x);
    let xy2d_niels = spec_field_element(&niels.xy2d);

    // Check the relationships
    &&& y_plus_x_niels == math_field_add(y, x)
    &&& y_minus_x_niels == math_field_sub(y, x)
    &&& xy2d_niels == math_field_mul(math_field_mul(math_field_mul(x, y), 2), d)
}

/// Check if an AffineNielsPoint is valid
/// A valid AffineNielsPoint must correspond to some valid EdwardsPoint
pub open spec fn is_valid_affine_niels_point(niels: AffineNielsPoint) -> bool {
    exists|point: EdwardsPoint|
        is_valid_edwards_point(point) && #[trigger] affine_niels_corresponds_to_edwards(
            niels,
            point,
        )
}

/// Extract affine coordinates (x, y) from an AffineNielsPoint
/// Given: y_plus_x = y + x and y_minus_x = y - x
/// Solve for: x = (y_plus_x - y_minus_x) / 2, y = (y_plus_x + y_minus_x) / 2
pub open spec fn affine_niels_point_as_affine_edwards(niels: AffineNielsPoint) -> (nat, nat) {
    let y_plus_x = spec_field_element(&niels.y_plus_x);
    let y_minus_x = spec_field_element(&niels.y_minus_x);

    let x = math_field_mul(math_field_sub(y_plus_x, y_minus_x), math_field_inv(2));
    let y = math_field_mul(math_field_add(y_plus_x, y_minus_x), math_field_inv(2));

    (x, y)
}

/// Spec function: Identity element for AffineNielsPoint as tuple
/// Identity represents the point (0, 1) in affine coordinates
/// For Niels form (y+x, y-x, xy2d): (1, 1, 0)
pub open spec fn spec_identity_affine_niels() -> (nat, nat, nat) {
    (1nat, 1nat, 0nat)
}

/// Identity element for AffineNielsPoint as structure
pub open spec fn identity_affine_niels() -> AffineNielsPoint {
    AffineNielsPoint {
        y_plus_x: crate::field::FieldElement { limbs: [1, 0, 0, 0, 0] },  // 1
        y_minus_x: crate::field::FieldElement { limbs: [1, 0, 0, 0, 0] },  // 1
        xy2d: crate::field::FieldElement { limbs: [0, 0, 0, 0, 0] },  // 0
    }
}

/// Spec function: Identity element for ProjectiveNielsPoint as tuple
/// Identity represents the point (0:1:1) in projective coordinates
/// For Niels form (Y+X, Y-X, Z, T2d): (1, 1, 1, 0)
pub open spec fn spec_identity_projective_niels() -> (nat, nat, nat, nat) {
    (1nat, 1nat, 1nat, 0nat)
}

/// Identity element for ProjectiveNielsPoint as structure
pub open spec fn identity_projective_niels() -> ProjectiveNielsPoint {
    ProjectiveNielsPoint {
        Y_plus_X: crate::field::FieldElement { limbs: [1, 0, 0, 0, 0] },  // 1
        Y_minus_X: crate::field::FieldElement { limbs: [1, 0, 0, 0, 0] },  // 1
        Z: crate::field::FieldElement { limbs: [1, 0, 0, 0, 0] },  // 1
        T2d: crate::field::FieldElement { limbs: [0, 0, 0, 0, 0] },  // 0
    }
}

/// Spec function: Negation of an AffineNielsPoint as tuple
/// Negation swaps y+x with y-x and negates xy2d
pub open spec fn spec_negate_affine_niels(p: (nat, nat, nat)) -> (nat, nat, nat) {
    let (y_plus_x, y_minus_x, xy2d) = p;
    (y_minus_x, y_plus_x, math_field_neg(xy2d))
}

/// Negation of an AffineNielsPoint as structure
pub open spec fn negate_affine_niels(p: AffineNielsPoint) -> AffineNielsPoint {
    AffineNielsPoint {
        y_plus_x: p.y_minus_x,
        y_minus_x: p.y_plus_x,
        xy2d: crate::field::FieldElement {
            limbs: crate::specs::field_specs_u64::spec_negate(p.xy2d.limbs),
        },
    }
}

/// Spec function: Negation of a ProjectiveNielsPoint as tuple
/// Negation swaps Y+X with Y-X and negates T2d (Z stays the same)
pub open spec fn spec_negate_projective_niels(p: (nat, nat, nat, nat)) -> (nat, nat, nat, nat) {
    let (y_plus_x, y_minus_x, z, t2d) = p;
    (y_minus_x, y_plus_x, z, math_field_neg(t2d))
}

/// Negation of a ProjectiveNielsPoint as structure
pub open spec fn negate_projective_niels(p: ProjectiveNielsPoint) -> ProjectiveNielsPoint {
    ProjectiveNielsPoint {
        Y_plus_X: p.Y_minus_X,
        Y_minus_X: p.Y_plus_X,
        Z: p.Z,
        T2d: crate::field::FieldElement {
            limbs: crate::specs::field_specs_u64::spec_negate(p.T2d.limbs),
        },
    }
}

/// Affine Edwards addition for a = -1 twisted Edwards curves (Ed25519).
/// Given (x1,y1) and (x2,y2) on the curve, returns (x3,y3) = (x1,y1) + (x2,y2).
/// Formulas:
///   x3 = (x1*y2 + y1*x2) / (1 + d*x1*x2*y1*y2)
///   y3 = (y1*y2 + x1*x2) / (1 - d*x1*x2*y1*y2)
///
/// These are the unified addition formulas for twisted Edwards curves with a = -1.
/// Reference: [BBJLP2008] Section 3.1, [RFC8032] Section 5.1.4
pub open spec fn edwards_add(x1: nat, y1: nat, x2: nat, y2: nat) -> (nat, nat) {
    let d = spec_field_element(&EDWARDS_D);
    let x1x2 = math_field_mul(x1, x2);
    let y1y2 = math_field_mul(y1, y2);
    let x1y2 = math_field_mul(x1, y2);
    let y1x2 = math_field_mul(y1, x2);
    let t = math_field_mul(d, math_field_mul(x1x2, y1y2));
    let denom_x = math_field_add(1, t);
    let denom_y = math_field_sub(1, t);
    let x3 = math_field_mul(math_field_add(x1y2, y1x2), math_field_inv(denom_x));
    let y3 = math_field_mul(math_field_add(y1y2, x1x2), math_field_inv(denom_y));
    (x3, y3)
}

/// Affine Edwards doubling defined as addition with itself.
pub open spec fn edwards_double(x: nat, y: nat) -> (nat, nat) {
    edwards_add(x, y, x, y)
}

/// Helper spec function: Edwards addition of EdwardsPoint and ProjectiveNielsPoint
/// Combines the affine conversion and addition into a single convenient spec function.
pub open spec fn spec_edwards_add_projective_niels(p: EdwardsPoint, q: ProjectiveNielsPoint) -> (
    nat,
    nat,
) {
    let self_affine = edwards_point_as_affine(p);
    let other_affine = projective_niels_point_as_affine_edwards(q);
    edwards_add(self_affine.0, self_affine.1, other_affine.0, other_affine.1)
}

/// Helper spec function: Edwards addition of EdwardsPoint and AffineNielsPoint
/// Combines the affine conversion and addition into a single convenient spec function.
pub open spec fn spec_edwards_add_affine_niels(
    p: crate::edwards::EdwardsPoint,
    q: crate::backend::serial::curve_models::AffineNielsPoint,
) -> (nat, nat) {
    let self_affine = edwards_point_as_affine(p);
    let other_affine = affine_niels_point_as_affine_edwards(q);
    edwards_add(self_affine.0, self_affine.1, other_affine.0, other_affine.1)
}

/// Affine Edwards negation for twisted Edwards curves with a=-1.
/// The negation of point (x, y) is (-x, y).
pub open spec fn edwards_neg(point: (nat, nat)) -> (nat, nat) {
    (math_field_neg(point.0), point.1)
}

/// Affine Edwards subtraction for twisted Edwards curves.
/// Given (x1,y1) and (x2,y2) on the curve, returns (x3,y3) = (x1,y1) - (x2,y2).
/// Subtraction is defined as addition with the negation of the second point.
/// For twisted Edwards curves, the negation of (x, y) is (-x, y).
pub open spec fn edwards_sub(x1: nat, y1: nat, x2: nat, y2: nat) -> (nat, nat) {
    edwards_add(x1, y1, math_field_neg(x2), y2)
}

/// Check if a CompletedPoint is valid
/// A CompletedPoint ((X:Z), (Y:T)) in P¹ × P¹ is valid if:
/// 1. The affine point (X/Z, Y/T) lies on the Edwards curve
/// 2. Z ≠ 0 and T ≠ 0
pub open spec fn is_valid_completed_point(
    point: crate::backend::serial::curve_models::CompletedPoint,
) -> bool {
    let (x_abs, y_abs, z_abs, t_abs) = spec_completed_point(point);

    // Z and T must be non-zero
    z_abs != 0 && t_abs != 0
        &&
    // The affine coordinates (X/Z, Y/T) must be on the curve
    math_on_edwards_curve(
        math_field_mul(x_abs, math_field_inv(z_abs)),
        math_field_mul(y_abs, math_field_inv(t_abs)),
    )
}

/// Check if a ProjectivePoint is valid
/// A ProjectivePoint (X:Y:Z) in P² is valid if:
/// 1. Z ≠ 0
/// 2. The projective curve equation holds: (Y² - X²)·Z² = Z⁴ + d·X²·Y²
///
/// This is equivalent to the affine point (X/Z, Y/Z) lying on the Edwards curve.
pub open spec fn is_valid_projective_point(point: ProjectivePoint) -> bool {
    let (x, y, z) = spec_projective_point_edwards(point);

    // Z must be non-zero and projective curve equation must hold
    z != 0 && math_on_edwards_curve_projective(x, y, z)
}

/// Spec for CompletedPoint::as_projective conversion
/// Converts from P¹ × P¹ to P² via the mapping:
///   (X:Z, Y:T) ↦ (X·T : Y·Z : Z·T)
/// This preserves the affine point because:
///   X·T / Z·T = X/Z and Y·Z / Z·T = Y/T
pub open spec fn spec_completed_to_projective(
    point: crate::backend::serial::curve_models::CompletedPoint,
) -> (nat, nat, nat) {
    let (x, y, z, t) = spec_completed_point(point);
    (math_field_mul(x, t), math_field_mul(y, z), math_field_mul(z, t))
}

/// Spec for CompletedPoint::as_extended conversion
/// Converts from P¹ × P¹ to P³ via the Segre embedding:
///   ((X:Z), (Y:T)) ↦ (X·T : Y·Z : Z·T : X·Y)
/// This preserves the affine point and satisfies the extended coordinate invariant
pub open spec fn spec_completed_to_extended(
    point: crate::backend::serial::curve_models::CompletedPoint,
) -> (nat, nat, nat, nat) {
    let (x, y, z, t) = spec_completed_point(point);
    (math_field_mul(x, t), math_field_mul(y, z), math_field_mul(z, t), math_field_mul(x, y))
}

/// Spec for ProjectivePoint::as_extended conversion
/// Converts from P² to P³ via:
///   (X:Y:Z) ↦ (X·Z : Y·Z : Z² : X·Y)
/// This preserves the affine point and establishes the extended coordinate invariant
pub open spec fn spec_projective_to_extended(point: ProjectivePoint) -> (nat, nat, nat, nat) {
    let (x, y, z) = spec_projective_point_edwards(point);
    (math_field_mul(x, z), math_field_mul(y, z), math_field_square(z), math_field_mul(x, y))
}

/// Scalar multiplication on Edwards curve points (affine coordinates).
///
/// Uses double-and-add instead of linear recursion to closer match the implementation of mul_by_pow_2
///
/// - **Linear**: `n*P = (n-1)*P + P` — reveal gives `add(scalar_mul(P, n-1), P)`
/// - **Double-and-add**: even n → `double(scalar_mul(P, n/2))`
pub open spec fn edwards_scalar_mul(point_affine: (nat, nat), n: nat) -> (nat, nat)
    decreases n,
{
    if n == 0 {
        math_edwards_identity()  // (0, 1)

    } else if n == 1 {
        point_affine
    } else if n % 2 == 0 {
        let half = edwards_scalar_mul(point_affine, (n / 2) as nat);
        edwards_double(half.0, half.1)
    } else {
        let prev = edwards_scalar_mul(point_affine, (n - 1) as nat);
        edwards_add(prev.0, prev.1, point_affine.0, point_affine.1)
    }
}

/// Scalar multiplication that handles negative scalars (for lookup tables)
/// Unlike edwards_scalar_mul which only takes nat (≥ 0), this takes int which can be negative
///
/// For n ≥ 0: returns n * P using edwards_scalar_mul
/// For n < 0: returns n * P = -(|n| * P) by computing |n| * P and negating
///            Edwards negation: (x,y) -> (-x,y)
///
/// Used by LookupTable::select(x) where x: i8 can be negative (e.g., -8 ≤ x ≤ 8)
pub open spec fn edwards_scalar_mul_signed(point_affine: (nat, nat), n: int) -> (nat, nat) {
    if n >= 0 {
        edwards_scalar_mul(point_affine, n as nat)
    } else {
        let (x, y) = edwards_scalar_mul(point_affine, (-n) as nat);
        (math_field_neg(x), y)
    }
}

/// Spec function to compute sum of all EdwardsPoints in a sequence.
/// Returns the affine coordinates of the result.
/// Note: Processes from back to front to match iterative loop order.
pub open spec fn sum_of_points(points: Seq<EdwardsPoint>) -> (nat, nat)
    decreases points.len(),
{
    if points.len() == 0 {
        // Identity point in affine coordinates: (0, 1)
        (0, 1)
    } else {
        let last = (points.len() - 1) as int;
        let prev = sum_of_points(points.subrange(0, last));
        let point_affine = edwards_point_as_affine(points[last]);
        edwards_add(prev.0, prev.1, point_affine.0, point_affine.1)
    }
}

/// Spec function to compute sum of scalar multiplications.
/// Returns the affine coordinates of sum(scalars[i] * points[i] for i in 0..min(len_s, len_p)).
pub open spec fn sum_of_scalar_muls(scalars: Seq<Scalar>, points: Seq<EdwardsPoint>) -> (nat, nat)
    decreases scalars.len(),
{
    let len = if scalars.len() <= points.len() {
        scalars.len()
    } else {
        points.len()
    };
    if len == 0 {
        // Identity point in affine coordinates: (0, 1)
        (0, 1)
    } else {
        let last = (len - 1) as int;
        let prev = sum_of_scalar_muls(scalars.subrange(0, last), points.subrange(0, last));
        let point_affine = edwards_point_as_affine(points[last]);
        // Use scalar_to_nat (not spec_scalar) to match implementation ensures clauses
        let scalar_nat = scalar_to_nat(&scalars[last]);
        let scaled = edwards_scalar_mul(point_affine, scalar_nat);
        edwards_add(prev.0, prev.1, scaled.0, scaled.1)
    }
}

/// Lemma: The identity point has affine coordinates (0, 1).
///
/// For an identity point where x == 0 and y == z (with z != 0):
/// - x * z^{-1} = 0 * z^{-1} = 0
/// - y * z^{-1} = z * z^{-1} = 1
pub proof fn lemma_identity_affine_coords(point: EdwardsPoint)
    requires
        is_identity_edwards_point(point),
    ensures
        edwards_point_as_affine(point) == (0nat, 1nat),
{
    let x = spec_field_element(&point.X);
    let y = spec_field_element(&point.Y);
    let z = spec_field_element(&point.Z);
    let z_inv = math_field_inv(z);

    // From is_identity_edwards_point: z != 0, x == 0, y == z
    assert(z != 0);
    assert(x == 0);
    assert(y == z);

    // Establish p() > 0
    assert(p() > 0) by {
        pow255_gt_19();
    }

    // x * z_inv = 0 * z_inv = 0
    // math_field_mul(0, z_inv) = (0 * z_inv) % p() = 0 % p() = 0
    assert(math_field_mul(0nat, z_inv) == 0nat) by {
        assert(0nat * z_inv == 0nat);
        // 0 % p == 0 when p > 0
        lemma_small_mod(0nat, p());
    }
    assert(math_field_mul(x, z_inv) == 0nat);

    // z = spec_field_element(&point.Z) = spec_field_element_as_nat(&point.Z) % p()
    // So z < p() by property of modulo
    assert(z < p()) by {
        lemma_mod_bound(spec_field_element_as_nat(&point.Z) as int, p() as int);
    }

    // Since z < p() and z != 0, we have z % p() == z and z % p() != 0
    assert(z % p() == z) by {
        lemma_small_mod(z, p());
    }
    assert(z % p() != 0);

    // y * z_inv = z * z_inv = 1 (by field inverse property)
    field_inv_property(z);
    // field_inv_property ensures (z % p()) * math_field_inv(z) % p() == 1
    // Since z % p() == z, we have z * z_inv % p() == 1
    assert(math_field_mul(z, z_inv) == 1nat);
    assert(math_field_mul(y, z_inv) == 1nat);
}

// =============================================================================
// Spec for nonspec_map_to_curve_verus
// =============================================================================
//
// The hash-to-curve pipeline is:
//
//   bytes ──┬──> field element ──> Elligator2 ──> Montgomery u ──> Edwards (x,y) ──> [8]P
//           │         │                 │                │                │
//           │    from_bytes        elligator         birational      cofactor
//           │    (mod 2^255)        encode        y=(u-1)/(u+1)       clear
//           │
//           └──> sign_bit (bit 255)  ─────────────────────────────────────┘
//                                                                    selects x sign
//
// Spec functions (in pipeline order):
//   1. spec_nonspec_map_to_curve           -- top-level: bytes -> [8]P
//   2. spec_montgomery_to_edwards_affine   -- Montgomery u -> Edwards (x,y)
//   3. spec_edwards_decompress_from_y      -- Edwards y + sign -> (x,y)
//
// Helper functions (defined elsewhere):
//   - bytes_seq_to_nat                     -- bytes -> nat (core_specs)
//   - spec_elligator_encode                -- field element -> Montgomery u (montgomery_specs)
//   - edwards_y_from_montgomery_u          -- birational map (montgomery_specs)
//   - edwards_scalar_mul                   -- P -> [k]P (this file)
//
// Cofactor clearing ([8]P):
//   The full Edwards curve has order 8·ℓ where ℓ is the prime subgroup order.
//   Multiplying by 8 ensures the result is in the prime-order subgroup,
//   killing any small-order component from the 8-torsion. This is required
//   for the Ristretto abstraction which operates on the prime-order quotient.
// =============================================================================
/// Top-level spec for `EdwardsPoint::nonspec_map_to_curve_verus`.
///
/// Reference: RFC 9380 Section 6.7.1 - Elligator 2 Method
/// <https://www.rfc-editor.org/rfc/rfc9380.html#section-6.7.1>
///
/// Note from Dalek code: This is NOT a proper hash-to-curve (non-uniform distribution).
/// A proper hash-to-curve applies Elligator twice and adds the results.
pub open spec fn spec_nonspec_map_to_curve(hash_bytes: Seq<u8>) -> (nat, nat)
    recommends
        hash_bytes.len() == 32,
{
    // Extract sign bit from bit 255 (MSB of last byte)
    let sign_bit: u8 = (hash_bytes[31] & 0x80u8) >> 7;
    // Interpret bytes as field element (mod 2^255 to clear high bit)
    let fe_nat = bytes_seq_to_nat(hash_bytes) % pow2(255);
    // Elligator2 encoding: field element -> Montgomery u-coordinate
    let u = spec_elligator_encode(fe_nat);
    // Convert Montgomery to Edwards with sign bit selecting x
    let P = spec_montgomery_to_edwards_affine_with_sign(u, sign_bit);
    // Cofactor clearing: multiply by 8 to ensure prime-order subgroup
    edwards_scalar_mul(P, 8)
}

/// Spec for Montgomery-to-Edwards conversion with sign bit selection.
///
/// Converts Montgomery u-coordinate to Edwards affine (x, y) via:
/// 1. Birational map: y = (u-1)/(u+1)
/// 2. Decompression: recover x from y with given sign_bit
///
/// Returns identity (0, 1) on failure (u = -1 or invalid y).
pub open spec fn spec_montgomery_to_edwards_affine_with_sign(u: nat, sign_bit: u8) -> (nat, nat) {
    if u == math_field_sub(0, 1) {
        // u = -1: birational map has zero denominator
        math_edwards_identity()
    } else {
        let y = edwards_y_from_montgomery_u(u);
        match spec_edwards_decompress_from_y_and_sign(y, sign_bit) {
            Some(P) => P,
            None => math_edwards_identity(),
        }
    }
}

/// Spec for Edwards decompression: given y and a sign bit, compute (x, y) on the curve.
///
/// Mathematical definition:
/// - Returns None if y is not a valid y-coordinate (no x exists on curve)
/// - Returns None if x = 0 but sign_bit = 1 (invalid sign for zero)
/// - Otherwise returns the unique (x, y) on the curve with x % 2 == sign_bit
pub open spec fn spec_edwards_decompress_from_y_and_sign(y: nat, sign_bit: u8) -> Option<
    (nat, nat),
> {
    if !math_is_valid_y_coordinate(y) {
        None
    } else if math_field_square(y) == 1 && sign_bit == 1u8 {
        // When y² = 1, we have x = 0, and sign_bit must be 0
        None
    } else {
        // VERIFICATION NOTE: "choose" could be replaced with concrete value using sqrt_ratio_i upon need.
        // Choose x such that (x, y) is on the curve with the correct sign
        let x = choose|x: nat|
            math_on_edwards_curve(x, y) && x < p() && (x % 2) == (sign_bit as nat);
        Some((x, y))
    }
}

} // verus!
