// Specifications for mathematical operations on Curve25519
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::backend::serial::curve_models::{
    AffineNielsPoint, ProjectiveNielsPoint, ProjectivePoint,
};
#[allow(unused_imports)] // Used in verus! blocks
use crate::backend::serial::u64::constants::EDWARDS_D;
#[allow(unused_imports)] // Used in verus! blocks
use crate::edwards::{CompressedEdwardsY, EdwardsPoint};
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
use vstd::prelude::*;

verus! {

/// Edwards curve equation: -x² + y² = 1 + d·x²·y²
/// where d = -121665/121666 (mod p)
/// Check if a point (x, y) satisfies the Edwards curve equation
/// -x² + y² = 1 + d·x²·y²  (mod p)
pub open spec fn on_edwards_curve(x: nat, y: nat) -> bool {
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
pub open spec fn on_edwards_curve_projective(x: nat, y: nat, z: nat) -> bool {
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
pub open spec fn is_valid_y_coordinate(y: nat) -> bool {
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
pub open spec fn edwards_identity_affine() -> (nat, nat) {
    (0, 1)
}

/// Check if affine coordinates represent the identity point
pub open spec fn is_edwards_identity(x: nat, y: nat) -> bool {
    x % p() == 0 && y % p() == 1
}

/// Check if an EdwardsPoint represents the identity point
/// The identity point is (0, 1) in affine coordinates
/// In projective coordinates (X:Y:Z:T), this means X/Z = 0 and Y/Z = 1
/// Which is equivalent to X ≡ 0 (mod p) and Y ≡ Z (mod p) with Z ≠ 0
pub open spec fn is_identity(point: crate::edwards::EdwardsPoint) -> bool {
    let x = spec_field_element(&point.X);
    let y = spec_field_element(&point.Y);
    let z = spec_field_element(&point.Z);

    z != 0 && x == 0 && y == z
}

/// Check if an EdwardsPoint in projective coordinates is valid
/// An EdwardsPoint (X:Y:Z:T) is valid if:
/// 1. The affine point (X/Z, Y/Z) lies on the Edwards curve
/// 2. The extended coordinate satisfies T = X*Y/Z
/// 3. Z ≠ 0
pub open spec fn is_valid_edwards_point(point: crate::edwards::EdwardsPoint) -> bool {
    let x = spec_field_element(&point.X);
    let y = spec_field_element(&point.Y);
    let z = spec_field_element(&point.Z);
    let t = spec_field_element(&point.T);

    // Z must be non-zero
    z != 0 &&
    // The affine coordinates (X/Z, Y/Z) must be on the curve
    on_edwards_curve(math_field_mul(x, math_field_inv(z)), math_field_mul(y, math_field_inv(z)))
        &&
    // Extended coordinate must satisfy T = X*Y/Z
    t == math_field_mul(math_field_mul(x, y), math_field_inv(z))
}

/// Returns the abstract affine coordinates (x, y) of this point.
pub open spec fn affine_coords(point: crate::edwards::EdwardsPoint) -> (nat, nat) {
    let x_abs = spec_field_element(&point.X);
    let y_abs = spec_field_element(&point.Y);
    let z_abs = spec_field_element(&point.Z);
    let z_inv = math_field_inv(z_abs);
    (math_field_mul(x_abs, z_inv), math_field_mul(y_abs, z_inv))
}

/// Check if a CompressedEdwardsY represents the identity point
/// The identity point is (0, 1) in affine coordinates
/// When compressed, this is represented as y=1 with sign bit 0
pub open spec fn is_compressed_identity(compressed: CompressedEdwardsY) -> bool {
    // Extract the y-coordinate (identity has y = 1)
    spec_field_element_from_bytes(&compressed.0) == 1
        &&
    // Sign bit should be 0 (since x = 0)
    (compressed.0[31] >> 7) == 0
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

} // verus!
