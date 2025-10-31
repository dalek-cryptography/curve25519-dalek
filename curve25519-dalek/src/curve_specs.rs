// Specifications for mathematical operations on Curve25519
use crate::backend::serial::u64::field_lemmas::field_core::*;
use crate::field_specs::*;
use vstd::prelude::*;

verus! {

/// Edwards curve equation: -x² + y² = 1 + d·x²·y²
/// where d = -121665/121666 (mod p)
/// Check if a point (x, y) satisfies the Edwards curve equation
/// -x² + y² = 1 + d·x²·y²  (mod p)
pub open spec fn on_edwards_curve(x: nat, y: nat) -> bool {
    let p = p();
    let d = field_element(&crate::backend::serial::u64::constants::EDWARDS_D);
    let x2 = field_square(x);
    let y2 = field_square(y);
    let x2y2 = field_mul(x2, y2);

    // -x² + y² = 1 + d·x²·y²
    let lhs = field_sub(y2, x2);  // y² - x²
    let rhs = field_add(1, field_mul(d, x2y2));  // 1 + d·x²·y²

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
    let d = field_element(&crate::backend::serial::u64::constants::EDWARDS_D);
    let y2 = field_square(y);

    // Compute u = y² - 1
    let u = field_sub(y2, 1);

    // Compute v = d·y² + 1
    let v = field_add(field_mul(d, y2), 1);

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
            r < p() && (#[trigger] field_mul(field_square(r), v) == u % p() || #[trigger] field_mul(
                field_square(r),
                v,
            ) == field_neg(u))
    }
}

/// Spec: The identity point in affine coordinates (0, 1)
pub open spec fn edwards_identity_affine() -> (nat, nat) {
    (0, 1)
}

/// Spec: Check if affine coordinates represent the identity point
pub open spec fn is_edwards_identity(x: nat, y: nat) -> bool {
    x % p() == 0 && y % p() == 1
}

/// Spec: Check if an EdwardsPoint represents the identity point
/// The identity point is (0, 1) in affine coordinates
/// In projective coordinates (X:Y:Z:T), this means X/Z = 0 and Y/Z = 1
/// Which is equivalent to X ≡ 0 (mod p) and Y ≡ Z (mod p) with Z ≠ 0
pub open spec fn is_identity(point: crate::edwards::EdwardsPoint) -> bool {
    let x = field_element(&point.X);
    let y = field_element(&point.Y);
    let z = field_element(&point.Z);

    z != 0 && x == 0 && y == z
}

/// Spec: Check if an EdwardsPoint in projective coordinates is valid
/// An EdwardsPoint (X:Y:Z:T) is valid if:
/// 1. The affine point (X/Z, Y/Z) lies on the Edwards curve
/// 2. The extended coordinate satisfies T = X*Y/Z
/// 3. Z ≠ 0
pub open spec fn is_valid_edwards_point(point: crate::edwards::EdwardsPoint) -> bool {
    let x = field_element(&point.X);
    let y = field_element(&point.Y);
    let z = field_element(&point.Z);
    let t = field_element(&point.T);

    // Z must be non-zero
    z != 0 &&
    // The affine coordinates (X/Z, Y/Z) must be on the curve
    on_edwards_curve(field_mul(x, field_inv(z)), field_mul(y, field_inv(z)))
        &&
    // Extended coordinate must satisfy T = X*Y/Z
    t == field_mul(field_mul(x, y), field_inv(z))
}

/// Returns the abstract affine coordinates (x, y) of this point.
pub open spec fn affine_coords(point: crate::edwards::EdwardsPoint) -> (nat, nat) {
    let x_abs = field_element(&point.X);
    let y_abs = field_element(&point.Y);
    let z_abs = field_element(&point.Z);
    let z_inv = field_inv(z_abs);
    (field_mul(x_abs, z_inv), field_mul(y_abs, z_inv))
}

/// Spec: Check if a CompressedEdwardsY represents the identity point
/// The identity point is (0, 1) in affine coordinates
/// When compressed, this is represented as y=1 with sign bit 0
pub open spec fn is_compressed_identity(compressed: crate::edwards::CompressedEdwardsY) -> bool {
    // Extract the y-coordinate (identity has y = 1)
    field_element_from_bytes(&compressed.0) == 1
        &&
    // Sign bit should be 0 (since x = 0)
    (compressed.0[31] >> 7) == 0
}

} // verus!
