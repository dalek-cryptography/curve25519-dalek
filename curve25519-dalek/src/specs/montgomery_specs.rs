//! Specifications for Montgomery curve operations on Curve25519.
//!
//! ## Montgomery Curve (Curve25519)
//!
//! Curve equation: `B·v² = u·(u² + A·u + 1)` with `A = 486662`, `B = 1`.
//!
//! Point representations:
//! - **Affine**: `(u, v)` satisfying the curve equation, plus point at infinity `∞`
//! - **Projective x-only**: `(U:W)` where affine `u = U/W`; infinity when `W = 0`
//!
//! ## Contents
//!
//! - **MontgomeryAffine**: Affine point type with `Infinity` and `Finite { u, v }`
//! - **Group operations**: `montgomery_add`, `montgomery_neg`, `montgomery_sub`
//! - **Scalar multiplication**: `montgomery_scalar_mul` computing `[n]P`
//! - **Projective representation**: specs connecting `(U:W)` to affine points
//! - **Edwards-Montgomery maps**: birational equivalence `u = (1+y)/(1-y)`
//! - **Elligator2**: hash-to-curve mapping
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::MONTGOMERY_A;
#[allow(unused_imports)]
use crate::constants::APLUS2_OVER_FOUR;
#[allow(unused_imports)]
use crate::constants::X25519_BASEPOINT;
#[allow(unused_imports)]
use crate::montgomery::ProjectivePoint;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
use vstd::prelude::*;

verus! {

/// Affine Montgomery point: either infinity or a finite point (u, v).
///
/// General Montgomery curve: `B·v² = u·(u² + A·u + 1)`.
/// For Curve25519: `A = 486662`, `B = 1`, so the equation simplifies to `v² = u·(u² + A·u + 1)`.
pub enum MontgomeryAffine {
    /// Point at infinity (identity element of the group)
    Infinity,
    /// Finite point with u-coordinate and v-coordinate
    Finite { u: nat, v: nat },
}

/// Check if `(u, v)` satisfies the Montgomery curve equation `v² = u·(u² + A·u + 1)`.
pub open spec fn math_on_montgomery_curve(u: nat, v: nat) -> bool {
    let a = spec_field_element(&MONTGOMERY_A);
    let u2 = math_field_square(u);
    let u3 = math_field_mul(u, u2);
    let v2 = math_field_square(v);

    // v² = u³ + A·u² + u
    let rhs = math_field_add(math_field_add(u3, math_field_mul(a, u2)), u);

    v2 == rhs
}

/// Check if a MontgomeryAffine point is valid.
/// A point is valid if it's either:
/// - Infinity (the identity element), or
/// - A finite point (u, v) that satisfies the Montgomery curve equation
pub open spec fn is_valid_montgomery_affine(point: MontgomeryAffine) -> bool {
    match point {
        MontgomeryAffine::Infinity => true,
        MontgomeryAffine::Finite { u, v } => math_on_montgomery_curve(u, v),
    }
}

/// Compute f(u) = u^3 + A*u^2 + u over the field.
pub open spec fn montgomery_rhs(u: nat) -> nat {
    let A = spec_field_element(&MONTGOMERY_A);
    let u2 = math_field_mul(u, u);  // u^2
    let u3 = math_field_mul(u2, u);  // u^3
    let Au2 = math_field_mul(A, u2);  // A*u^2
    math_field_add(math_field_add(u3, Au2), u)  // u^3 + A*u^2 + u

}

/// Choose a canonical square root.
/// Return the sqrt(r) whose least-significant bit is 0.
/// (This matches Ed25519’s canonical-sign rule.)
pub open spec fn canonical_sqrt(r: nat) -> nat
    recommends
        math_is_square(r),
{
    let s1 = math_sqrt(r);  // some square root
    let s2 = math_field_neg(s1);  // the other root

    if (s1 % 2 == 0) {
        s1
    } else {
        s2
    }
}

pub open spec fn is_valid_u_coordinate(u: nat) -> bool {
    math_is_square(montgomery_rhs(u))
}

/// Given u-coordinate of a Montgomery point (non-torsion),
/// return the unique affine Montgomery point (u, v)
/// where v is the canonical square root of u*(u^2 + A*u + 1).
pub open spec fn canonical_montgomery_lift(u: nat) -> MontgomeryAffine
    recommends
        is_valid_u_coordinate(u),
{
    let v = canonical_sqrt(montgomery_rhs(u));
    MontgomeryAffine::Finite { u: u % p(), v }
}

/// Check if a MontgomeryPoint's u-coordinate corresponds to a valid point on the Montgomery curve.
///
/// A MontgomeryPoint is valid if its u-coordinate allows a canonical Montgomery lift,
/// which requires that montgomery_rhs(u) = u³ + A·u² + u is a quadratic residue (square) mod p.
/// This ensures there exists a v such that v² = montgomery_rhs(u), making (u,v) a point on the curve.
pub open spec fn is_valid_montgomery_point(point: crate::montgomery::MontgomeryPoint) -> bool {
    let u = spec_montgomery(point);
    is_valid_u_coordinate(u)
}

/// Negation on the Montgomery curve.
/// For the Montgomery curve v² = u³ + A·u² + u, the negation of a point is:
/// - Infinity → Infinity (the identity element is its own inverse)
/// - (u, v) → (u, -v) (negate the v-coordinate)
pub open spec fn montgomery_neg(P: MontgomeryAffine) -> MontgomeryAffine {
    match P {
        MontgomeryAffine::Infinity => MontgomeryAffine::Infinity,
        MontgomeryAffine::Finite { u, v } => { MontgomeryAffine::Finite { u, v: math_field_neg(v) }
        },
    }
}

/// Addition on the Montgomery curve using the chord-tangent method.
/// For the Montgomery curve B·v² = u³ + A·u² + u (with B=1, A=486662):
///
/// Addition formulas:
/// - If P = ∞ or Q = ∞: return the other point (identity element)
/// - If P = -Q (same u, opposite v): return ∞
/// - If P = Q (point doubling): λ = (3u₁² + 2Au₁ + 1) / (2v₁)
/// - Otherwise (distinct points): λ = (v₂ - v₁) / (u₂ - u₁)
///
/// Then: u₃ = λ² - A - u₁ - u₂  and  v₃ = λ(u₁ - u₃) - v₁
pub open spec fn montgomery_add(P: MontgomeryAffine, Q: MontgomeryAffine) -> MontgomeryAffine {
    match (P, Q) {
        (MontgomeryAffine::Infinity, _) => Q,
        (_, MontgomeryAffine::Infinity) => P,
        (MontgomeryAffine::Finite { u: u1, v: v1 }, MontgomeryAffine::Finite { u: u2, v: v2 }) => {
            let A = spec_field_element(&MONTGOMERY_A);

            // P = -Q (same u, opposite v)
            if u1 == u2 && math_field_add(v1, v2) == 0 {
                MontgomeryAffine::Infinity
            }
            // P = Q (doubling)
             else if u1 == u2 && v1 == v2 {
                let u1_sq = math_field_square(u1);
                let numerator = math_field_add(
                    math_field_add(
                        math_field_mul(3, u1_sq),
                        math_field_mul(math_field_mul(2, A), u1),
                    ),
                    1,
                );
                let denominator = math_field_mul(2, v1);
                let lambda = math_field_mul(numerator, math_field_inv(denominator));

                let lambda_sq = math_field_square(lambda);
                let u3 = math_field_sub(math_field_sub(lambda_sq, A), math_field_mul(2, u1));
                let v3 = math_field_sub(math_field_mul(lambda, math_field_sub(u1, u3)), v1);

                MontgomeryAffine::Finite { u: u3, v: v3 }
            }
            // Add for distinct points P != Q
             else {
                let numerator = math_field_sub(v2, v1);
                let denominator = math_field_sub(u2, u1);
                let lambda = math_field_mul(numerator, math_field_inv(denominator));

                let lambda_sq = math_field_square(lambda);
                let u3 = math_field_sub(math_field_sub(math_field_sub(lambda_sq, A), u1), u2);
                let v3 = math_field_sub(math_field_mul(lambda, math_field_sub(u1, u3)), v1);

                MontgomeryAffine::Finite { u: u3, v: v3 }
            }
        },
    }
}

/// Subtraction on the Montgomery curve, defined as P - Q = P + (-Q).
pub open spec fn montgomery_sub(P: MontgomeryAffine, Q: MontgomeryAffine) -> MontgomeryAffine {
    montgomery_add(P, montgomery_neg(Q))
}

/// Extract the u-coordinate from a MontgomeryAffine point.
/// Maps Infinity to 0, and Finite{u, v} to u.
pub open spec fn spec_u_coordinate(point: MontgomeryAffine) -> nat {
    match point {
        MontgomeryAffine::Infinity => 0,
        MontgomeryAffine::Finite { u, v: _ } => u,
    }
}

/// Returns the u-coordinate of a Montgomery point as a field element
/// Montgomery points only store the u-coordinate; sign information is lost
pub open spec fn spec_montgomery(point: crate::montgomery::MontgomeryPoint) -> nat {
    spec_field_element_from_bytes(&point.0)
}

/// Check if a MontgomeryPoint corresponds to an EdwardsPoint
/// via the birational map u = (1+y)/(1-y)
/// Special case: Edwards identity (y=1) maps to u=0
pub open spec fn montgomery_corresponds_to_edwards(
    montgomery: crate::montgomery::MontgomeryPoint,
    edwards: crate::edwards::EdwardsPoint,
) -> bool {
    let u = spec_montgomery(montgomery);
    let (x, y) = crate::specs::edwards_specs::edwards_point_as_affine(edwards);
    let denominator = math_field_sub(1, y);

    if denominator == 0 {
        // Special case: Edwards identity (x=0, y=1) maps to Montgomery u=0
        u == 0
    } else {
        // General case: u = (1+y)/(1-y)
        let numerator = math_field_add(1, y);
        u == math_field_mul(numerator, math_field_inv(denominator))
    }
}

/// Returns the abstract affine u-coordinate from a Montgomery ProjectivePoint.
/// A Montgomery ProjectivePoint (U:W) represents affine point u = U/W.
pub open spec fn affine_projective_point_montgomery(
    point: crate::montgomery::ProjectivePoint,
) -> nat {
    let (u, w) = spec_projective_point_montgomery(point);
    if w == 0 {
        0  // Identity case

    } else {
        math_field_mul(u, math_field_inv(w))
    }
}

/// Returns the field element values (U, W) from a Montgomery ProjectivePoint.
/// A Montgomery ProjectivePoint (U:W) is in projective coordinates on the Montgomery curve.
pub open spec fn spec_projective_point_montgomery(point: crate::montgomery::ProjectivePoint) -> (
    nat,
    nat,
) {
    let u = spec_field_element(&point.U);
    let w = spec_field_element(&point.W);
    (u, w)
}

/// Check if a Montgomery u-coordinate is invalid for conversion to Edwards
/// u = -1 is invalid because it corresponds to a point on the twist
pub open spec fn is_equal_to_minus_one(u: nat) -> bool {
    u == math_field_sub(0, 1)  // u == -1

}

/// Map Edwards affine y to Montgomery u via u = (1+y)/(1-y). Special-case y=1 -> u=0.
pub open spec fn montgomery_u_from_edwards_y(y: nat) -> nat {
    let denom = math_field_sub(1, y);
    if denom == 0 {
        0
    } else {
        let numerator = math_field_add(1, y);
        math_field_mul(numerator, math_field_inv(denom))
    }
}

/// Map Montgomery u to Edwards affine y via y = (u-1)/(u+1).
/// Recommends u != -1 to avoid division by zero.
pub open spec fn edwards_y_from_montgomery_u(u: nat) -> nat
    recommends
        u != math_field_sub(0, 1),
{
    let denom = math_field_add(u, 1);
    let numerator = math_field_sub(u, 1);
    math_field_mul(numerator, math_field_inv(denom))
}

/// Extract the u-coordinate from a ProjectivePoint (U:W) as u = U/W.
/// Returns 0 if W = 0 (which represents the point at infinity).
pub open spec fn spec_projective_u_coordinate(P: ProjectivePoint) -> nat {
    let U = spec_field_element(&P.U);
    let W = spec_field_element(&P.W);
    if W == 0 {
        0
    } else {
        math_field_mul(U, math_field_inv(W))
    }
}

/// Check if a Montgomery ProjectivePoint (U:W) represents a MontgomeryAffine point (u,v) for some v.
///
/// A ProjectivePoint stores only the u-coordinate in projective form: u = U/W.
///
/// Returns true if:
/// - The affine point is finite (not infinity)
/// - W ≠ 0 (valid projective representation)
/// - U/W equals the affine u-coordinate
pub open spec fn projective_represents_montgomery(
    P_proj: ProjectivePoint,
    P_aff: MontgomeryAffine,
) -> bool {
    match P_aff {
        MontgomeryAffine::Infinity =>
        // The ladder never uses or produces ∞, so it should never be represented.
        false,
        MontgomeryAffine::Finite { u, v } => {
            // W must not be zero for a meaningful U/W value
            let W = spec_field_element(&P_proj.W);
            let U = spec_field_element(&P_proj.U);

            W != 0 &&
            // Encoding requirement: U/W = u
            // Use cross-multiplication to avoid division.
            U == math_field_mul(u, W)
        },
    }
}

/// Check if a Montgomery ProjectivePoint (U:W) represents a MontgomeryAffine point, including ∞.
///
/// We cannot use u-coordinates alone because both ∞ and the finite point (0,0) have u=0.
/// Instead, we distinguish them structurally: ∞ requires W=0 (and U≠0), while finite points
/// require W≠0.
pub open spec fn projective_represents_montgomery_or_infinity(
    P_proj: ProjectivePoint,
    P_aff: MontgomeryAffine,
) -> bool {
    match P_aff {
        MontgomeryAffine::Infinity => {
            // Infinity is represented by W = 0 in projective coordinates.
            // We require U ≠ 0 to exclude the degenerate (0:0), which represents no valid point.
            spec_field_element(&P_proj.W) == 0 && spec_field_element(&P_proj.U) != 0
        },
        MontgomeryAffine::Finite { u, v: _ } => {
            // Same encoding requirement as `projective_represents_montgomery`.
            let W = spec_field_element(&P_proj.W);
            let U = spec_field_element(&P_proj.U);
            W != 0 && U == math_field_mul(u, W)
        },
    }
}

/// Nat-only variant of `projective_represents_montgomery_or_infinity`.
///
/// This is convenient for stating algebraic properties of x-only algorithms without needing
/// to construct concrete `FieldElement`s in specs.
pub open spec fn projective_represents_montgomery_or_infinity_nat(
    U: nat,
    W: nat,
    P_aff: MontgomeryAffine,
) -> bool {
    match P_aff {
        MontgomeryAffine::Infinity => { W == 0 && U != 0 },
        MontgomeryAffine::Finite { u, v: _ } => { W != 0 && U == math_field_mul(u, W) },
    }
}

/// Scalar multiplication on Montgomery curve (abstract specification)
/// Computes [n]P where n is a scalar and P is a Montgomery point
pub open spec fn montgomery_scalar_mul(P: MontgomeryAffine, n: nat) -> MontgomeryAffine
    decreases n,
{
    if n == 0 {
        MontgomeryAffine::Infinity
    } else {
        montgomery_add(P, montgomery_scalar_mul(P, (n - 1) as nat))
    }
}

// =============================================================================
// X25519 / Montgomery Basepoint
// =============================================================================
/// The X25519/Montgomery basepoint u-coordinate.
///
/// References the actual constant `X25519_BASEPOINT` from `constants.rs`.
/// The u-coordinate is 9, as specified in:
/// - [RFC 7748] Section 4.1: "The u-coordinate of the base point is u = 9"
/// - https://www.rfc-editor.org/rfc/rfc7748#section-4.1
///
/// The Montgomery basepoint corresponds to the Ed25519 basepoint under
/// the birational map between twisted Edwards and Montgomery forms.
///
/// Note: X25519 uses X-only (u-coordinate only) arithmetic, so the full
/// affine point (u, v) is not needed - we only work with u-coordinates.
pub open spec fn spec_x25519_basepoint_u() -> nat {
    spec_field_element_from_bytes(&X25519_BASEPOINT.0)
}

/// Extract u-coordinate from a MontgomeryAffine point
pub open spec fn montgomery_affine_u(P: MontgomeryAffine) -> nat {
    match P {
        MontgomeryAffine::Infinity => 0,  // Convention: infinity maps to 0
        MontgomeryAffine::Finite { u, v: _ } => u,
    }
}

/// Scalar multiplication on Montgomery curve, returning only u-coordinate
/// This is what X25519 computes: [n]P returning just the u-coordinate
pub open spec fn montgomery_scalar_mul_u(u: nat, n: nat) -> nat {
    // Compute full scalar mul and extract u-coordinate
    montgomery_affine_u(
        montgomery_scalar_mul(
            MontgomeryAffine::Finite { u, v: canonical_sqrt(montgomery_rhs(u)) },
            n,
        ),
    )
}

// =============================================================================
// Elligator2 Mapping (hash-to-curve)
// =============================================================================
// Reference: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-10#section-6.7.1
// Also: RFC 9380 Section 6.7.1
/// Elligator2 mapping from a field element to a Montgomery u-coordinate.
///
/// Given input r, computes:
///   d = -A / (1 + 2*r²)
///   eps = d³ + A*d² + d = d * (d² + A*d + 1)
///   if eps is square: u = d       (point lands on the curve)
///   if eps is not square: u = -d - A  (point lands on the quadratic twist)
///
/// ## Quadratic Twist
///
/// For a Montgomery curve v² = u³ + Au² + u, not every u-coordinate has a
/// corresponding v (i.e., u³ + Au² + u may not be a square). The "quadratic
/// twist" is a related curve containing exactly those points whose u-coordinates
/// are invalid on the original curve.
///
/// - If eps = u³ + Au² + u is a **quadratic residue** (square) → u is on the **curve**
/// - If eps is a **non-residue** (not a square) → u is on the **twist**
///
/// ## Twist Security
///
/// Curve25519 is specifically designed to be "twist-secure". The twist has group
/// order 4 * p' where p' is a large prime, similar to the main curve's order 8 * q.
/// This means:
/// - The Montgomery ladder (used in X25519) produces correct results regardless
///   of whether the input u-coordinate is on the curve or the twist
/// - An attacker cannot learn secret key bits by sending a malicious u-coordinate
///   that corresponds to a point on the twist (a "small subgroup attack")
///
/// The output u is always a valid u-coordinate on either the Montgomery curve
/// or its quadratic twist. This provides a deterministic mapping from field
/// elements to curve points.
pub open spec fn spec_elligator_encode(r: nat) -> nat {
    let A = spec_field_element(&MONTGOMERY_A);
    let r_sq = math_field_square(r);
    let two_r_sq = math_field_mul(2, r_sq);
    let d_denom = math_field_add(1, two_r_sq);  // 1 + 2r²

    // d = -A / (1 + 2r²)
    let d = math_field_mul(math_field_neg(A), math_field_inv(d_denom));

    // eps = d³ + A*d² + d = d * (d² + A*d + 1)
    let d_sq = math_field_square(d);
    let A_d = math_field_mul(A, d);
    let inner = math_field_add(math_field_add(d_sq, A_d), 1);
    let eps = math_field_mul(d, inner);

    // Choose u based on whether eps is a quadratic residue
    let eps_is_square = math_is_square(eps);

    if eps_is_square {
        // eps is square → point is on curve → result u = d
        d
    } else {
        // eps is not square → point is on twist → result u = -d - A
        math_field_neg(math_field_add(d, A))
    }
}

} // verus!
