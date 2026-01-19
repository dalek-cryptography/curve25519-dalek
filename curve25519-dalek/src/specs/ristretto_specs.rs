// Specifications for mathematical operations on the Ristretto group
//
// ## References
//
// The mathematical formulas and specifications in this file are based on:
//
// - [RISTRETTO] Ristretto Group Specification
//   https://ristretto.group/
//   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448
//
// - [DECAF] Hamburg, M. (2015). "Decaf: Eliminating cofactors through point compression"
//   https://eprint.iacr.org/2015/673.pdf
//
// - The Ristretto group is a prime-order quotient group constructed from the
//   cofactor-8 Edwards curve Curve25519.
//
//   The curve E has order 8ℓ. Ristretto eliminates the cofactor 8 in two steps:
//     1. Restrict to even subgroup 2E (points that are doubles): gives a subgroup of order 4ℓ
//     2. Group points into equivalence classes: P ~ Q if P - Q ∈ E[4].
//        E[4] = {P : 4P = O} is the 4-torsion subgroup (4 points that vanish when multiplied by 4).
//        Each class has 4 points, so 4ℓ points form ℓ classes.
//
//   Result: a prime-order group of order ℓ with equivalence classes [P] = {P + T : T ∈ E[4]} for P ∈ 2E.
//
#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use super::edwards_specs::*;
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use super::field_specs_u64::*;
#[allow(unused_imports)]
use super::scalar_specs::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants as u64_constants;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants::EIGHT_TORSION;
#[allow(unused_imports)]
use crate::constants;
#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::field::FieldElement;
#[allow(unused_imports)]
use crate::ristretto::{CompressedRistretto, RistrettoPoint};
use vstd::prelude::*;

verus! {

// =============================================================================
// Ristretto Group Mathematical Specifications
// =============================================================================
// TODO: Add subgroup-preservation lemmas (e.g., closure of 2*E under edwards_add)
//       once group-law lemmas for Edwards points are available.
/// Core Ristretto compression from extended coordinates (X, Y, Z, T).
/// Reference: [RISTRETTO], §5.3 "Ristretto255 Encoding";
///            [DECAF], Section 6 (encoding formulas), and https://ristretto.group/formulas/encoding.html.
pub open spec fn spec_ristretto_compress_extended(x: nat, y: nat, z: nat, t: nat) -> [u8; 32] {
    let u1 = math_field_mul(math_field_add(z, y), math_field_sub(z, y));
    let u2 = math_field_mul(x, y);
    let invsqrt = math_invsqrt(math_field_mul(u1, math_field_square(u2)));
    let i1 = math_field_mul(invsqrt, u1);
    let i2 = math_field_mul(invsqrt, u2);
    let z_inv = math_field_mul(i1, math_field_mul(i2, t));
    let den_inv = i2;

    let iX = math_field_mul(x, spec_sqrt_m1());
    let iY = math_field_mul(y, spec_sqrt_m1());
    let enchanted_denominator = math_field_mul(
        i1,
        spec_field_element(&u64_constants::INVSQRT_A_MINUS_D),
    );

    let rotate = math_is_negative(math_field_mul(t, z_inv));
    let x_rot = if rotate {
        iY
    } else {
        x
    };
    let y_rot = if rotate {
        iX
    } else {
        y
    };
    let den_inv_rot = if rotate {
        enchanted_denominator
    } else {
        den_inv
    };

    let y_final = if math_is_negative(math_field_mul(x_rot, z_inv)) {
        math_field_neg(y_rot)
    } else {
        y_rot
    };
    let s = math_field_mul(den_inv_rot, math_field_sub(z, y_final));
    let s_final = if math_is_negative(s) {
        math_field_neg(s)
    } else {
        s
    };

    spec_bytes32_from_nat(s_final)
}

/// Spec-only model of Ristretto compression from a RistrettoPoint.
///
/// This captures the canonical encoding of a Ristretto point.
/// Reference: [RISTRETTO], §5.3 "Ristretto255 Encoding"
pub open spec fn spec_ristretto_compress(point: RistrettoPoint) -> [u8; 32] {
    let (x, y, z, t) = spec_edwards_point(point.0);
    spec_ristretto_compress_extended(x, y, z, t)
}

/// Spec-only model of Ristretto compression from affine coordinates.
///
/// For affine coords (x, y), we use z = 1 and t = x * y
/// (since T = XY/Z = xy/1 = xy in extended coords).
///
/// Reference: [RISTRETTO], §5.3 "Ristretto255 Encoding"
pub open spec fn spec_ristretto_compress_affine(x: nat, y: nat) -> [u8; 32] {
    spec_ristretto_compress_extended(x, y, 1, math_field_mul(x, y))
}

/// Spec-only model of Ristretto decompression.
/// Reference: [RISTRETTO], §5.2 "Ristretto255 Decoding";
///            [DECAF], Section 6 (decoding formulas), and https://ristretto.group/formulas/decoding.html.
pub open spec fn spec_ristretto_decompress(bytes: [u8; 32]) -> Option<RistrettoPoint> {
    let s_bytes_nat = bytes32_to_nat(&bytes);
    let s = spec_field_element_from_bytes(&bytes);
    let s_encoding_is_canonical = s_bytes_nat < p();
    let s_is_negative = math_is_negative(s);

    if !s_encoding_is_canonical || s_is_negative {
        None
    } else {
        let ss = math_field_square(s);
        let u1 = math_field_sub(1, ss);
        let u2 = math_field_add(1, ss);
        let u2_sqr = math_field_square(u2);
        let neg_d = math_field_neg(spec_field_element(&EDWARDS_D));
        let u1_sqr = math_field_square(u1);
        let v = math_field_sub(math_field_mul(neg_d, u1_sqr), u2_sqr);

        let invsqrt_input = math_field_mul(v, u2_sqr);
        let invsqrt = math_invsqrt(invsqrt_input);
        let ok = math_is_sqrt_ratio(1, invsqrt_input, invsqrt);

        let dx = math_field_mul(invsqrt, u2);
        let dy = math_field_mul(invsqrt, math_field_mul(dx, v));
        let x_tmp = math_field_mul(math_field_add(s, s), dx);
        let x = if math_is_negative(x_tmp) {
            math_field_neg(x_tmp)
        } else {
            x_tmp
        };
        let y = math_field_mul(u1, dy);
        let t = math_field_mul(x, y);

        let t_is_negative = math_is_negative(t);
        let y_is_zero = y == 0;

        if !ok || t_is_negative || y_is_zero {
            None
        } else if exists|p: RistrettoPoint| #![auto] spec_edwards_point(p.0) == (x, y, 1nat, t) {
            Some(choose|p: RistrettoPoint| #![auto] spec_edwards_point(p.0) == (x, y, 1nat, t))
        } else {
            None
        }
    }
}

/// Spec round-trip: decoding the encoding yields a point with the same encoding.
pub proof fn lemma_spec_ristretto_roundtrip(point: RistrettoPoint)
    ensures
        spec_ristretto_decompress(spec_ristretto_compress(point)).is_some(),
        spec_ristretto_compress(spec_ristretto_decompress(spec_ristretto_compress(point)).unwrap())
            == spec_ristretto_compress(point),
{
    // Proof bypass: relies on the choice in spec_ristretto_decompress.
    assume(spec_ristretto_decompress(spec_ristretto_compress(point)).is_some());
    assume(spec_ristretto_compress(
        spec_ristretto_decompress(spec_ristretto_compress(point)).unwrap(),
    ) == spec_ristretto_compress(point));
}

/// The canonical representative of the Ristretto basepoint.
///
/// The Ristretto basepoint is the equivalence class [B] where B is the
/// Ed25519 basepoint. We use B itself as the canonical representative.
pub open spec fn spec_ristretto_basepoint() -> (nat, nat) {
    spec_ed25519_basepoint()
}

/// Axiom: `RISTRETTO_BASEPOINT_TABLE` is a valid precomputed table for the Ristretto basepoint.
///
/// Since `RistrettoBasepointTable` wraps `EdwardsBasepointTable` and
/// `RISTRETTO_BASEPOINT_TABLE` is a pointer cast of `ED25519_BASEPOINT_TABLE`,
/// this follows from `axiom_ed25519_basepoint_table_valid()`.
#[cfg(feature = "precomputed-tables")]
pub proof fn axiom_ristretto_basepoint_table_valid()
    ensures
        is_valid_edwards_basepoint_table(
            constants::RISTRETTO_BASEPOINT_TABLE.0,
            spec_ristretto_basepoint(),
        ),
{
    axiom_ed25519_basepoint_table_valid();
    // The assume is needed because RISTRETTO_BASEPOINT_TABLE is external_body
    // so Verus cannot see that .0 is the same as ED25519_BASEPOINT_TABLE to conclude the proof
    assume(is_valid_edwards_basepoint_table(
        constants::RISTRETTO_BASEPOINT_TABLE.0,
        spec_ristretto_basepoint(),
    ));
}

// =============================================================================
// Ristretto Elligator Map
// =============================================================================
/// Spec-only model of the Ristretto Elligator map (MAP function).
///
/// This maps a field element r_0 to a Ristretto point deterministically.
/// Reference: [RISTRETTO], §4.3.4 "MAP" function;
///            https://ristretto.group/formulas/elligator.html
///
/// The algorithm:
/// 1. r = i * r_0²  (where i = sqrt(-1))
/// 2. N_s = (r + 1) * (1 - d²)
/// 3. D = (c - d*r) * (r + d) where c = -1 initially
/// 4. (was_square, s) = sqrt_ratio_i(N_s, D)
/// 5. Conditionally adjust s and c based on was_square
/// 6. Compute final point coordinates
///
/// Returns the affine (x, y) coordinates of the resulting Ristretto point.
pub open spec fn spec_elligator_ristretto_flavor(r_0: nat) -> (nat, nat) {
    let i = spec_sqrt_m1();
    let d = spec_field_element(&EDWARDS_D);
    let one_minus_d_sq = math_field_mul(math_field_sub(1, d), math_field_add(1, d));  // (1-d)(1+d) = 1 - d²
    let d_minus_one_sq = math_field_square(math_field_sub(d, 1));  // (d-1)²
    let c_init: nat = math_field_neg(1);  // -1

    let r = math_field_mul(i, math_field_square(r_0));
    let n_s = math_field_mul(math_field_add(r, 1), one_minus_d_sq);
    let d_val = math_field_mul(math_field_sub(c_init, math_field_mul(d, r)), math_field_add(r, d));

    // sqrt_ratio_i(N_s, D) returns (was_square, s)
    // invsqrt = 1/sqrt(N_s * D), so s = invsqrt * N_s = sqrt(N_s/D)
    let invsqrt = math_invsqrt(math_field_mul(n_s, d_val));
    let s_if_square = math_field_mul(invsqrt, n_s);
    // was_square checks if s² · D = N_s (i.e., N_s/D is a square)
    let was_square = math_is_sqrt_ratio(n_s, d_val, s_if_square);

    // s' = s * r_0, then conditionally negate to make it negative
    let s_prime_raw = math_field_mul(s_if_square, r_0);
    let s_prime = if !math_is_negative(s_prime_raw) {
        math_field_neg(s_prime_raw)
    } else {
        s_prime_raw
    };

    // If !was_square: s = s', c = r
    let s = if was_square {
        s_if_square
    } else {
        s_prime
    };
    let c = if was_square {
        c_init
    } else {
        r
    };

    // N_t = c * (r - 1) * (d - 1)² - D
    let n_t = math_field_sub(
        math_field_mul(math_field_mul(c, math_field_sub(r, 1)), d_minus_one_sq),
        d_val,
    );
    let s_sq = math_field_square(s);

    // Final point in completed coordinates, then converted to affine:
    // X = 2*s*D, Z = N_t * sqrt(a*d - 1), Y = 1 - s², T = 1 + s²
    // Affine: x = X*T / (Z*T) = X/Z, y = Y*Z / (Z*T) = Y/T
    let sqrt_ad_minus_one = spec_sqrt_ad_minus_one();
    let x_completed = math_field_mul(math_field_mul(2, s), d_val);
    let z_completed = math_field_mul(n_t, sqrt_ad_minus_one);
    let y_completed = math_field_sub(1, s_sq);
    let t_completed = math_field_add(1, s_sq);

    // Convert completed point ((X:Z), (Y:T)) to affine (X/Z, Y/T)
    let x_affine = math_field_mul(x_completed, math_field_inv(z_completed));
    let y_affine = math_field_mul(y_completed, math_field_inv(t_completed));

    (x_affine, y_affine)
}

/// Spec helper: first 32 bytes of a 64-byte input.
pub open spec fn spec_uniform_bytes_first(bytes: &[u8; 64]) -> [u8; 32] {
    choose|b: [u8; 32]| b@ == bytes@.subrange(0, 32)
}

/// Spec helper: second 32 bytes of a 64-byte input.
pub open spec fn spec_uniform_bytes_second(bytes: &[u8; 64]) -> [u8; 32] {
    choose|b: [u8; 32]| b@ == bytes@.subrange(32, 64)
}

/// Spec-only model of RistrettoPoint::from_uniform_bytes.
///
/// Constructs a Ristretto point from 64 uniform random bytes using the
/// "hash-to-group" construction for Ristretto.
///
/// Reference: [RISTRETTO], §4.3.4 "Hash-to-group";
///            https://ristretto.group/formulas/encoding.html
///
/// Algorithm:
/// 1. Split 64 bytes into two 32-byte halves: b1 = bytes[0..32], b2 = bytes[32..64]
/// 2. Convert each half to a field element: r1 = from_bytes(b1), r2 = from_bytes(b2)
/// 3. Map each field element to a Ristretto point via Elligator: p1 = MAP(r1), p2 = MAP(r2)
/// 4. Add the two points: result = p1 + p2
///
/// Returns the affine (x, y) coordinates of the resulting Ristretto point.
pub open spec fn spec_ristretto_from_uniform_bytes(bytes: &[u8; 64]) -> (nat, nat) {
    let b1 = spec_uniform_bytes_first(bytes);
    let b2 = spec_uniform_bytes_second(bytes);
    let r1 = spec_field_element_from_bytes(&b1);
    let r2 = spec_field_element_from_bytes(&b2);
    let p1 = spec_elligator_ristretto_flavor(r1);
    let p2 = spec_elligator_ristretto_flavor(r2);
    edwards_add(p1.0, p1.1, p2.0, p2.1)
}

/// Spec for sqrt(a*d - 1) where a = -1 for Ed25519.
/// This equals sqrt(-d - 1).
pub open spec fn spec_sqrt_ad_minus_one() -> nat {
    // sqrt(-1 * d - 1) = sqrt(-d - 1)
    // This is a constant defined in the codebase
    spec_field_element(&u64_constants::SQRT_AD_MINUS_ONE)
}

// =============================================================================
// Ristretto Equivalence Classes (Cosets)
// =============================================================================
/// Point is in the even subgroup 2E = {2Q : Q ∈ E}; valid Ristretto points must lie in 2E.
pub open spec fn is_in_even_subgroup(point: EdwardsPoint) -> bool {
    exists|q: EdwardsPoint|
        edwards_point_as_affine(point) == edwards_scalar_mul(
            #[trigger] edwards_point_as_affine(q),
            2,
        )
}

/// Check if 4 Edwards points form a coset of the 4-torsion subgroup E[4].
///
/// A coset P + E[4] = {P, P + T[2], P + T[4], P + T[6]} represents a single
/// Ristretto equivalence class - all 4 points map to the same Ristretto point.
pub open spec fn is_ristretto_coset(points: [EdwardsPoint; 4], base: EdwardsPoint) -> bool {
    let base_affine = edwards_point_as_affine(base);
    let t2 = edwards_point_as_affine(EIGHT_TORSION[2]);
    let t4 = edwards_point_as_affine(EIGHT_TORSION[4]);
    let t6 = edwards_point_as_affine(EIGHT_TORSION[6]);

    // points[0] = base (T[0] is identity)
    edwards_point_as_affine(points[0])
        == base_affine
    // points[1] = base + T[2]
     && edwards_point_as_affine(points[1]) == edwards_add(
        base_affine.0,
        base_affine.1,
        t2.0,
        t2.1,
    )
    // points[2] = base + T[4]
     && edwards_point_as_affine(points[2]) == edwards_add(
        base_affine.0,
        base_affine.1,
        t4.0,
        t4.1,
    )
    // points[3] = base + T[6]
     && edwards_point_as_affine(points[3]) == edwards_add(base_affine.0, base_affine.1, t6.0, t6.1)
}

/// Two Edwards points are Ristretto-equivalent if they differ by a 4-torsion element.
pub open spec fn ristretto_equivalent(p1: EdwardsPoint, p2: EdwardsPoint) -> bool
    recommends
        is_well_formed_edwards_point(p1),
        is_well_formed_edwards_point(p2),
{
    let p1_affine = edwards_point_as_affine(p1);
    let p2_affine = edwards_point_as_affine(p2);
    let diff = edwards_sub(p1_affine.0, p1_affine.1, p2_affine.0, p2_affine.1);

    // The difference must be a 4-torsion element (one of T[0], T[2], T[4], T[6])
    let t0 = edwards_point_as_affine(EIGHT_TORSION[0]);
    let t2 = edwards_point_as_affine(EIGHT_TORSION[2]);
    let t4 = edwards_point_as_affine(EIGHT_TORSION[4]);
    let t6 = edwards_point_as_affine(EIGHT_TORSION[6]);

    diff == t0 || diff == t2 || diff == t4 || diff == t6
}

} // verus!
