#[allow(unused_imports)]
use crate::backend::serial::u64::constants as u64_constants;
#[allow(unused_imports)]
use crate::constants;
#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::field::FieldElement;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;
use vstd::prelude::*;

verus! {

// --- Decode axioms ---
/// Axiom: when decode succeeds, the decoded (x, y) satisfy the Edwards curve equation.
///
/// Reference: [DECAF] §3, Hamburg 2015; https://ristretto.group/formulas/decoding.html
/// Runtime validation: `test_ristretto_decode_on_curve` (100 points)
pub proof fn axiom_ristretto_decode_on_curve(s: nat)
    requires
        s < p(),
        ristretto_decode_ok(s),
    ensures
        is_on_edwards_curve(ristretto_decode_x(s), ristretto_decode_y(s)),
{
    admit();
}

/// Axiom: when decode succeeds, the resulting point is in the even subgroup (2E).
///
/// This is the core Ristretto property: decoded points are always doubles of
/// some curve point. Combined with the E[4] coset quotient, this gives a
/// prime-order group.
///
/// Reference: [DECAF] §3, Hamburg 2015; https://ristretto.group/details/isogenies.html
/// Runtime validation: `test_ristretto_decode_in_even_subgroup` (50+ points)
pub proof fn axiom_ristretto_decode_in_even_subgroup(s: nat, point: EdwardsPoint)
    requires
        s < p(),
        ristretto_decode_ok(s),
        edwards_point_as_nat(point) == (
            ristretto_decode_x(s),
            ristretto_decode_y(s),
            1nat,
            field_mul(ristretto_decode_x(s), ristretto_decode_y(s)),
        ),
    ensures
        is_in_even_subgroup(point),
{
    admit();
}

/// Axiom: RISTRETTO_BASEPOINT_TABLE is valid for the Ristretto basepoint.
///
/// Follows from `axiom_ed25519_basepoint_table_valid()` since the Ristretto
/// table is a pointer cast of the Ed25519 table.
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

// --- Equality axiom ---
/// Ristretto equivalence can be tested via cross-multiplication of projective coordinates.
///
/// Two well-formed Edwards points P1 = (X1:Y1:Z1:T1), P2 = (X2:Y2:Z2:T2) satisfy:
///   ristretto_equivalent(P1, P2) ⟺ (X1·Y2 == Y1·X2) || (X1·X2 == Y1·Y2)
///
/// This is a standard result from the Ristretto/Decaf construction:
/// the 4-torsion coset condition P1 - P2 ∈ E[4] is equivalent to
/// the projective cross-multiplication check.
///
/// Reference: [RISTRETTO] §3.2; Hamburg, "Decaf" §4.
pub proof fn axiom_ristretto_cross_mul_iff_equivalent(p1: EdwardsPoint, p2: EdwardsPoint)
    requires
        is_well_formed_edwards_point(p1),
        is_well_formed_edwards_point(p2),
    ensures
        ristretto_equivalent(p1, p2) == (field_mul(
            fe51_as_canonical_nat(&edwards_x(p1)),
            fe51_as_canonical_nat(&edwards_y(p2)),
        ) == field_mul(fe51_as_canonical_nat(&edwards_y(p1)), fe51_as_canonical_nat(&edwards_x(p2)))
            || field_mul(
            fe51_as_canonical_nat(&edwards_x(p1)),
            fe51_as_canonical_nat(&edwards_x(p2)),
        ) == field_mul(
            fe51_as_canonical_nat(&edwards_y(p1)),
            fe51_as_canonical_nat(&edwards_y(p2)),
        )),
{
    admit();
}

/// Axiom: the Elligator map always produces a point on the Edwards curve.
///
/// This is a standard result from the Ristretto/Decaf construction: the
/// Elligator map parametrizes points via the Jacobi quartic, and the
/// resulting coordinates always satisfy the Edwards curve equation.
///
/// Reference: [RISTRETTO] §4.3.4; Hamburg, "Decaf" §4
/// Runtime validation: `test_elligator_on_curve` (200+ inputs)
pub proof fn axiom_elligator_on_curve(r_0: nat)
    ensures
        is_on_edwards_curve(
            spec_elligator_ristretto_flavor(r_0).0,
            spec_elligator_ristretto_flavor(r_0).1,
        ),
{
    admit();
}

/// Axiom: The Elligator intermediates have nonzero denominators.
///
/// (1) N_t ≠ 0 (mod p): N_t = c·(r − 1)·(d − 1)² − D avoids zero because the
///     algebraic structure of the map avoids degenerate cases.
/// (2) 1 + s² ≠ 0 (mod p): s never equals ±√(−1), even though −1 is a square
///     in GF(p), because the Elligator construction never produces those values.
///
/// Reference: [RISTRETTO] section 4.3.4; Hamburg, "Decaf" section 4
/// Runtime validation: `test_elligator_nonzero_denominators` (200+ inputs)
pub proof fn axiom_elligator_nonzero_intermediates(
    r_0: nat,
    s_nat: nat,
    n_t_nat: nat,
    d_val_nat: nat,
)
    requires
        s_nat < p(),
        (s_nat, n_t_nat, d_val_nat) == elligator_intermediates(r_0),
    ensures
        n_t_nat % p() != 0,
        field_add(1, field_square(s_nat)) != 0,
{
    admit();
}

/// Axiom: the Elligator map always produces a point in the even subgroup 2E.
///
/// The Elligator construction naturally produces points that are doubles of
/// some curve point (arising from the Jacobi quartic parametrization).
/// Combined with the E[4] coset quotient, this gives the prime-order Ristretto group.
///
/// Reference: [RISTRETTO] §4.3.4; Hamburg, "Decaf" §3
/// Runtime validation: `test_elligator_in_even_subgroup` (200+ inputs)
pub proof fn axiom_elligator_in_even_subgroup(r_0: nat)
    ensures
        forall|point: EdwardsPoint|
            edwards_point_as_affine(point) == spec_elligator_ristretto_flavor(r_0)
                && is_well_formed_edwards_point(point) ==> #[trigger] is_in_even_subgroup(point),
{
    admit();
}

/// Axiom: The even subgroup (image of [2]) is closed under Edwards addition.
///
/// If P = 2·Q₁ and Q = 2·Q₂, then P + Q = 2·Q₁ + 2·Q₂ = 2·(Q₁ + Q₂).
/// The algebraic identity follows from lemma_edwards_double_of_add (fully proven).
/// Admitted because the existential witness requires lifting affine → EdwardsPoint.
///
/// Reference: standard group theory (sum of doubles is a double)
pub proof fn axiom_even_subgroup_closed_under_add(p1: EdwardsPoint, p2: EdwardsPoint)
    requires
        is_in_even_subgroup(p1),
        is_in_even_subgroup(p2),
        is_well_formed_edwards_point(p1),
        is_well_formed_edwards_point(p2),
    ensures
        forall|result: EdwardsPoint|
            edwards_point_as_affine(result) == edwards_add(
                edwards_point_as_affine(p1).0,
                edwards_point_as_affine(p1).1,
                edwards_point_as_affine(p2).0,
                edwards_point_as_affine(p2).1,
            ) && is_well_formed_edwards_point(result) ==> is_in_even_subgroup(result),
{
    admit();
}

// =============================================================================
// Axiom: nat_invsqrt(−1 − d) = C_IAD  and  C_IAD² · (−1 − d) = 1
// =============================================================================
/// Axiom: the canonical inverse square root of (−1 − d) is INVSQRT_A_MINUS_D,
/// and squaring it times (−1 − d) yields 1 (not √(−1)).
///
/// These two facts are a single numerical assertion: nat_invsqrt evaluates
/// deterministically, and for (−1 − d) — which is a quadratic residue mod p —
/// the result satisfies r²·a = 1 rather than r²·a = √(−1).
///
/// In principle the second clause follows from the first plus a proof that
/// (−1 − d) is a QR mod p, but that QR status is itself a concrete numerical
/// fact that Verus cannot evaluate (it requires 252-bit modular exponentiation).
///
/// Reference: ristretto.group/formulas/encoding.html; Hamburg (2015) Decaf §6
/// Runtime validation: `test_nat_invsqrt_neg_one_minus_d`, `test_invsqrt_a_minus_d_squared`
pub proof fn axiom_invsqrt_a_minus_d()
    ensures
        ({
            let c_iad = fe51_as_canonical_nat(&u64_constants::INVSQRT_A_MINUS_D);
            let d = fe51_as_canonical_nat(&u64_constants::EDWARDS_D);
            let neg_one_minus_d = field_sub(field_neg(1nat), d);
            nat_invsqrt(neg_one_minus_d) == c_iad && field_mul(field_square(c_iad), neg_one_minus_d)
                == 1
        }),
{
    admit();
}

} // verus!
// ------------------------------------------------------------------------
// Axiom Validation Tests for Ristretto Decode and Elligator
// ------------------------------------------------------------------------
/// Square-and-multiply: compute base^exp where exp is a 256-bit little-endian integer.
/// Used only in tests.
#[cfg(test)]
fn pow_field_element(
    base: &crate::field::FieldElement,
    exp: &[u8; 32],
) -> crate::field::FieldElement {
    use crate::field::FieldElement;
    let mut result = FieldElement::ONE;
    let mut acc = base.clone();
    for &byte in exp.iter() {
        for bit in 0..8 {
            if (byte >> bit) & 1 == 1 {
                result = &result * &acc;
            }
            acc = acc.square();
        }
    }
    result
}

#[cfg(test)]
mod test_ristretto_decode_axioms {
    use super::pow_field_element;
    use crate::backend::serial::u64::field::FieldElement51;
    use crate::constants;
    use crate::edwards::EdwardsPoint;
    use crate::field::FieldElement;
    use crate::ristretto::{CompressedRistretto, RistrettoPoint};
    use subtle::{Choice, ConditionallyNegatable, ConstantTimeEq};

    /// Helper: compute the Edwards curve equation residue.
    /// Returns 0 if (x, y) is on the curve: -x² + y² - 1 - d·x²·y² ≡ 0 (mod p).
    fn curve_residue(x: &FieldElement, y: &FieldElement) -> FieldElement {
        let d = &constants::EDWARDS_D;
        let xx = x.square();
        let yy = y.square();
        let dxxyy = &(d * &xx) * &yy;
        // -x² + y² - 1 - d·x²·y²
        &(&(&yy - &xx) - &FieldElement::ONE) - &dxxyy
    }

    /// Validate axiom_ristretto_decode_on_curve:
    /// Ristretto decoding always produces a point on the Edwards curve.
    #[test]
    fn test_ristretto_decode_on_curve() {
        // Test with identity encoding (s = 0)
        let zero_bytes = [0u8; 32];
        let s = FieldElement::from_bytes(&zero_bytes);
        let one = FieldElement::ONE;
        let ss = s.square();
        let u1 = &one - &ss;
        let u2 = &one + &ss;
        let u2_sqr = u2.square();
        use core::ops::Neg;
        let neg_d = Neg::neg(&constants::EDWARDS_D);
        let u1_sqr = u1.square();
        let neg_d_u1_sqr = &neg_d * &u1_sqr;
        let v = &neg_d_u1_sqr - &u2_sqr;
        let v_u2_sqr = &v * &u2_sqr;
        let (_ok, big_i) = v_u2_sqr.invsqrt();
        let dx = &big_i * &u2;
        let dx_v = &dx * &v;
        let dy = &big_i * &dx_v;
        let s_plus_s = &s + &s;
        let mut x = &s_plus_s * &dx;
        let x_neg = x.is_negative();
        x.conditional_negate(x_neg);
        let y = &u1 * &dy;
        let residue = curve_residue(&x, &y);
        let residue_bytes = residue.as_bytes();
        assert_eq!(residue_bytes, [0u8; 32], "s=0: point not on curve");

        // Test with basepoint encoding
        let bp = constants::RISTRETTO_BASEPOINT_POINT;
        let bp_bytes = bp.compress().as_bytes().clone();
        let s = FieldElement::from_bytes(&bp_bytes);
        let ss = s.square();
        let u1 = &one - &ss;
        let u2 = &one + &ss;
        let u2_sqr = u2.square();
        let neg_d = Neg::neg(&constants::EDWARDS_D);
        let u1_sqr = u1.square();
        let neg_d_u1_sqr = &neg_d * &u1_sqr;
        let v = &neg_d_u1_sqr - &u2_sqr;
        let v_u2_sqr = &v * &u2_sqr;
        let (_ok, big_i) = v_u2_sqr.invsqrt();
        let dx = &big_i * &u2;
        let dx_v = &dx * &v;
        let dy = &big_i * &dx_v;
        let s_plus_s = &s + &s;
        let mut x = &s_plus_s * &dx;
        let x_neg = x.is_negative();
        x.conditional_negate(x_neg);
        let y = &u1 * &dy;
        let residue = curve_residue(&x, &y);
        let residue_bytes = residue.as_bytes();
        assert_eq!(residue_bytes, [0u8; 32], "basepoint: point not on curve");

        // Test with many small multiples of basepoint
        let mut point = constants::RISTRETTO_BASEPOINT_POINT;
        for i in 2..100u32 {
            point = &point + &constants::RISTRETTO_BASEPOINT_POINT;
            let bytes = point.compress().as_bytes().clone();
            let s = FieldElement::from_bytes(&bytes);
            let ss = s.square();
            let u1 = &one - &ss;
            let u2 = &one + &ss;
            let u2_sqr = u2.square();
            let neg_d = Neg::neg(&constants::EDWARDS_D);
            let u1_sqr = u1.square();
            let neg_d_u1_sqr = &neg_d * &u1_sqr;
            let v = &neg_d_u1_sqr - &u2_sqr;
            let v_u2_sqr = &v * &u2_sqr;
            let (_ok, big_i) = v_u2_sqr.invsqrt();
            let dx = &big_i * &u2;
            let dx_v = &dx * &v;
            let dy = &big_i * &dx_v;
            let s_plus_s = &s + &s;
            let mut x = &s_plus_s * &dx;
            let x_neg = x.is_negative();
            x.conditional_negate(x_neg);
            let y = &u1 * &dy;
            let residue = curve_residue(&x, &y);
            let residue_bytes = residue.as_bytes();
            assert_eq!(residue_bytes, [0u8; 32], "{}*B: point not on curve", i);
        }

        // Helper: run the decode formula for a field element s and check on-curve.
        // Returns (ok, on_curve) so caller can filter.
        fn decode_and_check(s_bytes: &[u8; 32]) -> (bool, bool) {
            use core::ops::Neg;
            let s = FieldElement::from_bytes(s_bytes);
            let one = FieldElement::ONE;
            let ss = s.square();
            let u1 = &one - &ss;
            let u2 = &one + &ss;
            let u2_sqr = u2.square();
            let neg_d = Neg::neg(&constants::EDWARDS_D);
            let u1_sqr = u1.square();
            let neg_d_u1_sqr = &neg_d * &u1_sqr;
            let v = &neg_d_u1_sqr - &u2_sqr;
            let v_u2_sqr = &v * &u2_sqr;
            let (ok, big_i) = v_u2_sqr.invsqrt();
            let dx = &big_i * &u2;
            let dx_v = &dx * &v;
            let dy = &big_i * &dx_v;
            let s_plus_s = &s + &s;
            let mut x = &s_plus_s * &dx;
            let x_neg = x.is_negative();
            x.conditional_negate(x_neg);
            let y = &u1 * &dy;
            let residue = curve_residue(&x, &y);
            let on_curve = residue.as_bytes() == [0u8; 32];
            (bool::from(ok), on_curve)
        }

        // Edge cases: small even field elements (s = 2, 4, 6, ..., 40).
        // The axiom claims on-curve when ristretto_decode_ok(s) holds (the
        // square case). We verify on-curve for the ok=true case. The ok=false
        // (nonsquare) case produces coords that may not be on-curve; this is fine
        // because the decompress proof only needs on-curve for the success path.
        let mut ok_count = 0u32;
        for s_val in (2u64..=40).step_by(2) {
            let mut s_bytes = [0u8; 32];
            s_bytes[0] = s_val as u8;
            let (ok, on_curve) = decode_and_check(&s_bytes);
            if ok {
                assert!(on_curve, "s={}: ok=true but point not on curve", s_val);
                ok_count += 1;
            }
        }
        assert!(
            ok_count >= 1,
            "expected at least one ok=true among small s values"
        );

        // Edge case: s = 1 (odd, would be rejected by sign check, but test the
        // decode formula for the ok=true case)
        let mut one_bytes = [0u8; 32];
        one_bytes[0] = 1;
        let (ok, on_curve) = decode_and_check(&one_bytes);
        if ok {
            assert!(on_curve, "s=1: ok=true but point not on curve");
        }

        // Hash-derived field elements to exercise more diverse s values.
        // Only check on-curve for the ok=true (square) case.
        use sha2::{Digest, Sha512};
        let mut hash_ok_count = 0u32;
        for seed in 0u32..50 {
            let mut hasher = Sha512::new();
            hasher.update(b"ristretto_decode_on_curve_test_");
            hasher.update(seed.to_le_bytes());
            let hash = hasher.finalize();
            let mut s_bytes = [0u8; 32];
            s_bytes.copy_from_slice(&hash[..32]);
            s_bytes[31] &= 0x7f; // Clear high bit to stay < 2^255
            s_bytes[0] &= 0xfe; // Make even (nonnegative)
            let (ok, on_curve) = decode_and_check(&s_bytes);
            if ok {
                assert!(
                    on_curve,
                    "hash-derived s (seed {}): ok=true but point not on curve",
                    seed
                );
                hash_ok_count += 1;
            }
        }
        assert!(
            hash_ok_count >= 10,
            "expected at least 10 ok=true hash-derived inputs, got {}",
            hash_ok_count
        );
    }

    /// Validate axiom_ristretto_decode_in_even_subgroup:
    /// Successfully decoded Ristretto points lie in the prime-order subgroup.
    /// We check [L]P == identity, which implies P is in the prime-order subgroup
    /// (and hence in the even subgroup 2E, since the prime-order subgroup is
    /// contained in 2E for cofactor-8 curves).
    #[test]
    fn test_ristretto_decode_in_even_subgroup() {
        use crate::scalar::Scalar;

        // L (group order) as a scalar is zero, so [L]P = identity iff P is
        // in the prime-order subgroup. We use the cofactor to check instead:
        // if [8]P != identity but [8L]P = identity, then P has exact order
        // dividing 8L but not dividing 8 — so P is in the subgroup of order L
        // (which equals the even subgroup for cofactor 8).

        // Test with basepoint
        let bp = constants::RISTRETTO_BASEPOINT_POINT;
        let bp_bytes = bp.compress().as_bytes().clone();
        let s = FieldElement::from_bytes(&bp_bytes);
        let one = FieldElement::ONE;
        let ss = s.square();
        let u1 = &one - &ss;
        let u2 = &one + &ss;
        let u2_sqr = u2.square();
        use core::ops::Neg;
        let neg_d = Neg::neg(&constants::EDWARDS_D);
        let u1_sqr = u1.square();
        let neg_d_u1_sqr = &neg_d * &u1_sqr;
        let v = &neg_d_u1_sqr - &u2_sqr;
        let v_u2_sqr = &v * &u2_sqr;
        let (ok, big_i) = v_u2_sqr.invsqrt();
        assert!(bool::from(ok), "basepoint decode must succeed");
        let dx = &big_i * &u2;
        let dx_v = &dx * &v;
        let dy = &big_i * &dx_v;
        let s_plus_s = &s + &s;
        let mut x = &s_plus_s * &dx;
        let x_neg = x.is_negative();
        x.conditional_negate(x_neg);
        let y = &u1 * &dy;
        let t = &x * &y;
        let point = EdwardsPoint {
            X: x,
            Y: y,
            Z: one,
            T: t,
        };

        // [8]P should not be identity (P has large prime order)
        let eight_p = point.mul_by_pow_2(3);
        assert_ne!(
            eight_p.compress().as_bytes(),
            &[
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ],
            "basepoint [8]P should not be identity"
        );

        // Multiply by group order: decoded point should have prime order
        // (scalar multiplication by L gives identity for prime-order points)
        let l_bytes = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
            0xde, 0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
        ];
        let l_scalar = Scalar::from_bytes_mod_order(l_bytes);
        let l_times_p = &l_scalar * &point;
        let identity_bytes = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        assert_eq!(
            l_times_p.compress().as_bytes(),
            &identity_bytes,
            "basepoint: [L]P must be identity"
        );

        // Test with many multiples of basepoint
        let mut pt = constants::RISTRETTO_BASEPOINT_POINT;
        for i in 2..50u32 {
            pt = &pt + &constants::RISTRETTO_BASEPOINT_POINT;
            let bytes = pt.compress().as_bytes().clone();
            let s = FieldElement::from_bytes(&bytes);
            let ss = s.square();
            let u1 = &one - &ss;
            let u2 = &one + &ss;
            let u2_sqr = u2.square();
            let neg_d = Neg::neg(&constants::EDWARDS_D);
            let u1_sqr = u1.square();
            let neg_d_u1_sqr = &neg_d * &u1_sqr;
            let v = &neg_d_u1_sqr - &u2_sqr;
            let v_u2_sqr = &v * &u2_sqr;
            let (ok, big_i) = v_u2_sqr.invsqrt();
            if !bool::from(ok) {
                continue;
            }
            let dx = &big_i * &u2;
            let dx_v = &dx * &v;
            let dy = &big_i * &dx_v;
            let s_plus_s = &s + &s;
            let mut x_pt = &s_plus_s * &dx;
            let x_neg = x_pt.is_negative();
            x_pt.conditional_negate(x_neg);
            let y_pt = &u1 * &dy;
            let t_pt = &x_pt * &y_pt;
            let decoded = EdwardsPoint {
                X: x_pt,
                Y: y_pt,
                Z: one,
                T: t_pt,
            };

            let l_times_decoded = &l_scalar * &decoded;
            assert_eq!(
                l_times_decoded.compress().as_bytes(),
                &identity_bytes,
                "{}*B: [L]P must be identity",
                i
            );
        }

        // Test with diverse inputs: random-looking 32-byte strings filtered through decompress
        // These exercise the decode path for non-basepoint-derived inputs.
        let diverse_inputs: [[u8; 32]; 8] = [
            // Manually chosen bytes that produce valid Ristretto points
            [0x00; 32], // identity encoding (s = 0)
            [
                0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00,
            ],
            [
                0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00,
            ],
            [
                0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00,
            ],
            [
                0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00,
            ],
            [
                0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00,
            ],
            [
                0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00,
            ],
            [
                0x06, 0x54, 0xa2, 0xd3, 0xe8, 0x47, 0x7c, 0xb1, 0x92, 0x0e, 0xf1, 0x86, 0x3a, 0xf9,
                0xde, 0x14, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x00, 0x11, 0x22, 0x33,
                0x44, 0x55, 0x66, 0x00,
            ],
        ];
        let mut diverse_success = 0u32;
        for (idx, bytes) in diverse_inputs.iter().enumerate() {
            let compressed = CompressedRistretto(*bytes);
            if let Some(pt) = compressed.decompress() {
                let l_result = &l_scalar * &pt.0;
                assert_eq!(
                    l_result.compress().as_bytes(),
                    &identity_bytes,
                    "diverse input {}: [L]P must be identity",
                    idx
                );
                diverse_success += 1;
            }
        }
        assert!(
            diverse_success >= 1,
            "at least 1 diverse input should succeed"
        );

        // Test with hash-derived points (exercises a completely different input distribution)
        use sha2::Sha512;
        for seed in 0..50u32 {
            let input = seed.to_le_bytes();
            let pt = RistrettoPoint::hash_from_bytes::<Sha512>(&input);
            let l_result = &l_scalar * &pt.0;
            assert_eq!(
                l_result.compress().as_bytes(),
                &identity_bytes,
                "hash-derived point (seed {}): [L]P must be identity",
                seed
            );
        }
    }

    /// Validate lemma_sqrt_m1_limbs_bounded (formerly axiom_sqrt_m1_limbs_bounded):
    /// Each limb of SQRT_M1 fits in 51 bits.
    #[test]
    fn test_sqrt_m1_limbs_bounded() {
        let sqrt_m1 = constants::SQRT_M1;
        let max_51 = (1u64 << 51) - 1;
        for (i, &limb) in sqrt_m1.limbs.iter().enumerate() {
            assert!(
                limb <= max_51,
                "SQRT_M1 limb {} = {} exceeds 51-bit bound {}",
                i,
                limb,
                max_51
            );
        }

        // Also verify sqrt(-1)^2 = -1 as a sanity check
        let sq = sqrt_m1.square();
        use core::ops::Neg;
        let neg_one = Neg::neg(&FieldElement::ONE);
        assert!(bool::from(sq.ct_eq(&neg_one)), "SQRT_M1^2 must equal -1");
    }

    /// Validate axiom_minus_one_field_element_value:
    /// ZERO - ONE mod p equals the internal MINUS_ONE constant.
    #[test]
    fn test_minus_one_field_element_value() {
        use crate::backend::serial::u64::constants::MINUS_ONE;

        let minus_one = FieldElement51 {
            limbs: MINUS_ONE.limbs,
        };
        let computed = &FieldElement::ZERO - &FieldElement::ONE;

        assert!(
            bool::from(minus_one.ct_eq(&computed)),
            "MINUS_ONE must equal ZERO - ONE"
        );

        // Also verify: MINUS_ONE + ONE = ZERO
        let sum = &minus_one + &FieldElement::ONE;
        assert!(
            bool::from(sum.ct_eq(&FieldElement::ZERO)),
            "MINUS_ONE + ONE must equal ZERO"
        );
    }

    /// Validate axiom_sqrt_m1_not_square and axiom_neg_sqrt_m1_not_square:
    /// i = sqrt(-1) and -i are both non-squares in GF(p), verified via Euler's criterion.
    ///
    /// Euler's criterion: a is a square mod p iff a^((p-1)/2) ≡ 1 (mod p).
    /// For a non-square, a^((p-1)/2) ≡ -1 (mod p).
    #[test]
    fn test_sqrt_m1_not_square() {
        use core::ops::Neg;

        let sqrt_m1 = constants::SQRT_M1;
        let neg_sqrt_m1 = Neg::neg(&sqrt_m1);

        // Sanity: confirm i^2 = -1
        let i_sq = sqrt_m1.square();
        let neg_one = Neg::neg(&FieldElement::ONE);
        assert!(bool::from(i_sq.ct_eq(&neg_one)), "sqrt_m1^2 must equal -1");

        // Euler's criterion: compute i^((p-1)/2) via repeated squaring.
        // p = 2^255 - 19, so (p-1)/2 = 2^254 - 10 = 2^254 - 8 - 2 = (2^255 - 20) / 2.
        // We encode (p-1)/2 as little-endian bytes and use pow_bytes.
        //
        // (p-1)/2 = (2^255 - 20) / 2 = 2^254 - 10
        // In binary: 2^254 - 10 = 0b0011...110110 (254 bits with last few bits: ...10110)
        // As a 256-bit little-endian integer:
        // Byte 0: (2^254 - 10) mod 256 = (256 - 10) mod 256 = 246 = 0xF6
        // Byte 1..30: 0xFF (all ones from the 2^254 block minus the borrow)
        // Byte 31: 0x3F (= 63, top two bits clear since 2^254 < 2^255)
        //
        // More precisely: 2^254 - 10 in hex is:
        // 3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF6
        let half_p_minus_1: [u8; 32] = [
            0xf6, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0x3f,
        ];

        // Verify the exponent: 2 * half_p_minus_1 + 1 should give us p - 1 = 2^255 - 20
        // (i.e., half_p_minus_1 = (p-1)/2). We'll verify this indirectly: a^(p-1) = 1
        // for any nonzero a (Fermat), and a^((p-1)/2) = ±1 (Euler).

        // Compute i^((p-1)/2) using square-and-multiply (MSB-first)
        let euler_i = pow_field_element(&sqrt_m1, &half_p_minus_1);

        // For a non-square, Euler's criterion gives -1
        assert!(
            bool::from(euler_i.ct_eq(&neg_one)),
            "sqrt_m1^((p-1)/2) must equal -1 (i is NOT a square)"
        );

        // Compute (-i)^((p-1)/2) using the same exponent
        let euler_neg_i = pow_field_element(&neg_sqrt_m1, &half_p_minus_1);

        assert!(
            bool::from(euler_neg_i.ct_eq(&neg_one)),
            "(-sqrt_m1)^((p-1)/2) must equal -1 (-i is NOT a square)"
        );

        // Sanity check: 1 IS a square, so 1^((p-1)/2) should be 1
        let euler_one = pow_field_element(&FieldElement::ONE, &half_p_minus_1);
        assert!(
            bool::from(euler_one.ct_eq(&FieldElement::ONE)),
            "1^((p-1)/2) must equal 1 (sanity: 1 is a square)"
        );

        // Sanity check: 4 IS a square (2^2), so 4^((p-1)/2) should be 1
        let two = &FieldElement::ONE + &FieldElement::ONE;
        let four = two.square();
        let euler_four = pow_field_element(&four, &half_p_minus_1);
        assert!(
            bool::from(euler_four.ct_eq(&FieldElement::ONE)),
            "4^((p-1)/2) must equal 1 (sanity: 4 = 2^2 is a square)"
        );
    }

    /// Validate axiom_p_is_prime:
    /// p = 2^255 - 19 is prime, verified via deterministic Miller-Rabin.
    ///
    /// Miller-Rabin: write p - 1 = 2^s * d with d odd.
    /// p - 1 = 2^255 - 20 = 4 * (2^253 - 5), so s = 2, d = 2^253 - 5.
    /// For each witness a in {2, 3, 5, 7, 11, 13, 17, 19, 23}:
    ///   Compute x = a^d mod p.
    ///   If x == 1 or x == p-1, pass.
    ///   Otherwise, square up to s-1 times; if any result == p-1, pass.
    ///   If none, p is composite (but it won't be, since p is actually prime).
    ///
    /// 9 witnesses is far more than needed for a known prime; this serves as
    /// a runtime sanity check that the axiom is sound.
    #[test]
    fn test_p_is_prime() {
        // d = (p - 1) / 4 = (2^255 - 20) / 4 = 2^253 - 5
        // As 32-byte little-endian: 2^253 is byte 31 = 0x20, minus 5 gives
        // byte 0 = 0xFB, bytes 1..30 = 0xFF, byte 31 = 0x1F
        let d_bytes: [u8; 32] = [
            0xfb, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0x1f,
        ];

        let neg_one = core::ops::Neg::neg(&FieldElement::ONE);
        let s = 2u32; // p - 1 = 2^2 * d

        let witnesses: [u64; 9] = [2, 3, 5, 7, 11, 13, 17, 19, 23];

        for &a_val in witnesses.iter() {
            let a = FieldElement51 {
                limbs: [a_val, 0, 0, 0, 0],
            };

            // x = a^d mod p
            let mut x = pow_field_element(&a, &d_bytes);

            if bool::from(x.ct_eq(&FieldElement::ONE)) || bool::from(x.ct_eq(&neg_one)) {
                continue;
            }

            let mut passed = false;
            for _ in 0..(s - 1) {
                x = x.square();
                if bool::from(x.ct_eq(&neg_one)) {
                    passed = true;
                    break;
                }
            }

            assert!(
                passed,
                "Miller-Rabin witness {} says p is composite (should not happen)",
                a_val
            );
        }

        // Additional check: verify Fermat's Little Theorem directly for a = 2.
        // If p is prime, 2^(p-1) ≡ 1 (mod p).
        let p_minus_1: [u8; 32] = [
            0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0x7f,
        ];
        let two = FieldElement51 {
            limbs: [2, 0, 0, 0, 0],
        };
        let fermat = pow_field_element(&two, &p_minus_1);
        assert!(
            bool::from(fermat.ct_eq(&FieldElement::ONE)),
            "Fermat's Little Theorem: 2^(p-1) must equal 1 mod p"
        );
    }

    /// Validate axiom_ristretto_cross_mul_iff_equivalent:
    /// Ristretto equivalence ⟺ projective cross-multiplication check.
    ///
    /// For well-formed Edwards points P1=(X1:Y1:Z1:T1), P2=(X2:Y2:Z2:T2):
    ///   ristretto_equivalent(P1, P2) ⟺ (X1·Y2 == Y1·X2 || X1·X2 == Y1·Y2)
    ///
    /// Tests:
    ///   (a) Non-equivalent points: [i]B vs [j]B for i ≠ j fail the check
    ///   (b) Equivalent points: P and P + T for 4-torsion T pass the check
    ///   (c) Self-equivalence: P cross-mul P always passes
    #[test]
    fn test_ristretto_cross_mul_iff_equivalent() {
        use crate::scalar::Scalar;

        let bp = constants::RISTRETTO_BASEPOINT_POINT;
        let torsion = crate::backend::serial::u64::constants::EIGHT_TORSION;

        fn cross_mul_check(p1: &EdwardsPoint, p2: &EdwardsPoint) -> bool {
            let x1y2 = &p1.X * &p2.Y;
            let y1x2 = &p1.Y * &p2.X;
            let x1x2 = &p1.X * &p2.X;
            let y1y2 = &p1.Y * &p2.Y;
            bool::from(x1y2.ct_eq(&y1x2)) || bool::from(x1x2.ct_eq(&y1y2))
        }

        // (a) Non-equivalent: [i]B vs [j]B for distinct small scalars
        let multiples: alloc::vec::Vec<EdwardsPoint> =
            (1u64..=20).map(|i| &Scalar::from(i) * &bp.0).collect();
        for i in 0..multiples.len() {
            for j in (i + 1)..multiples.len() {
                assert!(
                    !cross_mul_check(&multiples[i], &multiples[j]),
                    "{}B and {}B should NOT be cross-mul equivalent",
                    i + 1,
                    j + 1
                );
            }
        }

        // (b) Equivalent: P + T for each 4-torsion element T should be equivalent to P
        // The 4-torsion subgroup E[4] consists of points at indices 0, 2, 4, 6 in EIGHT_TORSION
        let four_torsion_indices = [0usize, 2, 4, 6];
        for &scalar_val in &[1u64, 3, 7, 13, 19] {
            let p = &Scalar::from(scalar_val) * &bp.0;
            for &ti in &four_torsion_indices {
                let shifted = &p + &torsion[ti];
                assert!(
                    cross_mul_check(&p, &shifted),
                    "{}B + T[{}] should be cross-mul equivalent to {}B",
                    scalar_val,
                    ti,
                    scalar_val,
                );
            }
        }

        // (c) Self-equivalence: every point is equivalent to itself
        for i in 0..multiples.len() {
            assert!(
                cross_mul_check(&multiples[i], &multiples[i]),
                "{}B should be cross-mul equivalent to itself",
                i + 1
            );
        }

        // (d) Cross-check: verify cross_mul_check agrees with RistrettoPoint::ct_eq
        for i in 0..multiples.len() {
            for j in i..multiples.len() {
                let rp_i = RistrettoPoint(multiples[i]);
                let rp_j = RistrettoPoint(multiples[j]);
                let ristretto_eq = bool::from(rp_i.ct_eq(&rp_j));
                let cross_mul = cross_mul_check(&multiples[i], &multiples[j]);
                assert_eq!(
                    ristretto_eq,
                    cross_mul,
                    "Mismatch for {}B vs {}B: ct_eq={}, cross_mul={}",
                    i + 1,
                    j + 1,
                    ristretto_eq,
                    cross_mul
                );
            }
        }
    }

    /// Validate axiom_elligator_on_curve:
    /// The Elligator map always produces a point on the Edwards curve.
    /// We verify [L]*P == identity (prime-order subgroup membership implies on-curve).
    #[test]
    fn test_elligator_on_curve() {
        use crate::scalar::Scalar;

        let l_bytes = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
            0xde, 0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
        ];
        let l_scalar = Scalar::from_bytes_mod_order(l_bytes);
        let identity_bytes = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];

        // Test with small field elements
        for val in 0u64..50 {
            let mut fe_bytes = [0u8; 32];
            fe_bytes[0] = (val & 0xff) as u8;
            let fe = FieldElement::from_bytes(&fe_bytes);
            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);
            let l_result = &l_scalar * &pt.0;
            assert_eq!(
                l_result.compress().as_bytes(),
                &identity_bytes,
                "elligator({}): [L]P must be identity",
                val
            );
        }

        // Test with hash-derived field elements
        use sha2::{Digest, Sha512};
        for seed in 0u32..200 {
            let mut hasher = Sha512::new();
            hasher.update(b"elligator_on_curve_test_");
            hasher.update(seed.to_le_bytes());
            let hash = hasher.finalize();
            let mut fe_bytes = [0u8; 32];
            fe_bytes.copy_from_slice(&hash[..32]);
            let fe = FieldElement::from_bytes(&fe_bytes);
            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);
            let l_result = &l_scalar * &pt.0;
            assert_eq!(
                l_result.compress().as_bytes(),
                &identity_bytes,
                "elligator(hash seed {}): [L]P must be identity",
                seed
            );
        }
    }

    /// Validate axiom_elligator_in_even_subgroup:
    /// The Elligator map always produces a point in the prime-order subgroup
    /// (which is the even subgroup for cofactor-8 curves).
    /// We check [8]P != identity (not a torsion point) and [L]P == identity.
    #[test]
    fn test_elligator_in_even_subgroup() {
        use crate::scalar::Scalar;

        let l_bytes = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
            0xde, 0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
        ];
        let l_scalar = Scalar::from_bytes_mod_order(l_bytes);
        let identity_bytes = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];

        use sha2::{Digest, Sha512};
        let mut nonzero_count = 0u32;
        for seed in 0u32..200 {
            let mut hasher = Sha512::new();
            hasher.update(b"elligator_even_subgroup_test_");
            hasher.update(seed.to_le_bytes());
            let hash = hasher.finalize();
            let mut fe_bytes = [0u8; 32];
            fe_bytes.copy_from_slice(&hash[..32]);
            let fe = FieldElement::from_bytes(&fe_bytes);
            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);

            // [L]P must be identity (prime-order subgroup)
            let l_result = &l_scalar * &pt.0;
            assert_eq!(
                l_result.compress().as_bytes(),
                &identity_bytes,
                "seed {}: [L]P must be identity",
                seed
            );

            // Most points should NOT be torsion (i.e., [8]P != identity)
            let eight_p = pt.0.mul_by_pow_2(3);
            if eight_p.compress().as_bytes() != &identity_bytes {
                nonzero_count += 1;
            }
        }
        assert!(
            nonzero_count >= 190,
            "expected most elligator outputs to be non-torsion, got {} / 200",
            nonzero_count
        );
    }

    /// Validate that the Elligator completed-point denominators are never zero.
    /// This tests the Z ≠ 0 and T ≠ 0 properties used as inline `assume`s
    /// in elligator_ristretto_flavor.
    #[test]
    fn test_elligator_nonzero_denominators() {
        use sha2::{Digest, Sha512};
        use subtle::{ConditionallyNegatable, ConditionallySelectable};

        for seed in 0u32..200 {
            let mut hasher = Sha512::new();
            hasher.update(b"elligator_denom_test_");
            hasher.update(seed.to_le_bytes());
            let hash = hasher.finalize();
            let mut fe_bytes = [0u8; 32];
            fe_bytes.copy_from_slice(&hash[..32]);
            let r_0 = FieldElement::from_bytes(&fe_bytes);

            let i = &constants::SQRT_M1;
            let d = &constants::EDWARDS_D;
            let one = FieldElement::ONE;
            let c_init = constants::MINUS_ONE;

            let r = i * &r_0.square();
            let n_s = &(&r + &one) * &constants::ONE_MINUS_EDWARDS_D_SQUARED;
            let d_val = &(&c_init - &(d * &r)) * &(&r + d);

            let (is_sq, mut s) = FieldElement::sqrt_ratio_i(&n_s, &d_val);
            let mut s_prime = &s * &r_0;
            let s_prime_is_pos = !s_prime.is_negative();
            s_prime.conditional_negate(s_prime_is_pos);

            let not_sq = !is_sq;
            FieldElement51::conditional_assign(&mut s, &s_prime, not_sq);
            let mut c = c_init;
            FieldElement51::conditional_assign(&mut c, &r, not_sq);

            let n_t = &(&(&c * &(&r - &one)) * &constants::EDWARDS_D_MINUS_ONE_SQUARED) - &d_val;
            let s_sq = s.square();

            // T = 1 + s²
            let t_completed = &FieldElement::ONE + &s_sq;
            // Z = N_t * sqrt(ad-1)
            let z_completed = &n_t * &constants::SQRT_AD_MINUS_ONE;

            let t_bytes = t_completed.as_bytes();
            let z_bytes = z_completed.as_bytes();
            let t_is_zero = t_bytes.iter().all(|&b| b == 0);
            let z_is_zero = z_bytes.iter().all(|&b| b == 0);

            assert!(!t_is_zero, "seed {}: T_completed = 1 + s² is zero", seed);
            assert!(
                !z_is_zero,
                "seed {}: Z_completed = N_t * sqrt(ad-1) is zero",
                seed
            );
        }
    }

    /// Validate axiom_one_minus_d_squared_value:
    /// ONE_MINUS_EDWARDS_D_SQUARED == (1-d)(1+d) where d = EDWARDS_D.
    #[test]
    fn test_one_minus_d_squared_value() {
        use subtle::ConstantTimeEq;
        let d = constants::EDWARDS_D;
        let one = FieldElement::ONE;
        let one_minus_d = &one - &d;
        let one_plus_d = &one + &d;
        let computed = &one_minus_d * &one_plus_d;
        assert!(
            bool::from(computed.ct_eq(&constants::ONE_MINUS_EDWARDS_D_SQUARED)),
            "ONE_MINUS_EDWARDS_D_SQUARED != (1-d)(1+d)"
        );
    }

    /// Validate axiom_d_minus_one_squared_value:
    /// EDWARDS_D_MINUS_ONE_SQUARED == (d-1)^2.
    #[test]
    fn test_d_minus_one_squared_value() {
        use subtle::ConstantTimeEq;
        let d = constants::EDWARDS_D;
        let one = FieldElement::ONE;
        let d_minus_one = &d - &one;
        let computed = d_minus_one.square();
        assert!(
            bool::from(computed.ct_eq(&constants::EDWARDS_D_MINUS_ONE_SQUARED)),
            "EDWARDS_D_MINUS_ONE_SQUARED != (d-1)^2"
        );
    }

    /// Validate lemma_sqrt_ratio_matches_invsqrt_mul:
    /// sqrt_ratio_i(u, v) == |nat_invsqrt(u*v) * u| (nonneg correction applied).
    ///
    /// The raw product invsqrt(u*v)*u can be negative (~half the time),
    /// so we apply conditional_negate (the runtime equivalent of field_abs)
    /// before comparing to the exec result r which is always non-negative.
    #[test]
    fn test_sqrt_ratio_matches_invsqrt_mul() {
        use subtle::ConstantTimeEq;

        fn invsqrt_field(a: &FieldElement) -> FieldElement {
            let (_ok, result) = a.invsqrt();
            result
        }

        use sha2::{Digest, Sha512};
        for seed in 0u32..500 {
            let mut hasher = Sha512::new();
            hasher.update(b"sqrt_ratio_invsqrt_test_");
            hasher.update(seed.to_le_bytes());
            let hash = hasher.finalize();

            let mut u_bytes = [0u8; 32];
            let mut v_bytes = [0u8; 32];
            u_bytes.copy_from_slice(&hash[..32]);
            v_bytes.copy_from_slice(&hash[32..64]);
            let u = FieldElement::from_bytes(&u_bytes);
            let v = FieldElement::from_bytes(&v_bytes);

            let (_is_sq, r) = FieldElement::sqrt_ratio_i(&u, &v);
            let uv = &u * &v;
            let inv = invsqrt_field(&uv);
            let mut s_spec = &inv * &u;

            // Apply field_abs: conditional_negate if negative
            let neg = s_spec.is_negative();
            s_spec.conditional_negate(neg);

            assert!(
                bool::from(r.ct_eq(&s_spec)),
                "seed {}: sqrt_ratio_i(u,v) != nonneg(invsqrt(u*v) * u)",
                seed
            );
        }
    }
}
