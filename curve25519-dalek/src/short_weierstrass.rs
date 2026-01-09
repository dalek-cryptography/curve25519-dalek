//! Short Weierstrass form utilities for Curve25519.
//!
//! This module provides a lightweight affine representation and conversion
//! utilities for moving between the Edwards and short Weierstrass models.

use crate::edwards::EdwardsPoint;
use crate::field::FieldElement;
use crate::traits::{Identity, IsIdentity};

/// Affine point on the short Weierstrass form of Curve25519.
///
/// Note: the SW coefficient `a` is non-zero, which means SPPARK must be
/// instantiated with a valid `a4` constant matching `sw_a()`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SwPoint {
    /// The point at infinity.
    Identity,
    /// An affine point with coordinates (x, y).
    Affine {
        /// x-coordinate.
        x: FieldElement,
        /// y-coordinate.
        y: FieldElement,
    },
}

impl SwPoint {
    /// Return the identity point.
    pub fn identity() -> Self {
        SwPoint::Identity
    }

    /// Convert an Edwards point into the short Weierstrass model.
    pub fn from_edwards(point: &EdwardsPoint) -> Self {
        if point.is_identity() {
            return SwPoint::Identity;
        }

        let z_inv = point.Z.invert();
        let x_affine = &point.X * &z_inv;
        let y_affine = &point.Y * &z_inv;
        let one = FieldElement::ONE;

        // Montgomery u = (1 + y) / (1 - y)
        let u = &(&one + &y_affine) * &(&one - &y_affine).invert();
        // Montgomery v = u / x, then scale to B=1 via sqrt(-486664)
        let v = &u * &x_affine.invert();
        let v = &montgomery_b_sqrt() * &v;

        let x = &u + &montgomery_a_over_three();
        let y = v;

        SwPoint::Affine { x, y }
    }

    /// Convert this point into an Edwards point, if defined.
    pub fn to_edwards(&self) -> Option<EdwardsPoint> {
        match self {
            SwPoint::Identity => Some(EdwardsPoint::identity()),
            SwPoint::Affine { x, y } => {
                if *y == FieldElement::ZERO {
                    return None;
                }

                let one = FieldElement::ONE;
                let u = x - &montgomery_a_over_three();
                let v = y * &montgomery_b_sqrt().invert();
                let v_inv = v.invert();

                // Edwards x = u / v
                let x_ed = &u * &v_inv;

                // Edwards y = (u - 1) / (u + 1)
                let denom = &u + &one;
                if denom == FieldElement::ZERO {
                    return None;
                }
                let denom_inv = denom.invert();
                let y_ed = &(&u - &one) * &denom_inv;

                Some(EdwardsPoint {
                    X: x_ed,
                    Y: y_ed,
                    Z: FieldElement::ONE,
                    T: &x_ed * &y_ed,
                })
            }
        }
    }

    /// Return affine coordinates as little-endian byte arrays.
    pub fn to_affine_le_bytes(&self) -> Option<([u8; 32], [u8; 32])> {
        match self {
            SwPoint::Identity => None,
            SwPoint::Affine { x, y } => Some((x.to_bytes(), y.to_bytes())),
        }
    }

    /// Build a point from affine little-endian byte arrays.
    pub fn from_affine_le_bytes(x: [u8; 32], y: [u8; 32]) -> Option<Self> {
        if x == [0u8; 32] && y == [0u8; 32] {
            return Some(SwPoint::Identity);
        }

        let x = FieldElement::from_bytes(&x);
        let y = FieldElement::from_bytes(&y);
        let point = SwPoint::Affine { x, y };
        if point.is_on_curve() {
            Some(point)
        } else {
            None
        }
    }

    /// Add two points in affine coordinates.
    pub fn add(&self, other: &SwPoint) -> SwPoint {
        match (self, other) {
            (SwPoint::Identity, _) => *other,
            (_, SwPoint::Identity) => *self,
            (SwPoint::Affine { x: x1, y: y1 }, SwPoint::Affine { x: x2, y: y2 }) => {
                if x1 == x2 {
                    if y1 == &(-y2) {
                        return SwPoint::Identity;
                    }
                    if y1 == y2 {
                        return double_affine(x1, y1);
                    }
                }

                let numerator = y2 - y1;
                let denominator = (x2 - x1).invert();
                let slope = &numerator * &denominator;
                let x3 = &(&slope.square() - x1) - x2;
                let y3 = &(&slope * &(x1 - &x3)) - y1;

                SwPoint::Affine { x: x3, y: y3 }
            }
        }
    }

    /// Check whether this point lies on the short Weierstrass curve.
    pub fn is_on_curve(&self) -> bool {
        match self {
            SwPoint::Identity => true,
            SwPoint::Affine { x, y } => {
                let y2 = y.square();
                let x2 = x.square();
                let x3 = &x2 * x;
                let rhs = &x3 + &(&sw_a() * x);
                y2 == &rhs + &sw_b()
            }
        }
    }
}

fn double_affine(x: &FieldElement, y: &FieldElement) -> SwPoint {
    if *y == FieldElement::ZERO {
        return SwPoint::Identity;
    }

    let two = fe_from_u64(2);
    let three = fe_from_u64(3);
    let numerator = &(&three * &x.square()) + &sw_a();
    let denominator = (&two * y).invert();
    let slope = &numerator * &denominator;
    let x3 = &slope.square() - &(&two * x);
    let y3 = &(&slope * &(x - &x3)) - y;

    SwPoint::Affine { x: x3, y: y3 }
}

fn fe_from_u64(n: u64) -> FieldElement {
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&n.to_le_bytes());
    FieldElement::from_bytes(&bytes)
}

fn montgomery_a_over_three() -> FieldElement {
    let inv_three = fe_from_u64(3).invert();
    &montgomery_a() * &inv_three
}

/// Return the short Weierstrass curve coefficient a.
///
/// This value must match the `a4` constant provided to SPPARK templates.
pub(crate) fn sw_a() -> FieldElement {
    let one = FieldElement::ONE;
    let inv_three = fe_from_u64(3).invert();
    let a_sq = montgomery_a().square();
    &one - &(&a_sq * &inv_three)
}

/// Return the short Weierstrass curve coefficient b.
pub(crate) fn sw_b() -> FieldElement {
    let a = montgomery_a();
    let a2 = a.square();
    let a3 = &a2 * &a;
    let inv_three = fe_from_u64(3).invert();
    let inv_twenty_seven = &(&inv_three * &inv_three) * &inv_three;
    let two = fe_from_u64(2);

    &(&a3 * &(&two * &inv_twenty_seven)) - &(&a * &inv_three)
}

fn montgomery_a() -> FieldElement {
    fe_from_u64(486662)
}

fn montgomery_b_sqrt() -> FieldElement {
    FieldElement::from_bytes(&[
        0x06, 0x7e, 0x45, 0xff, 0xaa, 0x04, 0x6e, 0xcc, 0x82, 0x1a, 0x7d, 0x4b, 0xd1, 0xd3, 0xa1,
        0xc5, 0x7e, 0x4f, 0xfc, 0x03, 0xdc, 0x08, 0x7b, 0xd2, 0xbb, 0x06, 0xa0, 0x60, 0xf4, 0xed,
        0x26, 0x0f,
    ])
}

#[cfg(test)]
mod tests {
    use super::SwPoint;
    use super::{sw_a, sw_b};
    use crate::constants;
    use crate::scalar::Scalar;

    fn sw_scalar_mul(point: &SwPoint, scalar: &Scalar) -> SwPoint {
        let mut acc = SwPoint::Identity;
        let mut base = *point;
        let bytes = scalar.to_bytes();

        for i in 0..256 {
            let byte = bytes[i / 8];
            if ((byte >> (i % 8)) & 1) == 1 {
                acc = acc.add(&base);
            }
            base = base.add(&base);
        }

        acc
    }

    #[test]
    fn sw_round_trip_add_matches_edwards() {
        let mut rng = rand::rng();

        for _ in 0..32 {
            let a = Scalar::random(&mut rng);
            let b = Scalar::random(&mut rng);
            let p = constants::ED25519_BASEPOINT_POINT * a;
            let q = constants::ED25519_BASEPOINT_POINT * b;

            let ed_sum = p + q;
            let sw_p = SwPoint::from_edwards(&p);
            let sw_q = SwPoint::from_edwards(&q);
            let sw_sum = sw_p.add(&sw_q);

            assert!(sw_sum.is_on_curve());
            let back = sw_sum.to_edwards().expect("sw->edwards should succeed");
            assert_eq!(back, ed_sum);

            let ed_double = p + p;
            let sw_double = sw_p.add(&sw_p);
            assert!(sw_double.is_on_curve());
            let back_double = sw_double.to_edwards().expect("sw->edwards should succeed");
            assert_eq!(back_double, ed_double);
        }
    }

    #[test]
    fn sw_scalar_mul_matches_edwards() {
        let mut rng = rand::rng();

        for _ in 0..32 {
            let s = Scalar::random(&mut rng);
            let t = Scalar::random(&mut rng);
            let p = constants::ED25519_BASEPOINT_POINT * s;

            let ed_result = p * t;
            let sw_p = SwPoint::from_edwards(&p);
            let sw_result = sw_scalar_mul(&sw_p, &t);

            assert!(sw_result.is_on_curve());
            let back = sw_result.to_edwards().expect("sw->edwards should succeed");
            assert_eq!(back, ed_result);
        }
    }

    #[test]
    fn sw_add_associativity() {
        let mut rng = rand::rng();

        for _ in 0..32 {
            let a = Scalar::random(&mut rng);
            let b = Scalar::random(&mut rng);
            let c = Scalar::random(&mut rng);

            let p = SwPoint::from_edwards(&(constants::ED25519_BASEPOINT_POINT * a));
            let q = SwPoint::from_edwards(&(constants::ED25519_BASEPOINT_POINT * b));
            let r = SwPoint::from_edwards(&(constants::ED25519_BASEPOINT_POINT * c));

            let left = p.add(&q).add(&r);
            let right = p.add(&q.add(&r));

            assert!(left.is_on_curve());
            assert!(right.is_on_curve());
            assert_eq!(left, right);
        }
    }

    #[test]
    fn sw_scalar_mul_associativity_commutes() {
        let mut rng = rand::rng();
        let base = SwPoint::from_edwards(&constants::ED25519_BASEPOINT_POINT);

        for _ in 0..32 {
            let a = Scalar::random(&mut rng);
            let b = Scalar::random(&mut rng);
            let ab = a * b;

            let left = sw_scalar_mul(&base, &ab);
            let b_p = sw_scalar_mul(&base, &b);
            let a_p = sw_scalar_mul(&base, &a);
            let right1 = sw_scalar_mul(&b_p, &a);
            let right2 = sw_scalar_mul(&a_p, &b);

            assert!(left.is_on_curve());
            assert!(right1.is_on_curve());
            assert!(right2.is_on_curve());
            assert_eq!(left, right1);
            assert_eq!(left, right2);
        }
    }

    #[test]
    fn sw_constants_match_expected() {
        let expected_a = crate::field::FieldElement::from_bytes(&[
            0x44, 0xa1, 0x14, 0x49, 0x98, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
            0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
            0xaa, 0xaa, 0xaa, 0x2a,
        ]);
        let expected_b = crate::field::FieldElement::from_bytes(&[
            0x64, 0xc8, 0x10, 0x77, 0x9c, 0x5e, 0x0b, 0x26, 0xb4, 0x97, 0xd0, 0x5e, 0x42, 0x7b,
            0x09, 0xed, 0x25, 0xb4, 0x97, 0xd0, 0x5e, 0x42, 0x7b, 0x09, 0xed, 0x25, 0xb4, 0x97,
            0xd0, 0x5e, 0x42, 0x7b,
        ]);

        assert_eq!(sw_a(), expected_a);
        assert_eq!(sw_b(), expected_b);
    }
}
