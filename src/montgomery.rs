// -*- mode: rust; -*-
//
// To the extent possible under law, the authors have waived all copyright and
// related or neighboring rights to curve25519-dalek, using the Creative
// Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full details.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Montgomery arithmetic prototype, subject to revision.

// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]


use constants;
use field::FieldElement;
use edwards::{ExtendedPoint, CompressedEdwardsY};

use subtle::ConditionallyAssignable;

/// In "Montgomery u" format, as used in X25519, a point `(u,v)` on
/// the Montgomery curve
///
///    v^2 = u * (u^2 + 486662*u + 1)
///
/// is represented just by `u`.  Note that we use `(u,v)` instead of
/// `(x,y)` for Montgomery coordinates to avoid confusion with Edwards
/// coordinates.  For Montgomery curves, it is possible to compute the
/// `u`-coordinate of `n(u,v)` just from `n` and `u`, so it is not
/// necessary to use `v` for a Diffie-Hellman key exchange.
///
/// XXX add note on monty, twist security, edwards impl of x25519, rfc7748
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CompressedMontgomeryU(pub [u8; 32]);

impl CompressedMontgomeryU {
    /// View this `CompressedMontgomeryU` as an array of bytes.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// Attempt to decompress to an `ExtendedPoint`.
    ///
    /// # Note
    ///
    /// Since there are two curve points with the same
    /// `u`-coordinate, the `u`-coordinate does not fully specify a
    /// point.  That is, roundtripping between an `ExtendedPoint` and
    /// a `CompressedMontgomeryU` discards its sign bit.
    ///
    /// # Warning
    ///
    /// This function is *not* constant time.
    ///
    /// # Return
    ///
    /// An `Option<ExtendedPoint>`, which will be `None` if either condition holds:
    ///
    /// * `u = -1`, or
    /// * `v` is not square.
    //
    // XXX any other exceptional points for the birational map?
    pub fn decompress(&self) -> Option<ExtendedPoint> {
        let u: FieldElement = FieldElement::from_bytes(&self.0);

        // If u = -1, then v^2 = u*(u^2+486662*u+1) = 486660.
        // But 486660 is nonsquare mod p, so this is not a curve point.
        //
        // Note: currently, without this check, u = -1 will accidentally
        // decode to a valid (but incorrect) point, since 0.invert() = 0.
        if u == FieldElement::minus_one() {
            return None;
        }

        let y: FieldElement = CompressedMontgomeryU::to_edwards_y(&u); // y = (u-1)/(u+1)

        // XXX this does two inversions: the above + one in .decompress()
        // is it possible to do one?
        CompressedEdwardsY(y.to_bytes()).decompress()
    }

    /// Given a Montgomery `u` coordinate, compute an Edwards `y` via
    /// `y = (u-1)/(u+1)`.
    ///
    /// # Return
    ///
    /// A `FieldElement` corresponding to this coordinate, but in Edwards form.
    pub fn to_edwards_y(u: &FieldElement) -> FieldElement {
        // Since `u = (1+y)/(1-y)` and `v = √(u(u²+Au+1))`, so `y = (u-1)/(u+1)`.
        &(u - &FieldElement::one()) * &(u + &FieldElement::one()).invert()
    }

    /// Given a Montgomery `u` coordinate, compute the corresponding
    /// Montgomery `v` coordinate by computing the right-hand side of
    /// the Montgomery field equation, `v² = u(u² + Au +1)`.
    ///
    /// # Return
    ///
    /// A tuple of (`u8`, `FieldElement`), where the `u8` is `1` if the v² was
    /// actually a square and `0` if otherwise, along with a `FieldElement`: the
    /// Montgomery `v` corresponding to this `u`.
    pub fn to_montgomery_v(u: &FieldElement) -> (u8, FieldElement) {
        let one:       FieldElement = FieldElement::one();
        let v_squared: FieldElement = u * &(&u.square() + &(&(&constants::A * u) + &one));

        let (okay, v_inv) = v_squared.invsqrt();
        let v = &v_inv * &v_squared;

        (okay, v)
    }

    /// Given Montgomery coordinates `(u, v)`, recover the Edwards `x` coordinate.
    ///
    /// # Inputs
    ///
    /// * `u` and `v` are both `&FieldElement`s, corresponding the the `(u, v)`
    ///   coordinates of this `CompressedMontgomeryU`.
    /// * `sign` is an &u8.
    ///
    /// ## Explanation of choice of `sign`
    ///
    /// ### Original Signal behaviour:
    ///
    /// - `1u8` will leave `x` negative if it is negative, and will negate
    ///   `x` if it is positive, and
    /// - `0u8` will leave `x` positive if it is positive, and will negate
    ///   `x` if it is negative.
    ///
    /// Hence, if `sign` is `1u8`, the returned `x` will be negative.
    /// Otherwise, if `sign` is `0u8`, the returned `x` will be positive.
    ///
    /// # Return
    ///
    /// A `FieldElement`, the Edwards `x` coordinate, by using `(u, v)` to
    /// convert from Montgomery to Edwards form via the right-hand side of the
    /// equation: `x=(u/v)*sqrt(-A-2)`.
    pub fn to_edwards_x(u: &FieldElement, v: &FieldElement, sign: &u8) -> FieldElement {
        let mut x: FieldElement = &(u * &v.invert()) * &constants::SQRT_MINUS_APLUS2;
        let neg_x: FieldElement = -(&x);
        let current_sign:    u8 = x.is_negative_ed25519();

        // Negate x to match the sign:
        x.conditional_assign(&neg_x, current_sign ^ sign);
        x
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use edwards::Identity;
    use super::*;

    /// The X25519 basepoint, in compressed Montgomery form.
    static BASE_CMPRSSD_MONTY: CompressedMontgomeryU =
        CompressedMontgomeryU([0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                               0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                               0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                               0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);

    /// Test Montgomery conversion against the X25519 basepoint.
    #[test]
    fn basepoint_to_montgomery() {
        assert_eq!(constants::ED25519_BASEPOINT_POINT.compress_montgomery().unwrap(),
                   BASE_CMPRSSD_MONTY);
    }

    /// Test Montgomery conversion against the X25519 basepoint.
    #[test]
    fn basepoint_from_montgomery() {
        assert_eq!(BASE_CMPRSSD_MONTY.decompress().unwrap().compress_edwards(),
                   constants::BASE_CMPRSSD);
    }

    /// If u = -1, then v^2 = u*(u^2+486662*u+1) = 486660.
    /// But 486660 is nonsquare mod p, so this should fail.
    ///
    /// XXX what does Signal do here?
    #[test]
    fn u_minus_one_monty() {
        let minus_one = FieldElement::minus_one();
        let minus_one_bytes = minus_one.to_bytes();
        let div_by_zero_u = CompressedMontgomeryU(minus_one_bytes);
        assert!(div_by_zero_u.decompress().is_none());
    }

    /// Montgomery compression of the identity point should
    /// fail (it's sent to infinity).
    #[test]
    fn identity_to_monty() {
        let id = ExtendedPoint::identity();
        assert!(id.compress_montgomery().is_none());
    }
}
