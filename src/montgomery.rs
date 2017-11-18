// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Montgomery arithmetic.
//!
//! Apart from the compressed point implementation
//! (i.e. `CompressedMontgomeryU`), this module is a "clean room" implementation
//! of the Montgomery arithmetic described in the following papers:
//!
//! * Costello, Craig, and Benjamin Smith. "Montgomery curves and their
//!   arithmetic." Journal of Cryptographic Engineering (2017): 1-14.
//!   [PDF](http://eprint.iacr.org/2017/212.pdf)
//!
//! * Montgomery, Peter L. "Speeding the Pollard and elliptic curve methods of
//!   factorization." Mathematics of computation 48.177 (1987): 243-264.
//!   [PDF](http://www.ams.org/mcom/1987-48-177/S0025-5718-1987-0866113-7/)

// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]

use core::ops::{Mul, MulAssign};

use constants;
use field::FieldElement;
use edwards::{ExtendedPoint, CompressedEdwardsY};
use scalar::Scalar;

// XXX Move these to a common "group" module?  At the same time, we should
// XXX probably make a `trait Group` once const generics are implemented in
// XXX Rust. —isis
use edwards::{Identity, ValidityCheck};

use subtle::ConditionallyAssignable;
use subtle::ConditionallySwappable;
use subtle::Equal;
use subtle::Mask;

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
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CompressedMontgomeryU(pub [u8; 32]);

impl CompressedMontgomeryU {
    /// View this `CompressedMontgomeryU` as an array of bytes.
    pub fn as_bytes<'a>(&'a self) -> &'a [u8; 32] {
        &self.0
    }

    /// Convert this `CompressedMontgomeryU` to an array of bytes.
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
    pub fn decompress_edwards(&self) -> Option<ExtendedPoint> {
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

    /// Decompress this `CompressedMontgomeryU` to a `MontgomeryPoint`.
    ///
    /// Going from affine to projective coordinates, we have:
    ///
    ///      u → U/W
    ///
    /// # Returns
    ///
    /// A projective `MontgomeryPoint` corresponding to this compressed point.
    pub fn decompress(&self) -> MontgomeryPoint {
        MontgomeryPoint{
            U: FieldElement::from_bytes(&self.0),
            W: FieldElement::one(),
        }
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
        let A = &constants::MONTGOMERY_A;
        let one:       FieldElement = FieldElement::one();
        let v_squared: FieldElement = u * &(&u.square() + &(&(A * u) + &one));

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
        let current_sign:    u8 = x.is_negative();

        // Negate x to match the sign:
        x.conditional_assign(&neg_x, current_sign ^ sign);
        x
    }
}

/// A point on the Montgomery form of the curve, in projective 𝗣^2 coordinates.
///
/// The transition between affine and projective is given by
///
///      u → U/W
///      v → V/W
///
/// thus the Montgomery curve equation
///
///      E_(A,B) : Bv² = u(u² + Au + 1)
///
/// becomes
///
///      E_(A,B) : BV²W = U(U² + AUW + W²) ⊆ 𝗣^2
///
/// Here, again, to differentiate from points in the twisted Edwards model, we
/// call the point `(x,y)` in affine coordinates `(u,v)` and similarly in projective
/// space we use `(U:V:W)`.  However, since (as per Montgomery's original work) the
/// v-coordinate is superfluous for the purposes of scalar multiplication, we merely
/// use `(U:W)`.
#[derive(Copy, Clone, Debug)]
#[allow(missing_docs)]
pub struct MontgomeryPoint{
    pub U: FieldElement,
    pub W: FieldElement,
}

/// The identity point is a unique point (the only where `W = 0`) on the curve.
///
/// In projective coordinates, the quotient map `x : E (A,B) → E/<⦵> = 𝗣¹` is
///
///               ⎧ (x_P:1) if P = (x_P:y_P:1) ,
///      x : P ↦  ⎨
///               ⎩   (1:0) if P = O = (0:1:0) .
///
/// We emphasize that the formula `x((U: V : W)) = (U : W)` only holds on the
/// open subset of `E_(A,B)` where `W ≠ 0`; it does not extend to the point
/// `O = (0:1:0)` at infinity, because `(0:0)` is not a projective point.
///
/// # Returns
///
/// The (exceptional) point at infinity in the Montgomery model.
impl Identity for MontgomeryPoint {
    fn identity() -> MontgomeryPoint {
        MontgomeryPoint {
            U: FieldElement::one(),
            W: FieldElement::zero(),
        }
    }
}

/// Determine if two `MontgomeryPoint`s are equal, in constant time.
///
/// # Note
///
/// Because a compressed point on the Montgomery form of the curve doesn't
/// include the sign bit, there's two points here (if translated from the
/// Edwards form) which will equate.
///
/// # Returns
///
/// `1` if the points are equal, and `0` otherwise.
impl Equal for MontgomeryPoint {
    fn ct_eq(&self, that: &MontgomeryPoint) -> u8 {
        // (U_P:W_P) = (U_Q:W_Q) iff U_P * W_Q == U_Q * W_P,
        // since U_P/W_P == U_Q/W_Q.
        (&self.U * &that.W).ct_eq(&(&self.W * &that.U))
    }
}

/// Determine if this `MontgomeryPoint` is valid.
///
/// # Note
///
/// All projective points, except for `(X:W) = (0:0)`, are valid, since the
/// projective model is linear through the origin and is comprised by all `X` in
/// ℤ/(2²⁵⁵-19), thus `(0:0)` is the only element in Fₚ² which is not a
/// projective point.
///
/// # Returns
///
/// `true` if it is valid, and `false` otherwise.
impl ValidityCheck for MontgomeryPoint {
    fn is_valid(&self) -> bool {
        let zero = FieldElement::zero();

        if (self.U.ct_eq(&zero) & self.W.ct_eq(&zero)) == 1 {
            return true;
        }
        false
    }
}

/// Conditionally assign another `MontgomeryPoint` to this point, in constant time.
///
/// If `choice == 1`, assign `that` to `self`.  Otherwise, leave `self`
/// unchanged.
impl ConditionallyAssignable for MontgomeryPoint {
    fn conditional_assign(&mut self, that: &MontgomeryPoint, choice: Mask) {
        self.U.conditional_assign(&that.U, choice);
        self.W.conditional_assign(&that.W, choice);
    }
}

impl MontgomeryPoint {
    /// Compress this point to only its u-coordinate (note: affine).
    ///
    /// # Returns
    ///
    /// A `CompressedMontgomeryU`.
    pub fn compress(&self) -> CompressedMontgomeryU {
        let u_affine: FieldElement = &self.U * &self.W.invert();

        CompressedMontgomeryU(u_affine.to_bytes())
    }

    /// Differential addition for single-coordinate Montgomery points.
    ///
    /// Montgomery coordinates in projective 𝗣¹ space are odd in that 𝗣¹
    /// inherits none of the group structure from E_(A,B).  Hence, the mapping
    /// of the group operation, `⊕`, is undefined for the pair `(x(P), x(Q))`;
    /// that is, given `x(P)` and `x(Q)`, we cannot derive `x(P ⊕ Q)`.  This is
    /// due to the fact that, in Montgomery coordinates, `x(P)` determines `P`
    /// only up to a sign, and thus we cannot differentiate `x(P ⊕ Q)` from
    /// `x(P ⊖ Q)`.  However, via differential addition, any three of the values
    /// `{x(P), x(Q), x(P ⊕ Q), x(P ⊖ Q)}` determines the forth, so we can
    /// define *pseudo-addition* for a singular coordinate.
    ///
    /// # Warning
    ///
    /// If the `difference` is the identity point, or a two torsion point, the
    /// results of this method are not correct, but instead result in `(0:0)`
    /// (an invalid projective point in the Montgomery model).
    ///
    /// The doubling case is degenerate, in that `P ⦵ Q ∉ {O,T}`, where `T` is
    /// the two torsion point.
    fn differential_add(&self, that: &MontgomeryPoint,
                        difference: &MontgomeryPoint) -> MontgomeryPoint {
        // XXX Do we want these debug assertions? We would need to implement
        // XXX is_two_torsion_point(). —isis
        // debug_assert!(!difference.is_identity()); // P ⦵ Q ∉ {O,T}
        // debug_assert!(!difference.is_two_torsion_point());

        let v1: FieldElement = &(&self.U + &self.W) * &(&that.U - &that.W);
        let v2: FieldElement = &(&self.U - &self.W) * &(&that.U + &that.W);

        MontgomeryPoint {
            U: &difference.W * &(&v1 + &v2).square(),  // does reduction on square()
            W: &difference.U * &(&v1 - &v2).square(),  // does reduction on square()
        }
    }

    /// Pseudo-doubling for single-coordinate Montgomery points.
    ///
    /// Given a Montgomery U-coordinate of a point `P`, compute the
    /// U-coordinate given by
    ///
    ///      differential_double: x(P) ⟼ x([2]P)
    ///
    /// # Returns
    ///
    /// A Montgomery point equal to doubling this one.
    ///
    // XXX It seems possible that combining the differential_add() and
    // XXX differential_double() methods would save a non-trivial amount of
    // XXX computation in the ladder. —isis
    fn differential_double(&self) -> MontgomeryPoint {
        let mut v1: FieldElement;
        let v2: FieldElement;
        let v3: FieldElement;

        v1 = (&self.U + &self.W).square();
        v2 = (&self.U - &self.W).square();

        let U: FieldElement = &v1 * &v2;

        v1 -= &v2;
        v3  = &(&constants::APLUS2_OVER_FOUR * &v1) + &v2;

        let W: FieldElement = &v1 * &v3;

        MontgomeryPoint{ U: U, W: W }
    }
}

/// Multiply this `MontgomeryPoint` by a `Scalar`.
///
/// The reader is refered to §5.3 of ["Montgomery Curves and Their Arithmetic"
/// by Craig Costello and Benjamin Smith](https://eprint.iacr.org/2017/212.pdf)
/// for an overview of side-channel-free Montgomery laddering algorithms.
impl<'a, 'b> Mul<&'b Scalar> for &'a MontgomeryPoint {
    type Output = MontgomeryPoint;

    fn mul(self, scalar: &'b Scalar) -> MontgomeryPoint {
        let mut x0: MontgomeryPoint = MontgomeryPoint::identity();
        let mut x1: MontgomeryPoint = *self;

        let bits: [i8; 256] = scalar.bits();

        for i in (0..255).rev() {
            let mask: u8 = (bits[i+1] ^ bits[i]) as u8;

            debug_assert!(mask == 0 || mask == 1);

            x0.conditional_swap(&mut x1, mask);
            x1 = x0.differential_add(&x1, &self);
            x0 = x0.differential_double();
        }
        x0.conditional_swap(&mut x1, bits[0] as u8);
        x0
    }
}

impl<'b> MulAssign<&'b Scalar> for MontgomeryPoint {
    fn mul_assign(&mut self, scalar: &'b Scalar) {
        let result = (self as &MontgomeryPoint) * scalar;
        *self = result;
    }
}

impl<'a, 'b> Mul<&'b MontgomeryPoint> for &'a Scalar {
    type Output = MontgomeryPoint;

    fn mul(self, point: &'b MontgomeryPoint) -> MontgomeryPoint {
        point * &self
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use constants::BASE_COMPRESSED_MONTGOMERY;
    use edwards::Identity;
    use super::*;

    use rand::OsRng;

    /// Test Montgomery conversion against the X25519 basepoint.
    #[test]
    fn basepoint_to_montgomery() {
        assert_eq!(constants::ED25519_BASEPOINT_POINT.to_montgomery().compress(),
                   BASE_COMPRESSED_MONTGOMERY);
    }

    /// Test Montgomery conversion against the X25519 basepoint.
    #[test]
    fn basepoint_from_montgomery() {
        assert_eq!(BASE_COMPRESSED_MONTGOMERY,
                   constants::BASE_CMPRSSD.decompress().unwrap().to_montgomery().compress());
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
        assert!(div_by_zero_u.decompress_edwards().is_none());
    }

    /// Montgomery compression of the identity point should not fail (since the
    /// mapping in `ProjectivePoint.to_montgomery()` should be valid for the
    /// identity.
    #[test]
    fn identity_to_monty() {
        let id = ExtendedPoint::identity();
        assert_eq!(id.to_montgomery().compress(), MontgomeryPoint::identity().compress());
    }

    #[test]
    fn projective_to_affine_roundtrips() {
        assert_eq!(BASE_COMPRESSED_MONTGOMERY.decompress().compress(),
                   BASE_COMPRESSED_MONTGOMERY);

    }

    #[test]
    fn differential_double_matches_double() {
        let p: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.double();
        let q: MontgomeryPoint = BASE_COMPRESSED_MONTGOMERY.decompress().differential_double();

        assert_eq!(p.to_montgomery().compress(), q.compress());
    }

    #[test]
    #[cfg(feature="precomputed_tables")]
    fn montgomery_ct_eq_ne() {
        let mut csprng: OsRng = OsRng::new().unwrap();
        let s1: Scalar = Scalar::random(&mut csprng);
        let s2: Scalar = Scalar::random(&mut csprng);
        let p1: MontgomeryPoint = (&s1 * &constants::ED25519_BASEPOINT_TABLE).to_montgomery();
        let p2: MontgomeryPoint = (&s2 * &constants::ED25519_BASEPOINT_TABLE).to_montgomery();

        assert_eq!(p1.ct_eq(&p2), 0);
    }

    #[test]
    #[cfg(feature="precomputed_tables")]
    fn montgomery_ct_eq_eq() {
        let mut csprng: OsRng = OsRng::new().unwrap();
        let s1: Scalar = Scalar::random(&mut csprng);
        let p1: MontgomeryPoint = (&s1 * &constants::ED25519_BASEPOINT_TABLE).to_montgomery();

        assert_eq!(p1.ct_eq(&p1), 1);
    }

    #[test]
    #[cfg(feature="precomputed_tables")]
    fn differential_add_matches_edwards_model() {
        let mut csprng: OsRng = OsRng::new().unwrap();

        let s1: Scalar = Scalar::random(&mut csprng);
        let s2: Scalar = Scalar::random(&mut csprng);
        let p1: ExtendedPoint = &constants::ED25519_BASEPOINT_TABLE * &s1;
        let p2: ExtendedPoint = &constants::ED25519_BASEPOINT_TABLE * &s2;
        let diff: ExtendedPoint = &p1 - &p2;

        let p1m: MontgomeryPoint = p1.to_montgomery();
        let p2m: MontgomeryPoint = p2.to_montgomery();
        let diffm: MontgomeryPoint = diff.to_montgomery();

        let result = p1m.differential_add(&p2m, &diffm);

        assert_eq!(result.compress(), (&p1 + &p2).to_montgomery().compress());
    }

    #[test]
    #[cfg(feature="precomputed_tables")]
    fn ladder_matches_scalarmult() {
        let mut csprng: OsRng = OsRng::new().unwrap();

        let s: Scalar = Scalar::random(&mut csprng);
        let p_edwards: ExtendedPoint = &constants::ED25519_BASEPOINT_TABLE * &s;
        let p_montgomery: MontgomeryPoint = p_edwards.to_montgomery();

        let expected = &s * &p_edwards;
        let result   = &s * &p_montgomery;

        assert_eq!(result.compress(), expected.to_montgomery().compress())
    }

    #[test]
    fn ladder_basepoint_times_two_matches_double() {
        let two: Scalar = Scalar::from_u64(2u64);
        let result: MontgomeryPoint = &BASE_COMPRESSED_MONTGOMERY.decompress() * &two;
        let expected: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.double();

        assert_eq!(result.compress(), expected.to_montgomery().compress());
    }

    #[test]
    #[should_panic(expected = "assertion failed: self[31] <= 127")]
    #[cfg(feature="precomputed_tables")]
    fn ladder_matches_scalarmult_with_scalar_high_bit_set() {
        let mut s: Scalar = Scalar::one();

        s[31] = 255;

        let result: MontgomeryPoint = &BASE_COMPRESSED_MONTGOMERY.decompress() * &s;
        let expected: ExtendedPoint = &constants::ED25519_BASEPOINT_TABLE * &s;

        assert_eq!(result.compress(), expected.to_montgomery().compress())
    }
}

#[cfg(all(test, feature = "bench"))]
#[cfg(feature="precomputed_tables")]
mod bench {
    use rand::OsRng;
    use constants::ED25519_BASEPOINT_TABLE;
    use constants::BASE_COMPRESSED_MONTGOMERY;
    use test::Bencher;
    use super::*;

    #[bench]
    fn montgomery_ct_eq(b: &mut Bencher) {
        let mut csprng: OsRng = OsRng::new().unwrap();
        let s1: Scalar = Scalar::random(&mut csprng);
        let s2: Scalar = Scalar::random(&mut csprng);
        let p1: MontgomeryPoint = (&s1 * &ED25519_BASEPOINT_TABLE).to_montgomery();
        let p2: MontgomeryPoint = (&s2 * &ED25519_BASEPOINT_TABLE).to_montgomery();

        b.iter(| | p1.ct_eq(&p2))
    }

    #[bench]
    fn montgomery_decompress(b: &mut Bencher) {
        b.iter(| | BASE_COMPRESSED_MONTGOMERY.decompress());
    }

    #[bench]
    fn montgomery_compress(b: &mut Bencher) {
        let p: MontgomeryPoint = BASE_COMPRESSED_MONTGOMERY.decompress();

        b.iter(| | p.compress());
    }

    #[bench]
    fn montgomery_ladder(b: &mut Bencher) {
        let mut csprng: OsRng = OsRng::new().unwrap();
        let s: Scalar = Scalar::random(&mut csprng);
        let p: MontgomeryPoint = (&Scalar::random(&mut csprng) * &ED25519_BASEPOINT_TABLE).to_montgomery();

        b.iter(| | &s * &p);
    }
}
