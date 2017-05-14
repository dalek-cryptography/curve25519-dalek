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

//! An implementation of Mike Hamburg's Decaf cofactor-eliminating
//! point-compression scheme, providing a prime-order group on top of
//! a non-prime-order elliptic curve.
//!
//! Note: this code is currently feature-gated with the `yolocrypto`
//! feature flag, because our implementation is still unfinished.

// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]

use core::fmt::Debug;

use constants;
use field::FieldElement;
use subtle::CTAssignable;
use subtle::CTNegatable;

use core::ops::{Add, Sub, Neg};
use core::ops::{Mul, MulAssign};

use curve;
use curve::ExtendedPoint;
use curve::EdwardsBasepointTable;
use curve::Identity;
use scalar::Scalar;

// ------------------------------------------------------------------------
// Compressed points
// ------------------------------------------------------------------------

/// A point serialized using Mike Hamburg's Decaf scheme.
///
/// XXX think about how this API should work
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct CompressedDecaf(pub [u8; 32]);

/// The result of compressing a `DecafPoint`.
impl CompressedDecaf {
    /// View this `CompressedDecaf` as an array of bytes.
    pub fn as_bytes<'a>(&'a self) -> &'a [u8;32] {
        &self.0
    }

    /// Attempt to decompress to an `DecafPoint`.
    pub fn decompress(&self) -> Option<DecafPoint> {
        // XXX should decoding be CT ?
        // XXX need to check that xy is nonnegative and reject otherwise
        let s = FieldElement::from_bytes(self.as_bytes());

        // Check that s = |s| and reject otherwise.
        let mut abs_s = s;
        let neg = abs_s.is_negative_decaf();
        abs_s.conditional_negate(neg);
        if abs_s != s { return None; }

        let ss = s.square();
        let X = &s + &s;                    // X = 2s
        let Z = &FieldElement::one() - &ss; // Z = 1+as^2
        let u = &(&Z * &Z) - &(&constants::d4 * &ss); // u = Z^2 - 4ds^2
        let uss = &u * &ss;

        let (uss_is_nonzero_square, mut v) = uss.invsqrt();
        if (uss_is_nonzero_square | uss.is_zero()) == 0u8 {
            return None; // us^2 is nonzero nonsquare
        }

        // Now v = 1/sqrt(us^2) if us^2 is a nonzero square, 0 if us^2 is zero.
        let uv = &v * &u;
        if uv.is_negative_decaf() == 1u8 {
            v.negate();
        }
        let mut two_minus_Z = -&Z; two_minus_Z[0] += 2;
        let mut w = &v * &(&s * &two_minus_Z);
        w.conditional_assign(&FieldElement::one(), s.is_zero());
        let Y = &w * &Z;
        let T = &w * &X;

        // "To decode the point, one must decode it to affine form
        // instead of projective, and check that xy is non-negative."
        //
        // XXX can we merge this inversion with the one above?
        let xy = &T * &Z.invert();
        if (Y.is_nonzero() & xy.is_nonnegative_decaf()) == 1u8 {
            Some(DecafPoint(ExtendedPoint{ X: X, Y: Y, Z: Z, T: T }))
        } else {
            None
        }
    }
}

impl Identity for CompressedDecaf {
    fn identity() -> CompressedDecaf {
        CompressedDecaf([0u8;32])
    }
}

/// A point in a prime-order group.
///
/// XXX think about how this API should work
#[derive(Copy, Clone)]
pub struct DecafPoint(pub ExtendedPoint);

impl DecafPoint {
    /// Compress in Decaf format.
    pub fn compress(&self) -> CompressedDecaf {
        // Q: Do we want to encode twisted or untwisted?
        //
        // Notes: 
        // Recall that the twisted Edwards curve E_{a,d} is of the form
        //
        //     ax^2 + y^2 = 1 + dx^2y^2. 
        //
        // Internally, we operate on the curve with a = -1, d =
        // -121665/121666, a.k.a., the twist.  But maybe we would like
        // to use Decaf on the untwisted curve with a = 1, d =
        // 121665/121666.  (why? interop?)
        //
        // Fix i, a square root of -1 (mod p).
        //
        // The map x -> ix is an isomorphism from E_{a,d} to E_{-a,-d}. 
        // Its inverse is x -> -ix.
        // let untwisted_X = &self.X * &constants::MSQRT_M1;
        // etc.

        // Step 0: pre-rotation, needed for Decaf with E[8] = Z/8

        let mut X = self.0.X;
        let mut Y = self.0.Y;
        let mut T = self.0.T;

        // If y nonzero and xy nonnegative, continue.
        // Otherwise, add Q_6 = (i,0) = constants::EIGHT_TORSION[6]
        // (x,y) + Q_6 = (iy,ix)
        // (X:Y:Z:T) + Q_6 = (iY:iX:Z:-T)

        // XXX it should be possible to avoid this inversion, but
        // let's make sure the code is correct first
        let xy = &T * &self.0.Z.invert();
        let is_neg_mask = 1u8 & !(Y.is_nonzero() & xy.is_nonnegative_decaf());
        let iX = &X * &constants::SQRT_M1;
        let iY = &Y * &constants::SQRT_M1;
        X.conditional_assign(&iY, is_neg_mask);
        Y.conditional_assign(&iX, is_neg_mask);
        T.conditional_negate(is_neg_mask);

        // Step 1: Compute r = 1/sqrt((a-d)(Z+Y)(Z-Y))
        let Z_plus_Y  = &self.0.Z + &Y;
        let Z_minus_Y = &self.0.Z - &Y;
        let t = &constants::a_minus_d * &(&Z_plus_Y * &Z_minus_Y);
        let (t_is_nonzero_square, mut r) = t.invsqrt();
        // t should always be square (why?)
        debug_assert_eq!( t_is_nonzero_square | t.is_zero(), 1u8 );

        // Step 2: Compute u = (a-d)r
        let u = &constants::a_minus_d * &r;

        // Step 3: Negate r if -2uZ is negative.
        let uZ = &u * &self.0.Z;
        let m2uZ = -&(&uZ + &uZ);
        r.conditional_negate(m2uZ.is_negative_decaf());

        // Step 4: Compute s = | u(r(aZX - dYT)+Y)/a|
        //                   = |u(r(-ZX - dYT)+Y)| since a = -1
        let minus_ZX = -&(&self.0.Z * &X);
        let dYT = &constants::d * &(&Y * &T);
        // Compute s = u(r(aZX - dYT)+Y) and cnegate for abs
        let mut s = &u * &(&(&r * &(&minus_ZX - &dYT)) + &Y);
        let neg = s.is_negative_decaf();
        s.conditional_negate(neg);
        CompressedDecaf(s.to_bytes())
    }

    /// Return the coset self + E[4], for debugging.
    fn coset4(&self) -> [ExtendedPoint; 4] {
        [  self.0
        , &self.0 + &constants::EIGHT_TORSION[2]
        , &self.0 + &constants::EIGHT_TORSION[4]
        , &self.0 + &constants::EIGHT_TORSION[6]
        ]
    }
}

impl Identity for DecafPoint {
    fn identity() -> DecafPoint {
        DecafPoint(ExtendedPoint::identity())
    }
}

// ------------------------------------------------------------------------
// Equality
// ------------------------------------------------------------------------

/// XXX check whether there's a simple way to do equality checking
/// with cofactor 8, not just cofactor 4, and add a CT equality function?
impl PartialEq for DecafPoint {
    fn eq(&self, other: &DecafPoint) -> bool {
        let  self_compressed =  self.compress();
        let other_compressed = other.compress();
        self_compressed == other_compressed
    }
}

impl Eq for DecafPoint {}

// ------------------------------------------------------------------------
// Arithmetic
// ------------------------------------------------------------------------

impl<'a, 'b> Add<&'b DecafPoint> for &'a DecafPoint {
    type Output = DecafPoint;

    fn add(self, other: &'b DecafPoint) -> DecafPoint {
        DecafPoint(&self.0 + &other.0)
    }
}

impl<'a, 'b> Sub<&'b DecafPoint> for &'a DecafPoint {
    type Output = DecafPoint;

    fn sub(self, other: &'b DecafPoint) -> DecafPoint {
        DecafPoint(&self.0 - &other.0)
    }
}

impl<'a> Neg for &'a DecafPoint {
    type Output = DecafPoint;

    fn neg(self) -> DecafPoint {
        DecafPoint(-&self.0)
    }
}

impl<'b> MulAssign<&'b Scalar> for DecafPoint {
    fn mul_assign(&mut self, scalar: &'b Scalar) {
        let result = (self as &DecafPoint) * scalar;
        *self = result;
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a DecafPoint {
    type Output = DecafPoint;
    /// Scalar multiplication: compute `scalar * self`.
    fn mul(self, scalar: &'b Scalar) -> DecafPoint {
        DecafPoint(&self.0 * scalar)
    }
}

/// Precomputation
#[derive(Clone)]
pub struct DecafBasepointTable(pub EdwardsBasepointTable);

impl<'a, 'b> Mul<&'b Scalar> for &'a DecafBasepointTable {
    type Output = DecafPoint;

    fn mul(self, scalar: &'b Scalar) -> DecafPoint {
        DecafPoint(&self.0 * scalar)
    }
}

impl<'a, 'b> Mul<&'a DecafBasepointTable> for &'b Scalar {
    type Output = DecafPoint;

    fn mul(self, basepoint_table: &'a DecafBasepointTable) -> DecafPoint {
        DecafPoint(self * &basepoint_table.0)
    }
}

impl DecafBasepointTable {
    /// Create a precomputed table of multiples of the given `basepoint`.
    pub fn create(basepoint: &DecafPoint) -> DecafBasepointTable {
        DecafBasepointTable(EdwardsBasepointTable::create(&basepoint.0))
    }

    /// Get the basepoint for this table as a `DecafPoint`.
    pub fn basepoint(&self) -> DecafPoint {
        DecafPoint(self.0.basepoint())
    }
}

// ------------------------------------------------------------------------
// Constant-time conditional assignment
// ------------------------------------------------------------------------

impl CTAssignable for DecafPoint {
    /// Conditionally assign `other` to `self`, if `choice == 1u8`.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::curve::Identity;
    /// # use curve25519_dalek::decaf::DecafPoint;
    /// # use curve25519_dalek::subtle::CTAssignable;
    /// # use curve25519_dalek::constants;
    /// let A = DecafPoint::identity();
    /// let B = constants::DECAF_ED25519_BASEPOINT;
    ///
    /// let mut P = A;
    ///
    /// P.conditional_assign(&B, 0u8);
    /// assert!(P == A);
    /// P.conditional_assign(&B, 1u8);
    /// assert!(P == B);
    /// ```
    fn conditional_assign(&mut self, other: &DecafPoint, choice: u8) {
        self.0.X.conditional_assign(&other.0.X, choice);
        self.0.Y.conditional_assign(&other.0.Y, choice);
        self.0.Z.conditional_assign(&other.0.Z, choice);
        self.0.T.conditional_assign(&other.0.T, choice);
    }
}

// ------------------------------------------------------------------------
// Debug traits
// ------------------------------------------------------------------------

impl Debug for CompressedDecaf {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "CompressedDecaf: {:?}", self.as_bytes())
    }
}

impl Debug for DecafPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        let coset = self.coset4();
        write!(f, "DecafPoint: coset \n{:?}\n{:?}\n{:?}\n{:?}",
               coset[0], coset[1], coset[2], coset[3])
    }
}

// ------------------------------------------------------------------------
// Variable-time functions
// ------------------------------------------------------------------------

pub mod vartime {
    //! Variable-time operations on decaf points, useful for non-secret data.
    use super::*;

    /// Given a vector of public scalars and a vector of (possibly secret)
    /// points, compute
    ///
    ///    c_1 P_1 + ... + c_n P_n.
    ///
    /// # Input
    ///
    /// A vector of `Scalar`s and a vector of `ExtendedPoints`.  It is an
    /// error to call this function with two vectors of different lengths.
    pub fn k_fold_scalar_mult<'a,'b,I,J>(scalars: I, points: J) -> DecafPoint
        where I: IntoIterator<Item=&'a Scalar>, J: IntoIterator<Item=&'b DecafPoint>
    {
        let extended_points = points.into_iter().map(|P| &P.0);
        DecafPoint(curve::vartime::k_fold_scalar_mult(scalars, extended_points))
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use rand::OsRng;

    use scalar::Scalar;
    use constants;
    use curve::CompressedEdwardsY;
    use curve::ExtendedPoint;
    use curve::Identity;
    use super::*;

    #[test]
    fn decaf_decompress_negative_s_fails() {
        // constants::d is neg, so decompression should fail as |d| != d.
        let bad_compressed = CompressedDecaf(constants::d.to_bytes());
        assert!(bad_compressed.decompress().is_none());
    }

    #[test]
    fn decaf_decompress_id() {
        let compressed_id = CompressedDecaf::identity();
        let id = compressed_id.decompress().unwrap();
        assert_eq!(id.0.compress_edwards(), CompressedEdwardsY::identity());
    }

    #[test]
    fn decaf_compress_id() {
        let id = DecafPoint::identity();
        assert_eq!(id.compress(), CompressedDecaf::identity());
    }

    #[test]
    fn decaf_basepoint_roundtrip() {
        let bp_compressed_decaf = constants::DECAF_ED25519_BASEPOINT.compress();
        let bp_recaf = bp_compressed_decaf.decompress().unwrap().0;
        // Check that bp_recaf differs from bp by a point of order 4
        let diff = &constants::ED25519_BASEPOINT - &bp_recaf;
        let diff4 = diff.mult_by_pow_2(4); // XXX this is wrong
        assert_eq!(diff4.compress_edwards(), CompressedEdwardsY::identity());
    }

    #[test]
    fn decaf_four_torsion_basepoint() {
        let bp = constants::DECAF_ED25519_BASEPOINT;
        let bp_coset = bp.coset4();
        for i in 0..4 {
            assert_eq!(bp, DecafPoint(bp_coset[i]));
        }
    }

    #[test]
    fn decaf_four_torsion_random() {
        let mut rng = OsRng::new().unwrap();
        let B = &constants::DECAF_ED25519_BASEPOINT_TABLE;
        let P = B * &Scalar::random(&mut rng);
        let P_coset = P.coset4();
        for i in 0..4 {
            assert_eq!(P, DecafPoint(P_coset[i]));
        }
    }

    #[test]
    fn decaf_random_roundtrip() {
        let mut rng = OsRng::new().unwrap();
        let B = &constants::DECAF_ED25519_BASEPOINT_TABLE;
        for _ in 0..100 {
            let P = B * &Scalar::random(&mut rng);
            let compressed_P = P.compress();
            let Q = compressed_P.decompress().unwrap();
            assert_eq!(P, Q);
        }
    }
}

#[cfg(all(test, feature = "bench"))]
mod bench {
    use rand::OsRng;
    use test::Bencher;

    use super::*;

    #[bench]
    fn decompression(b: &mut Bencher) {
        let mut rng = OsRng::new().unwrap();
        let B = &constants::DECAF_ED25519_BASEPOINT_TABLE;
        let P = B * &Scalar::random(&mut rng);
        let P_compressed = P.compress();
        b.iter(|| P_compressed.decompress().unwrap());
    }

    #[bench]
    fn compression(b: &mut Bencher) {
        let mut rng = OsRng::new().unwrap();
        let B = &constants::DECAF_ED25519_BASEPOINT_TABLE;
        let P = B * &Scalar::random(&mut rng);
        b.iter(|| P.compress());
    }
}

