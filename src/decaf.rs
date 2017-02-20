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

// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]

use core::fmt::Debug;

use constants;
use field::FieldElement;
use subtle::CTAssignable;

use core::ops::{Add, Sub, Neg};

use curve::ExtendedPoint;
use curve::BasepointMult;
use curve::ScalarMult;
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
    pub fn to_bytes(&self) -> [u8;32] {
        self.0
    }

    /// Attempt to decompress to an `DecafPoint`.
    pub fn decompress(&self) -> Option<DecafPoint> {
        // XXX should decoding be CT ?
        // XXX should reject unless s = |s|
        // XXX need to check that xy is nonnegative and reject otherwise
        let s = FieldElement::from_bytes(&self.0);
        let ss = s.square();
        let X = &s + &s;                    // X = 2s
        let Z = &FieldElement::one() - &ss; // Z = 1+as^2
        let u = &(&Z * &Z) - &(&constants::d4 * &ss); // u = Z^2 - 4ds^2
        let uss = &u * &ss;
        let mut v = match uss.invsqrt() {
            Some(v) => v,
            None => return None,
        };
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

        Some(DecafPoint(ExtendedPoint{ X: X, Y: Y, Z: Z, T: T }))
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
        let minus_T = -&T;
        T.conditional_assign(&minus_T, is_neg_mask);

        // Step 1: Compute r = 1/sqrt((a-d)(Z+Y)(Z-Y))
        let Z_plus_Y  = &self.0.Z + &Y;
        let Z_minus_Y = &self.0.Z - &Y;
        let t = &constants::a_minus_d * &(&Z_plus_Y * &Z_minus_Y);
        // t should always be square (why?)
        // XXX is it safe to use option types here?
        let mut r = t.invsqrt().unwrap();

        // Step 2: Compute u = (a-d)r
        let u = &constants::a_minus_d * &r;

        // Step 3: Negate r if -2uZ is negative.
        let uZ = &u * &self.0.Z;
        let minus_r = -&r;
        let m2uZ = -&(&uZ + &uZ);
        let mask = m2uZ.is_negative_decaf();
        r.conditional_assign(&minus_r, mask);

        // Step 4: Compute s = |u(r(aZX - dYT)+Y)/a|
        let minus_ZX = -&(&self.0.Z * &X);
        let dYT = &constants::d * &(&Y * &T);
        let mut s = &u * &(&(&r * &(&minus_ZX - &dYT)) + &Y);
        s.negate();
        CompressedDecaf(s.abs_decaf().to_bytes())
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

impl ScalarMult<Scalar> for DecafPoint {
    fn scalar_mult(&self, scalar: &Scalar) -> DecafPoint {
        DecafPoint(self.0.scalar_mult(scalar))
    }
}

impl BasepointMult<Scalar> for DecafPoint {
    fn basepoint() -> DecafPoint {
        DecafPoint(constants::BASEPOINT)
    }

    fn basepoint_mult(scalar: &Scalar) -> DecafPoint {
        DecafPoint(ExtendedPoint::basepoint_mult(scalar))
    }
}

// ------------------------------------------------------------------------
// Debug traits
// ------------------------------------------------------------------------

impl Debug for CompressedDecaf {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "CompressedDecaf: {:?}", &self.0[..])
    }
}

impl Debug for DecafPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "DecafPoint: {:?}", &self.0)
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
    use constants::BASE_CMPRSSD;
    use curve::CompressedEdwardsY;
    use curve::ExtendedPoint;
    use curve::BasepointMult;
    use curve::Identity;
    use super::*;

    #[test]
    fn test_decaf_decompress_id() {
        let compressed_id = CompressedDecaf([0u8; 32]);
        let id = compressed_id.decompress().unwrap();
        // This should compress (as ed25519) to the following:
        let mut bytes = [0u8; 32]; bytes[0] = 1;
        assert_eq!(id.0.compress(), CompressedEdwardsY(bytes));
    }

    #[test]
    fn test_decaf_compress_id() {
        let id = DecafPoint(ExtendedPoint::identity());
        assert_eq!(id.compress(), CompressedDecaf([0u8; 32]));
    }

    #[test]
    fn test_decaf_basepoint_roundtrip() {
        // XXX fix up this test
        let bp = BASE_CMPRSSD.decompress().unwrap();
        let bp_decaf = DecafPoint(bp).compress();
        let bp_recaf = bp_decaf.decompress().unwrap().0;
        let diff = &bp - &bp_recaf;
        let diff2 = diff.double();
        let diff4 = diff2.double();
        //println!("bp {:?}",       bp);
        //println!("bp_decaf {:?}", bp_decaf);
        //println!("bp_recaf {:?}", bp_recaf);
        //println!("diff {:?}", diff.compress());
        //println!("diff2 {:?}", diff2.compress());
        //println!("diff4 {:?}", diff4.compress());
        assert_eq!(diff4.compress(), ExtendedPoint::identity().compress());
    }

    #[test]
    fn test_decaf_four_torsion_basepoint() {
        //println!("");
        let bp = BASE_CMPRSSD.decompress().unwrap();
        let bp_decaf = DecafPoint(bp).compress();
        //println!("orig, {:?}", bp.compress());
        for i in (0..8).filter(|x| x % 2 == 0) {
            let Q = &bp + &constants::EIGHT_TORSION[i];
            //println!("{}, {:?}", i, Q.compress());
            assert_eq!(DecafPoint(Q).compress(), bp_decaf);
        }
    }

    #[test]
    fn test_decaf_four_torsion_random() {
        //println!("");
        let mut rng = OsRng::new().unwrap();
        let s = Scalar::random(&mut rng);
        let P = ExtendedPoint::basepoint_mult(&s);
        let P_decaf = DecafPoint(P).compress();
        //println!("orig, {:?}", P.compress());
        for i in (0..8).filter(|x| x % 2 == 0) {
            let Q = &P + &constants::EIGHT_TORSION[i];
            //println!("{}, {:?}", i, Q.compress());
            assert_eq!(DecafPoint(Q).compress(), P_decaf);
        }
    }
}
