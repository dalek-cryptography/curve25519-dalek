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

#[cfg(feature = "std")]
use rand::Rng;

use digest::Digest;
use generic_array::typenum::U32;

use constants;
use field::FieldElement;
use subtle::CTAssignable;
use subtle::CTNegatable;

use core::ops::{Add, Sub, Neg};
use core::ops::{AddAssign, SubAssign};
use core::ops::{Mul, MulAssign};

use curve;
use curve::ValidityCheck;
use curve::ExtendedPoint;
use curve::CompletedPoint;
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
    pub fn as_bytes<'a>(&'a self) -> &'a [u8; 32] {
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
        let ZZ = Z.square();
        let u = &ZZ- &(&constants::d4 * &ss); // u = Z^2 - 4ds^2
        let uss = &u * &ss;
        let ussZZ = &uss * &ZZ;

        if Z.is_zero() == 1u8 { return None; }

        // Batch inversion: set b = 1/sqrt(us^2 Z^2)
        let (ussZZ_is_nonzero_square, b) = ussZZ.invsqrt();
        if (ussZZ_is_nonzero_square | uss.is_zero()) == 0u8 {
            return None; // us^2 is nonzero nonsquare
        }

        let mut v = &b * &Z; // now v = 1/sqrt(us^2)
        let Zinv = &b * &(&v * &uss); // now Zinv = b^2 Z us^2 = 1/Z

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

        // Use the value of 1/Z previously computed in the batch inversion
        let xy = &T * &Zinv;
        if (Y.is_nonzero() & xy.is_nonnegative_decaf()) == 1u8 {
            Some(DecafPoint(ExtendedPoint{ X: X, Y: Y, Z: Z, T: T }))
        } else {
            None
        }
    }
}

impl Identity for CompressedDecaf {
    fn identity() -> CompressedDecaf {
        CompressedDecaf([0u8; 32])
    }
}

// ------------------------------------------------------------------------
// Serde support
// ------------------------------------------------------------------------
// Serializes to and from `DecafPoint` directly, doing compression
// and decompression internally.  This means that users can create
// structs containing `DecafPoint`s and use Serde's derived
// serializers to serialize those structures.

#[cfg(feature = "serde")]
use serde::{self, Serialize, Deserialize, Serializer, Deserializer};
#[cfg(feature = "serde")]
use serde::de::Visitor;

#[cfg(feature = "serde")]
impl Serialize for DecafPoint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_bytes(self.compress().as_bytes())
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for DecafPoint {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        struct DecafPointVisitor;

        impl<'de> Visitor<'de> for DecafPointVisitor {
            type Value = DecafPoint;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid point in Decaf format")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<DecafPoint, E>
                where E: serde::de::Error
            {
                if v.len() == 32 {
                    let arr32 = array_ref!(v, 0, 32); // &[u8;32] from &[u8]
                    CompressedDecaf(*arr32)
                        .decompress()
                        .ok_or(serde::de::Error::custom("decompression failed"))
                } else {
                    Err(serde::de::Error::invalid_length(v.len(), &self))
                }
            }
        }

        deserializer.deserialize_bytes(DecafPointVisitor)
    }
}

// ------------------------------------------------------------------------
// Internal point representations
// ------------------------------------------------------------------------

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
        //
        // Step 0: pre-rotation, needed for Decaf with E[8] = Z/8.
        //
        // We want to select a point (x,y) in the coset P + E[4] with
        // y nonzero and xy nonnegative.  The naive approach is as
        // follows.  First, compute xy = T/Z and check that Y is
        // nonzero and xy is nonnegative.  If not, then "rotate" the
        // original point by adding (x,y) + (i,0) = (iy,ix) = (x',y'):
        // this rotated point has x'y' = -xy.  Then perform the normal
        // Decaf encoding, as described in Appendix A.1 of the Decaf
        // paper, using the rotated point (x',y').
        //
        // This is straightforward but requires an extra inversion.
        // We would like to batch the inversion in xy = T/Z with the
        // inverse square root in the computation of
        //
        //   r = invsqrt((a-d)*(Z+Y)*(Z-Y))
        //     = invsqrt(a-d)*invsqrt(Z^2-Y^2),
        //
        // but the X and Y we are trying to decode depend on whether
        // we rotated the coset representative!
        //
        // However, it is possible to batch these inversions.  Credit:
        // the following explanation (and trick) is adapted from an
        // email from Mike Hamburg, but of course any errors are ours.
        //
        // Let the initial point be  ( X_0 :  Y_0 : Z_0 :  T_0).
        // The rotated point is then (iY_0 : iX_0 : Z_0 : -T_0).
        //
        // We want to relate the computation of:
        //
        //   invsqrt(Z^2 - Y^2) = invsqrt(Z_0^2 - Y_0^2)  [non-rotated]
        //   invsqrt(Z^2 - Y^2) = invsqrt(Z_0^2 + X_0^2)  [rotated]
        //
        // The curve equation in extended coordinates is
        //
        //   0 = (-X^2 + Y^2)*Z^2 - Z^4 - d*X^2*Y^2,
        //
        // so
        //                0 = (-X^2 + Y^2)*Z^2 - Z^4 - d*T^2*Z^2         since XY=TZ
        //                  = (-X^2 + Y^2 - Z^2 - d*T^2)*Z^2
        //                  = ( X^2 - Y^2 + Z^2 + d*T^2)*Z^2             mult by -1
        //         -T^2*Z^2 = (X^2 - Y^2 + Z^2 + d*T^2)*Z^2 - T^2*Z^2    sub T^2*Z^2
        //         -T^2*Z^2 = (X^2 - Y^2 + Z^2 - T^2)*Z^2 + d*T^2*Z^2
        //   (-1-d)*T^2*Z^2 = (X^2 - Y^2 + Z^2 - T^2)*Z^2
        //
        // for any point (X:Y:Z:T) in extended coordinates.  Therefore,
        //
        //   (Z^2 - Y^2)*(Z^2 + X^2) = Z^4 + Z^2*X^2 - Y^2*Z^2 - Y^2*X^2
        //                           = Z^4 + Z^2*X^2 - Y^2*Z^2 - T^2*Z^2    since XY=TZ
        //                           = Z^2*(X^2 - Y^2 + Z^2 - T^2)
        //                           = (-1-d)*T^2*Z^2.
        //
        // Taking square roots of both sides and rearranging, we get
        //
        //   invsqrt(Z^2 - Y^2) = invsqrt(-1-d)*(Z^2+X^2)*(1/TZ)*invsqrt(Z^2+X^2)
        //                        `-----------'           `---------------------'
        //                        curve constant           batchable
        //
        // for any point (X:Y:Z:T) in extended coordinates.
        //
        // Therefore, we can do the computation with only one inverse
        // square root like so:
        //
        // W <--- invsqrt((T_0 * Z_0)^2 * (Z_0^2+X_0^2))
        //     =  1/(T_0 * Z_0 * sqrt(Z_0^2 + X_0^2))
        //
        // xy <--- T_0^2 * W^2 * (T_0 * Z_0) * (Z_0^2 + X_0^2)
        //      =  T_0 / Z_0 = xy
        //
        // if Y_0 nonzero and xy nonnegative:
        //   (X : Y : Z : T) <--- (X_0 : Y_0 : Z_0 : T_0)
        //   r <--- (1/(-1-d)) * (Z_0^2 + X_0^2) * W
        //       =  invsqrt(a-d) * invsqrt(Z_0^2 - Y_0^2)    since a = -1
        //       =  invsqrt(a-d) * invsqrt(Z^2 - Y^2)
        // otherwise:
        //   (X : Y : Z : T) <--- (i*Y_0 : i*X_0 : Z_0 : -T_0)
        //   r <--- invsqrt(a-d) * (T_0 * Z_0) * W
        //       =  invsqrt(a-d) * invsqrt(Z_0^2 + X_0^2)
        //       =  invsqrt(a-d) * invsqrt(Z^2 - Y^2)
        //
        // The rest of the compression follows the steps in the
        // appendix of the Decaf paper.

        let mut X = self.0.X;
        let mut Y = self.0.Y;
        let mut T = self.0.T;
        let Z = &self.0.Z;

        let TZ = &T * Z;
        let ZZ_plus_XX = &Z.square() + &X.square();
        let tmp = &TZ.square() * &ZZ_plus_XX;
        let (tmp_is_nonzero_square, W) = tmp.invsqrt();
        // tmp should always be a square (why? related to being in the
        // image of the isogeny?)
        debug_assert_eq!(tmp_is_nonzero_square | tmp.is_zero(), 1u8);

        let xy = &T.square() * &(&W.square() * &(&TZ * &ZZ_plus_XX));
        let rotate = 1u8 & !(Y.is_nonzero() & xy.is_nonnegative_decaf());

        let mut r = &W * &(&ZZ_plus_XX * &constants::inv_a_minus_d);
        let r_rot = &W * &(&TZ * &constants::invsqrt_a_minus_d);

        let iX = &X * &constants::SQRT_M1;
        let iY = &Y * &constants::SQRT_M1;

        r.conditional_assign(&r_rot, rotate);
        X.conditional_assign(&iY,    rotate);
        Y.conditional_assign(&iX,    rotate);
        T.conditional_negate(rotate);

        // Step 2: Compute u = (a-d)r
        let u = &constants::a_minus_d * &r;

        // Step 3: Negate r if -2uZ is negative.
        let uZ = &u * Z;
        let m2uZ = -&(&uZ + &uZ);
        r.conditional_negate(m2uZ.is_negative_decaf());

        // Step 4: Compute s = | u(r(aZX - dYT)+Y)/a|
        //                   = |u(r(-ZX - dYT)+Y)| since a = -1
        let minus_ZX = -&(Z * &X);
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

    /// Computes the Elligator map as described in the Decaf paper.
    ///
    /// # Note
    ///
    /// This method is not public because it's just used for hashing
    /// to a point -- proper elligator support is deferred for now.
    pub fn elligator_decaf_flavour(r_0: &FieldElement) -> DecafPoint {
        // Follows Appendix C of the Decaf paper.
        // Use n = 2 as the quadratic nonresidue so that n*x = x + x.
        let minus_one = -&FieldElement::one();

        // 1. Compute r <--- nr_0^2.
        let r_0_squared = r_0.square();
        let r = &r_0_squared + &r_0_squared;

        // 2. Compute D <--- (dr + (a-d)) * (dr - (d + ar))
        let dr = &constants::d * &r;
        // D = (dr + (a-d)) * (dr - (d + ar))
        //   = (dr + (a-d)) * (dr - (d-r)) since a=-1
        // writing as
        //   = (dr + (a-d)) * dr - (dr + (a-d)) * (d - r)
        // avoids two consecutive additions (could cause overflow)
        let dr_plus_amd = &dr + &constants::a_minus_d;
        let D = &(&dr_plus_amd * &dr) - &(&dr_plus_amd * &(&constants::d - &r));

        // 3. Compute N <--- (r+1) * (a-2d)
        let N = &(&r + &FieldElement::one()) * &(&minus_one - &constants::d2);

        // 4. Compute
        //           / +1,     1 / sqrt(ND)   if ND is square
        // c, e <--- | +1, 0                  if N or D = 0
        //           \ -1,  nr_0 / sqrt(nND)  otherwise
        let ND = &N * &D;
        let nND = &ND + &ND;
        let mut c = FieldElement::one();
        let mut e = FieldElement::zero();
        let (ND_is_nonzero_square, ND_invsqrt) = ND.invsqrt();
        e.conditional_assign(&ND_invsqrt, ND_is_nonzero_square);
        let (nND_is_nonzero_square, nND_invsqrt) = nND.invsqrt();
        let nr_0_nND_invsqrt = &nND_invsqrt * &(r_0 + r_0);
        c.conditional_assign(&minus_one, nND_is_nonzero_square);
        e.conditional_assign(&nr_0_nND_invsqrt, nND_is_nonzero_square);

        // 5. Compute s <--- c*|N*e|
        let mut s = &N * &e;
        let neg = s.is_negative_decaf();
        s.conditional_negate(neg);
        s *= &c;

        // 6. Compute t <--- -c*N*(r-1)* ((a-2d)*e)^2  -1
        let a_minus_2d_e_sq = (&(&minus_one - &constants::d2) * &e).square();
        let c_N_r_minus_1 = &c * &(&N * &(&r + &minus_one));
        let t = &minus_one - &(&c_N_r_minus_1 * &a_minus_2d_e_sq);

        // 7. Apply the isogeny:
        // (x,y) = ((2s)/(1+as^2), (1-as^2)/(t))
        let as_sq = &minus_one * &s.square();
        let P = CompletedPoint{
            X: &s + &s,
            Z: &FieldElement::one() + &as_sq,
            Y: &FieldElement::one() - &as_sq,
            T: t,
        };

        // Convert to extended and return.
        DecafPoint(P.to_extended())
    }

    /// Return a `DecafPoint` chosen uniformly at random using a user-provided RNG.
    ///
    /// # Inputs
    ///
    /// * `rng`: any RNG which implements the `rand::Rng` interface.
    ///
    /// # Returns
    ///
    /// A random element of the Decaf group.
    ///
    /// # Implementation
    ///
    /// Uses the Decaf-flavoured Elligator 2 map, so that the discrete log of the
    /// output point with respect to any other point should be unknown.
    #[cfg(feature = "std")]
    pub fn random<T: Rng>(rng: &mut T) -> Self {
        let mut field_bytes = [0u8; 32];
        rng.fill_bytes(&mut field_bytes);
        let r_0 = FieldElement::from_bytes(&field_bytes);
        DecafPoint::elligator_decaf_flavour(&r_0)
    }

    /// Hash a slice of bytes into a `DecafPoint`.
    ///
    /// Takes a type parameter `D`, which is any `Digest` producing 32
    /// bytes (256 bits) of output.
    ///
    /// Convenience wrapper around `from_hash`.
    ///
    /// # Implementation
    ///
    /// Uses the Decaf-flavoured Elligator 2 map, so that the discrete log of the
    /// output point with respect to any other point should be unknown.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate curve25519_dalek;
    /// # use curve25519_dalek::decaf::DecafPoint;
    /// extern crate sha2;
    /// use sha2::Sha256;
    ///
    /// # // Need fn main() here in comment so the doctest compiles
    /// # // See https://doc.rust-lang.org/book/documentation.html#documentation-as-tests
    /// # fn main() {
    /// let msg = "To really appreciate architecture, you may even need to commit a murder";
    /// let P = DecafPoint::hash_from_bytes::<Sha256>(msg.as_bytes());
    /// # }
    /// ```
    ///
    pub fn hash_from_bytes<D>(input: &[u8]) -> DecafPoint
        where D: Digest<OutputSize = U32> + Default
    {
        let mut hash = D::default();
        hash.input(input);
        DecafPoint::from_hash(hash)
    }

    /// Construct a `DecafPoint` from an existing `Digest` instance.
    ///
    /// Use this instead of `hash_from_bytes` if it is more convenient
    /// to stream data into the `Digest` than to pass a single byte
    /// slice.
    pub fn from_hash<D>(hash: D) -> DecafPoint
        where D: Digest<OutputSize = U32> + Default
    {
        // XXX this seems clumsy
        let mut output = [0u8; 32];
        output.copy_from_slice(hash.result().as_slice());
        let r_0 = FieldElement::from_bytes(&output);
        DecafPoint::elligator_decaf_flavour(&r_0)
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

impl<'b> AddAssign<&'b DecafPoint> for DecafPoint {
    fn add_assign(&mut self, _rhs: &DecafPoint) {
        *self = (self as &DecafPoint) + _rhs;
    }
}

impl<'a, 'b> Sub<&'b DecafPoint> for &'a DecafPoint {
    type Output = DecafPoint;

    fn sub(self, other: &'b DecafPoint) -> DecafPoint {
        DecafPoint(&self.0 - &other.0)
    }
}

impl<'b> SubAssign<&'b DecafPoint> for DecafPoint {
    fn sub_assign(&mut self, _rhs: &DecafPoint) {
        *self = (self as &DecafPoint) - _rhs;
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

impl<'a, 'b> Mul<&'b DecafPoint> for &'a Scalar {
    type Output = DecafPoint;

    /// Scalar multiplication: compute `self * scalar`.
    fn mul(self, point: &'b DecafPoint) -> DecafPoint {
        DecafPoint(self * &point.0)
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
    /// # extern crate subtle;
    /// # extern crate curve25519_dalek;
    /// #
    /// # use subtle::CTAssignable;
    /// #
    /// # use curve25519_dalek::curve::Identity;
    /// # use curve25519_dalek::decaf::DecafPoint;
    /// # use curve25519_dalek::constants;
    /// # fn main() {
    /// let A = DecafPoint::identity();
    /// let B = constants::DECAF_ED25519_BASEPOINT;
    ///
    /// let mut P = A;
    ///
    /// P.conditional_assign(&B, 0u8);
    /// assert!(P == A);
    /// P.conditional_assign(&B, 1u8);
    /// assert!(P == B);
    /// # }
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
    pub fn k_fold_scalar_mult<'a, 'b, I, J>(scalars: I, points: J) -> DecafPoint
        where I: IntoIterator<Item = &'a Scalar>,
              J: IntoIterator<Item = &'b DecafPoint>
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
    use curve::Identity;
    use super::*;

    #[cfg(feature = "serde")]
    use serde_cbor;

    #[test]
    #[cfg(feature = "serde")]
    fn serde_cbor_basepoint_roundtrip() {
        let output = serde_cbor::to_vec(&constants::DECAF_ED25519_BASEPOINT).unwrap();
        let parsed: DecafPoint = serde_cbor::from_slice(&output).unwrap();
        assert_eq!(parsed, constants::DECAF_ED25519_BASEPOINT);
    }


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
    fn encodings_of_small_multiples_of_basepoint() {
        // Table of encodings of (1+i)*basepoint
        // Generated using the previous naive implementation.
        let compressed = [
            CompressedDecaf([141, 190, 226, 107, 177, 201, 35, 118, 14, 55, 160, 165, 242, 207, 121, 161, 177, 80, 8, 132, 205, 254, 101, 169, 233, 65, 124, 96, 255, 182, 249, 40]),
            CompressedDecaf([131, 57, 148, 16, 8, 196, 141, 82, 144, 220, 105, 112, 66, 33, 48, 16, 182, 198, 173, 35, 248, 181, 92, 231, 222, 35, 85, 56, 5, 252, 91, 40]),
            CompressedDecaf([199, 132, 32, 144, 156, 143, 81, 170, 240, 56, 232, 6, 178, 37, 118, 190, 110, 201, 26, 173, 156, 97, 59, 162, 240, 247, 226, 107, 197, 111, 107, 26]),
            CompressedDecaf([210, 120, 34, 214, 175, 27, 61, 6, 229, 181, 216, 36, 11, 245, 146, 232, 130, 215, 77, 29, 210, 30, 54, 155, 191, 81, 59, 124, 174, 3, 135, 36]),
            CompressedDecaf([155, 52, 159, 52, 189, 27, 181, 0, 245, 131, 0, 197, 79, 208, 252, 122, 104, 161, 245, 143, 67, 94, 13, 129, 153, 173, 129, 179, 118, 231, 90, 52]),
            CompressedDecaf([42, 117, 252, 118, 8, 1, 72, 25, 111, 246, 247, 103, 236, 86, 235, 29, 100, 156, 186, 209, 159, 21, 61, 26, 249, 25, 137, 228, 84, 23, 10, 27]),
            CompressedDecaf([21, 126, 181, 117, 58, 90, 216, 28, 184, 57, 9, 23, 158, 68, 159, 171, 109, 150, 232, 140, 144, 73, 139, 122, 124, 105, 125, 160, 94, 185, 150, 52]),
            CompressedDecaf([232, 167, 112, 233, 126, 33, 105, 63, 151, 6, 88, 225, 181, 17, 223, 12, 116, 138, 203, 47, 243, 225, 50, 171, 21, 220, 186, 179, 132, 20, 48, 6]),
            CompressedDecaf([99, 44, 97, 48, 242, 174, 78, 198, 112, 154, 146, 36, 239, 34, 94, 4, 0, 244, 175, 34, 46, 0, 83, 187, 5, 163, 225, 63, 51, 237, 234, 22]),
            CompressedDecaf([2, 33, 89, 176, 178, 123, 159, 75, 235, 172, 251, 11, 137, 177, 90, 122, 149, 186, 52, 243, 153, 190, 185, 202, 59, 137, 204, 160, 150, 152, 148, 55]),
            CompressedDecaf([245, 79, 78, 226, 114, 69, 247, 112, 18, 54, 90, 225, 176, 77, 231, 235, 196, 123, 49, 221, 34, 205, 151, 228, 244, 112, 82, 58, 30, 31, 58, 12]),
            CompressedDecaf([135, 53, 175, 167, 13, 94, 62, 31, 29, 248, 13, 132, 29, 69, 7, 188, 145, 49, 62, 55, 181, 109, 214, 11, 248, 162, 70, 15, 236, 126, 100, 60]),
            CompressedDecaf([98, 150, 69, 229, 144, 122, 237, 107, 127, 177, 33, 64, 59, 173, 210, 102, 74, 34, 23, 16, 252, 117, 14, 97, 231, 178, 63, 193, 157, 28, 178, 17]),
            CompressedDecaf([222, 104, 6, 1, 72, 12, 72, 178, 204, 238, 128, 70, 41, 150, 235, 96, 153, 150, 18, 4, 141, 206, 0, 38, 122, 112, 249, 51, 94, 251, 20, 57]),
            CompressedDecaf([7, 221, 140, 57, 13, 146, 248, 27, 56, 4, 128, 23, 145, 120, 126, 4, 158, 173, 52, 213, 164, 250, 26, 55, 89, 96, 187, 111, 211, 18, 63, 19]),
            CompressedDecaf([91, 213, 193, 10, 102, 92, 199, 124, 61, 176, 1, 47, 111, 59, 183, 91, 79, 56, 208, 109, 172, 209, 17, 167, 229, 216, 3, 236, 200, 208, 15, 20]),
        ];
        let mut bp = constants::DECAF_ED25519_BASEPOINT;
        for i in 0..16 {
            assert_eq!(bp.compress(), compressed[i]);
            bp = &bp + &constants::DECAF_ED25519_BASEPOINT;
        }
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

    #[test]
    fn decaf_random_is_valid() {
        let mut rng = OsRng::new().unwrap();
        for _ in 0..100 {
            let P = DecafPoint::random(&mut rng);
            // Check that P is on the curve
            assert!(P.0.is_valid());
            // Check that P is in the image of the decaf map
            P.compress();
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
