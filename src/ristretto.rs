// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! An implementation of Mike Hamburg's Ristretto cofactor-eliminating
//! point-compression scheme, providing a prime-order group on top of
//! Curve25519.
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

use core::ops::{Add, Sub, Neg};
use core::ops::{AddAssign, SubAssign};
use core::ops::{Mul, MulAssign};

use edwards;
use edwards::ExtendedPoint;
use edwards::CompletedPoint;
use edwards::EdwardsBasepointTable;
use edwards::Identity;
use scalar::Scalar;

use subtle;
use subtle::ConditionallyAssignable;
use subtle::ConditionallyNegatable;
use subtle::Equal;

// ------------------------------------------------------------------------
// Compressed points
// ------------------------------------------------------------------------

/// A point serialized using Mike Hamburg's Ristretto scheme.
///
/// XXX think about how this API should work
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct CompressedRistretto(pub [u8; 32]);

/// The result of compressing a `RistrettoPoint`.
impl CompressedRistretto {
    /// View this `CompressedRistretto` as an array of bytes.
    pub fn as_bytes<'a>(&'a self) -> &'a [u8; 32] {
        &self.0
    }

    /// Attempt to decompress to an `RistrettoPoint`.
    ///
    /// This function executes in constant time for all valid inputs.
    /// Inputs which do not decode to a RistrettoPoint may return
    /// early.
    pub fn decompress(&self) -> Option<RistrettoPoint> {
        // Step 1. Check s for validity:
        // 1.a) s must be 32 bytes (we get this from the type system)
        // 1.b) s < p
        // 1.c) s is nonnegative
        //
        // Our decoding routine ignores the high bit, so the only
        // possible failure for 1.b) is if someone encodes s in 0..18
        // as s+p in 2^255-19..2^255-1.  We can check this by
        // converting back to bytes, and checking that we get the
        // original input, since our encoding routine is canonical.

        let s = FieldElement::from_bytes(self.as_bytes());
        let s_bytes_check = s.to_bytes();
        let s_encoding_is_canonical =
            subtle::slices_equal(&s_bytes_check[..], self.as_bytes());
        let s_is_negative = s.is_negative_ed25519();

        if s_encoding_is_canonical == 0u8 || s_is_negative == 1u8 {
            return None;
        }

        // Step 2.  The rest.  (XXX write comments)
        let ss = s.square();
        let yden = &FieldElement::one() + &ss;
        let ynum = &FieldElement::one() - &ss;
        let yden_sqr = yden.square();
        let xden_sqr = &(&(-&constants::d) * &ynum.square()) - &yden_sqr;

        let (ok, invsqrt) = (&xden_sqr * &yden_sqr).invsqrt();

        let xden_inv = &invsqrt * &yden;
        let yden_inv = &invsqrt * &(&xden_inv * &xden_sqr);

        let mut x = &(&s + &s) * &xden_inv;
        let x_is_negative = x.is_negative_ed25519();
        x.conditional_negate(x_is_negative);
        let y = &ynum * &yden_inv;

        let t = &x * &y;

        if ok == 0u8 || t.is_negative_ed25519() == 1u8 || x.is_zero() == 1u8 {
            return None;
        } else {
            return Some(RistrettoPoint(ExtendedPoint{
                X: x, Y: y, Z: FieldElement::one(), T: t
            }));
        }
    }
}

impl Identity for CompressedRistretto {
    fn identity() -> CompressedRistretto {
        // After tweaking Decaf to Ristretto, the identity compresses as -1 :(
        CompressedRistretto([0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f])
    }
}

// ------------------------------------------------------------------------
// Serde support
// ------------------------------------------------------------------------
// Serializes to and from `RistrettoPoint` directly, doing compression
// and decompression internally.  This means that users can create
// structs containing `RistrettoPoint`s and use Serde's derived
// serializers to serialize those structures.

#[cfg(feature = "serde")]
use serde::{self, Serialize, Deserialize, Serializer, Deserializer};
#[cfg(feature = "serde")]
use serde::de::Visitor;

#[cfg(feature = "serde")]
impl Serialize for RistrettoPoint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_bytes(self.compress().as_bytes())
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for RistrettoPoint {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        struct RistrettoPointVisitor;

        impl<'de> Visitor<'de> for RistrettoPointVisitor {
            type Value = RistrettoPoint;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid point in Ristretto format")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<RistrettoPoint, E>
                where E: serde::de::Error
            {
                if v.len() == 32 {
                    let arr32 = array_ref!(v, 0, 32); // &[u8;32] from &[u8]
                    CompressedRistretto(*arr32)
                        .decompress()
                        .ok_or(serde::de::Error::custom("decompression failed"))
                } else {
                    Err(serde::de::Error::invalid_length(v.len(), &self))
                }
            }
        }

        deserializer.deserialize_bytes(RistrettoPointVisitor)
    }
}

// ------------------------------------------------------------------------
// Internal point representations
// ------------------------------------------------------------------------

/// A point in a prime-order group.
///
/// XXX think about how this API should work
#[derive(Copy, Clone)]
pub struct RistrettoPoint(pub ExtendedPoint);

impl RistrettoPoint {
    /// Compress in Ristretto format.
    pub fn compress(&self) -> CompressedRistretto {
        let mut X = self.0.X;
        let mut Y = self.0.Y;
        let Z = &self.0.Z;
        let T = &self.0.T;

        println!("{:?}", self);
        println!("Z = {:?}", self.0.Z);
        println!("Y = {:?}", self.0.Y);

        let u1 = &(Z + &Y) * &(Z - &Y);
        let u2 = &X * &Y;
        // Ignore return value since this is always square
        let (_, invsqrt) = (&u1 * &u2.square()).invsqrt();
        let i1 = &invsqrt * &u1;
        let i2 = &invsqrt * &u2;
        let z_inv = &i1 * &(&i2 * T);
        let mut den_inv = i2;

        let iX = &X * &constants::SQRT_M1;
        let iY = &Y * &constants::SQRT_M1;
        let ristretto_magic = &constants::invsqrt_a_minus_d;
        let enchanted_denominator = &i1 * ristretto_magic;

        let rotate = (T * &z_inv).is_negative_ed25519();

        X.conditional_assign(&iY, rotate);
        Y.conditional_assign(&iX, rotate);
        den_inv.conditional_assign(&enchanted_denominator, rotate);

        Y.conditional_negate((&X * &z_inv).is_negative_ed25519());

        let mut s = &den_inv * &(Z - &Y);
        let s_is_zero = s.is_zero();
        s.conditional_assign(&FieldElement::one(), s_is_zero);
        let s_is_negative = s.is_negative_ed25519();
        s.conditional_negate(s_is_negative);

        CompressedRistretto(s.to_bytes())
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
    pub fn elligator_decaf_flavour(r_0: &FieldElement) -> RistrettoPoint {
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
        RistrettoPoint(P.to_extended())
    }

    /// Return a `RistrettoPoint` chosen uniformly at random using a user-provided RNG.
    ///
    /// # Inputs
    ///
    /// * `rng`: any RNG which implements the `rand::Rng` interface.
    ///
    /// # Returns
    ///
    /// A random element of the Ristretto group.
    ///
    /// # Implementation
    ///
    /// Uses the Ristretto-flavoured Elligator 2 map, so that the discrete log of the
    /// output point with respect to any other point should be unknown.
    #[cfg(feature = "std")]
    pub fn random<T: Rng>(rng: &mut T) -> Self {
        let mut field_bytes = [0u8; 32];
        rng.fill_bytes(&mut field_bytes);
        let r_0 = FieldElement::from_bytes(&field_bytes);
        RistrettoPoint::elligator_decaf_flavour(&r_0)
    }

    /// Hash a slice of bytes into a `RistrettoPoint`.
    ///
    /// Takes a type parameter `D`, which is any `Digest` producing 32
    /// bytes (256 bits) of output.
    ///
    /// Convenience wrapper around `from_hash`.
    ///
    /// # Implementation
    ///
    /// Uses the Ristretto-flavoured Elligator 2 map, so that the discrete log of the
    /// output point with respect to any other point should be unknown.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate curve25519_dalek;
    /// # use curve25519_dalek::ristretto::RistrettoPoint;
    /// extern crate sha2;
    /// use sha2::Sha256;
    ///
    /// # // Need fn main() here in comment so the doctest compiles
    /// # // See https://doc.rust-lang.org/book/documentation.html#documentation-as-tests
    /// # fn main() {
    /// let msg = "To really appreciate architecture, you may even need to commit a murder";
    /// let P = RistrettoPoint::hash_from_bytes::<Sha256>(msg.as_bytes());
    /// # }
    /// ```
    ///
    pub fn hash_from_bytes<D>(input: &[u8]) -> RistrettoPoint
        where D: Digest<OutputSize = U32> + Default
    {
        let mut hash = D::default();
        hash.input(input);
        RistrettoPoint::from_hash(hash)
    }

    /// Construct a `RistrettoPoint` from an existing `Digest` instance.
    ///
    /// Use this instead of `hash_from_bytes` if it is more convenient
    /// to stream data into the `Digest` than to pass a single byte
    /// slice.
    pub fn from_hash<D>(hash: D) -> RistrettoPoint
        where D: Digest<OutputSize = U32> + Default
    {
        // XXX this seems clumsy
        let mut output = [0u8; 32];
        output.copy_from_slice(hash.result().as_slice());
        let r_0 = FieldElement::from_bytes(&output);
        RistrettoPoint::elligator_decaf_flavour(&r_0)
    }
}

impl Identity for RistrettoPoint {
    fn identity() -> RistrettoPoint {
        RistrettoPoint(ExtendedPoint::identity())
    }
}

// ------------------------------------------------------------------------
// Equality
// ------------------------------------------------------------------------

impl PartialEq for RistrettoPoint {
    fn eq(&self, other: &RistrettoPoint) -> bool {
        self.ct_eq(other) == 1u8
    }
}

impl Equal for RistrettoPoint {
    /// Test equality between two `RistrettoPoint`s.
    ///
    /// # Returns
    ///
    /// `1u8` if the two `RistrettoPoint`s are equal, and `0u8` otherwise.
    fn ct_eq(&self, other: &RistrettoPoint) -> u8 {
        let X1Y2 = &self.0.X * &other.0.Y;
        let Y1X2 = &self.0.Y * &other.0.X;
        let X1X2 = &self.0.X * &other.0.X;
        let Y1Y2 = &self.0.Y * &other.0.Y;
        
        X1Y2.ct_eq(&Y1X2) | X1X2.ct_eq(&Y1Y2)
    }
}

impl Eq for RistrettoPoint {}

// ------------------------------------------------------------------------
// Arithmetic
// ------------------------------------------------------------------------

impl<'a, 'b> Add<&'b RistrettoPoint> for &'a RistrettoPoint {
    type Output = RistrettoPoint;

    fn add(self, other: &'b RistrettoPoint) -> RistrettoPoint {
        RistrettoPoint(&self.0 + &other.0)
    }
}

impl<'b> AddAssign<&'b RistrettoPoint> for RistrettoPoint {
    fn add_assign(&mut self, _rhs: &RistrettoPoint) {
        *self = (self as &RistrettoPoint) + _rhs;
    }
}

impl<'a, 'b> Sub<&'b RistrettoPoint> for &'a RistrettoPoint {
    type Output = RistrettoPoint;

    fn sub(self, other: &'b RistrettoPoint) -> RistrettoPoint {
        RistrettoPoint(&self.0 - &other.0)
    }
}

impl<'b> SubAssign<&'b RistrettoPoint> for RistrettoPoint {
    fn sub_assign(&mut self, _rhs: &RistrettoPoint) {
        *self = (self as &RistrettoPoint) - _rhs;
    }
}

impl<'a> Neg for &'a RistrettoPoint {
    type Output = RistrettoPoint;

    fn neg(self) -> RistrettoPoint {
        RistrettoPoint(-&self.0)
    }
}

impl<'b> MulAssign<&'b Scalar> for RistrettoPoint {
    fn mul_assign(&mut self, scalar: &'b Scalar) {
        let result = (self as &RistrettoPoint) * scalar;
        *self = result;
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a RistrettoPoint {
    type Output = RistrettoPoint;
    /// Scalar multiplication: compute `scalar * self`.
    fn mul(self, scalar: &'b Scalar) -> RistrettoPoint {
        RistrettoPoint(&self.0 * scalar)
    }
}

impl<'a, 'b> Mul<&'b RistrettoPoint> for &'a Scalar {
    type Output = RistrettoPoint;

    /// Scalar multiplication: compute `self * scalar`.
    fn mul(self, point: &'b RistrettoPoint) -> RistrettoPoint {
        RistrettoPoint(self * &point.0)
    }
}

/// Given a vector of (possibly secret) scalars and a vector of
/// (possibly secret) points, compute `c_1 P_1 + ... + c_n P_n`.
///
/// This function has the same behaviour as
/// `vartime::multiscalar_mult` but is constant-time.
///
/// # Input
///
/// An iterable of `Scalar`s and a iterable of `DecafPoints`.  It is an
/// error to call this function with two iterators of different lengths.
#[cfg(any(feature = "alloc", feature = "std"))]
pub fn multiscalar_mult<'a, 'b, I, J>(scalars: I, points: J) -> RistrettoPoint
    where I: IntoIterator<Item = &'a Scalar>,
          J: IntoIterator<Item = &'b RistrettoPoint>,
{
    let extended_points = points.into_iter().map(|P| &P.0);
    RistrettoPoint(edwards::multiscalar_mult(scalars, extended_points))
}

/// Precomputation
#[derive(Clone)]
pub struct RistrettoBasepointTable(pub EdwardsBasepointTable);

impl<'a, 'b> Mul<&'b Scalar> for &'a RistrettoBasepointTable {
    type Output = RistrettoPoint;

    fn mul(self, scalar: &'b Scalar) -> RistrettoPoint {
        RistrettoPoint(&self.0 * scalar)
    }
}

impl<'a, 'b> Mul<&'a RistrettoBasepointTable> for &'b Scalar {
    type Output = RistrettoPoint;

    fn mul(self, basepoint_table: &'a RistrettoBasepointTable) -> RistrettoPoint {
        RistrettoPoint(self * &basepoint_table.0)
    }
}

impl RistrettoBasepointTable {
    /// Create a precomputed table of multiples of the given `basepoint`.
    pub fn create(basepoint: &RistrettoPoint) -> RistrettoBasepointTable {
        RistrettoBasepointTable(EdwardsBasepointTable::create(&basepoint.0))
    }

    /// Get the basepoint for this table as a `RistrettoPoint`.
    pub fn basepoint(&self) -> RistrettoPoint {
        RistrettoPoint(self.0.basepoint())
    }
}

// ------------------------------------------------------------------------
// Constant-time conditional assignment
// ------------------------------------------------------------------------

impl ConditionallyAssignable for RistrettoPoint {
    /// Conditionally assign `other` to `self`, if `choice == 1u8`.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate subtle;
    /// # extern crate curve25519_dalek;
    /// #
    /// # use subtle::ConditionallyAssignable;
    /// #
    /// # use curve25519_dalek::edwards::Identity;
    /// # use curve25519_dalek::ristretto::RistrettoPoint;
    /// # use curve25519_dalek::constants;
    /// # fn main() {
    /// let A = RistrettoPoint::identity();
    /// let B = constants::RISTRETTO_BASEPOINT_POINT;
    ///
    /// let mut P = A;
    ///
    /// P.conditional_assign(&B, 0u8);
    /// assert!(P == A);
    /// P.conditional_assign(&B, 1u8);
    /// assert!(P == B);
    /// # }
    /// ```
    fn conditional_assign(&mut self, other: &RistrettoPoint, choice: u8) {
        self.0.X.conditional_assign(&other.0.X, choice);
        self.0.Y.conditional_assign(&other.0.Y, choice);
        self.0.Z.conditional_assign(&other.0.Z, choice);
        self.0.T.conditional_assign(&other.0.T, choice);
    }
}

// ------------------------------------------------------------------------
// Debug traits
// ------------------------------------------------------------------------

impl Debug for CompressedRistretto {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "CompressedRistretto: {:?}", self.as_bytes())
    }
}

impl Debug for RistrettoPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        let coset = self.coset4();
        write!(f, "RistrettoPoint: coset \n{:?}\n{:?}\n{:?}\n{:?}",
               coset[0], coset[1], coset[2], coset[3])
    }
}

// ------------------------------------------------------------------------
// Variable-time functions
// ------------------------------------------------------------------------

pub mod vartime {
    //! Variable-time operations on ristretto points, useful for non-secret data.
    use super::*;

    /// Given a vector of public scalars and a vector of (possibly secret)
    /// points, compute
    ///
    ///    c_1 P_1 + ... + c_n P_n.
    ///
    /// # Input
    ///
    /// A vector of `Scalar`s and a vector of `RistrettoPoints`.  It is an
    /// error to call this function with two vectors of different lengths.
    pub fn multiscalar_mult<'a, 'b, I, J>(scalars: I, points: J) -> RistrettoPoint
        where I: IntoIterator<Item = &'a Scalar>,
              J: IntoIterator<Item = &'b RistrettoPoint>
    {
        let extended_points = points.into_iter().map(|P| &P.0);
        RistrettoPoint(edwards::vartime::multiscalar_mult(scalars, extended_points))
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
    use edwards::CompressedEdwardsY;
    use edwards::Identity;
    use edwards::ValidityCheck;
    use super::*;

    #[cfg(feature = "serde")]
    use serde_cbor;

    #[test]
    #[cfg(feature = "serde")]
    fn serde_cbor_basepoint_roundtrip() {
        let output = serde_cbor::to_vec(&constants::RISTRETTO_BASEPOINT_POINT).unwrap();
        let parsed: RistrettoPoint = serde_cbor::from_slice(&output).unwrap();
        assert_eq!(parsed, constants::RISTRETTO_BASEPOINT_POINT);
    }

    #[test]
    fn scalarmult_ristrettopoint_works_both_ways() {
        let P = constants::RISTRETTO_BASEPOINT_POINT;
        let s = Scalar::from_u64(999);

        let P1 = &P * &s;
        let P2 = &s * &P;

        assert!(P1.compress().as_bytes() == P2.compress().as_bytes());
    }

    #[test]
    fn decompress_negative_s_fails() {
        // constants::d is neg, so decompression should fail as |d| != d.
        let bad_compressed = CompressedRistretto(constants::d.to_bytes());
        assert!(bad_compressed.decompress().is_none());
    }

    #[test]
    fn decompress_id() {
        let compressed_id = CompressedRistretto::identity();
        let id = compressed_id.decompress().unwrap();
        let mut identity_in_coset = false;
        for P in &id.coset4() {
            if P.compress() == CompressedEdwardsY::identity() {
                identity_in_coset = true;
            }
        }
        assert!(identity_in_coset);
    }

    #[test]
    fn compress_id() {
        let id = RistrettoPoint::identity();
        assert_eq!(id.compress(), CompressedRistretto::identity());
    }

    #[test]
    fn basepoint_roundtrip() {
        let bp_compressed_ristretto = constants::RISTRETTO_BASEPOINT_POINT.compress();
        let bp_recaf = bp_compressed_ristretto.decompress().unwrap().0;
        // Check that bp_recaf differs from bp by a point of order 4
        let diff = &constants::RISTRETTO_BASEPOINT_POINT.0 - &bp_recaf;
        let diff4 = diff.mult_by_pow_2(2);
        assert_eq!(diff4.compress(), CompressedEdwardsY::identity());
    }

    #[test]
    fn encodings_of_small_multiples_of_basepoint() {
        // Table of encodings of i*basepoint
        // Generated using ristretto.sage
        let compressed = [
            CompressedRistretto([236, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 127]),
            CompressedRistretto([226, 242, 174, 10, 106, 188, 78, 113, 168, 132, 169, 97, 197, 0, 81, 95, 88, 227, 11, 106, 165, 130, 221, 141, 182, 166, 89, 69, 224, 141, 45, 118]),
            CompressedRistretto([106, 73, 50, 16, 247, 73, 156, 209, 127, 236, 181, 16, 174, 12, 234, 35, 161, 16, 232, 213, 185, 1, 248, 172, 173, 211, 9, 92, 115, 163, 185, 25]),
            CompressedRistretto([148, 116, 31, 93, 93, 82, 117, 94, 206, 79, 35, 240, 68, 238, 39, 213, 209, 234, 30, 43, 209, 150, 180, 98, 22, 107, 22, 21, 42, 157, 2, 89]),
            CompressedRistretto([218, 128, 134, 39, 115, 53, 139, 70, 111, 250, 223, 224, 179, 41, 58, 179, 217, 253, 83, 197, 234, 108, 149, 83, 88, 245, 104, 50, 45, 175, 106, 87]),
            CompressedRistretto([232, 130, 177, 49, 1, 107, 82, 193, 211, 51, 112, 128, 24, 124, 247, 104, 66, 62, 252, 203, 181, 23, 187, 73, 90, 184, 18, 196, 22, 15, 244, 78]),
            CompressedRistretto([246, 71, 70, 211, 201, 43, 19, 5, 14, 216, 216, 2, 54, 167, 240, 0, 124, 59, 63, 150, 47, 91, 167, 147, 209, 154, 96, 30, 187, 29, 244, 3]),
            CompressedRistretto([68, 245, 53, 32, 146, 110, 200, 31, 189, 90, 56, 120, 69, 190, 183, 223, 133, 169, 106, 36, 236, 225, 135, 56, 189, 207, 166, 167, 130, 42, 23, 109]),
            CompressedRistretto([144, 50, 147, 216, 242, 40, 126, 190, 16, 226, 55, 77, 193, 165, 62, 11, 200, 135, 229, 146, 105, 159, 2, 208, 119, 213, 38, 60, 221, 85, 96, 28]),
            CompressedRistretto([2, 98, 42, 206, 143, 115, 3, 163, 28, 175, 198, 63, 143, 196, 143, 220, 22, 225, 200, 200, 210, 52, 178, 240, 214, 104, 82, 130, 169, 7, 96, 49]),
            CompressedRistretto([32, 112, 111, 215, 136, 178, 114, 10, 30, 210, 165, 218, 212, 149, 43, 1, 244, 19, 188, 240, 231, 86, 77, 232, 205, 200, 22, 104, 158, 45, 185, 95]),
            CompressedRistretto([188, 232, 63, 139, 165, 221, 47, 165, 114, 134, 76, 36, 186, 24, 16, 249, 82, 43, 198, 0, 74, 254, 149, 135, 122, 199, 50, 65, 202, 253, 171, 66]),
            CompressedRistretto([228, 84, 158, 225, 107, 154, 160, 48, 153, 202, 32, 140, 103, 173, 175, 202, 250, 76, 63, 62, 78, 83, 3, 222, 96, 38, 227, 202, 143, 248, 68, 96]),
            CompressedRistretto([170, 82, 224, 0, 223, 46, 22, 245, 95, 177, 3, 47, 195, 59, 196, 39, 66, 218, 214, 189, 90, 143, 192, 190, 1, 103, 67, 108, 89, 72, 80, 31]),
            CompressedRistretto([70, 55, 107, 128, 244, 9, 178, 157, 194, 181, 246, 240, 197, 37, 145, 153, 8, 150, 229, 113, 111, 65, 71, 124, 211, 0, 133, 171, 127, 16, 48, 30]),
            CompressedRistretto([224, 196, 24, 247, 200, 217, 196, 205, 215, 57, 91, 147, 234, 18, 79, 58, 217, 144, 33, 187, 104, 29, 252, 51, 2, 169, 217, 154, 46, 83, 230, 78]),
        ];
        let mut bp = RistrettoPoint::identity();
        for i in 0..16 {
            assert_eq!(bp.compress(), compressed[i]);
            bp = &bp + &constants::RISTRETTO_BASEPOINT_POINT;
        }
    }

    #[test]
    fn four_torsion_basepoint() {
        let bp = constants::RISTRETTO_BASEPOINT_POINT;
        let bp_coset = bp.coset4();
        for i in 0..4 {
            assert_eq!(bp, RistrettoPoint(bp_coset[i]));
        }
    }

    #[test]
    fn four_torsion_random() {
        let mut rng = OsRng::new().unwrap();
        let B = &constants::RISTRETTO_BASEPOINT_TABLE;
        let P = B * &Scalar::random(&mut rng);
        let P_coset = P.coset4();
        for i in 0..4 {
            assert_eq!(P, RistrettoPoint(P_coset[i]));
        }
    }

    #[test]
    fn random_roundtrip() {
        let mut rng = OsRng::new().unwrap();
        let B = &constants::RISTRETTO_BASEPOINT_TABLE;
        for _ in 0..100 {
            let P = B * &Scalar::random(&mut rng);
            let compressed_P = P.compress();
            let Q = compressed_P.decompress().unwrap();
            assert_eq!(P, Q);
        }
    }

    #[test]
    fn random_is_valid() {
        let mut rng = OsRng::new().unwrap();
        for _ in 0..100 {
            let P = RistrettoPoint::random(&mut rng);
            // Check that P is on the curve
            assert!(P.0.is_valid());
            // Check that P is in the image of the ristretto map
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
        let B = &constants::RISTRETTO_BASEPOINT_TABLE;
        let P = B * &Scalar::random(&mut rng);
        let P_compressed = P.compress();
        b.iter(|| P_compressed.decompress().unwrap());
    }

    #[bench]
    fn compression(b: &mut Bencher) {
        let mut rng = OsRng::new().unwrap();
        let B = &constants::RISTRETTO_BASEPOINT_TABLE;
        let P = B * &Scalar::random(&mut rng);
        b.iter(|| P.compress());
    }
}
