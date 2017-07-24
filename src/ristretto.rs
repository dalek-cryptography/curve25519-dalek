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

    /*
    // XXX replace these with ristretto encodings from the python implementation
    #[test]
    fn encodings_of_small_multiples_of_basepoint() {
        // Table of encodings of (1+i)*basepoint
        // Generated using the previous naive implementation.
        let compressed = [
            CompressedRistretto([141, 190, 226, 107, 177, 201, 35, 118, 14, 55, 160, 165, 242, 207, 121, 161, 177, 80, 8, 132, 205, 254, 101, 169, 233, 65, 124, 96, 255, 182, 249, 40]),
            CompressedRistretto([131, 57, 148, 16, 8, 196, 141, 82, 144, 220, 105, 112, 66, 33, 48, 16, 182, 198, 173, 35, 248, 181, 92, 231, 222, 35, 85, 56, 5, 252, 91, 40]),
            CompressedRistretto([199, 132, 32, 144, 156, 143, 81, 170, 240, 56, 232, 6, 178, 37, 118, 190, 110, 201, 26, 173, 156, 97, 59, 162, 240, 247, 226, 107, 197, 111, 107, 26]),
            CompressedRistretto([210, 120, 34, 214, 175, 27, 61, 6, 229, 181, 216, 36, 11, 245, 146, 232, 130, 215, 77, 29, 210, 30, 54, 155, 191, 81, 59, 124, 174, 3, 135, 36]),
            CompressedRistretto([155, 52, 159, 52, 189, 27, 181, 0, 245, 131, 0, 197, 79, 208, 252, 122, 104, 161, 245, 143, 67, 94, 13, 129, 153, 173, 129, 179, 118, 231, 90, 52]),
            CompressedRistretto([42, 117, 252, 118, 8, 1, 72, 25, 111, 246, 247, 103, 236, 86, 235, 29, 100, 156, 186, 209, 159, 21, 61, 26, 249, 25, 137, 228, 84, 23, 10, 27]),
            CompressedRistretto([21, 126, 181, 117, 58, 90, 216, 28, 184, 57, 9, 23, 158, 68, 159, 171, 109, 150, 232, 140, 144, 73, 139, 122, 124, 105, 125, 160, 94, 185, 150, 52]),
            CompressedRistretto([232, 167, 112, 233, 126, 33, 105, 63, 151, 6, 88, 225, 181, 17, 223, 12, 116, 138, 203, 47, 243, 225, 50, 171, 21, 220, 186, 179, 132, 20, 48, 6]),
            CompressedRistretto([99, 44, 97, 48, 242, 174, 78, 198, 112, 154, 146, 36, 239, 34, 94, 4, 0, 244, 175, 34, 46, 0, 83, 187, 5, 163, 225, 63, 51, 237, 234, 22]),
            CompressedRistretto([2, 33, 89, 176, 178, 123, 159, 75, 235, 172, 251, 11, 137, 177, 90, 122, 149, 186, 52, 243, 153, 190, 185, 202, 59, 137, 204, 160, 150, 152, 148, 55]),
            CompressedRistretto([245, 79, 78, 226, 114, 69, 247, 112, 18, 54, 90, 225, 176, 77, 231, 235, 196, 123, 49, 221, 34, 205, 151, 228, 244, 112, 82, 58, 30, 31, 58, 12]),
            CompressedRistretto([135, 53, 175, 167, 13, 94, 62, 31, 29, 248, 13, 132, 29, 69, 7, 188, 145, 49, 62, 55, 181, 109, 214, 11, 248, 162, 70, 15, 236, 126, 100, 60]),
            CompressedRistretto([98, 150, 69, 229, 144, 122, 237, 107, 127, 177, 33, 64, 59, 173, 210, 102, 74, 34, 23, 16, 252, 117, 14, 97, 231, 178, 63, 193, 157, 28, 178, 17]),
            CompressedRistretto([222, 104, 6, 1, 72, 12, 72, 178, 204, 238, 128, 70, 41, 150, 235, 96, 153, 150, 18, 4, 141, 206, 0, 38, 122, 112, 249, 51, 94, 251, 20, 57]),
            CompressedRistretto([7, 221, 140, 57, 13, 146, 248, 27, 56, 4, 128, 23, 145, 120, 126, 4, 158, 173, 52, 213, 164, 250, 26, 55, 89, 96, 187, 111, 211, 18, 63, 19]),
            CompressedRistretto([91, 213, 193, 10, 102, 92, 199, 124, 61, 176, 1, 47, 111, 59, 183, 91, 79, 56, 208, 109, 172, 209, 17, 167, 229, 216, 3, 236, 200, 208, 15, 20]),
        ];
        let mut bp = RistrettoPoint::identity();
        for i in 0..16 {
            assert_eq!(bp.compress(), compressed[i]);
            bp = &bp + &constants::RISTRETTO_BASEPOINT_POINT;
        }
    }
    */

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
