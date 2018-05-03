// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Group operations for Curve25519, in Edwards form.
//!
//! ## Encoding and Decoding
//!
//! Encoding is done by converting to and from a `CompressedEdwardsY`
//! struct, which is a typed wrapper around `[u8; 32]`.
//!
//! ## Equality Testing
//!
//! The `EdwardsPoint` struct implements the `subtle::ConstantTimeEq`
//! trait for constant-time equality checking, and the Rust `Eq` trait
//! for variable-time equality checking.
//!
//! ## Cofactor-related functions
//!
//! The order of the group of points on the curve \\(\mathcal E\\)
//! is \\(|\mathcal E| = 8\ell \\), so its structure is \\( \mathcal
//! E = \mathcal E[8] \times \mathcal E[\ell]\\).  The torsion
//! subgroup \\( \mathcal E[8] \\) consists of eight points of small
//! order.  Technically, all of \\(\mathcal E\\) is torsion, but we
//! use the word only to refer to the small \\(\mathcal E[8]\\) part, not
//! the large prime-order \\(\mathcal E[\ell]\\) part.
//!
//! To test if a point is in \\( \mathcal E[8] \\), use
//! `EdwardsPoint::is_small_order()`.
//!
//! To test if a point is in \\( \mathcal E[\ell] \\), use
//! `EdwardsPoint::is_torsion_free()`.
//!
//! To multiply by the cofactor, use `EdwardsPoint::mul_by_cofactor()`.
//!
//! To avoid dealing with cofactors entirely, consider using Ristretto.
//!
//! ## Scalars
//!
//! Scalars are represented by the `Scalar` struct.  To construct a scalar with a specific bit
//! pattern, see `Scalar::from_bits()`.
//!
//! ## Scalar Multiplication
//!
//! Scalar multiplication on Edwards points is provided by:
//!
//! * the `*` operator between a `Scalar` and a `EdwardsPoint`, which
//! performs constant-time variable-base scalar multiplication;
//!
//! * the `*` operator between a `Scalar` and a
//! `EdwardsBasepointTable`, which performs constant-time fixed-base
//! scalar multiplication;
//!
//! * the `edwards::multiscalar_mul` function, which performs
//! constant-time variable-base multiscalar multiplication;
//!
//! * the `edwards::vartime::multiscalar_mul` function, which
//! performs variable-time variable-base multiscalar multiplication.
//!
//! ## Implementation
//!
//! The Edwards arithmetic is implemented using the “extended twisted
//! coordinates” of Hisil, Wong, Carter, and Dawson, and the
//! corresponding complete formulas.  For more details,
//! see the [`curve_models` submodule][curve_models] 
//! of the internal documentation.
//!
//! ## Validity Checking
//!
//! There is no function for checking whether a point is valid.
//! Instead, the `EdwardsPoint` struct is guaranteed to hold a valid
//! point on the curve.
//!
//! We use the Rust type system to make invalid points
//! unrepresentable: `EdwardsPoint` objects can only be created via
//! successful decompression of a compressed point, or else by
//! operations on other (valid) `EdwardsPoint`s.
//!
//! [curve_models]: https://doc-internal.dalek.rs/curve25519_dalek/curve_models/index.html

// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]

#[cfg(feature = "alloc")]
use alloc::Vec;

use core::fmt::Debug;
use core::iter::Iterator;
use core::ops::{Add, Sub, Neg};
use core::ops::{AddAssign, SubAssign};
use core::ops::{Mul, MulAssign};
use core::iter::Sum;
use core::borrow::Borrow;

use subtle::ConditionallyAssignable;
use subtle::ConditionallyNegatable;
use subtle::Choice;
use subtle::ConstantTimeEq;

use constants;

use field::FieldElement;
use scalar::Scalar;

use montgomery::MontgomeryPoint;
use curve_models::ProjectivePoint;
use curve_models::CompletedPoint;
use curve_models::AffineNielsPoint;
use curve_models::ProjectiveNielsPoint;

use scalar_mul::window::LookupTable;

use traits::{Identity, IsIdentity};
use traits::ValidityCheck;

// ------------------------------------------------------------------------
// Compressed points
// ------------------------------------------------------------------------

/// In "Edwards y" / "Ed25519" format, the curve point \\((x,y)\\) is
/// determined by the \\(y\\)-coordinate and the sign of \\(x\\).
///
/// The first 255 bits of a `CompressedEdwardsY` represent the
/// \\(y\\)-coordinate.  The high bit of the 32nd byte gives the sign of \\(x\\).
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct CompressedEdwardsY(pub [u8; 32]);

impl Debug for CompressedEdwardsY {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "CompressedEdwardsY: {:?}", self.as_bytes())
    }
}

impl CompressedEdwardsY {
    /// View this `CompressedEdwardsY` as an array of bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Copy this `CompressedEdwardsY` to an array of bytes.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// Attempt to decompress to an `EdwardsPoint`.
    ///
    /// Returns `None` if the input is not the \\(y\\)-coordinate of a
    /// curve point.
    pub fn decompress(&self) -> Option<EdwardsPoint> {
        let Y = FieldElement::from_bytes(self.as_bytes());
        let Z = FieldElement::one();
        let YY = Y.square();
        let u = &YY - &Z;                            // u =  y²-1
        let v = &(&YY * &constants::EDWARDS_D) + &Z; // v = dy²+1
        let (is_nonzero_square, mut X) = FieldElement::sqrt_ratio(&u, &v);

        if is_nonzero_square.unwrap_u8() != 1u8 { return None; }

        // Flip the sign of X if it's not correct
        let compressed_sign_bit = Choice::from(self.as_bytes()[31] >> 7);
        let    current_sign_bit = X.is_negative();

        X.conditional_negate(current_sign_bit ^ compressed_sign_bit);

        Some(EdwardsPoint{ X: X, Y: Y, Z: Z, T: &X * &Y })
    }
}

// ------------------------------------------------------------------------
// Serde support
// ------------------------------------------------------------------------
// Serializes to and from `EdwardsPoint` directly, doing compression
// and decompression internally.  This means that users can create
// structs containing `EdwardsPoint`s and use Serde's derived
// serializers to serialize those structures.

#[cfg(feature = "serde")]
use serde::{self, Serialize, Deserialize, Serializer, Deserializer};
#[cfg(feature = "serde")]
use serde::de::Visitor;

#[cfg(feature = "serde")]
impl Serialize for EdwardsPoint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_bytes(self.compress().as_bytes())
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for EdwardsPoint {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        struct EdwardsPointVisitor;

        impl<'de> Visitor<'de> for EdwardsPointVisitor {
            type Value = EdwardsPoint;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid point in Edwards y + sign format")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<EdwardsPoint, E>
                where E: serde::de::Error
            {
                if v.len() == 32 {
                    let mut arr32 = [0u8; 32];
                    arr32[0..32].copy_from_slice(v);
                    CompressedEdwardsY(arr32)
                        .decompress()
                        .ok_or(serde::de::Error::custom("decompression failed"))
                } else {
                    Err(serde::de::Error::invalid_length(v.len(), &self))
                }
            }
        }

        deserializer.deserialize_bytes(EdwardsPointVisitor)
    }
}

// ------------------------------------------------------------------------
// Internal point representations
// ------------------------------------------------------------------------

/// An `EdwardsPoint` represents a point on the Edwards form of Curve25519.
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct EdwardsPoint {
    pub(crate) X: FieldElement,
    pub(crate) Y: FieldElement,
    pub(crate) Z: FieldElement,
    pub(crate) T: FieldElement,
}

// ------------------------------------------------------------------------
// Constructors
// ------------------------------------------------------------------------

impl Identity for CompressedEdwardsY {
    fn identity() -> CompressedEdwardsY {
        CompressedEdwardsY([1, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0])
    }
}

impl Identity for EdwardsPoint {
    fn identity() -> EdwardsPoint {
        EdwardsPoint{ X: FieldElement::zero(),
                       Y: FieldElement::one(),
                       Z: FieldElement::one(),
                       T: FieldElement::zero() }
    }
}

// ------------------------------------------------------------------------
// Validity checks (for debugging, not CT)
// ------------------------------------------------------------------------

impl ValidityCheck for EdwardsPoint {
    // XXX this should also check that T is correct
    fn is_valid(&self) -> bool {
        self.to_projective().is_valid()
    }
}

// ------------------------------------------------------------------------
// Constant-time assignment
// ------------------------------------------------------------------------

impl ConditionallyAssignable for EdwardsPoint {
    fn conditional_assign(&mut self, other: &EdwardsPoint, choice: Choice) {
        self.X.conditional_assign(&other.X, choice);
        self.Y.conditional_assign(&other.Y, choice);
        self.Z.conditional_assign(&other.Z, choice);
        self.T.conditional_assign(&other.T, choice);
    }
}

// ------------------------------------------------------------------------
// Equality
// ------------------------------------------------------------------------

impl ConstantTimeEq for EdwardsPoint {
    fn ct_eq(&self, other: &EdwardsPoint) -> Choice {
        self.compress().as_bytes().ct_eq(other.compress().as_bytes())
    }
}

impl PartialEq for EdwardsPoint {
    fn eq(&self, other: &EdwardsPoint) -> bool {
        self.ct_eq(other).unwrap_u8() == 1u8
    }
}

impl Eq for EdwardsPoint {}

// ------------------------------------------------------------------------
// Point conversions
// ------------------------------------------------------------------------

impl EdwardsPoint {
    /// Convert to a ProjectiveNielsPoint
    pub(crate) fn to_projective_niels(&self) -> ProjectiveNielsPoint {
        ProjectiveNielsPoint{
            Y_plus_X:  &self.Y + &self.X,
            Y_minus_X: &self.Y - &self.X,
            Z:          self.Z,
            T2d:       &self.T * &constants::EDWARDS_D2,
        }
    }

    /// Convert the representation of this point from extended
    /// coordinates to projective coordinates.
    ///
    /// Free.
    pub(crate) fn to_projective(&self) -> ProjectivePoint {
        ProjectivePoint{
            X: self.X,
            Y: self.Y,
            Z: self.Z,
        }
    }

    /// Dehomogenize to a AffineNielsPoint.
    /// Mainly for testing.
    pub(crate) fn to_affine_niels(&self) -> AffineNielsPoint {
        let recip = self.Z.invert();
        let x = &self.X * &recip;
        let y = &self.Y * &recip;
        let xy2d = &(&x * &y) * &constants::EDWARDS_D2;
        AffineNielsPoint{
            y_plus_x:  &y + &x,
            y_minus_x: &y - &x,
            xy2d:      xy2d
        }
    }

    /// Convert this `EdwardsPoint` on the Edwards model to the
    /// corresponding `MontgomeryPoint` on the Montgomery model.
    ///
    /// Note that this is a one-way conversion, since the Montgomery
    /// model does not retain sign information.
    pub fn to_montgomery(&self) -> MontgomeryPoint {
        // We have u = (1+y)/(1-y) = (Z+Y)/(Z-Y).
        //
        // The denominator is zero only when y=1, the identity point of
        // the Edwards curve.  Since 0.invert() = 0, in this case we
        // compute u = 0, the identity point of the Montgomery line.
        let U = &self.Z + &self.Y;
        let W = &self.Z - &self.Y;
        let u = &U * &W.invert();
        MontgomeryPoint(u.to_bytes())
    }

    /// Compress this point to `CompressedEdwardsY` format.
    pub fn compress(&self) -> CompressedEdwardsY {
        let recip = self.Z.invert();
        let x = &self.X * &recip;
        let y = &self.Y * &recip;
        let mut s: [u8; 32];

        s = y.to_bytes();
        s[31] ^= x.is_negative().unwrap_u8() << 7;
        CompressedEdwardsY(s)
    }
}

// ------------------------------------------------------------------------
// Doubling
// ------------------------------------------------------------------------

impl EdwardsPoint {
    /// Add this point to itself.
    pub(crate) fn double(&self) -> EdwardsPoint {
        self.to_projective().double().to_extended()
    }
}

// ------------------------------------------------------------------------
// Addition and Subtraction
// ------------------------------------------------------------------------

impl<'a, 'b> Add<&'b EdwardsPoint> for &'a EdwardsPoint {
    type Output = EdwardsPoint;
    fn add(self, other: &'b EdwardsPoint) -> EdwardsPoint {
        (self + &other.to_projective_niels()).to_extended()
    }
}

define_add_variants!(LHS = EdwardsPoint, RHS = EdwardsPoint, Output = EdwardsPoint);

impl<'b> AddAssign<&'b EdwardsPoint> for EdwardsPoint {
    fn add_assign(&mut self, _rhs: &'b EdwardsPoint) {
        *self = (self as &EdwardsPoint) + _rhs;
    }
}

define_add_assign_variants!(LHS = EdwardsPoint, RHS = EdwardsPoint);

impl<'a, 'b> Sub<&'b EdwardsPoint> for &'a EdwardsPoint {
    type Output = EdwardsPoint;
    fn sub(self, other: &'b EdwardsPoint) -> EdwardsPoint {
        (self - &other.to_projective_niels()).to_extended()
    }
}

define_sub_variants!(LHS = EdwardsPoint, RHS = EdwardsPoint, Output = EdwardsPoint);

impl<'b> SubAssign<&'b EdwardsPoint> for EdwardsPoint {
    fn sub_assign(&mut self, _rhs: &'b EdwardsPoint) {
        *self = (self as &EdwardsPoint) - _rhs;
    }
}

define_sub_assign_variants!(LHS = EdwardsPoint, RHS = EdwardsPoint);

define_point_sum_variants!(PointType = EdwardsPoint);

// ------------------------------------------------------------------------
// Negation
// ------------------------------------------------------------------------

impl<'a> Neg for &'a EdwardsPoint {
    type Output = EdwardsPoint;

    fn neg(self) -> EdwardsPoint {
        EdwardsPoint{
            X: -(&self.X),
            Y:  self.Y,
            Z:  self.Z,
            T: -(&self.T),
        }
    }
}

impl Neg for EdwardsPoint {
    type Output = EdwardsPoint;

    fn neg(self) -> EdwardsPoint {
        -&self
    }
}

// ------------------------------------------------------------------------
// Scalar multiplication
// ------------------------------------------------------------------------

impl<'b> MulAssign<&'b Scalar> for EdwardsPoint {
    fn mul_assign(&mut self, scalar: &'b Scalar) {
        let result = (self as &EdwardsPoint) * scalar;
        *self = result;
    }
}

define_mul_assign_variants!(LHS = EdwardsPoint, RHS = Scalar);

define_mul_variants!(LHS = EdwardsPoint, RHS = Scalar, Output = EdwardsPoint);
define_mul_variants!(LHS = Scalar, RHS = EdwardsPoint, Output = EdwardsPoint);

impl<'a, 'b> Mul<&'b Scalar> for &'a EdwardsPoint {
    type Output = EdwardsPoint;
    /// Scalar multiplication: compute `scalar * self`.
    ///
    /// For scalar multiplication of a basepoint,
    /// `EdwardsBasepointTable` is approximately 4x faster.
    fn mul(self, scalar: &'b Scalar) -> EdwardsPoint {
        // If we built with AVX2, use the AVX2 backend.
        #[cfg(all(feature="nightly", all(feature="avx2_backend", target_feature="avx2")))]
        {
            use backend::avx2::scalar_mul::variable_base::mul;
            mul(self, scalar)
        }
        // Otherwise, use the serial backend:
        #[cfg(not(all(feature="nightly", all(feature="avx2_backend", target_feature="avx2"))))]
        {
            use scalar_mul::variable_base::mul;
            mul(self, scalar)
        }
    }
}

impl<'a, 'b> Mul<&'b EdwardsPoint> for &'a Scalar {
    type Output = EdwardsPoint;

    /// Scalar multiplication: compute `scalar * self`.
    ///
    /// For scalar multiplication of a basepoint,
    /// `EdwardsBasepointTable` is approximately 4x faster.
    fn mul(self, point: &'b EdwardsPoint) -> EdwardsPoint {
        point * self
    }
}

/// Given an iterator of (possibly secret) scalars and an iterator of
/// (possibly secret) points, compute
/// $$
/// Q = c\_1 P\_1 + \cdots + c\_n P\_n.
/// $$
///
/// This function has the same behaviour as
/// `vartime::multiscalar_mul` but is constant-time.
///
/// It is an error to call this function with two iterators of different lengths.
///
/// # Examples
///
/// The trait bound aims for maximum flexibility: the inputs must be
/// convertable to iterators (`I: IntoIter`), and the iterator's items
/// must be `Borrow<Scalar>` (or `Borrow<EdwardsPoint>`), to allow
/// iterators returning either `Scalar`s or `&Scalar`s.
///
/// ```
/// use curve25519_dalek::{constants, edwards};
/// use curve25519_dalek::scalar::Scalar;
///
/// // Some scalars
/// let a = Scalar::from_u64(87329482);
/// let b = Scalar::from_u64(37264829);
/// let c = Scalar::from_u64(98098098);
///
/// // Some points
/// let P = constants::ED25519_BASEPOINT_POINT;
/// let Q = P + P;
/// let R = P + Q;
///
/// // A1 = a*P + b*Q + c*R
/// let abc = [a,b,c];
/// let A1 = edwards::multiscalar_mul(&abc, &[P,Q,R]);
/// // Note: (&abc).into_iter(): Iterator<Item=&Scalar>
///
/// // A2 = (-a)*P + (-b)*Q + (-c)*R
/// let minus_abc = abc.iter().map(|x| -x);
/// let A2 = edwards::multiscalar_mul(minus_abc, &[P,Q,R]);
/// // Note: minus_abc.into_iter(): Iterator<Item=Scalar>
///
/// assert_eq!(A1.compress(), (-A2).compress());
/// ```
#[cfg(any(feature = "alloc", feature = "std"))]
pub fn multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint
    where I: IntoIterator,
          I::Item: Borrow<Scalar>,
          J: IntoIterator,
          J::Item: Borrow<EdwardsPoint>,
{
    // XXX later when we do more fancy multiscalar mults, we can
    // delegate based on the iter's size hint -- hdevalence

    // If we built with AVX2, use the AVX2 backend.
    #[cfg(all(feature="nightly", all(feature="avx2_backend", target_feature="avx2")))]
    {
        use backend::avx2::scalar_mul::straus::multiscalar_mul;
        multiscalar_mul(scalars, points)
    }
    // Otherwise, proceed as normal:
    #[cfg(not(all(feature="nightly", all(feature="avx2_backend", target_feature="avx2"))))]
    {
        use scalar_mul::straus::multiscalar_mul;
        multiscalar_mul(scalars, points)
    }
}

/// A precomputed table of multiples of a basepoint, for accelerating
/// fixed-base scalar multiplication.  One table, for the Ed25519
/// basepoint, is provided in the `constants` module.
///
/// The basepoint tables are reasonably large (30KB), so they should
/// probably be boxed.
#[derive(Clone)]
pub struct EdwardsBasepointTable(pub(crate) [LookupTable<AffineNielsPoint>; 32]);

impl EdwardsBasepointTable {
    /// The computation uses Pippeneger's algorithm, as described on
    /// page 13 of the Ed25519 paper.  Write the scalar \\(a\\) in radix \\(16\\) with
    /// coefficients in \\([-8,8)\\), i.e.,
    /// $$
    ///     a = a\_0 + a\_1 16\^1 + \cdots + a\_{63} 16\^{63},
    /// $$
    /// with \\(-8 \leq a_i < 8\\), \\(-8 \leq a\_{63} \leq 8\\).  Then
    /// $$
    ///     a B = a\_0 B + a\_1 16\^1 B + \cdots + a\_{63} 16\^{63} B.
    /// $$
    /// Grouping even and odd coefficients gives
    /// $$
    /// \begin{aligned}
    ///     a B = \quad a\_0 16\^0 B +& a\_2 16\^2 B + \cdots + a\_{62} 16\^{62} B    \\\\
    ///               + a\_1 16\^1 B +& a\_3 16\^3 B + \cdots + a\_{63} 16\^{63} B    \\\\
    ///         = \quad(a\_0 16\^0 B +& a\_2 16\^2 B + \cdots + a\_{62} 16\^{62} B)   \\\\
    ///            + 16(a\_1 16\^0 B +& a\_3 16\^2 B + \cdots + a\_{63} 16\^{62} B).  \\\\
    /// \end{aligned}
    /// $$
    /// For each \\(i = 0 \ldots 31\\), we create a lookup table of
    /// $$
    /// [16\^{2i} B, \ldots, 8\cdot16\^{2i} B],
    /// $$
    /// and use it to select \\( x \cdot 16\^{2i} \cdot B \\) in constant time.
    ///
    /// The radix-\\(16\\) representation requires that the scalar is bounded
    /// by \\(2\^{255}\\), which is always the case.
    fn basepoint_mul(&self, scalar: &Scalar) -> EdwardsPoint {
        let a = scalar.to_radix_16();

        let tables = &self.0;
        let mut P = EdwardsPoint::identity();

        for i in (0..64).filter(|x| x % 2 == 1) {
            P = (&P + &tables[i/2].select(a[i])).to_extended();
        }

        P = P.mul_by_pow_2(4);

        for i in (0..64).filter(|x| x % 2 == 0) {
            P = (&P + &tables[i/2].select(a[i])).to_extended();
        }

        P
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a EdwardsBasepointTable {
    type Output = EdwardsPoint;

    /// Construct an `EdwardsPoint` from a `Scalar` \\(a\\) by
    /// computing the multiple \\(aB\\) of this basepoint \\(B\\).
    fn mul(self, scalar: &'b Scalar) -> EdwardsPoint {
        // delegate to a private function so that its documentation appears in internal docs
        self.basepoint_mul(scalar)
    }
}

impl<'a, 'b> Mul<&'a EdwardsBasepointTable> for &'b Scalar {
    type Output = EdwardsPoint;

    /// Construct an `EdwardsPoint` from a `Scalar` \\(a\\) by
    /// computing the multiple \\(aB\\) of this basepoint \\(B\\).
    fn mul(self, basepoint_table: &'a EdwardsBasepointTable) -> EdwardsPoint {
        basepoint_table * &self
    }
}

impl EdwardsBasepointTable {
    /// Create a table of precomputed multiples of `basepoint`.
    pub fn create(basepoint: &EdwardsPoint) -> EdwardsBasepointTable {
        // XXX use init_with
        let mut table = EdwardsBasepointTable([LookupTable::default(); 32]);
        let mut P = *basepoint;
        for i in 0..32 {
            // P = (16^2)^i * B
            table.0[i] = LookupTable::from(&P);
            P = P.mul_by_pow_2(8);
        }
        table
    }

    /// Get the basepoint for this table as an `EdwardsPoint`.
    ///
    /// XXX maybe this would be better as a `From` impl
    pub fn basepoint(&self) -> EdwardsPoint {
        // self.0[0].select(1) = 1*(16^2)^0*B
        // but as an `AffineNielsPoint`, so add identity to convert to extended.
        (&EdwardsPoint::identity() + &self.0[0].select(1)).to_extended()
    }
}

impl EdwardsPoint {
    /// Multiply by the cofactor: return \\([8]P\\).
    pub fn mul_by_cofactor(&self) -> EdwardsPoint {
        self.mul_by_pow_2(3)
    }

    /// Compute \\([2\^k] P \\) by successive doublings. Requires \\( k > 0 \\).
    pub(crate) fn mul_by_pow_2(&self, k: u32) -> EdwardsPoint {
        debug_assert!( k > 0 );
        let mut r: CompletedPoint;
        let mut s = self.to_projective();
        for _ in 0..(k-1) {
            r = s.double(); s = r.to_projective();
        }
        // Unroll last iteration so we can go directly to_extended()
        s.double().to_extended()
    }

    /// Determine if this point is of small order.
    ///
    /// # Return
    ///
    /// * `true` if `self` is in the torsion subgroup \\( \mathcal E[8] \\);
    /// * `false` if `self` is not in the torsion subgroup \\( \mathcal E[8] \\).
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::constants;
    ///
    /// // Generator of the prime-order subgroup
    /// let P = constants::ED25519_BASEPOINT_POINT;
    /// // Generator of the torsion subgroup
    /// let Q = constants::EIGHT_TORSION[1];
    ///
    /// // P has large order
    /// assert_eq!(P.is_small_order(), false);
    ///
    /// // Q has small order
    /// assert_eq!(Q.is_small_order(), true);
    /// ```
    pub fn is_small_order(&self) -> bool {
        self.mul_by_cofactor().is_identity()
    }

    /// Determine if this point is “torsion-free”, i.e., is contained in
    /// the prime-order subgroup.
    ///
    /// # Return
    ///
    /// * `true` if `self` has zero torsion component and is in the
    /// prime-order subgroup;
    /// * `false` if `self` has a nonzero torsion component and is not
    /// in the prime-order subgroup.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::constants;
    ///
    /// // Generator of the prime-order subgroup
    /// let P = constants::ED25519_BASEPOINT_POINT;
    /// // Generator of the torsion subgroup
    /// let Q = constants::EIGHT_TORSION[1];
    ///
    /// // P is torsion-free
    /// assert_eq!(P.is_torsion_free(), true);
    ///
    /// // P + Q is not torsion-free
    /// assert_eq!((P+Q).is_torsion_free(), false);
    /// ```
    pub fn is_torsion_free(&self) -> bool {
        (self * &constants::BASEPOINT_ORDER).is_identity()
    }
}

// ------------------------------------------------------------------------
// Debug traits
// ------------------------------------------------------------------------

impl Debug for EdwardsPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "EdwardsPoint{{\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?},\n\tT: {:?}\n}}",
               &self.X, &self.Y, &self.Z, &self.T)
    }
}

impl Debug for EdwardsBasepointTable {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "EdwardsBasepointTable([\n")?;
        for i in 0..32 {
            write!(f, "\t{:?},\n", &self.0[i])?;
        }
        write!(f, "])")
    }
}

// ------------------------------------------------------------------------
// Variable-time functions
// ------------------------------------------------------------------------

pub mod vartime {
    //! Variable-time operations on curve points, useful for non-secret data.
    use super::*;

    /// Given an iterator of public scalars and an iterator of public points, compute
    /// $$
    /// Q = c\_1 P\_1 + \cdots + c\_n P\_n.
    /// $$
    ///
    /// This function has the same behaviour as
    /// `edwards::multiscalar_mul` but operates on non-secret data.
    ///
    /// It is an error to call this function with two iterators of different lengths.
    ///
    /// # Examples
    ///
    /// The trait bound aims for maximum flexibility: the inputs must be
    /// convertable to iterators (`I: IntoIter`), and the iterator's items
    /// must be `Borrow<Scalar>` (or `Borrow<EdwardsPoint>`), to allow
    /// iterators returning either `Scalar`s or `&Scalar`s.
    ///
    /// ```
    /// use curve25519_dalek::{constants, edwards};
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// // Some scalars
    /// let a = Scalar::from_u64(87329482);
    /// let b = Scalar::from_u64(37264829);
    /// let c = Scalar::from_u64(98098098);
    ///
    /// // Some points
    /// let P = constants::ED25519_BASEPOINT_POINT;
    /// let Q = P + P;
    /// let R = P + Q;
    ///
    /// // A1 = a*P + b*Q + c*R
    /// let abc = [a,b,c];
    /// let A1 = edwards::vartime::multiscalar_mul(&abc, &[P,Q,R]);
    /// // Note: (&abc).into_iter(): Iterator<Item=&Scalar>
    ///
    /// // A2 = (-a)*P + (-b)*Q + (-c)*R
    /// let minus_abc = abc.iter().map(|x| -x);
    /// let A2 = edwards::vartime::multiscalar_mul(minus_abc, &[P,Q,R]);
    /// // Note: minus_abc.into_iter(): Iterator<Item=Scalar>
    ///
    /// assert_eq!(A1.compress(), (-A2).compress());
    /// ```
    #[cfg(any(feature = "alloc", feature = "std"))]
    pub fn multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint
        where I: IntoIterator,
              I::Item: Borrow<Scalar>,
              J: IntoIterator,
              J::Item: Borrow<EdwardsPoint>,
    {
        // XXX later when we do more fancy multiscalar mults, we can delegate
        // based on the iter's size hint -- hdevalence
        // If we built with AVX2, use the AVX2 backend.
        #[cfg(all(feature="nightly", all(feature="avx2_backend", target_feature="avx2")))]
        {
            use backend::avx2::scalar_mul::vartime_straus::multiscalar_mul;
            multiscalar_mul(scalars, points)
        }
        // Otherwise, proceed as normal:
        #[cfg(not(all(feature="nightly", all(feature="avx2_backend", target_feature="avx2"))))]
        {
            use scalar_mul::vartime_straus::multiscalar_mul;
            multiscalar_mul(scalars, points)
        }
    }

    /// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
    #[cfg(feature="precomputed_tables")]
    pub fn double_scalar_mul_basepoint(a: &Scalar, A: &EdwardsPoint, b: &Scalar) -> EdwardsPoint {
        // If we built with AVX2, use the AVX2 backend.
        #[cfg(all(feature="nightly", all(feature="avx2_backend", target_feature="avx2")))]
        {
            use backend::avx2::scalar_mul::vartime_double_base::mul;
            mul(a, A, b)
        }
        // Otherwise, proceed as normal:
        #[cfg(not(all(feature="nightly", all(feature="avx2_backend", target_feature="avx2"))))]
        {
            use scalar_mul::vartime_double_base::mul;
            mul(a, A, b)
        }
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use field::FieldElement;
    use scalar::Scalar;
    use subtle::ConditionallyAssignable;
    use constants;
    use super::*;

    /// X coordinate of the basepoint.
    /// = 15112221349535400772501151409588531511454012693041857206046113283949847762202
    static BASE_X_COORD_BYTES: [u8; 32] =
        [0x1a, 0xd5, 0x25, 0x8f, 0x60, 0x2d, 0x56, 0xc9, 0xb2, 0xa7, 0x25, 0x95, 0x60, 0xc7, 0x2c, 0x69,
         0x5c, 0xdc, 0xd6, 0xfd, 0x31, 0xe2, 0xa4, 0xc0, 0xfe, 0x53, 0x6e, 0xcd, 0xd3, 0x36, 0x69, 0x21];

    /// Compressed Edwards Y form of 2*basepoint.
    static BASE2_CMPRSSD: CompressedEdwardsY =
        CompressedEdwardsY([0xc9, 0xa3, 0xf8, 0x6a, 0xae, 0x46, 0x5f, 0xe,
                            0x56, 0x51, 0x38, 0x64, 0x51, 0x0f, 0x39, 0x97,
                            0x56, 0x1f, 0xa2, 0xc9, 0xe8, 0x5e, 0xa2, 0x1d,
                            0xc2, 0x29, 0x23, 0x09, 0xf3, 0xcd, 0x60, 0x22]);

    /// Compressed Edwards Y form of 16*basepoint.
    static BASE16_CMPRSSD: CompressedEdwardsY =
        CompressedEdwardsY([0xeb, 0x27, 0x67, 0xc1, 0x37, 0xab, 0x7a, 0xd8,
                            0x27, 0x9c, 0x07, 0x8e, 0xff, 0x11, 0x6a, 0xb0,
                            0x78, 0x6e, 0xad, 0x3a, 0x2e, 0x0f, 0x98, 0x9f,
                            0x72, 0xc3, 0x7f, 0x82, 0xf2, 0x96, 0x96, 0x70]);

    /// 4493907448824000747700850167940867464579944529806937181821189941592931634714
    pub static A_SCALAR: Scalar = Scalar{
        bytes: [
            0x1a, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d,
            0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8, 0x26, 0x4d,
            0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1,
            0x58, 0x9e, 0x7b, 0x7f, 0x23, 0x76, 0xef, 0x09,
        ],
    };

    /// 2506056684125797857694181776241676200180934651973138769173342316833279714961
    pub static B_SCALAR: Scalar = Scalar{
        bytes: [
            0x91, 0x26, 0x7a, 0xcf, 0x25, 0xc2, 0x09, 0x1b,
            0xa2, 0x17, 0x74, 0x7b, 0x66, 0xf0, 0xb3, 0x2e,
            0x9d, 0xf2, 0xa5, 0x67, 0x41, 0xcf, 0xda, 0xc4,
            0x56, 0xa7, 0xd4, 0xaa, 0xb8, 0x60, 0x8a, 0x05,
        ],
    };

    /// A_SCALAR * basepoint, computed with ed25519.py
    pub static A_TIMES_BASEPOINT: CompressedEdwardsY = CompressedEdwardsY([
        0xea, 0x27, 0xe2, 0x60, 0x53, 0xdf, 0x1b, 0x59,
        0x56, 0xf1, 0x4d, 0x5d, 0xec, 0x3c, 0x34, 0xc3,
        0x84, 0xa2, 0x69, 0xb7, 0x4c, 0xc3, 0x80, 0x3e,
        0xa8, 0xe2, 0xe7, 0xc9, 0x42, 0x5e, 0x40, 0xa5]);

    /// A_SCALAR * (A_TIMES_BASEPOINT) + B_SCALAR * BASEPOINT
    /// computed with ed25519.py
    static DOUBLE_SCALAR_MULT_RESULT: CompressedEdwardsY = CompressedEdwardsY([
        0x7d, 0xfd, 0x6c, 0x45, 0xaf, 0x6d, 0x6e, 0x0e,
        0xba, 0x20, 0x37, 0x1a, 0x23, 0x64, 0x59, 0xc4,
        0xc0, 0x46, 0x83, 0x43, 0xde, 0x70, 0x4b, 0x85,
        0x09, 0x6f, 0xfe, 0x35, 0x4f, 0x13, 0x2b, 0x42]);

    /// Test round-trip decompression for the basepoint.
    #[test]
    fn basepoint_decompression_compression() {
        let base_X = FieldElement::from_bytes(&BASE_X_COORD_BYTES);
        let bp = constants::ED25519_BASEPOINT_COMPRESSED.decompress().unwrap();
        assert!(bp.is_valid());
        // Check that decompression actually gives the correct X coordinate
        assert_eq!(base_X, bp.X);
        assert_eq!(bp.compress(), constants::ED25519_BASEPOINT_COMPRESSED);
    }

    /// Test sign handling in decompression
    #[test]
    fn decompression_sign_handling() {
        // Manually set the high bit of the last byte to flip the sign
        let mut minus_basepoint_bytes = constants::ED25519_BASEPOINT_COMPRESSED.as_bytes().clone();
        minus_basepoint_bytes[31] |= 1 << 7;
        let minus_basepoint = CompressedEdwardsY(minus_basepoint_bytes)
                              .decompress().unwrap();
        // Test projective coordinates exactly since we know they should
        // only differ by a flipped sign.
        assert_eq!(minus_basepoint.X, -(&constants::ED25519_BASEPOINT_POINT.X));
        assert_eq!(minus_basepoint.Y,    constants::ED25519_BASEPOINT_POINT.Y);
        assert_eq!(minus_basepoint.Z,    constants::ED25519_BASEPOINT_POINT.Z);
        assert_eq!(minus_basepoint.T, -(&constants::ED25519_BASEPOINT_POINT.T));
    }

    /// Test that computing 1*basepoint gives the correct basepoint.
    #[test]
    #[cfg(feature="precomputed_tables")]
    fn basepoint_mult_one_vs_basepoint() {
        let bp = &constants::ED25519_BASEPOINT_TABLE * &Scalar::one();
        let compressed = bp.compress();
        assert_eq!(compressed, constants::ED25519_BASEPOINT_COMPRESSED);
    }

    /// Test that `EdwardsBasepointTable::basepoint()` gives the correct basepoint.
    #[test]
    #[cfg(feature="precomputed_tables")]
    fn basepoint_table_basepoint_function_correct() {
        let bp = constants::ED25519_BASEPOINT_TABLE.basepoint();
        assert_eq!(bp.compress(), constants::ED25519_BASEPOINT_COMPRESSED);
    }

    /// Test `impl Add<EdwardsPoint> for EdwardsPoint`
    /// using basepoint + basepoint versus the 2*basepoint constant.
    #[test]
    fn basepoint_plus_basepoint_vs_basepoint2() {
        let bp = constants::ED25519_BASEPOINT_POINT;
        let bp_added = &bp + &bp;
        assert_eq!(bp_added.compress(), BASE2_CMPRSSD);
    }

    /// Test `impl Add<ProjectiveNielsPoint> for EdwardsPoint`
    /// using the basepoint, basepoint2 constants
    #[test]
    fn basepoint_plus_basepoint_projective_niels_vs_basepoint2() {
        let bp = constants::ED25519_BASEPOINT_POINT;
        let bp_added = (&bp + &bp.to_projective_niels()).to_extended();
        assert_eq!(bp_added.compress(), BASE2_CMPRSSD);
    }

    /// Test `impl Add<AffineNielsPoint> for EdwardsPoint`
    /// using the basepoint, basepoint2 constants
    #[test]
    fn basepoint_plus_basepoint_affine_niels_vs_basepoint2() {
        let bp = constants::ED25519_BASEPOINT_POINT;
        let bp_affine_niels = bp.to_affine_niels();
        let bp_added = (&bp + &bp_affine_niels).to_extended();
        assert_eq!(bp_added.compress(), BASE2_CMPRSSD);
    }

    /// Check that equality of `EdwardsPoints` handles projective
    /// coordinates correctly.
    #[test]
    fn extended_point_equality_handles_scaling() {
        let mut two_bytes = [0u8; 32]; two_bytes[0] = 2;
        let id1 = EdwardsPoint::identity();
        let id2 = EdwardsPoint{
            X: FieldElement::zero(),
            Y: FieldElement::from_bytes(&two_bytes),
            Z: FieldElement::from_bytes(&two_bytes),
            T: FieldElement::zero()
        };
        assert_eq!(id1.ct_eq(&id2).unwrap_u8(), 1u8);
    }

    /// Sanity check for conversion to precomputed points
    #[test]
    #[cfg(feature="precomputed_tables")]
    fn to_affine_niels_clears_denominators() {
        // construct a point as aB so it has denominators (ie. Z != 1)
        let aB = &constants::ED25519_BASEPOINT_TABLE * &A_SCALAR;
        let aB_affine_niels = aB.to_affine_niels();
        let also_aB = (&EdwardsPoint::identity() + &aB_affine_niels).to_extended();
        assert_eq!(     aB.compress(),
                   also_aB.compress());
    }

    /// Test basepoint_mult versus a known scalar multiple from ed25519.py
    #[test]
    #[cfg(feature="precomputed_tables")]
    fn basepoint_mult_vs_ed25519py() {
        let aB = &constants::ED25519_BASEPOINT_TABLE * &A_SCALAR;
        assert_eq!(aB.compress(), A_TIMES_BASEPOINT);
    }

    /// Test that multiplication by the basepoint order kills the basepoint
    #[test]
    #[cfg(feature="precomputed_tables")]
    fn basepoint_mult_by_basepoint_order() {
        let B = &constants::ED25519_BASEPOINT_TABLE;
        let should_be_id = B * &constants::BASEPOINT_ORDER;
        assert!(should_be_id.is_identity());
    }

    /// Test precomputed basepoint mult
    #[test]
    #[cfg(feature="precomputed_tables")]
    fn test_precomputed_basepoint_mult() {
        let table = EdwardsBasepointTable::create(&constants::ED25519_BASEPOINT_POINT);
        let aB_1 = &constants::ED25519_BASEPOINT_TABLE * &A_SCALAR;
        let aB_2 = &table * &A_SCALAR;
        assert_eq!(aB_1.compress(), aB_2.compress());
    }

    /// Test scalar_mul versus a known scalar multiple from ed25519.py
    #[test]
    fn scalar_mul_vs_ed25519py() {
        let aB = &constants::ED25519_BASEPOINT_POINT * &A_SCALAR;
        assert_eq!(aB.compress(), A_TIMES_BASEPOINT);
    }

    /// Test basepoint.double() versus the 2*basepoint constant.
    #[test]
    fn basepoint_double_vs_basepoint2() {
        assert_eq!(constants::ED25519_BASEPOINT_POINT.double().compress(),
                   BASE2_CMPRSSD);
    }

    /// Test that computing 2*basepoint is the same as basepoint.double()
    #[test]
    #[cfg(feature="precomputed_tables")]
    fn basepoint_mult_two_vs_basepoint2() {
        let two = Scalar::from_u64(2);
        let bp2 = &constants::ED25519_BASEPOINT_TABLE * &two;
        assert_eq!(bp2.compress(), BASE2_CMPRSSD);
    }

    /// Check that converting to projective and then back to extended round-trips.
    #[test]
    fn basepoint_projective_extended_round_trip() {
        assert_eq!(constants::ED25519_BASEPOINT_POINT
                       .to_projective().to_extended().compress(),
                   constants::ED25519_BASEPOINT_COMPRESSED);
    }

    /// Test computing 16*basepoint vs mul_by_pow_2(4)
    #[test]
    fn basepoint16_vs_mul_by_pow_2_4() {
        let bp16 = constants::ED25519_BASEPOINT_POINT.mul_by_pow_2(4);
        assert_eq!(bp16.compress(), BASE16_CMPRSSD);
    }

    #[test]
    fn impl_sum() {

        // Test that sum works for non-empty iterators
        let BASE = constants::ED25519_BASEPOINT_POINT;

        let s1 = Scalar::from_u64(999);
        let P1 = &BASE * &s1;

        let s2 = Scalar::from_u64(333);
        let P2 = &BASE * &s2;

        let vec = vec![P1.clone(), P2.clone()];
        let sum: EdwardsPoint = vec.iter().sum();

        assert_eq!(sum, P1 + P2);

        // Test that sum works for the empty iterator
        let empty_vector: Vec<EdwardsPoint> = vec![];
        let sum: EdwardsPoint = empty_vector.iter().sum();

        assert_eq!(sum, EdwardsPoint::identity());

        // Test that sum works on owning iterators
        let s = Scalar::from_u64(2);
        let mapped = vec.iter().map(|x| x * &s);
        let sum: EdwardsPoint = mapped.sum();

        assert_eq!(sum, &P1 * &s + &P2 * &s);
      }


    /// Test that the conditional assignment trait works for AffineNielsPoints.
    #[test]
    fn conditional_assign_for_affine_niels_point() {
        let id     = AffineNielsPoint::identity();
        let mut p1 = AffineNielsPoint::identity();
        let bp     = constants::ED25519_BASEPOINT_POINT.to_affine_niels();

        p1.conditional_assign(&bp, Choice::from(0));
        assert_eq!(p1, id);
        p1.conditional_assign(&bp, Choice::from(1));
        assert_eq!(p1, bp);
    }

    #[test]
    fn is_small_order() {
        // The basepoint has large prime order
        assert!(constants::ED25519_BASEPOINT_POINT.is_small_order() == false);
        // constants::EIGHT_TORSION has all points of small order.
        for torsion_point in &constants::EIGHT_TORSION {
            assert!(torsion_point.is_small_order() == true);
        }
    }

    #[test]
    fn compressed_identity() {
        assert_eq!(EdwardsPoint::identity().compress(),
                   CompressedEdwardsY::identity());
    }

    #[test]
    fn is_identity() {
        assert!(   EdwardsPoint::identity().is_identity() == true);
        assert!(constants::ED25519_BASEPOINT_POINT.is_identity() == false);
    }

    /// Rust's debug builds have overflow and underflow trapping,
    /// and enable `debug_assert!()`.  This performs many scalar
    /// multiplications to attempt to trigger possible overflows etc.
    ///
    /// For instance, the `radix_51` `Mul` implementation for
    /// `FieldElements` requires the input `Limb`s to be bounded by
    /// 2^54, but we cannot enforce this dynamically at runtime, or
    /// statically at compile time (until Rust gets type-level
    /// integers, at which point we can encode "bits of headroom" into
    /// the type system and prove correctness).
    #[test]
    fn monte_carlo_overflow_underflow_debug_assert_test() {
        let mut P = constants::ED25519_BASEPOINT_POINT;
        // N.B. each scalar_mul does 1407 field mults, 1024 field squarings,
        // so this does ~ 1M of each operation.
        for _ in 0..1_000 {
            P *= &A_SCALAR;
        }
    }

    #[test]
    fn scalarmult_extended_point_works_both_ways() {
        let G: EdwardsPoint = constants::ED25519_BASEPOINT_POINT;
        let s: Scalar = A_SCALAR;

        let P1 = &G * &s;
        let P2 = &s * &G;

        assert!(P1.compress().to_bytes() == P2.compress().to_bytes());
    }

    mod vartime {
        use super::super::*;
        use super::{A_SCALAR, B_SCALAR, A_TIMES_BASEPOINT, DOUBLE_SCALAR_MULT_RESULT};

        /// Test double_scalar_mul_vartime vs ed25519.py
        #[test]
        #[cfg(feature="precomputed_tables")]
        fn double_scalar_mul_basepoint_vs_ed25519py() {
            let A = A_TIMES_BASEPOINT.decompress().unwrap();
            let result = vartime::double_scalar_mul_basepoint(&A_SCALAR, &A, &B_SCALAR);
            assert_eq!(result.compress(), DOUBLE_SCALAR_MULT_RESULT);
        }

        #[test]
        fn multiscalar_mul_vs_ed25519py() {
            let A = A_TIMES_BASEPOINT.decompress().unwrap();
            let result = vartime::multiscalar_mul(
                &[A_SCALAR, B_SCALAR],
                &[A, constants::ED25519_BASEPOINT_POINT]
            );
            assert_eq!(result.compress(), DOUBLE_SCALAR_MULT_RESULT);
        }

        #[test]
        fn multiscalar_mul_vartime_vs_consttime() {
            let A = A_TIMES_BASEPOINT.decompress().unwrap();
            let result_vartime = vartime::multiscalar_mul(
                &[A_SCALAR, B_SCALAR],
                &[A, constants::ED25519_BASEPOINT_POINT]
            );
            let result_consttime = multiscalar_mul(
                &[A_SCALAR, B_SCALAR],
                &[A, constants::ED25519_BASEPOINT_POINT]
            );

            assert_eq!(result_vartime.compress(), result_consttime.compress());
        }
    }

    #[cfg(feature = "serde")]
    use serde_cbor;

    #[test]
    #[cfg(feature = "serde")]
    fn serde_cbor_basepoint_roundtrip() {
        let output = serde_cbor::to_vec(&constants::ED25519_BASEPOINT_POINT).unwrap();
        let parsed: EdwardsPoint = serde_cbor::from_slice(&output).unwrap();
        assert_eq!(parsed.compress(), constants::ED25519_BASEPOINT_COMPRESSED);
    }

    #[test]
    #[cfg(feature = "serde")]
    fn serde_cbor_decode_invalid_fails() {
        let mut output = serde_cbor::to_vec(&constants::ED25519_BASEPOINT_POINT).unwrap();
        // CBOR apparently has two bytes of overhead for a 32-byte string.
        // Set the low byte of the compressed point to 1 to make it invalid.
        output[2] = 1;
        let parsed: Result<EdwardsPoint, _> = serde_cbor::from_slice(&output);
        assert!(parsed.is_err());
    }
}
