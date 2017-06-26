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

//! Group operations for Curve25519, in the form of the twisted
//! Edwards curve -x²+y²=1+dx²y² modulo p=2²⁵⁵-19 with
//! parameter d=-121665/121666.
//!
//! # Curve representations
//!
//! Internally, we use several different models for the curve.  Here
//! is a sketch of the relationship between the models, following [a
//! post](https://moderncrypto.org/mail-archive/curves/2016/000807.html)
//! by Ben Smith on the moderncrypto mailing list.
//!
//! Begin with the affine equation for the curve,
//!
//!     -x² + y² = 1 + dx²y².       <span style="float: right">(1)</span>
//!
//! Next, pass to the projective closure 𝗣^1 x 𝗣^1 by setting x=X/Z,
//! y=Y/T.  Clearing denominators gives the model
//!
//!     -X²T² + Y²Z² = Z²T² + dX²Y². <span style="float: right">(2)<span>
//!
//! To map from 𝗣^1 x 𝗣^1, a product of two lines, to 𝗣^3, we use the
//! Segre embedding,
//!
//!     σ : ((X:Z),(Y:T)) ↦ (XY:XT:ZY:ZT).  <span style="float: right">(3)</span>
//!
//! Using coordinates (W₀:W₁:W₂:W₃) for 𝗣^3, the image of σ(𝗣^1 x 𝗣^1)
//! is the surface defined by W₀W₃=W₁W₂, and under σ, equation (2)
//! becomes
//!
//!     -W₁² + W₂² = W₃² + dW₀².   <span style="float: right">(4)</span>
//!
//! Up to variable naming, this is exactly the curve model introduced
//! in ["Twisted Edwards Curves
//! Revisited"](https://www.iacr.org/archive/asiacrypt2008/53500329/53500329.pdf)
//! by Hisil, Wong, Carter, and Dawson.  We can map from 𝗣^3 to 𝗣² by
//! sending (W₀:W₁:W₂:W₃) to (W₁:W₂:W₃).  Notice that
//!
//!     W₁/W₃ = XT/ZT = X/Z = x    <span style="float: right">(5)</span>
//!
//!     W₂/W₃ = ZY/ZT = Y/T = y,   <span style="float: right">(6)</span>
//!
//! so this is the same as if we had started with the affine model (1)
//! and passed to 𝗣^2 by setting `x = W₁/W₃`, `y = W₂/W₃`.  Up to
//! variable naming, this is the projective representation introduced
//! in ["Twisted Edwards Curves"](https://eprint.iacr.org/2008/013).
//!
//! Following the implementation strategy in the ref10 reference
//! implementation for [Ed25519](https://ed25519.cr.yp.to/ed25519-20110926.pdf),
//! we use several different models for curve points:
//!
//! * `CompletedPoint`: points in 𝗣^1 x 𝗣^1;
//! * `ExtendedPoint`: points in 𝗣^3;
//! * `ProjectivePoint`: points in 𝗣^2.
//!
//! Finally, to accelerate additions, we use two cached point formats,
//! one for the affine model and one for the 𝗣^3 model:
//!
//! * `AffineNielsPoint`: `(y+x, y-x, 2dxy)`
//! * `ProjectiveNielsPoint`: `(Y+X, Y-X, Z, 2dXY)`
//!
//! [1]: https://moderncrypto.org/mail-archive/curves/2016/000807.html

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
use core::ops::Index;

use constants;
use field::FieldElement;
use scalar::Scalar;
use subtle::arrays_equal;
use subtle::bytes_equal;
use subtle::CTAssignable;
use subtle::CTEq;
use subtle::CTNegatable;

// ------------------------------------------------------------------------
// Compressed points
// ------------------------------------------------------------------------

/// In "Edwards y" format, the point `(x,y)` on the curve is
/// determined by the `y`-coordinate and the sign of `x`, marshalled
/// into a 32-byte array.
///
/// The first 255 bits of a `CompressedEdwardsY` represent the
/// y-coordinate. The high bit of the 32nd byte gives the sign of `x`.
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
    /// XXX is this useful?
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// Attempt to decompress to an `ExtendedPoint`.
    ///
    /// Returns `None` if the input is not the `y`-coordinate of a
    /// curve point.
    pub fn decompress(&self) -> Option<ExtendedPoint> { // FromBytes()
        let Y = FieldElement::from_bytes(self.as_bytes());
        let Z = FieldElement::one();
        let YY = Y.square();
        let u = &YY - &Z;                    // u =  y²-1
        let v = &(&YY * &constants::d) + &Z; // v = dy²+1
        let (is_nonzero_square, mut X) = FieldElement::sqrt_ratio(&u, &v);

        if is_nonzero_square != 1u8 { return None; }

        // Flip the sign of X if it's not correct
        let compressed_sign_bit = self.as_bytes()[31] >> 7;
        let    current_sign_bit = X.is_negative_ed25519();
        X.conditional_negate(current_sign_bit ^ compressed_sign_bit);

        Some(ExtendedPoint{ X: X, Y: Y, Z: Z, T: &X * &Y })
    }
}

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
// Serde support
// ------------------------------------------------------------------------
// Serializes to and from `ExtendedPoint` directly, doing compression
// and decompression internally.  This means that users can create
// structs containing `ExtendedPoint`s and use Serde's derived
// serializers to serialize those structures.

#[cfg(feature = "serde")]
use serde::{self, Serialize, Deserialize, Serializer, Deserializer};
#[cfg(feature = "serde")]
use serde::de::Visitor;

#[cfg(feature = "serde")]
impl Serialize for ExtendedPoint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_bytes(self.compress_edwards().as_bytes())
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for ExtendedPoint {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        struct ExtendedPointVisitor;

        impl<'de> Visitor<'de> for ExtendedPointVisitor {
            type Value = ExtendedPoint;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid point in Edwards y + sign format")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<ExtendedPoint, E>
                where E: serde::de::Error
            {
                if v.len() == 32 {
                    let arr32 = array_ref!(v, 0, 32); // &[u8;32] from &[u8]
                    CompressedEdwardsY(*arr32)
                        .decompress()
                        .ok_or(serde::de::Error::custom("decompression failed"))
                } else {
                    Err(serde::de::Error::invalid_length(v.len(), &self))
                }
            }
        }

        deserializer.deserialize_bytes(ExtendedPointVisitor)
    }
}

// ------------------------------------------------------------------------
// Internal point representations
// ------------------------------------------------------------------------

/// An `ExtendedPoint` is a point on the curve in 𝗣³(𝔽ₚ).
/// A point (x,y) in the affine model corresponds to (x:y:1:xy).
// XXX members should not be public, but that's needed for the
// constants module. Fix when RFC #1422 lands:
// https://github.com/rust-lang/rust/issues/32409
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct ExtendedPoint {
    pub X: FieldElement,
    pub Y: FieldElement,
    pub Z: FieldElement,
    pub T: FieldElement,
}

/// A `ProjectivePoint` is a point on the curve in 𝗣²(𝔽ₚ).
/// A point (x,y) in the affine model corresponds to (x:y:1).
#[derive(Copy, Clone)]
pub struct ProjectivePoint {
    X: FieldElement,
    Y: FieldElement,
    Z: FieldElement,
}

/// A `CompletedPoint` is a point ((X:Z), (Y:T)) in 𝗣¹(𝔽ₚ)×𝗣¹(𝔽ₚ).
/// A point (x,y) in the affine model corresponds to ((x:1),(y:1)).
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct CompletedPoint {
    pub X: FieldElement,
    pub Y: FieldElement,
    pub Z: FieldElement,
    pub T: FieldElement,
}

/// A pre-computed point in the affine model for the curve, represented as
/// (y+x, y-x, 2dxy).  These precomputations accelerate addition and
/// subtraction, and were introduced by Niels Duif in the ed25519 paper
/// ["High-Speed High-Security Signatures"](https://ed25519.cr.yp.to/ed25519-20110926.pdf).
// Safe to derive Eq because affine coordinates.
#[derive(Copy, Clone, Eq, PartialEq)]
#[allow(missing_docs)]
pub struct AffineNielsPoint {
    pub y_plus_x:  FieldElement,
    pub y_minus_x: FieldElement,
    pub xy2d:      FieldElement,
}

/// A pre-computed point in the P³(𝔽ₚ) model for the curve, represented as
/// (Y+X, Y-X, Z, 2dXY).  These precomputations accelerate addition and
/// subtraction, and were introduced by Niels Duif in the ed25519 paper
/// ["High-Speed High-Security Signatures"](https://ed25519.cr.yp.to/ed25519-20110926.pdf).
#[derive(Copy, Clone)]
pub struct ProjectiveNielsPoint {
    Y_plus_X:  FieldElement,
    Y_minus_X: FieldElement,
    Z:         FieldElement,
    T2d:       FieldElement,
}

// ------------------------------------------------------------------------
// Constructors
// ------------------------------------------------------------------------

/// Trait for curve point types which have an identity constructor.
pub trait Identity {
    /// Returns the identity element of the curve.
    /// Can be used as a constructor.
    fn identity() -> Self;
}

impl Identity for CompressedEdwardsY {
    fn identity() -> CompressedEdwardsY {
        CompressedEdwardsY([1, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0])
    }
}

impl Identity for ExtendedPoint {
    fn identity() -> ExtendedPoint {
        ExtendedPoint{ X: FieldElement::zero(),
                       Y: FieldElement::one(),
                       Z: FieldElement::one(),
                       T: FieldElement::zero() }
    }
}

impl Identity for ProjectivePoint {
    fn identity() -> ProjectivePoint {
        ProjectivePoint{ X: FieldElement::zero(),
                         Y: FieldElement::one(),
                         Z: FieldElement::one() }
    }
}

impl Identity for ProjectiveNielsPoint {
    fn identity() -> ProjectiveNielsPoint {
        ProjectiveNielsPoint{ Y_plus_X:  FieldElement::one(),
                     Y_minus_X: FieldElement::one(),
                     Z:         FieldElement::one(),
                     T2d:       FieldElement::zero() }
    }
}

impl Identity for AffineNielsPoint {
    fn identity() -> AffineNielsPoint {
        AffineNielsPoint{
            y_plus_x:  FieldElement::one(),
            y_minus_x: FieldElement::one(),
            xy2d:      FieldElement::zero(),
        }
    }
}

// ------------------------------------------------------------------------
// Validity checks (for debugging, not CT)
// ------------------------------------------------------------------------

/// Trait for checking whether a point is on the curve
pub trait ValidityCheck {
    /// Checks whether the point is on the curve. Not CT.
    fn is_valid(&self) -> bool;
}

impl ValidityCheck for ProjectivePoint {
    fn is_valid(&self) -> bool {
        // Curve equation is    -x^2 + y^2 = 1 + d*x^2*y^2,
        // homogenized as (-X^2 + Y^2)*Z^2 = Z^4 + d*X^2*Y^2
        let XX = self.X.square();
        let YY = self.Y.square();
        let ZZ = self.Z.square();
        let ZZZZ = ZZ.square();
        let lhs = &(&YY - &XX) * &ZZ;
        let rhs = &ZZZZ + &(&constants::d * &(&XX * &YY));

        lhs == rhs
    }
}

impl ValidityCheck for ExtendedPoint {
    // XXX this should also check that T is correct
    fn is_valid(&self) -> bool {
        self.to_projective().is_valid()
    }
}

// ------------------------------------------------------------------------
// Constant-time assignment
// ------------------------------------------------------------------------

impl CTAssignable for ProjectiveNielsPoint {
    fn conditional_assign(&mut self, other: &ProjectiveNielsPoint, choice: u8) {
        self.Y_plus_X.conditional_assign(&other.Y_plus_X, choice);
        self.Y_minus_X.conditional_assign(&other.Y_minus_X, choice);
        self.Z.conditional_assign(&other.Z, choice);
        self.T2d.conditional_assign(&other.T2d, choice);
    }
}

impl CTAssignable for AffineNielsPoint {
    fn conditional_assign(&mut self, other: &AffineNielsPoint, choice: u8) {
        // PreComputedGroupElementCMove()
        self.y_plus_x.conditional_assign(&other.y_plus_x, choice);
        self.y_minus_x.conditional_assign(&other.y_minus_x, choice);
        self.xy2d.conditional_assign(&other.xy2d, choice);
    }
}

impl CTAssignable for ExtendedPoint {
    fn conditional_assign(&mut self, other: &ExtendedPoint, choice: u8) {
        self.X.conditional_assign(&other.X, choice);
        self.Y.conditional_assign(&other.Y, choice);
        self.Z.conditional_assign(&other.Z, choice);
        self.T.conditional_assign(&other.T, choice);
    }
}

// ------------------------------------------------------------------------
// Constant-time Equality
// ------------------------------------------------------------------------

impl CTEq for ExtendedPoint {
    fn ct_eq(&self, other: &ExtendedPoint) -> u8 {
        arrays_equal(self.compress_edwards().as_bytes(),
                     other.compress_edwards().as_bytes())
    }
}

/// Trait for testing if a curve point is equivalent to the identity point.
pub trait IsIdentity {
    /// Return true if this element is the identity element of the curve.
    fn is_identity(&self) -> bool;
}

/// Implement generic identity equality testing for a point representations
/// which have constant-time equality testing and a defined identity
/// constructor.
impl<T> IsIdentity for T where T: CTEq + Identity {
    fn is_identity(&self) -> bool {
        self.ct_eq(&T::identity()) == 1u8
    }
}

// ------------------------------------------------------------------------
// Point conversions
// ------------------------------------------------------------------------

impl ProjectivePoint {
    /// Convert to the extended twisted Edwards representation of this
    /// point.
    ///
    /// From §3 in [0]:
    ///
    /// Given (X:Y:Z) in Ɛ, passing to Ɛₑ can be performed in 3M+1S by
    /// computing (XZ,YZ,XY,Z²).  (Note that in that paper, points are
    /// (X:Y:T:Z) so this really does match the code below).
    #[allow(dead_code)] // rustc complains this is unused even when it's used
    fn to_extended(&self) -> ExtendedPoint {
        ExtendedPoint{
            X: &self.X * &self.Z,
            Y: &self.Y * &self.Z,
            Z: self.Z.square(),
            T: &self.X * &self.Y,
        }
    }

    /// Convert this point to a `CompressedEdwardsY`
    pub fn compress_edwards(&self) -> CompressedEdwardsY {
        let recip = self.Z.invert();
        let x = &self.X * &recip;
        let y = &self.Y * &recip;
        let mut s: [u8; 32];

        s      =  y.to_bytes();
        s[31] ^= (x.is_negative_ed25519() << 7) as u8;
        CompressedEdwardsY(s)
    }

    /// Convert this point to a `CompressedMontgomeryU`.
    /// Note that this discards the sign.
    ///
    /// # Return
    /// - `None` if `self` is the identity point;
    /// - `Some(CompressedMontgomeryU)` otherwise.
    ///
    pub fn compress_montgomery(&self) -> Option<CompressedMontgomeryU> {
        // u = (1 + y) /  (1 - y)
        // v = sqrt(-486664) * u / x
        //
        // since y = Y/Z, x = X/Z,
        //
        // u = (1 + Y/Z) / (1 - Y/Z);
        //   =   (Z + Y) / (Z - Y);
        //
        // exceptional points:
        // y = 1 <=> Y/Z = 1 <=> Z - Y = 0
        let Z_plus_Y   = &self.Z + &self.Y;
        let Z_minus_Y  = &self.Z - &self.Y;
        let u = &Z_plus_Y * &Z_minus_Y.invert();

        if Z_minus_Y.is_zero() == 0u8 {
            Some(CompressedMontgomeryU(u.to_bytes()))
        } else {
            None
        }
    }
}

impl ExtendedPoint {
    /// Convert to a ProjectiveNielsPoint
    pub fn to_projective_niels(&self) -> ProjectiveNielsPoint {
        ProjectiveNielsPoint{
            Y_plus_X:  &self.Y + &self.X,
            Y_minus_X: &self.Y - &self.X,
            Z:          self.Z,
            T2d:       &self.T * &constants::d2,
        }
    }

    /// Convert the representation of this point from extended Twisted Edwards
    /// coodinates to projective coordinates.
    ///
    /// Given a point in Ɛₑ, we can convert to projective coordinates
    /// cost-free by simply ignoring T.
    fn to_projective(&self) -> ProjectivePoint {
        ProjectivePoint{
            X: self.X,
            Y: self.Y,
            Z: self.Z,
        }
    }

    /// Dehomogenize to a AffineNielsPoint.
    /// Mainly for testing.
    pub fn to_affine_niels(&self) -> AffineNielsPoint {
        let recip = self.Z.invert();
        let x = &self.X * &recip;
        let y = &self.Y * &recip;
        let xy2d = &(&x * &y) * &constants::d2;
        AffineNielsPoint{
            y_plus_x:  &y + &x,
            y_minus_x: &y - &x,
            xy2d:      xy2d
        }
    }

    /// Compress this point to `CompressedEdwardsY` format.
    pub fn compress_edwards(&self) -> CompressedEdwardsY {
        self.to_projective().compress_edwards()
    }

    /// Convert this point to a `CompressedMontgomeryU`.
    /// Note that this discards the sign.
    ///
    /// # Return
    /// - `None` if `self` is the identity point;
    /// - `Some(CompressedMontgomeryU)` otherwise.
    ///
    pub fn compress_montgomery(&self) -> Option<CompressedMontgomeryU> {
        self.to_projective().compress_montgomery()
    }
}

impl CompletedPoint {
    /// Convert to a ProjectivePoint
    pub fn to_projective(&self) -> ProjectivePoint {
        ProjectivePoint{
            X: &self.X * &self.T,
            Y: &self.Y * &self.Z,
            Z: &self.Z * &self.T,
        }
    }

    /// Convert to an ExtendedPoint
    pub fn to_extended(&self) -> ExtendedPoint {
        ExtendedPoint{
            X: &self.X * &self.T,
            Y: &self.Y * &self.Z,
            Z: &self.Z * &self.T,
            T: &self.X * &self.Y,
        }
    }
}

// ------------------------------------------------------------------------
// Doubling
// ------------------------------------------------------------------------

impl ProjectivePoint {
    /// Double this point: return self + self
    pub fn double(&self) -> CompletedPoint { // Double()
        let XX          = self.X.square();
        let YY          = self.Y.square();
        let ZZ2         = self.Z.square2();
        let X_plus_Y    = &self.X + &self.Y;
        let X_plus_Y_sq = X_plus_Y.square();
        let YY_plus_XX  = &YY + &XX;
        let YY_minus_XX = &YY - &XX;

        CompletedPoint{
            X: &X_plus_Y_sq - &YY_plus_XX,
            Y: YY_plus_XX,
            Z: YY_minus_XX,
            T: &ZZ2 - &YY_minus_XX
        }
    }
}

impl ExtendedPoint {
    /// Add this point to itself.
    pub fn double(&self) -> ExtendedPoint {
        self.to_projective().double().to_extended()
    }
}

// ------------------------------------------------------------------------
// Addition and Subtraction
// ------------------------------------------------------------------------

impl<'a, 'b> Add<&'b ProjectiveNielsPoint> for &'a ExtendedPoint {
    type Output = CompletedPoint;

    fn add(self, other: &'b ProjectiveNielsPoint) -> CompletedPoint {
        let Y_plus_X  = &self.Y + &self.X;
        let Y_minus_X = &self.Y - &self.X;
        let PP = &Y_plus_X  * &other.Y_plus_X;
        let MM = &Y_minus_X * &other.Y_minus_X;
        let TT2d = &self.T * &other.T2d;
        let ZZ   = &self.Z * &other.Z;
        let ZZ2  = &ZZ + &ZZ;

        CompletedPoint{
            X: &PP - &MM,
            Y: &PP + &MM,
            Z: &ZZ2 + &TT2d,
            T: &ZZ2 - &TT2d
        }
    }
}

impl<'a, 'b> Sub<&'b ProjectiveNielsPoint> for &'a ExtendedPoint {
    type Output = CompletedPoint;

    fn sub(self, other: &'b ProjectiveNielsPoint) -> CompletedPoint {
        let Y_plus_X  = &self.Y + &self.X;
        let Y_minus_X = &self.Y - &self.X;
        let PM = &Y_plus_X * &other.Y_minus_X;
        let MP = &Y_minus_X  * &other.Y_plus_X;
        let TT2d = &self.T * &other.T2d;
        let ZZ   = &self.Z * &other.Z;
        let ZZ2  = &ZZ + &ZZ;

        CompletedPoint{
            X: &PM - &MP,
            Y: &PM + &MP,
            Z: &ZZ2 - &TT2d,
            T: &ZZ2 + &TT2d
        }
    }
}

impl<'a, 'b> Add<&'b AffineNielsPoint> for &'a ExtendedPoint {
    type Output = CompletedPoint;

    fn add(self, other: &'b AffineNielsPoint) -> CompletedPoint {
        let Y_plus_X  = &self.Y + &self.X;
        let Y_minus_X = &self.Y - &self.X;
        let PP        = &Y_plus_X  * &other.y_plus_x;
        let MM        = &Y_minus_X * &other.y_minus_x;
        let Txy2d     = &self.T * &other.xy2d;
        let Z2        = &self.Z + &self.Z;

        CompletedPoint{
            X: &PP - &MM,
            Y: &PP + &MM,
            Z: &Z2 + &Txy2d,
            T: &Z2 - &Txy2d
        }
    }
}

impl<'a, 'b> Sub<&'b AffineNielsPoint> for &'a ExtendedPoint {
    type Output = CompletedPoint;

    fn sub(self, other: &'b AffineNielsPoint) -> CompletedPoint {
        let Y_plus_X  = &self.Y + &self.X;
        let Y_minus_X = &self.Y - &self.X;
        let PM        = &Y_plus_X  * &other.y_minus_x;
        let MP        = &Y_minus_X * &other.y_plus_x;
        let Txy2d     = &self.T * &other.xy2d;
        let Z2        = &self.Z + &self.Z;

        CompletedPoint{
            X: &PM - &MP,
            Y: &PM + &MP,
            Z: &Z2 - &Txy2d,
            T: &Z2 + &Txy2d
        }
    }
}

impl<'a, 'b> Add<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;
    fn add(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        (self + &other.to_projective_niels()).to_extended()
    }
}

impl<'b> AddAssign<&'b ExtendedPoint> for ExtendedPoint {
    fn add_assign(&mut self, _rhs: &'b ExtendedPoint) {
        *self = (self as &ExtendedPoint) + _rhs;
    }
}

impl<'a, 'b> Sub<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;
    fn sub(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        (self - &other.to_projective_niels()).to_extended()
    }
}

impl<'b> SubAssign<&'b ExtendedPoint> for ExtendedPoint {
    fn sub_assign(&mut self, _rhs: &'b ExtendedPoint) {
        *self = (self as &ExtendedPoint) - _rhs;
    }
}

// ------------------------------------------------------------------------
// Negation
// ------------------------------------------------------------------------

impl<'a> Neg for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    fn neg(self) -> ExtendedPoint {
        ExtendedPoint{
            X: -(&self.X),
            Y:  self.Y,
            Z:  self.Z,
            T: -(&self.T),
        }
    }
}

impl<'a> Neg for &'a ProjectiveNielsPoint {
    type Output = ProjectiveNielsPoint;

    fn neg(self) -> ProjectiveNielsPoint {
        ProjectiveNielsPoint{
            Y_plus_X:   self.Y_minus_X,
            Y_minus_X:  self.Y_plus_X,
            Z:          self.Z,
            T2d:        -(&self.T2d),
        }
    }
}


impl<'a> Neg for &'a AffineNielsPoint {
    type Output = AffineNielsPoint;

    fn neg(self) -> AffineNielsPoint {
        AffineNielsPoint{
            y_plus_x:   self.y_minus_x,
            y_minus_x:  self.y_plus_x,
            xy2d:       -(&self.xy2d)
        }
    }
}

// ------------------------------------------------------------------------
// Scalar multiplication
// ------------------------------------------------------------------------

impl<'b> MulAssign<&'b Scalar> for ExtendedPoint {
    fn mul_assign(&mut self, scalar: &'b Scalar) {
        let result = (self as &ExtendedPoint) * scalar;
        *self = result;
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a ExtendedPoint {
    type Output = ExtendedPoint;
    /// Scalar multiplication: compute `scalar * self`.
    ///
    /// Uses a window of size 4.  Note: for scalar multiplication of
    /// the basepoint, `basepoint_mult` is approximately 4x faster.
    fn mul(self, scalar: &'b Scalar) -> ExtendedPoint {
        let A = self.to_projective_niels();
        let mut As: [ProjectiveNielsPoint; 8] = [A; 8];
        for i in 0..7 {
            As[i+1] = (self + &As[i]).to_extended().to_projective_niels();
        }
        let e = scalar.to_radix_16();
        let mut h = ExtendedPoint::identity();
        let mut t: CompletedPoint;
        for i in (0..64).rev() {
            h = h.mult_by_pow_2(4);
            t = &h + &select_precomputed_point(e[i], &As);
            h = t.to_extended();
        }
        h
    }
}

impl<'a, 'b> Mul<&'b ExtendedPoint> for &'a Scalar {
    type Output = ExtendedPoint;

    /// Scalar multiplication: compute `self * point`.
    ///
    /// Uses a window of size 4.  Note: for scalar multiplication of
    /// the basepoint, `basepoint_mult` is approximately 4x faster.
    fn mul(self, point: &'b ExtendedPoint) -> ExtendedPoint {
        point * &self
    }
}


/// Precomputation
#[derive(Clone)]
pub struct EdwardsBasepointTable(pub [[AffineNielsPoint; 8]; 32]);

impl<'a, 'b> Mul<&'b Scalar> for &'a EdwardsBasepointTable {
    type Output = ExtendedPoint;

    /// Construct an `ExtendedPoint` from a `Scalar`, `scalar`, by
    /// computing the multiple `aB` of the basepoint `B`.
    ///
    /// Precondition: the scalar must be reduced.
    ///
    /// The computation proceeds as follows, as described on page 13
    /// of the Ed25519 paper.  Write the scalar `a` in radix 16 with
    /// coefficients in [-8,8), i.e.,
    ///
    ///    a = a_0 + a_1*16^1 + ... + a_63*16^63,
    ///
    /// with -8 ≤ a_i < 8.  Then
    ///
    ///    a*B = a_0*B + a_1*16^1*B + ... + a_63*16^63*B.
    ///
    /// Grouping even and odd coefficients gives
    ///
    ///    a*B =       a_0*16^0*B + a_2*16^2*B + ... + a_62*16^62*B
    ///              + a_1*16^1*B + a_3*16^3*B + ... + a_63*16^63*B
    ///        =      (a_0*16^0*B + a_2*16^2*B + ... + a_62*16^62*B)
    ///          + 16*(a_1*16^0*B + a_3*16^2*B + ... + a_63*16^62*B).
    ///
    /// We then use the `select_precomputed_point` function, which
    /// takes `-8 ≤ x < 8` and `[16^2i * B, ..., 8 * 16^2i * B]`,
    /// and returns `x * 16^2i * B` in constant time.
    fn mul(self, scalar: &'b Scalar) -> ExtendedPoint {
        let e = scalar.to_radix_16();
        let mut h = ExtendedPoint::identity();
        let mut t: CompletedPoint;

        for i in (0..64).filter(|x| x % 2 == 1) {
            t = &h + &select_precomputed_point(e[i], &self.0[i/2]);
            h = t.to_extended();
        }

        h = h.mult_by_pow_2(4);

        for i in (0..64).filter(|x| x % 2 == 0) {
            t = &h + &select_precomputed_point(e[i], &self.0[i/2]);
            h = t.to_extended();
        }

        h
    }
}

impl<'a, 'b> Mul<&'a EdwardsBasepointTable> for &'b Scalar {
    type Output = ExtendedPoint;

    /// Construct an `ExtendedPoint` by via this `Scalar` times
    /// a the basepoint, `B` included in a precomputed `basepoint_table`.
    ///
    /// Precondition: this scalar must be reduced.
    ///
    /// The computation proceeds as follows, as described on page 13
    /// of the Ed25519 paper.  Write this scalar `a` in radix 16 with
    /// coefficients in [-8,8), i.e.,
    ///
    ///    a = a_0 + a_1*16^1 + ... + a_63*16^63,
    ///
    /// with -8 ≤ a_i < 8.  Then
    ///
    ///    a*B = a_0*B + a_1*16^1*B + ... + a_63*16^63*B.
    ///
    /// Grouping even and odd coefficients gives
    ///
    ///    a*B =       a_0*16^0*B + a_2*16^2*B + ... + a_62*16^62*B
    ///              + a_1*16^1*B + a_3*16^3*B + ... + a_63*16^63*B
    ///        =      (a_0*16^0*B + a_2*16^2*B + ... + a_62*16^62*B)
    ///          + 16*(a_1*16^0*B + a_3*16^2*B + ... + a_63*16^62*B).
    ///
    /// We then use the `select_precomputed_point` function, which
    /// takes `-8 ≤ x < 8` and `[16^2i * B, ..., 8 * 16^2i * B]`,
    /// and returns `x * 16^2i * B` in constant time.
    fn mul(self, basepoint_table: &'a EdwardsBasepointTable) -> ExtendedPoint {
        basepoint_table * &self
    }
}

impl EdwardsBasepointTable {
    /// Create a table of precomputed multiples of `basepoint`.
    pub fn create(basepoint: &ExtendedPoint) -> EdwardsBasepointTable {
        // Create the table storage
        // XXX can we skip the initialization without too much unsafety?
        // stick 30K on the stack and call it a day.
        let mut table = EdwardsBasepointTable([[AffineNielsPoint::identity(); 8]; 32]);
        let mut P = *basepoint;
        for i in 0..32 {
            // P = (16^2)^i * B
            let mut jP = P.to_affine_niels();
            for j in 1..9 {
                // table[i][j-1] is supposed to be j*(16^2)^i*B
                table.0[i][j-1] = jP;
                jP = (&P + &jP).to_extended().to_affine_niels();
            }
            P = P.mult_by_pow_2(8);
        }
        table
    }

    /// Get the basepoint for this table as an `ExtendedPoint`.
    pub fn basepoint(&self) -> ExtendedPoint {
        // self.0[0][0] has 1*(16^2)^0*B, but as an `AffineNielsPoint`
        // Add identity to convert to extended.
        (&ExtendedPoint::identity() + &self.0[0][0]).to_extended()
    }
}

impl ExtendedPoint {
    /// Multiply by the cofactor: compute `8 * self`.
    ///
    /// Convenience wrapper around `mult_by_pow_2`.
    #[inline]
    pub fn mult_by_cofactor(&self) -> ExtendedPoint {
        self.mult_by_pow_2(3)
    }

    /// Compute `2^k * self` by successive doublings.
    /// Requires `k > 0`.
    #[inline]
    pub fn mult_by_pow_2(&self, k: u32) -> ExtendedPoint {
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
    /// The order of the group of points on the curve Ɛ is |Ɛ| = 8q.  Thus, to
    /// check if a point P is of small order, we multiply by 8 and then test
    /// if the result is equal to the identity.
    ///
    /// # Return
    ///
    /// True if it is of small order; false otherwise.
    pub fn is_small_order(&self) -> bool {
        self.mult_by_cofactor().is_identity()
    }
}

/// Given precomputed points `[P, 2P, 3P, ..., 8P]`, as well as `-8 ≤
/// x ≤ 8`, compute `x * B` in constant time, i.e., without branching
/// on x or using it as an array index.
fn select_precomputed_point<T>(x: i8, points: &[T; 8]) -> T
    where T: Identity + CTAssignable, for<'a> &'a T: Neg<Output=T>
{
    debug_assert!(x >= -8); debug_assert!(x <= 8);

    // Compute xabs = |x|
    let xmask = x >> 7;
    let xabs  = (x + xmask) ^ xmask;

    // Set t = 0 * P = identity
    let mut t = T::identity();
    for j in 1..9 {
        // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
        t.conditional_assign(&points[j-1],
                             bytes_equal(xabs as u8, j as u8));
    }
    // Now t == |x| * P.

    let neg_mask = (xmask & 1) as u8;
    t.conditional_negate(neg_mask);
    // Now t == x * P.

    t
}

// ------------------------------------------------------------------------
// Elligator2 (uniform encoding/decoding of curve points)
// ------------------------------------------------------------------------

impl ExtendedPoint {
    /// Use Elligator2 to try to convert `self` to a uniformly random
    /// string.
    ///
    /// Returns `Some<[u8;32]>` if `self` is in the image of the
    /// Elligator2 map.  For a random point on the curve, this happens
    /// with probability 1/2.  Otherwise, returns `None`.
    pub fn to_uniform_representative(&self) -> Option<[u8; 32]> {
        unimplemented!();
    }

    /// Use Elligator2 to convert a uniformly random string to a curve
    /// point.
    #[allow(unused_variables)] // REMOVE WHEN IMPLEMENTED
    pub fn from_uniform_representative(bytes: &[u8; 32]) -> ExtendedPoint {
        unimplemented!();
    }
}

// ------------------------------------------------------------------------
// Debug traits
// ------------------------------------------------------------------------

impl Debug for ExtendedPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "ExtendedPoint(\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?},\n\tT: {:?}\n)",
               &self.X, &self.Y, &self.Z, &self.T)
    }
}

impl Debug for ProjectivePoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "ProjectivePoint(\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?}\n)",
               &self.X, &self.Y, &self.Z)
    }
}

impl Debug for CompletedPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "CompletedPoint(\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?},\n\tT: {:?}\n)",
               &self.X, &self.Y, &self.Z, &self.T)
    }
}

impl Debug for AffineNielsPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "AffineNielsPoint(\n\ty_plus_x: {:?},\n\ty_minus_x: {:?},\n\txy2d: {:?}\n)",
               &self.y_plus_x, &self.y_minus_x, &self.xy2d)
    }
}

impl Debug for ProjectiveNielsPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "ProjectiveNielsPoint(\n\tY_plus_X: {:?},\n\tY_minus_X: {:?},\n\tZ: {:?},\n\tT2d: {:?}\n)",
               &self.Y_plus_X, &self.Y_minus_X, &self.Z, &self.T2d)
    }
}

// ------------------------------------------------------------------------
// Variable-time functions
// ------------------------------------------------------------------------

pub mod vartime {
    //! Variable-time operations on curve points, useful for non-secret data.
    use super::*;

    /// Holds odd multiples 1A, 3A, ..., 15A of a point A.
    struct OddMultiples([ProjectiveNielsPoint; 8]);

    impl OddMultiples {
        fn create(A: &ExtendedPoint) -> OddMultiples {
            let mut Ai = [ProjectiveNielsPoint::identity(); 8];
            let A2 = A.double();
            Ai[0]  = A.to_projective_niels();
            for i in 0..7 {
                Ai[i+1] = (&A2 + &Ai[i]).to_extended().to_projective_niels();
            }
            // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
            OddMultiples(Ai)
        }
    }

    impl Index<usize> for OddMultiples {
        type Output = ProjectiveNielsPoint;

        fn index(&self, _index: usize) -> &ProjectiveNielsPoint {
            &(self.0[_index])
        }
    }

    /// Given a vector of public scalars and a vector of (possibly secret)
    /// points, compute `c_1 P_1 + ... + c_n P_n`.
    ///
    /// # Input
    ///
    /// A vector of `Scalar`s and a vector of `ExtendedPoints`.  It is an
    /// error to call this function with two vectors of different lengths.
    #[cfg(any(feature = "alloc", feature = "std"))]
    pub fn k_fold_scalar_mult<'a, 'b, I, J>(scalars: I, points: J) -> ExtendedPoint
        where I: IntoIterator<Item = &'a Scalar>,
              J: IntoIterator<Item = &'b ExtendedPoint>
    {
        //assert_eq!(scalars.len(), points.len());

        let nafs: Vec<_> = scalars.into_iter()
            .map(|c| c.non_adjacent_form()).collect();
        let odd_multiples: Vec<_> = points.into_iter()
            .map(|P| OddMultiples::create(P)).collect();

        let mut r = ProjectivePoint::identity();

        for i in (0..255).rev() {
            let mut t = r.double();

            for (naf, odd_multiple) in nafs.iter().zip(odd_multiples.iter()) {
                if naf[i] > 0 {
                    t = &t.to_extended() + &odd_multiple[( naf[i]/2) as usize];
                } else if naf[i] < 0 {
                    t = &t.to_extended() - &odd_multiple[(-naf[i]/2) as usize];
                }
            }

            r = t.to_projective();
        }

        r.to_extended()
    }

    /// Given a point `A` and scalars `a` and `b`, compute the point
    /// `aA+bB`, where `B` is the Ed25519 basepoint (i.e., `B = (x,4/5)`
    /// with x positive).
    pub fn double_scalar_mult_basepoint(a: &Scalar,
                                        A: &ExtendedPoint,
                                        b: &Scalar) -> ProjectivePoint {
        let a_naf = a.non_adjacent_form();
        let b_naf = b.non_adjacent_form();

        // Find starting index
        let mut i: usize = 255;
        for j in (0..255).rev() {
            i = j;
            if a_naf[i] != 0 || b_naf[i] != 0 {
                break;
            }
        }

        let odd_multiples_of_A = OddMultiples::create(A);

        let mut r = ProjectivePoint::identity();
        loop {
            let mut t = r.double();

            if a_naf[i] > 0 {
                t = &t.to_extended() + &odd_multiples_of_A[( a_naf[i]/2) as usize];
            } else if a_naf[i] < 0 {
                t = &t.to_extended() - &odd_multiples_of_A[(-a_naf[i]/2) as usize];
            }

            if b_naf[i] > 0 {
                t = &t.to_extended() + &constants::bi[( b_naf[i]/2) as usize];
            } else if b_naf[i] < 0 {
                t = &t.to_extended() - &constants::bi[(-b_naf[i]/2) as usize];
            }

            r = t.to_projective();

            if i == 0 {
                break;
            }
            i -= 1;
        }

        r
    }

}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    #[cfg(feature = "yolocrypto")]
    use decaf::DecafPoint;
    use field::FieldElement;
    use scalar::Scalar;
    use subtle::CTAssignable;
    use constants;
    use super::*;

    /// The X25519 basepoint, in compressed Montgomery form.
    static BASE_CMPRSSD_MONTY: CompressedMontgomeryU =
        CompressedMontgomeryU([0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                               0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                               0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                               0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);

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
    pub static A_SCALAR: Scalar = Scalar([
        0x1a, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d,
        0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8, 0x26, 0x4d,
        0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1,
        0x58, 0x9e, 0x7b, 0x7f, 0x23, 0x76, 0xef, 0x09]);

    /// 2506056684125797857694181776241676200180934651973138769173342316833279714961
    pub static B_SCALAR: Scalar = Scalar([
        0x91, 0x26, 0x7a, 0xcf, 0x25, 0xc2, 0x09, 0x1b,
        0xa2, 0x17, 0x74, 0x7b, 0x66, 0xf0, 0xb3, 0x2e,
        0x9d, 0xf2, 0xa5, 0x67, 0x41, 0xcf, 0xda, 0xc4,
        0x56, 0xa7, 0xd4, 0xaa, 0xb8, 0x60, 0x8a, 0x05]);

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

    /// Test Montgomery conversion against the X25519 basepoint.
    #[test]
    fn basepoint_to_montgomery() {
        assert_eq!(constants::ED25519_BASEPOINT.compress_montgomery().unwrap(),
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

    /// Test round-trip decompression for the basepoint.
    #[test]
    fn basepoint_decompression_compression() {
        let base_X = FieldElement::from_bytes(&BASE_X_COORD_BYTES);
        let bp = constants::BASE_CMPRSSD.decompress().unwrap();
        assert!(bp.is_valid());
        // Check that decompression actually gives the correct X coordinate
        assert_eq!(base_X, bp.X);
        assert_eq!(bp.compress_edwards(), constants::BASE_CMPRSSD);
    }

    /// Test sign handling in decompression
    #[test]
    fn decompression_sign_handling() {
        // Manually set the high bit of the last byte to flip the sign
        let mut minus_basepoint_bytes = constants::BASE_CMPRSSD.as_bytes().clone();
        minus_basepoint_bytes[31] |= 1 << 7;
        let minus_basepoint = CompressedEdwardsY(minus_basepoint_bytes)
                              .decompress().unwrap();
        // Test projective coordinates exactly since we know they should
        // only differ by a flipped sign.
        assert_eq!(minus_basepoint.X, -(&constants::ED25519_BASEPOINT.X));
        assert_eq!(minus_basepoint.Y,    constants::ED25519_BASEPOINT.Y);
        assert_eq!(minus_basepoint.Z,    constants::ED25519_BASEPOINT.Z);
        assert_eq!(minus_basepoint.T, -(&constants::ED25519_BASEPOINT.T));
    }

    /// Test that computing 1*basepoint gives the correct basepoint.
    #[test]
    fn basepoint_mult_one_vs_basepoint() {
        let bp = &constants::ED25519_BASEPOINT_TABLE * &Scalar::one();
        let compressed = bp.compress_edwards();
        assert_eq!(compressed, constants::BASE_CMPRSSD);
    }

    /// Test that `EdwardsBasepointTable::basepoint()` gives the correct basepoint.
    #[test]
    fn basepoint_table_basepoint_function_correct() {
        let bp = constants::ED25519_BASEPOINT_TABLE.basepoint();
        assert_eq!(bp.compress_edwards(), constants::BASE_CMPRSSD);
    }

    /// Test `impl Add<ExtendedPoint> for ExtendedPoint`
    /// using basepoint + basepoint versus the 2*basepoint constant.
    #[test]
    fn basepoint_plus_basepoint_vs_basepoint2() {
        let bp = constants::ED25519_BASEPOINT;
        let bp_added = &bp + &bp;
        assert_eq!(bp_added.compress_edwards(), BASE2_CMPRSSD);
    }

    /// Test `impl Add<ProjectiveNielsPoint> for ExtendedPoint`
    /// using the basepoint, basepoint2 constants
    #[test]
    fn basepoint_plus_basepoint_projective_niels_vs_basepoint2() {
        let bp = constants::ED25519_BASEPOINT;
        let bp_added = (&bp + &bp.to_projective_niels()).to_extended();
        assert_eq!(bp_added.compress_edwards(), BASE2_CMPRSSD);
    }

    /// Test `impl Add<AffineNielsPoint> for ExtendedPoint`
    /// using the basepoint, basepoint2 constants
    #[test]
    fn basepoint_plus_basepoint_affine_niels_vs_basepoint2() {
        let bp = constants::ED25519_BASEPOINT;
        let bp_affine_niels = bp.to_affine_niels();
        let bp_added = (&bp + &bp_affine_niels).to_extended();
        assert_eq!(bp_added.compress_edwards(), BASE2_CMPRSSD);
    }

    /// Check that equality of `ExtendedPoints` handles projective
    /// coordinates correctly.
    #[test]
    fn extended_point_equality_handles_scaling() {
        let mut two_bytes = [0u8; 32]; two_bytes[0] = 2;
        let id1 = ExtendedPoint::identity();
        let id2 = ExtendedPoint{
            X: FieldElement::zero(),
            Y: FieldElement::from_bytes(&two_bytes),
            Z: FieldElement::from_bytes(&two_bytes),
            T: FieldElement::zero()
        };
        assert!(id1.ct_eq(&id2) == 1u8);
    }

    /// Sanity check for conversion to precomputed points
    #[test]
    fn to_affine_niels_clears_denominators() {
        // construct a point as aB so it has denominators (ie. Z != 1)
        let aB = &constants::ED25519_BASEPOINT_TABLE * &A_SCALAR;
        let aB_affine_niels = aB.to_affine_niels();
        let also_aB = (&ExtendedPoint::identity() + &aB_affine_niels).to_extended();
        assert_eq!(     aB.compress_edwards(),
                   also_aB.compress_edwards());
    }

    /// Test basepoint_mult versus a known scalar multiple from ed25519.py
    #[test]
    fn basepoint_mult_vs_ed25519py() {
        let aB = &constants::ED25519_BASEPOINT_TABLE * &A_SCALAR;
        assert_eq!(aB.compress_edwards(), A_TIMES_BASEPOINT);
    }

    /// Test that multiplication by the basepoint order kills the basepoint
    #[test]
    fn basepoint_mult_by_basepoint_order() {
        let B = &constants::ED25519_BASEPOINT_TABLE;
        let should_be_id = B * &constants::l;
        assert!(should_be_id.is_identity());
    }

    /// Test precomputed basepoint mult
    #[test]
    #[cfg(feature="basepoint_table_creation")]
    fn test_precomputed_basepoint_mult() {
        let table = EdwardsBasepointTable::create(&constants::ED25519_BASEPOINT);
        let aB_1 = &constants::ED25519_BASEPOINT_TABLE * &A_SCALAR;
        let aB_2 = &table * &A_SCALAR;
        assert_eq!(aB_1.compress_edwards(), aB_2.compress_edwards());
    }

    /// Test scalar_mult versus a known scalar multiple from ed25519.py
    #[test]
    fn scalar_mult_vs_ed25519py() {
        let aB = &constants::ED25519_BASEPOINT * &A_SCALAR;
        assert_eq!(aB.compress_edwards(), A_TIMES_BASEPOINT);
    }

    /// Test basepoint.double() versus the 2*basepoint constant.
    #[test]
    fn basepoint_double_vs_basepoint2() {
        assert_eq!(constants::ED25519_BASEPOINT.double().compress_edwards(),
                   BASE2_CMPRSSD);
    }

    /// Test that computing 2*basepoint is the same as basepoint.double()
    #[test]
    fn basepoint_mult_two_vs_basepoint2() {
        let mut two_bytes = [0u8; 32]; two_bytes[0] = 2;
        let bp2 = &constants::ED25519_BASEPOINT_TABLE * &Scalar(two_bytes);
        assert_eq!(bp2.compress_edwards(), BASE2_CMPRSSD);
    }

    /// Check that converting to projective and then back to extended round-trips.
    #[test]
    fn basepoint_projective_extended_round_trip() {
        assert_eq!(constants::ED25519_BASEPOINT
                       .to_projective().to_extended().compress_edwards(),
                   constants::BASE_CMPRSSD);
    }

    /// Test computing 16*basepoint vs mult_by_pow_2(4)
    #[test]
    fn basepoint16_vs_mult_by_pow_2_4() {
        let bp16 = constants::ED25519_BASEPOINT.mult_by_pow_2(4);
        assert_eq!(bp16.compress_edwards(), BASE16_CMPRSSD);
    }

    /// Test that the conditional assignment trait works for AffineNielsPoints.
    #[test]
    fn conditional_assign_for_affine_niels_point() {
        let id     = AffineNielsPoint::identity();
        let mut p1 = AffineNielsPoint::identity();
        let bp     = constants::ED25519_BASEPOINT.to_affine_niels();

        p1.conditional_assign(&bp, 0);
        assert_eq!(p1, id);
        p1.conditional_assign(&bp, 1);
        assert_eq!(p1, bp);
    }

    #[test]
    fn is_small_order() {
        // The basepoint has large prime order
        assert!(constants::ED25519_BASEPOINT.is_small_order() == false);
        // constants::EIGHT_TORSION has all points of small order.
        for torsion_point in &constants::EIGHT_TORSION {
            assert!(torsion_point.is_small_order() == true);
        }
    }

    #[test]
    fn compressed_identity() {
        assert_eq!(ExtendedPoint::identity().compress_edwards(),
                   CompressedEdwardsY::identity());
    }

    #[test]
    fn is_identity() {
        assert!(   ExtendedPoint::identity().is_identity() == true);
        assert!(constants::ED25519_BASEPOINT.is_identity() == false);
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
        let mut P = constants::ED25519_BASEPOINT;
        // N.B. each scalar_mult does 1407 field mults, 1024 field squarings,
        // so this does ~ 1M of each operation.
        for _ in 0..1_000 {
            P *= &A_SCALAR;
        }
    }

    #[test]
    fn scalarmult_extended_point_works_both_ways() {
        let G: ExtendedPoint = constants::ED25519_BASEPOINT;
        let s: Scalar = A_SCALAR;

        let P1 = &G * &s;
        let P2 = &s * &G;

        assert!(P1.compress_edwards().to_bytes() == P2.compress_edwards().to_bytes());
    }

    #[test]
    #[cfg(feature = "yolocrypto")]
    fn scalarmult_decafpoint_works_both_ways() {
        let P: DecafPoint = DecafPoint(constants::ED25519_BASEPOINT);
        let s: Scalar = A_SCALAR;

        let P1 = &P * &s;
        let P2 = &s * &P;

        assert!(P1.compress().as_bytes() == P2.compress().as_bytes());
    }

    mod vartime {
        use super::super::*;
        use super::{A_SCALAR, B_SCALAR, A_TIMES_BASEPOINT, DOUBLE_SCALAR_MULT_RESULT};

        /// Test double_scalar_mult_vartime vs ed25519.py
        #[test]
        fn double_scalar_mult_basepoint_vs_ed25519py() {
            let A = A_TIMES_BASEPOINT.decompress().unwrap();
            let result = vartime::double_scalar_mult_basepoint(&A_SCALAR, &A, &B_SCALAR);
            assert_eq!(result.compress_edwards(), DOUBLE_SCALAR_MULT_RESULT);
        }

        #[test]
        fn k_fold_scalar_mult_vs_ed25519py() {
            let A = A_TIMES_BASEPOINT.decompress().unwrap();
            let result = vartime::k_fold_scalar_mult(
                &[A_SCALAR, B_SCALAR],
                &[A, constants::ED25519_BASEPOINT]
            );
            assert_eq!(result.compress_edwards(), DOUBLE_SCALAR_MULT_RESULT);
        }
    }

    #[cfg(feature = "serde")]
    use serde_cbor;

    #[test]
    #[cfg(feature = "serde")]
    fn serde_cbor_basepoint_roundtrip() {
        let output = serde_cbor::to_vec(&constants::ED25519_BASEPOINT).unwrap();
        let parsed: ExtendedPoint = serde_cbor::from_slice(&output).unwrap();
        assert_eq!(parsed.compress_edwards(), constants::BASE_CMPRSSD);
    }

    #[test]
    #[cfg(feature = "serde")]
    fn serde_cbor_decode_invalid_fails() {
        let mut output = serde_cbor::to_vec(&constants::ED25519_BASEPOINT).unwrap();
        // CBOR apparently has two bytes of overhead for a 32-byte string.
        // Set the low byte of the compressed point to 1 to make it invalid.
        output[2] = 1;
        let parsed: Result<ExtendedPoint, _> = serde_cbor::from_slice(&output);
        assert!(parsed.is_err());
    }
}

// ------------------------------------------------------------------------
// Benchmarks
// ------------------------------------------------------------------------

#[cfg(all(test, feature = "bench"))]
mod bench {
    use rand::OsRng;
    use test::Bencher;
    use constants;
    use super::*;
    use super::test::A_SCALAR;

    #[bench]
    fn edwards_decompress(b: &mut Bencher) {
        let B = &constants::BASE_CMPRSSD;
        b.iter(|| B.decompress().unwrap());
    }

    #[bench]
    fn edwards_compress(b: &mut Bencher) {
        let B = &constants::ED25519_BASEPOINT;
        b.iter(|| B.compress_edwards());
    }

    #[bench]
    fn basepoint_mult(b: &mut Bencher) {
        let B = &constants::ED25519_BASEPOINT_TABLE;
        b.iter(|| B * &A_SCALAR);
    }

    #[bench]
    fn scalar_mult(b: &mut Bencher) {
        let B = &constants::ED25519_BASEPOINT;
        b.iter(|| B * &A_SCALAR);
    }

    #[bench]
    fn bench_select_precomputed_point(b: &mut Bencher) {
        b.iter(|| select_precomputed_point(0, &constants::ED25519_BASEPOINT_TABLE.0[0]));
    }

    #[bench]
    fn add_extended_and_projective_niels_output_completed(b: &mut Bencher) {
        let p1 = constants::ED25519_BASEPOINT;
        let p2 = constants::ED25519_BASEPOINT.to_projective_niels();

        b.iter(|| &p1 + &p2);
    }

    #[bench]
    fn add_extended_and_projective_niels_output_extended(b: &mut Bencher) {
        let p1 = constants::ED25519_BASEPOINT;
        let p2 = constants::ED25519_BASEPOINT.to_projective_niels();

        b.iter(|| (&p1 + &p2).to_extended());
    }

    #[bench]
    fn add_extended_and_affine_niels_output_completed(b: &mut Bencher) {
        let p1 = constants::ED25519_BASEPOINT;
        let p2 = constants::ED25519_BASEPOINT.to_affine_niels();

        b.iter(|| &p1 + &p2);
    }

    #[bench]
    fn add_extended_and_affine_niels_output_extended(b: &mut Bencher) {
        let p1 = constants::ED25519_BASEPOINT;
        let p2 = constants::ED25519_BASEPOINT.to_affine_niels();

        b.iter(|| (&p1 + &p2).to_extended());
    }

    #[bench]
    fn projective_double_output_completed(b: &mut Bencher) {
        let p1 = constants::ED25519_BASEPOINT.to_projective();

        b.iter(|| p1.double());
    }

    #[bench]
    fn extended_double_output_extended(b: &mut Bencher) {
        let p1 = constants::ED25519_BASEPOINT;

        b.iter(|| p1.double());
    }

    #[bench]
    fn mult_by_cofactor(b: &mut Bencher) {
        let p1 = constants::ED25519_BASEPOINT;

        b.iter(|| p1.mult_by_cofactor());
    }

    #[cfg(feature="basepoint_table_creation")]
    #[bench]
    fn create_basepoint_table(b: &mut Bencher) {
        let aB = &constants::ED25519_BASEPOINT_TABLE * &A_SCALAR;
        b.iter(|| EdwardsBasepointTable::create(&aB));
    }

    mod vartime {
        use super::super::*;
        use super::super::test::{A_SCALAR, B_SCALAR, A_TIMES_BASEPOINT};
        use super::{Bencher, OsRng};

        #[bench]
        fn bench_double_scalar_mult_basepoint(b: &mut Bencher) {
            let A = A_TIMES_BASEPOINT.decompress().unwrap();
            b.iter(|| vartime::double_scalar_mult_basepoint(&A_SCALAR, &A, &B_SCALAR));
        }

        #[bench]
        fn ten_fold_scalar_mult(b: &mut Bencher) {
            let mut csprng: OsRng = OsRng::new().unwrap();
            // Create 10 random scalars
            let scalars: Vec<_> = (0..10).map(|_| Scalar::random(&mut csprng)).collect();
            // Create 10 points (by doing scalar mults)
            let B = &constants::ED25519_BASEPOINT_TABLE;
            let points: Vec<_> = scalars.iter().map(|s| B * &s).collect();

            // XXX Currently Rust's benchmarking implementation doesn't
            // allow you to specify a sequence of random inputs, but only
            // many trials of the same input.
            //
            // Since this is a variable-time function, this means the
            // benchmark is only useful as a ballpark measurement.
            b.iter(|| vartime::k_fold_scalar_mult(&scalars, &points));
        }
    }
}
