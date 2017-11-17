// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! This module contains internal curve representations which are not part
//! of the public API.
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

#![allow(non_snake_case)]

use core::fmt::Debug;
use core::ops::{Add, Sub, Neg};
use core::ops::Index;

use constants;

use field::FieldElement;

use edwards::ExtendedPoint;
use edwards::CompressedEdwardsY;
use montgomery::MontgomeryPoint;

use subtle::ConditionallyAssignable;

use traits::ValidityCheck;


// ------------------------------------------------------------------------
// Internal point representations
// ------------------------------------------------------------------------

/// A `ProjectivePoint` is a point on the curve in 𝗣²(𝔽ₚ).
/// A point (x,y) in the affine model corresponds to (x:y:1).
#[derive(Copy, Clone)]
pub struct ProjectivePoint {
    pub X: FieldElement,
    pub Y: FieldElement,
    pub Z: FieldElement,
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
    pub Y_plus_X:  FieldElement,
    pub Y_minus_X: FieldElement,
    pub Z:         FieldElement,
    pub T2d:       FieldElement,
}

// ------------------------------------------------------------------------
// Constructors
// ------------------------------------------------------------------------

use traits::Identity;

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

impl ValidityCheck for ProjectivePoint {
    fn is_valid(&self) -> bool {
        // Curve equation is    -x^2 + y^2 = 1 + d*x^2*y^2,
        // homogenized as (-X^2 + Y^2)*Z^2 = Z^4 + d*X^2*Y^2
        let XX = self.X.square();
        let YY = self.Y.square();
        let ZZ = self.Z.square();
        let ZZZZ = ZZ.square();
        let lhs = &(&YY - &XX) * &ZZ;
        let rhs = &ZZZZ + &(&constants::EDWARDS_D * &(&XX * &YY));

        lhs == rhs
    }
}

// ------------------------------------------------------------------------
// Constant-time assignment
// ------------------------------------------------------------------------

impl ConditionallyAssignable for ProjectiveNielsPoint {
    fn conditional_assign(&mut self, other: &ProjectiveNielsPoint, choice: u8) {
        self.Y_plus_X.conditional_assign(&other.Y_plus_X, choice);
        self.Y_minus_X.conditional_assign(&other.Y_minus_X, choice);
        self.Z.conditional_assign(&other.Z, choice);
        self.T2d.conditional_assign(&other.T2d, choice);
    }
}

impl ConditionallyAssignable for AffineNielsPoint {
    fn conditional_assign(&mut self, other: &AffineNielsPoint, choice: u8) {
        // PreComputedGroupElementCMove()
        self.y_plus_x.conditional_assign(&other.y_plus_x, choice);
        self.y_minus_x.conditional_assign(&other.y_minus_x, choice);
        self.xy2d.conditional_assign(&other.xy2d, choice);
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
    pub fn to_extended(&self) -> ExtendedPoint {
        ExtendedPoint{
            X: &self.X * &self.Z,
            Y: &self.Y * &self.Z,
            Z: self.Z.square(),
            T: &self.X * &self.Y,
        }
    }

    /// Convert this point to a `CompressedEdwardsY`
    pub fn compress(&self) -> CompressedEdwardsY {
        let recip = self.Z.invert();
        let x = &self.X * &recip;
        let y = &self.Y * &recip;
        let mut s: [u8; 32];

        s      =  y.to_bytes();
        s[31] ^= (x.is_negative() << 7) as u8;
        CompressedEdwardsY(s)
    }

    /// Convert this projective point in the Edwards model to its equivalent
    /// projective point on the Montgomery form of the curve.
    ///
    /// Taking the Montgomery curve equation in affine coordinates:
    ///
    ///     E_(A,B) = Bv² = u³ + Au² + u   <span style="float: right">(1)</span>
    ///
    /// and given its relations to the coordinates of the Edwards model:
    ///
    ///     u = (1+y)/(1-y)                <span style="float: right">(2)</span>
    ///     v = (λu)/(x)
    ///
    /// Converting from affine to projective coordinates in the Montgomery
    /// model, we arrive at:
    ///
    ///     u = (Z+Y)/(Z-Y)                <span style="float: right">(3)</span>
    ///     v = λ * ((Z+Y)/(Z-Y)) * (Z/X)
    ///
    /// The transition between affine and projective is given by
    ///
    ///      u → U/W                       <span style="float: right">(4)</span>
    ///      v → V/W
    ///
    /// thus the Montgomery curve equation (1) becomes
    ///
    ///      E_(A,B) : BV²W = U³ + AU²W + UW² ⊆ 𝗣^2  <span style="float: right">(5)</span>
    ///
    /// Here, again, to differentiate from points in the twisted Edwards model, we
    /// call the point `(x,y)` in affine coordinates `(u,v)` and similarly in projective
    /// space we use `(U:V:W)`.  However, since (as per Montgomery's original work) the
    /// v-coordinate is superfluous to the definition of the group law, we merely
    /// use `(U:W)`.
    ///
    /// Therefore, the direct translation between projective Montgomery points
    /// and projective twisted Edwards points is
    ///
    ///      (U:W) = (Z+Y:Z-Y)             <span style="float: right">(6)</span>
    ///
    /// Note, however, that there appears to be an exception where `Z=Y`,
    /// since—from equation 2—this would imply that `y=1` (thus causing the
    /// denominator to be zero).  If this is the case, then it follows from the
    /// twisted Edwards curve equation
    ///
    ///      -x² + y² = 1 + dx²y²          <span style="float: right">(7)</span>
    ///
    /// that
    ///
    ///      -x² + 1 = 1 + dx²
    ///
    /// and, assuming that `d ≠ -1`,
    ///
    ///      -x² = x²
    ///       x  = 0
    ///
    /// Therefore, the only valid point with `y=1` is the twisted Edwards
    /// identity point, which correctly becomes `(1:0)`, that is, the identity,
    /// in the Montgomery model.
    pub fn to_montgomery(&self) -> MontgomeryPoint {
        MontgomeryPoint{
            U: &self.Z + &self.Y,
            W: &self.Z - &self.Y,
        }
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

// ------------------------------------------------------------------------
// Negation
// ------------------------------------------------------------------------

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
// Debug traits
// ------------------------------------------------------------------------

impl Debug for ProjectivePoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "ProjectivePoint{{\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?}\n}}",
               &self.X, &self.Y, &self.Z)
    }
}

impl Debug for CompletedPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "CompletedPoint{{\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?},\n\tT: {:?}\n}}",
               &self.X, &self.Y, &self.Z, &self.T)
    }
}

impl Debug for AffineNielsPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "AffineNielsPoint{{\n\ty_plus_x: {:?},\n\ty_minus_x: {:?},\n\txy2d: {:?}\n}}",
               &self.y_plus_x, &self.y_minus_x, &self.xy2d)
    }
}

impl Debug for ProjectiveNielsPoint {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "ProjectiveNielsPoint{{\n\tY_plus_X: {:?},\n\tY_minus_X: {:?},\n\tZ: {:?},\n\tT2d: {:?}\n}}",
               &self.Y_plus_X, &self.Y_minus_X, &self.Z, &self.T2d)
    }
}


