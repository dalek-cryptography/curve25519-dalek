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
//! Revisited"](iacr.org/archive/asiacrypt2008/53500329/53500329.pdf)
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
//! implementation for Ed25519, we use several different models for
//! curve points:
//!
//! * CompletedPoint: points in 𝗣^1 x 𝗣^1;
//! * ExtendedPoint: points in 𝗣^3;
//! * ProjectivePoint: points in 𝗣^2.
//!
//! Finally, to accelerate additions, we use two cached point formats,
//! one for the affine model and one for the 𝗣^3 model:
//!
//! * PreComputedPoint: `(y+x, y-x, 2dxy)`
//! * CachedPoint: `(Y+X, Y-X, Z, 2dXY)`
//!
//! [1]: https://moderncrypto.org/mail-archive/curves/2016/000807.html

// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]

use std::fmt::Debug;
use std::iter::Iterator;
use std::ops::{Add, Sub, Neg, Index};
use std::cmp::{PartialEq, Eq};

use constants;
use field::FieldElement;
use scalar::Scalar;
use util::bytes_equal_ct;

// ------------------------------------------------------------------------
// Compressed points
// ------------------------------------------------------------------------

/// An affine point `(x,y)` on the curve is determined by the
/// `y`-coordinate and the sign of `x`, marshalled into a 32-byte array.
///
/// The first 255 bits of a CompressedPoint represent the
/// y-coordinate. The high bit of the 32nd byte gives the sign of `x`.
#[derive(Copy, Clone)]
pub struct CompressedPoint(pub [u8; 32]);

impl Debug for CompressedPoint {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "CompressedPoint: {:?}", &self.0[..])
    }
}

impl Eq for CompressedPoint {}
impl PartialEq for CompressedPoint {
    /// Determine if this `CompressedPoint` is equal to another.
    ///
    /// # Warning
    ///
    /// This function is NOT constant time.
    fn eq(&self, other: &CompressedPoint) -> bool {
        return self.0 == other.0;
    }
}

impl Index<usize> for CompressedPoint {
    type Output = u8;

    fn index<'a>(&'a self, _index: usize) -> &'a u8 {
        let ret: &'a u8 = &(self.0[_index]);
        ret
    }
}

impl CompressedPoint {
    /// View this `CompressedPoint` as an array of bytes.
    pub fn to_bytes(&self) -> [u8;32] {
        self.0
    }

    /// Attempt to decompress to an `ExtendedPoint`.
    ///
    /// # Warning
    ///
    /// This function will fail and return None if both vx²-u=0 and vx²+u=0.
    pub fn decompress(&self) -> Option<ExtendedPoint> { // FromBytes()
        let mut u:     FieldElement;
        let mut v:     FieldElement;
        let     v3:    FieldElement;
        let     vxx:   FieldElement;

        let mut X: FieldElement;
        let     Y: FieldElement;
        let     Z: FieldElement;
        let     T: FieldElement;

        Y = FieldElement::from_bytes(&self.0);
        Z = FieldElement::one();

        u  = Y.square();
        v  = &u * &constants::d;
        u -= &Z;                   // u = y²-1
        v += &Z;                   // v = dy²+1
        v3 = &v.square() * &v;     // v3 = v³
        X  = (&v3.square() * &(&v * &u)).pow_p58(); // x = (uv⁷)^((q-5)/8)
        X *= &(&u * &v3);                           // x = (uv³)(uv⁷)^((q-5)/8)

        vxx = &v * &X.square();
        if (&vxx - &u).is_nonzero() == 1 {     // vx²-u
            if (&vxx + &u).is_nonzero() == 1 { // vx²+u
                return None;
            }
            X *= &constants::SQRT_M1;
        }

        if X.is_negative() != (self[31] >> 7) as i32 {
            X = X.neg();
        }
        T = &X * &Y;

        Some(ExtendedPoint{ X: X, Y: Y, Z: Z, T: T })
    }
}

// ------------------------------------------------------------------------
// Internal point representations
// ------------------------------------------------------------------------

/// An `ExtendedPoint` is a point on the curve in 𝗣³(𝔽ₚ).
/// A point (x,y) in the affine model corresponds to (x:y:1:xy).
#[derive(Copy, Clone)]
pub struct ExtendedPoint {
    X: FieldElement,
    Y: FieldElement,
    Z: FieldElement,
    T: FieldElement,
}

/// A `ProjectivePoint` is a point on the curve in 𝗣²(𝔽ₚ).
/// A point (x,y) in the affine model corresponds to (x:y:1).
#[derive(Copy, Clone)]
pub struct ProjectivePoint {
    X: FieldElement,
    Y: FieldElement,
    Z: FieldElement,
}

/// A CompletedPoint is a point ((X:Z), (Y:T)) in 𝗣¹(𝔽ₚ)×𝗣¹(𝔽ₚ).
/// A point (x,y) in the affine model corresponds to ((x:1),(y:1)).
#[derive(Copy, Clone)]
pub struct CompletedPoint {
    X: FieldElement,
    Y: FieldElement,
    Z: FieldElement,
    T: FieldElement,
}

/// A pre-computed point in the affine model for the curve,
/// represented as (y+x, y-x, 2dxy).  These precomputations
/// accelerate addition and subtraction.
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct PreComputedPoint {
    pub y_plus_x:  FieldElement,
    pub y_minus_x: FieldElement,
    pub xy2d:      FieldElement,
}

/// A pre-computed point in the P³(𝔽ₚ) model for the curve,
/// represented as (Y+X, Y-X, Z, 2dXY).  These precomputations
/// accelerate addition and subtraction.
#[derive(Copy, Clone)]
pub struct CachedPoint {
    Y_plus_X:  FieldElement,
    Y_minus_X: FieldElement,
    Z:         FieldElement,
    T2d:       FieldElement,
}

// ------------------------------------------------------------------------
// Constructors
// ------------------------------------------------------------------------

/// Trait for curve point types that have an identity constructor.
pub trait Identity {
    /// Returns the identity element of the curve.
    /// Can be used as a constructor.
    fn identity() -> Self;
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

impl Identity for CachedPoint {
    fn identity() -> CachedPoint {
        CachedPoint{ Y_plus_X:  FieldElement::one(),
                     Y_minus_X: FieldElement::one(),
                     Z:         FieldElement::one(),
                     T2d:       FieldElement::zero() }
    }
}

impl Identity for PreComputedPoint {
    fn identity() -> PreComputedPoint {
        PreComputedPoint{
            y_plus_x:  FieldElement::one(),
            y_minus_x: FieldElement::one(),
            xy2d:      FieldElement::zero(),
        }
    }
}

// ------------------------------------------------------------------------
// Constant-time assignment
// ------------------------------------------------------------------------

/// Trait for items which can be conditionally assigned in constant time.
pub trait CTAssignable {
    /// If `choice == 1u8`, assign `other` to `self`.
    /// Otherwise, leave `self` unchanged.  
    /// Executes in constant time.
    // XXX this trait should be extracted?
    fn conditional_assign(&mut self, other: &Self, choice: u8);
}

impl CTAssignable for CachedPoint {
    fn conditional_assign(&mut self, other: &CachedPoint, choice: u8) {
        self.Y_plus_X.conditional_assign(&other.Y_plus_X, choice);
        self.Y_minus_X.conditional_assign(&other.Y_minus_X, choice);
        self.Z.conditional_assign(&other.Z, choice);
        self.T2d.conditional_assign(&other.T2d, choice);
    }
}

impl CTAssignable for PreComputedPoint {
    fn conditional_assign(&mut self, other: &PreComputedPoint, choice: u8) {
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
    #[allow(dead_code)]  // rustc complains this is unused even when it's used
    fn to_extended(&self) -> ExtendedPoint {
        ExtendedPoint{
            X: &self.X * &self.Z,
            Y: &self.Y * &self.Z,
            Z: self.Z.square(),
            T: &self.X * &self.Y,
        }
    }

    /// Convert this point to a `CompressedPoint`
    pub fn compress(&self) -> CompressedPoint {
        let recip = self.Z.invert();
        let x = &self.X * &recip;
        let y = &self.Y * &recip;
        let mut s: [u8; 32];

        s      =  y.to_bytes();
        s[31] ^= (x.is_negative() << 7) as u8;
        CompressedPoint(s)
    }
}

impl ExtendedPoint {
    fn to_cached(&self) -> CachedPoint {
        CachedPoint{
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

    /// Convert this point to a `CompressedPoint`
    pub fn compress(&self) -> CompressedPoint {
        self.to_projective().compress()
    }

    /// Dehomogenize to a PreComputedPoint.
    /// Mainly for testing.
    pub fn to_precomputed(&self) -> PreComputedPoint {
        let recip = self.Z.invert();
        let x = &self.X * &recip;
        let y = &self.Y * &recip;
        let xy2d = &(&x * &y) * &constants::d2;
        PreComputedPoint{
            y_plus_x:  &y + &x,
            y_minus_x: &y - &x,
            xy2d:      xy2d
        }
    }
}

impl CompletedPoint {
    fn to_projective(&self) -> ProjectivePoint {
        ProjectivePoint{
            X: &self.X * &self.T,
            Y: &self.Y * &self.Z,
            Z: &self.Z * &self.T,
        }
    }

    fn to_extended(&self) -> ExtendedPoint {
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
    fn double(&self) -> CompletedPoint { // Double()
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
    fn double(&self) -> ExtendedPoint {
        self.to_projective().double().to_extended()
    }
}

// ------------------------------------------------------------------------
// Addition and Subtraction
// ------------------------------------------------------------------------

impl<'a,'b> Add<&'b CachedPoint> for &'a ExtendedPoint {
    type Output = CompletedPoint;

    fn add(self, other: &'b CachedPoint) -> CompletedPoint {
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

impl<'a,'b> Sub<&'b CachedPoint> for &'a ExtendedPoint {
    type Output = CompletedPoint;

    fn sub(self, other: &'b CachedPoint) -> CompletedPoint {
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

impl<'a,'b> Add<&'b PreComputedPoint> for &'a ExtendedPoint {
    type Output = CompletedPoint;

    fn add(self, other: &'b PreComputedPoint) -> CompletedPoint {
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

impl<'a,'b> Sub<&'b PreComputedPoint> for &'a ExtendedPoint {
    type Output = CompletedPoint;

    fn sub(self, other: &'b PreComputedPoint) -> CompletedPoint {
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

impl<'a,'b> Add<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;
    fn add(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        (self + &other.to_cached()).to_extended()
    }
}

impl<'a,'b> Sub<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;
    fn sub(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        (self - &other.to_cached()).to_extended()
    }
}

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

impl<'a> Neg for &'a CachedPoint {
    type Output = CachedPoint;

    fn neg(self) -> CachedPoint {
        CachedPoint{
            Y_plus_X:   self.Y_minus_X,
            Y_minus_X:  self.Y_plus_X,
            Z:          self.Z,
            T2d:        -(&self.T2d),
        }
    }
}


impl<'a> Neg for &'a PreComputedPoint {
    type Output = PreComputedPoint;

    fn neg(self) -> PreComputedPoint {
        PreComputedPoint{
            y_plus_x:   self.y_minus_x,
            y_minus_x:  self.y_plus_x,
            xy2d:       -(&self.xy2d)
        }
    }
}

// ------------------------------------------------------------------------
// Scalar multiplication
// ------------------------------------------------------------------------

impl ExtendedPoint {
    /// Scalar multiplication: compute `a * self`.
    ///
    /// Uses a window of size 4.  Note: for scalar multiplication of
    /// the basepoint, `basepoint_mult` is approximately 4x faster.
    pub fn scalar_mult(&self, a: &Scalar) -> ExtendedPoint {
        let A = self.to_cached();
        let mut As: [CachedPoint; 8] = [A; 8];
        for i in 0..7 {
            As[i+1] = (self + &As[i]).to_extended().to_cached();
        }
        let e = a.to_radix_16();
        let mut h = ExtendedPoint::identity();
        let mut t: CompletedPoint;
        for i in (0..64).rev() {
            h = h.mult_by_pow_2(4);
            t = &h + &select_precomputed_point(e[i], &As);
            h = t.to_extended();
        }
        h
    }

    /// Construct an `ExtendedPoint` from a `Scalar`, `a`, by
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
    pub fn basepoint_mult(a: &Scalar) -> ExtendedPoint { //GeScalarMultBase
        let e = a.to_radix_16();
        let mut h = ExtendedPoint::identity();
        let mut t: CompletedPoint;

        for i in (0..64).filter(|x| x % 2 == 1) {
            t = &h + &select_precomputed_point(e[i], &constants::base[i/2]);
            h = t.to_extended();
        }

        h = h.mult_by_pow_2(4);

        for i in (0..64).filter(|x| x % 2 == 0) {
            t = &h + &select_precomputed_point(e[i], &constants::base[i/2]);
            h = t.to_extended();
        }

        h
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
        r = s.double();
        return r.to_extended();
    }
}

/// Given a point `A` and scalars `a` and `b`, compute the point
/// `aA+bB`, where `B` is the Ed25519 basepoint (i.e., `B = (x,4/5)`
/// with x positive).
///
/// # Warning
///
/// This function is *not* constant time, hence its name.
// XXX should return ExtendedPoint?
pub fn double_scalar_mult_vartime(a: &Scalar, A: &ExtendedPoint, b: &Scalar) -> ProjectivePoint {
    let a_naf = a.non_adjacent_form();
    let b_naf = b.non_adjacent_form();

    // Build a lookup table of odd multiples of A
    let mut Ai = [CachedPoint::identity(); 8];
    let A2 = A.double();
    Ai[0]  = A.to_cached();
    for i in 0..7 {
        Ai[i+1] = (&A2 + &Ai[i]).to_extended().to_cached();
    }
    // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]

    // Find starting index
    let mut i: usize = 255;
    for j in (0..255).rev() {
        i = j;
        if a_naf[i] != 0 || b_naf[i] != 0 {
            break;
        }
    }

    let mut r = ProjectivePoint::identity();
    loop {
        let mut t = r.double();

        if a_naf[i] > 0 {
            t = &t.to_extended() + &Ai[( a_naf[i]/2) as usize];
        } else if a_naf[i] < 0 {
            t = &t.to_extended() - &Ai[(-a_naf[i]/2) as usize];
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
                             bytes_equal_ct(xabs as u8, j as u8));
    }
    // Now t == |x| * P.

    let minus_t = -(&t);
    let neg_mask = (xmask & 1) as u8;
    t.conditional_assign(&minus_t, neg_mask);
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
    pub fn to_uniform_representative(&self) -> Option<[u8;32]> {
        unimplemented!();
    }

    /// Use Elligator2 to convert a uniformly random string to a curve
    /// point.
    #[allow(unused_variables)] // REMOVE WHEN IMPLEMENTED
    pub fn from_uniform_representative(bytes: &[u8;32]) -> ExtendedPoint {
        unimplemented!();
    }
}

// ------------------------------------------------------------------------
// Debug traits
// ------------------------------------------------------------------------

impl Debug for ExtendedPoint {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "ExtendedPoint(\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?},\n\tT: {:?}\n)",
               &self.X, &self.Y, &self.Z, &self.T)
    }
}

impl Debug for ProjectivePoint {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "ProjectivePoint(\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?}\n)",
               &self.X, &self.Y, &self.Z)
    }
}

impl Debug for CompletedPoint {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "CompletedPoint(\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?},\n\tT: {:?}\n)",
               &self.X, &self.Y, &self.Z, &self.T)
    }
}

impl Debug for PreComputedPoint {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "PreComputedPoint(\n\ty_plus_x: {:?},\n\ty_minus_x: {:?},\n\txy2d: {:?}\n)",
               &self.y_plus_x, &self.y_minus_x, &self.xy2d)
    }
}

impl Debug for CachedPoint {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "CachedPoint(\n\tY_plus_X: {:?},\n\tY_minus_X: {:?},\n\tZ: {:?},\n\tT2d: {:?}\n)",
               &self.Y_plus_X, &self.Y_minus_X, &self.Z, &self.T2d)
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use test::Bencher;
    use field::FieldElement;
    use scalar::Scalar;
    use constants;
    use super::*;
    use super::select_precomputed_point;

    /// Basepoint has y = 4/5.
    ///
    /// Generated with Sage: these are the bytes of 4/5 in 𝔽_p.  The
    /// sign bit is 0 since the basepoint has x chosen to be positive.
    static BASE_CMPRSSD: CompressedPoint =
        CompressedPoint([0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
                         0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
                         0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
                         0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66]);

    /// X coordinate of the basepoint.
    /// = 15112221349535400772501151409588531511454012693041857206046113283949847762202
    static BASE_X_COORD_BYTES: [u8; 32] =
        [0x1a, 0xd5, 0x25, 0x8f, 0x60, 0x2d, 0x56, 0xc9, 0xb2, 0xa7, 0x25, 0x95, 0x60, 0xc7, 0x2c, 0x69,
         0x5c, 0xdc, 0xd6, 0xfd, 0x31, 0xe2, 0xa4, 0xc0, 0xfe, 0x53, 0x6e, 0xcd, 0xd3, 0x36, 0x69, 0x21];

    static BASE2_CMPRSSD: CompressedPoint =
        CompressedPoint([0xc9, 0xa3, 0xf8, 0x6a, 0xae, 0x46, 0x5f, 0xe,
                         0x56, 0x51, 0x38, 0x64, 0x51, 0x0f, 0x39, 0x97,
                         0x56, 0x1f, 0xa2, 0xc9, 0xe8, 0x5e, 0xa2, 0x1d,
                         0xc2, 0x29, 0x23, 0x09, 0xf3, 0xcd, 0x60, 0x22]);

    static BASE16_CMPRSSD: CompressedPoint =
        CompressedPoint([0xeb, 0x27, 0x67, 0xc1, 0x37, 0xab, 0x7a, 0xd8,
                         0x27, 0x9c, 0x07, 0x8e, 0xff, 0x11, 0x6a, 0xb0,
                         0x78, 0x6e, 0xad, 0x3a, 0x2e, 0x0f, 0x98, 0x9f,
                         0x72, 0xc3, 0x7f, 0x82, 0xf2, 0x96, 0x96, 0x70]);

    /// 4493907448824000747700850167940867464579944529806937181821189941592931634714
    static A_SCALAR: Scalar = Scalar([
        0x1a, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d,
        0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8, 0x26, 0x4d,
        0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1,
        0x58, 0x9e, 0x7b, 0x7f, 0x23, 0x76, 0xef, 0x09]);

    /// 2506056684125797857694181776241676200180934651973138769173342316833279714961
    static B_SCALAR: Scalar = Scalar([
        0x91, 0x26, 0x7a, 0xcf, 0x25, 0xc2, 0x09, 0x1b,
        0xa2, 0x17, 0x74, 0x7b, 0x66, 0xf0, 0xb3, 0x2e,
        0x9d, 0xf2, 0xa5, 0x67, 0x41, 0xcf, 0xda, 0xc4,
        0x56, 0xa7, 0xd4, 0xaa, 0xb8, 0x60, 0x8a, 0x05]);

    /// A_SCALAR * basepoint, computed with ed25519.py
    static A_TIMES_BASEPOINT: CompressedPoint = CompressedPoint([
        0xea, 0x27, 0xe2, 0x60, 0x53, 0xdf, 0x1b, 0x59,
        0x56, 0xf1, 0x4d, 0x5d, 0xec, 0x3c, 0x34, 0xc3,
        0x84, 0xa2, 0x69, 0xb7, 0x4c, 0xc3, 0x80, 0x3e,
        0xa8, 0xe2, 0xe7, 0xc9, 0x42, 0x5e, 0x40, 0xa5]);

    /// A_SCALAR * (A_TIMES_BASEPOINT) + B_SCALAR * BASEPOINT
    static DOUBLE_SCALAR_MULT_RESULT: CompressedPoint = CompressedPoint([
        0x7d, 0xfd, 0x6c, 0x45, 0xaf, 0x6d, 0x6e, 0x0e,
        0xba, 0x20, 0x37, 0x1a, 0x23, 0x64, 0x59, 0xc4,
        0xc0, 0x46, 0x83, 0x43, 0xde, 0x70, 0x4b, 0x85,
        0x09, 0x6f, 0xfe, 0x35, 0x4f, 0x13, 0x2b, 0x42]);

    /// Test round-trip decompression for the basepoint.
    #[test]
    fn test_basepoint_decompression_compression() {
        let base_X = FieldElement::from_bytes(&BASE_X_COORD_BYTES);
        let bp  =  BASE_CMPRSSD.decompress().unwrap();
        let bp2 = BASE2_CMPRSSD.decompress().unwrap();
        let compressed  =  bp.compress();
        let compressed2 = bp2.compress();
        // Check that decompression actually gives the correct X coordinate
        assert_eq!(base_X, bp.X);
        assert_eq!(compressed,   BASE_CMPRSSD);
        assert_eq!(compressed2, BASE2_CMPRSSD);
    }

    /// Test sign handling in decompression
    #[test]
    fn test_decompression_sign_handling() {
        let mut m_bp_bytes: [u8;32] = BASE_CMPRSSD.to_bytes().clone();
        // Set the high bit of the last byte to flip the sign
        m_bp_bytes[31] |= 1 << 7;
        let m_bp = CompressedPoint(m_bp_bytes).decompress().unwrap();
        let bp = BASE_CMPRSSD.decompress().unwrap();
        assert_eq!(m_bp.X, -(&bp.X));
        assert_eq!(m_bp.Y,  bp.Y);
        assert_eq!(m_bp.Z,  bp.Z);
        assert_eq!(m_bp.T, -(&bp.T));
    }

    /// Test that computing 1*basepoint gives the correct basepoint.
    #[test]
    fn test_basepoint_mult_one_vs_basepoint() {
        let bp = ExtendedPoint::basepoint_mult(&Scalar::one());
        let compressed = bp.compress();
        assert_eq!(compressed, BASE_CMPRSSD);
    }

    /// Test `impl Add<ExtendedPoint> for ExtendedPoint`
    /// using basepoint + basepoint versus the 2*basepoint constant.
    #[test]
    fn test_basepoint_plus_basepoint() {
        let bp = BASE_CMPRSSD.decompress().unwrap();
        let bp_added = &bp + &bp;
        assert_eq!(  bp_added.compress(), BASE2_CMPRSSD);
    }

    /// Test `impl Add<CachedPoint> for ExtendedPoint`
    /// using the basepoint, basepoint2 constants
    #[test]
    fn test_basepoint_plus_basepoint_cached() {
        let bp = BASE_CMPRSSD.decompress().unwrap();
        let bp_added = (&bp + &bp.to_cached()).to_extended();
        assert_eq!(  bp_added.compress(), BASE2_CMPRSSD);
    }

    /// Test `impl Add<PreComputedPoint> for ExtendedPoint`
    /// using the basepoint, basepoint2 constants
    #[test]
    fn test_basepoint_plus_basepoint_precomputed() {
        let bp = BASE_CMPRSSD.decompress().unwrap();
        // on decode, Z =1, so x = X/Z = X, y = Y/Z = Y, xy = T
        let bp_precomputed = PreComputedPoint{
            y_plus_x:  &bp.Y + &bp.X,
            y_minus_x: &bp.Y - &bp.X,
            xy2d:      &bp.T * &constants::d2,
        };
        let bp_added = (&bp + &bp_precomputed).to_extended();
        assert_eq!(  bp_added.compress(), BASE2_CMPRSSD);
    }

    /// Sanity check for conversion to precomputed points
    #[test]
    fn test_convert_to_precomputed() {
        // construct a point as aB so it has denominators (ie. Z != 1)
        let aB = ExtendedPoint::basepoint_mult(&A_SCALAR);
        let aB_pc = aB.to_precomputed();
        let id = ExtendedPoint::identity();
        let P = &id + &aB_pc;
        assert_eq!(P.to_extended().compress(), aB.compress())
    }

    /// Test basepoint_mult versus a known scalar multiple from ed25519.py
    #[test]
    fn test_basepoint_mult() {
        let aB = ExtendedPoint::basepoint_mult(&A_SCALAR);
        assert_eq!(aB.compress(), A_TIMES_BASEPOINT);
    }

    /// Test scalar_mult versus a known scalar multiple from ed25519.py
    #[test]
    fn test_scalar_mult() {
        let bp = BASE_CMPRSSD.decompress().unwrap();
        let aB = bp.scalar_mult(&A_SCALAR);
        assert_eq!(aB.compress(), A_TIMES_BASEPOINT);
    }

    /// Test double_scalar_mult_vartime vs ed25519.py
    #[test]
    fn test_double_scalar_mult_vartime() {
        let A = A_TIMES_BASEPOINT.decompress().unwrap();
        let result = double_scalar_mult_vartime(&A_SCALAR, &A, &B_SCALAR);
        assert_eq!(result.compress(), DOUBLE_SCALAR_MULT_RESULT);
    }

    /// Test basepoint.double() versus the 2*basepoint constant.
    #[test]
    fn test_basepoint_double() {
        let bp = BASE_CMPRSSD.decompress().unwrap();
        let bp_doubled = bp.double();
        assert_eq!(bp_doubled.compress(), BASE2_CMPRSSD);
    }

    /// Test that computing 2*basepoint is the same as basepoint.double()
    #[test]
    fn test_scalar_mult_two_vs_double() {
        // XXX this seems like a pain point: better way to construct small
        // scalars?
        let two = Scalar([ 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]);
        let bp = BASE_CMPRSSD.decompress().unwrap();
        let bp_doubled = bp.double();
        let bp2 = ExtendedPoint::basepoint_mult(&two);
        assert_eq!(bp_doubled.compress(), bp2.compress());
    }

    #[test]
    fn test_basepoint_projective_extended_round_trip() {
        let bp = BASE_CMPRSSD.decompress().unwrap();
        let bp_roundtrip = bp.to_projective().to_extended();

        assert_eq!(BASE_CMPRSSD, bp_roundtrip.compress());
    }

    /// Test computing 16*basepoint vs mult_by_pow_2
    #[test]
    fn test_mult_by_pow_2() {
        let bp   =   BASE_CMPRSSD.decompress().unwrap();
        let bp16 = bp.mult_by_pow_2(4);
        assert_eq!(bp16.compress(), BASE16_CMPRSSD);
    }

    /// The basepoint, doubled, minus the basepoint should equal the basepoint.
    #[test]
    fn test_ge_sub() {
        let p1: ExtendedPoint = BASE_CMPRSSD.decompress().unwrap();
        let p2: ExtendedPoint = BASE2_CMPRSSD.decompress().unwrap();
        let p3: ExtendedPoint = (&p2 - &p1.to_cached()).to_extended();

        assert_eq!(p1.compress(), p3.compress());
    }

    /// The basepoint plus the identity should equal the basepoint.
    #[test]
    fn test_ge_add() {
        let p1: ExtendedPoint = BASE_CMPRSSD.decompress().unwrap();
        let p2: ExtendedPoint = ExtendedPoint::identity();
        let p3: ExtendedPoint = (&p1 + &p2.to_cached()).to_extended();

        assert_eq!(p1.compress(), p3.compress());
    }

    #[test]
    fn test_PreComputedPoint_conditional_assign() {
        let id     = PreComputedPoint::identity();
        let mut p1 = PreComputedPoint::identity();
        let p2:     PreComputedPoint = PreComputedPoint{
            y_plus_x:  FieldElement([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
            y_minus_x: FieldElement([11, 22, 33, 44, 55, 66, 77, 88, 99, 100]),
            xy2d:    FieldElement([10, 20, 30, 40, 50, 60, 70, 80, 90, 101]),
        };

        p1.conditional_assign(&p2, 0);
        assert_eq!(p1.y_plus_x,  id.y_plus_x);
        assert_eq!(p1.y_minus_x, id.y_minus_x);
        assert_eq!(p1.xy2d,      id.xy2d);
        p1.conditional_assign(&p2, 1);
        assert_eq!(p1.y_plus_x,  p2.y_plus_x);
        assert_eq!(p1.y_minus_x, p2.y_minus_x);
        assert_eq!(p1.xy2d,      p2.xy2d);
    }

    #[bench]
    fn bench_basepoint_mult(b: &mut Bencher) {
        b.iter(|| ExtendedPoint::basepoint_mult(&A_SCALAR));
    }

    #[bench]
    fn bench_scalar_mult(b: &mut Bencher) {
        let bp = BASE_CMPRSSD.decompress().unwrap();
        b.iter(|| bp.scalar_mult(&A_SCALAR));
    }

    #[bench]
    fn bench_select_precomputed_point(b: &mut Bencher) {
        b.iter(|| select_precomputed_point(0, &constants::base[12]));
    }

    #[bench]
    fn bench_double_scalar_mult_vartime(bench: &mut Bencher) {
        let A = A_TIMES_BASEPOINT.decompress().unwrap();
        bench.iter(|| double_scalar_mult_vartime(&A_SCALAR, &A, &B_SCALAR));
    }

    #[bench]
    fn bench_extended_add_cached(b: &mut Bencher) {
        let p1 = BASE_CMPRSSD.decompress().unwrap();
        let p2 = BASE2_CMPRSSD.decompress().unwrap().to_cached();

        b.iter(| | &p1 + &p2);
    }

    #[bench]
    fn bench_extended_add_cached_to_extended(b: &mut Bencher) {
        let p1 = BASE_CMPRSSD.decompress().unwrap();
        let p2 = BASE2_CMPRSSD.decompress().unwrap().to_cached();

        b.iter(| | (&p1 + &p2).to_extended());
    }

    #[bench]
    fn bench_extended_add_precomputed(b: &mut Bencher) {
        let p1 = BASE_CMPRSSD.decompress().unwrap();
        let p2 = select_precomputed_point(6, &constants::base[27]);

        b.iter(| | &p1 + &p2);
    }

    #[bench]
    fn bench_extended_add_precomputed_to_extended(b: &mut Bencher) {
        let p1 = BASE_CMPRSSD.decompress().unwrap();
        let p2 = select_precomputed_point(6, &constants::base[27]);

        b.iter(| | (&p1 + &p2).to_extended());
    }

    #[bench]
    fn bench_double(b: &mut Bencher) {
        let p1 = BASE_CMPRSSD.decompress().unwrap().to_projective();

        b.iter(| | p1.double() );
    }

    #[bench]
    fn bench_double_to_extended(b: &mut Bencher) {
        let p1 = BASE_CMPRSSD.decompress().unwrap().to_projective();

        b.iter(| | p1.double().to_extended() );
    }

    #[bench]
    fn bench_mult_by_pow2_4(b: &mut Bencher) {
        let p1 = BASE_CMPRSSD.decompress().unwrap();

        b.iter(| | p1.mult_by_pow_2(4) );
    }
}
