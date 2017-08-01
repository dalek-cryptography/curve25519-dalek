
//
// To the extent possible under law, the authors have waived all
// copyright and related or neighboring rights to curve25519-dalek,
// using the Creative Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full
// details.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Field arithmetic for ℤ/(2²⁵⁵-19).
//!
//! Partially based on Adam Langley's curve25519-donna and (Golang)
//! ed25519 implementations, with other techniques inspired by Mike
//! Hamburg's code.
//!
//! This module re-exports either the 32-bit or 64-bit implementation,
//! and implements functions that are generic with respect to the
//! basic operations, such as inverses and square roots.

use core::cmp::{Eq, PartialEq};

use subtle::slices_equal;
use subtle::byte_is_nonzero;
use subtle::ConditionallyAssignable;
use subtle::Equal;

use constants;

/// A `FieldElement` represents an element of the field GF(2^255 - 19).
#[cfg(feature="radix_51")]
pub type FieldElement = FieldElement64;
/// A `FieldElement` represents an element of the field GF(2^255 - 19).
#[cfg(not(feature="radix_51"))]
pub type FieldElement = FieldElement32;
#[cfg(feature="radix_51")]
pub use field_64bit::*;
#[cfg(not(feature="radix_51"))]
pub use field_32bit::*;

impl Eq for FieldElement {}
impl PartialEq for FieldElement {
    /// Test equality between two `FieldElement`s.  Since the
    /// internal representation is not canonical, the field elements
    /// are normalized to wire format before comparison.
    ///
    /// # Warning
    ///
    /// This comparison is *not* constant time.  It could easily be
    /// made to be, but the main use of an `Eq` implementation is for
    /// branching, so it seems pointless to do so.
    fn eq(&self, other: &FieldElement) -> bool {
        let  self_bytes =  self.to_bytes();
        let other_bytes = other.to_bytes();
        let mut are_equal: bool = true;
        for i in 0..32 {
            are_equal &= self_bytes[i] == other_bytes[i];
        }
        are_equal
    }
}

impl Equal for FieldElement {
    /// Test equality between two `FieldElement`s.  Since the
    /// internal representation is not canonical, the field elements
    /// are normalized to wire format before comparison.
    ///
    /// # Returns
    ///
    /// `1u8` if the two `FieldElement`s are equal, and `0u8` otherwise.
    fn ct_eq(&self, other: &FieldElement) -> u8 {
        slices_equal(&self.to_bytes(), &other.to_bytes())
    }
}

impl FieldElement {
    /// Determine if this `FieldElement` is negative, in the sense
    /// used in the ed25519 paper: `x` is negative if the low bit is
    /// set.
    ///
    /// # Return
    ///
    /// If negative, return `1u8`.  Otherwise, return `0u8`.
    pub fn is_negative_ed25519(&self) -> u8 { //FeIsNegative
        let bytes = self.to_bytes();
        (bytes[0] & 1) as u8
    }

    /// Determine if this `FieldElement` is negative, in the
    /// sense used by Decaf: `x` is nonnegative if the least
    /// absolute residue for `x` lies in `[0, (p-1)/2]`, and
    /// is negative otherwise.
    ///
    /// # Return
    ///
    /// Returns `1u8` if negative, `0u8` if nonnegative.
    ///
    /// # Implementation
    ///
    /// Uses a trick borrowed from Mike Hamburg's code.  Let `x \in
    /// F_p` and let `y \in Z` be the least absolute residue for `x`.
    /// Suppose `y ≤ (p-1)/2`.  Then `2y < p` so `2y = 2y mod p` and
    /// `2y mod p` is even.  On the other hand, if `y > (p-1)/2` then
    /// `2y ≥ p`; since `y < p`, `2y \in [p, 2p)`, so `2y mod p =
    /// 2y-p`, which is odd.
    ///
    /// Thus we can test whether `y ≤ (p-1)/2` by checking whether `2y
    /// mod p` is even.
    pub fn is_negative_decaf(&self) -> u8 {
        let y = self + self;
        (y.to_bytes()[0] & 1) as u8
    }

    /// Determine if this `FieldElement` is nonnegative, in the
    /// sense used by Decaf: `x` is nonnegative if the least
    /// absolute residue for `x` lies in `[0, (p-1)/2]`, and
    /// is negative otherwise.
    pub fn is_nonnegative_decaf(&self) -> u8 {
        1u8 & (!self.is_negative_decaf())
    }

    /// Determine if this `FieldElement` is zero.
    ///
    /// # Return
    ///
    /// If zero, return `1u8`.  Otherwise, return `0u8`.
    pub fn is_zero(&self) -> u8 {
        1u8 & (!self.is_nonzero())
    }

    /// Determine if this `FieldElement` is non-zero.
    ///
    /// # Return
    ///
    /// If non-zero, return `1u8`.  Otherwise, return `0u8`.
    pub fn is_nonzero(&self) -> u8 {  //FeIsNonZero
        let bytes = self.to_bytes();
        let mut x = 0u8;
        for b in &bytes {
            x |= *b;
        }
        byte_is_nonzero(x)
    }

    #[inline]
    #[allow(dead_code)]
    /// Requires k > 0; raise self to the 2^(2^k)-th power.
    fn pow2k(&self, k: u32) -> FieldElement {
        let mut z = self.square();
        for _ in 1..k { z = z.square(); }
        z
    }

    /// Compute (self^(2^250-1), self^11), used as a helper function
    /// within invert() and pow22523().
    ///
    /// XXX This returns an extra intermediate to save computation in
    /// finding inverses, at the cost of an extra copy when it's not
    /// used (e.g., when raising to (p-1)/2 or (p-5)/8). Good idea?
    fn pow22501(&self) -> (FieldElement, FieldElement) {
        // Instead of managing which temporary variables are used
        // for what, we define as many as we need and trust the
        // compiler to reuse stack space as appropriate.
        //
        // XXX testing some examples suggests that this does happen,
        // but it would be good to check asm for this function.
        //
        // Each temporary variable t_i is of the form (self)^e_i.
        // Squaring t_i corresponds to multiplying e_i by 2,
        // so the pow2k function shifts e_i left by k places.
        // Multiplying t_i and t_j corresponds to adding e_i + e_j.
        //
        // Temporary t_i                      Nonzero bits of e_i
        //
        let t0  = self.square();           // 1         e_0 = 2^1
        let t1  = t0.square().square();    // 3         e_1 = 2^3
        let t2  = self * &t1;              // 3,0       e_2 = 2^3 + 2^0
        let t3  = &t0 * &t2;               // 3,1,0
        let t4  = t3.square();             // 4,2,1
        let t5  = &t2 * &t4;               // 4,3,2,1,0
        let t6  = t5.pow2k(5);             // 9,8,7,6,5
        let t7  = &t6 * &t5;               // 9,8,7,6,5,4,3,2,1,0
        let t8  = t7.pow2k(10);            // 19..10
        let t9  = &t8 * &t7;               // 19..0
        let t10 = t9.pow2k(20);            // 39..20
        let t11 = &t10 * &t9;              // 39..0
        let t12 = t11.pow2k(10);           // 49..10
        let t13 = &t12 * &t7;              // 49..0
        let t14 = t13.pow2k(50);           // 99..50
        let t15 = &t14 * &t13;             // 99..0
        let t16 = t15.pow2k(100);          // 199..100
        let t17 = &t16 * &t15;             // 199..0
        let t18 = t17.pow2k(50);           // 249..50
        let t19 = &t18 * &t13;             // 249..0

        (t19, t3)
    }

    /// Given a nonzero field element, compute its inverse.
    /// The inverse is computed as self^(p-2), since
    /// x^(p-2)x = x^(p-1) = 1 (mod p).
    ///
    /// XXX should we add a debug_assert that self is nonzero?
    pub fn invert(&self) -> FieldElement {
        // The bits of p-2 = 2^255 -19 -2 are 11010111111...11.
        //
        //                                 nonzero bits of exponent
        let (t19, t3) = self.pow22501();   // t19: 249..0 ; t3: 3,1,0
        let t20 = t19.pow2k(5);            // 254..5
        let t21 = &t20 * &t3;              // 254..5,3,1,0

        t21
    }

    /// Raise this field element to the power (p-5)/8 = 2^252 -3.
    /// Used in decoding.
    pub fn pow_p58(&self) -> FieldElement {
        // The bits of (p-5)/8 are 101111.....11.
        //
        //                                 nonzero bits of exponent
        let (t19, _) = self.pow22501();    // 249..0
        let t20 = t19.pow2k(2);            // 251..2
        let t21 = self * &t20;             // 251..2,0

        t21
    }

    /// Given `FieldElements` `u` and `v`, attempt to compute
    /// `sqrt(u/v)` in constant time.
    ///
    /// It would be much better to use an `Option` type here, but
    /// doing so forces the caller to branch, which we don't want to
    /// do.  This seems like the least bad solution.
    ///
    /// # Return
    ///
    /// - `(1u8, sqrt(u/v))` if `v` is nonzero and `u/v` is square;
    /// - `(0u8, zero)`      if `v` is zero;
    /// - `(0u8, garbage)`   if `u/v` is nonsquare.
    ///
    pub fn sqrt_ratio(u: &FieldElement, v: &FieldElement) -> (u8, FieldElement) {
        // Using the same trick as in ed25519 decoding, we merge the
        // inversion, the square root, and the square test as follows.
        //
        // To compute sqrt(α), we can compute β = α^((p+3)/8).
        // Then β^2 = ±α, so multiplying β by sqrt(-1) if necessary
        // gives sqrt(α).
        //
        // To compute 1/sqrt(α), we observe that
        //    1/β = α^(p-1 - (p+3)/8) = α^((7p-11)/8)
        //                            = α^3 * (α^7)^((p-5)/8).
        //
        // We can therefore compute sqrt(u/v) = sqrt(u)/sqrt(v)
        // by first computing
        //    r = u^((p+3)/8) v^(p-1-(p+3)/8)
        //      = u u^((p-5)/8) v^3 (v^7)^((p-5)/8)
        //      = (uv^3) (uv^7)^((p-5)/8).
        //
        // If v is nonzero and u/v is square, then r^2 = ±u/v,
        //                                     so vr^2 = ±u.
        // If vr^2 =  u, then sqrt(u/v) = r.
        // If vr^2 = -u, then sqrt(u/v) = r*sqrt(-1).
        //
        // If v is zero, r is also zero.

        let v3 = &v.square()  * v;
        let v7 = &v3.square() * v;
        let mut r = &(u * &v3) * &(u * &v7).pow_p58();
        let check = v * &r.square();

        let correct_sign_sqrt = check.ct_eq(   u);
        let flipped_sign_sqrt = check.ct_eq(&(-u));

        let r_prime = &constants::SQRT_M1 * &r;
        r.conditional_assign(&r_prime, flipped_sign_sqrt);

        let was_nonzero_square = correct_sign_sqrt | flipped_sign_sqrt;

        (was_nonzero_square, r)
    }

    /// For `self` a nonzero square, compute 1/sqrt(self) in
    /// constant time.
    ///
    /// It would be much better to use an `Option` type here, but
    /// doing so forces the caller to branch, which we don't want to
    /// do.  This seems like the least bad solution.
    ///
    /// # Return
    ///
    /// - `(1u8, 1/sqrt(self))` if `self` is a nonzero square;
    /// - `(0u8, zero)`         if `self` is zero;
    /// - `(0u8, garbage)`      if `self` is nonsquare.
    ///
    pub fn invsqrt(&self) -> (u8, FieldElement) {
        FieldElement::sqrt_ratio(&FieldElement::one(), self)
    }

    /// chi calculates `self^((p-1)/2)`.
    ///
    /// # Return
    ///
    /// * If this element is a non-zero square, returns `1`.
    /// * If it is zero, returns `0`.
    /// * If it is non-square, returns `-1`.
    pub fn chi(&self) -> FieldElement {  // extra25519.chi
        // The bits of (p-1)/2 = 2^254 -10 are 0110111111...11.
        //
        //                                 nonzero bits of exponent
        let (t19, _) = self.pow22501();    // 249..0
        let t20 = t19.pow2k(4);            // 253..4
        let t21 = self.square();           // 1
        let t22 = t21.square();            // 2
        let t23 = &t22 * &t21;             // 2,1
        let t24 = &t20 * &t23;             // 253..4,2,1

        t24
    }
}

#[cfg(test)]
mod test {
    use field::*;
    use subtle::ConditionallyNegatable;

    /// Random element a of GF(2^255-19), from Sage
    /// a = 1070314506888354081329385823235218444233221\
    ///     2228051251926706380353716438957572
    pub static A_BYTES: [u8; 32] =
        [ 0x04, 0xfe, 0xdf, 0x98, 0xa7, 0xfa, 0x0a, 0x68,
          0x84, 0x92, 0xbd, 0x59, 0x08, 0x07, 0xa7, 0x03,
          0x9e, 0xd1, 0xf6, 0xf2, 0xe1, 0xd9, 0xe2, 0xa4,
          0xa4, 0x51, 0x47, 0x36, 0xf3, 0xc3, 0xa9, 0x17];

    /// Byte representation of a**2
    static ASQ_BYTES: [u8; 32] =
        [ 0x75, 0x97, 0x24, 0x9e, 0xe6, 0x06, 0xfe, 0xab,
          0x24, 0x04, 0x56, 0x68, 0x07, 0x91, 0x2d, 0x5d,
          0x0b, 0x0f, 0x3f, 0x1c, 0xb2, 0x6e, 0xf2, 0xe2,
          0x63, 0x9c, 0x12, 0xba, 0x73, 0x0b, 0xe3, 0x62];

    /// Byte representation of 1/a
    static AINV_BYTES: [u8; 32] =
        [0x96, 0x1b, 0xcd, 0x8d, 0x4d, 0x5e, 0xa2, 0x3a,
         0xe9, 0x36, 0x37, 0x93, 0xdb, 0x7b, 0x4d, 0x70,
         0xb8, 0x0d, 0xc0, 0x55, 0xd0, 0x4c, 0x1d, 0x7b,
         0x90, 0x71, 0xd8, 0xe9, 0xb6, 0x18, 0xe6, 0x30];

    /// Byte representation of a^((p-5)/8)
    static AP58_BYTES: [u8; 32] =
        [0x6a, 0x4f, 0x24, 0x89, 0x1f, 0x57, 0x60, 0x36,
         0xd0, 0xbe, 0x12, 0x3c, 0x8f, 0xf5, 0xb1, 0x59,
         0xe0, 0xf0, 0xb8, 0x1b, 0x20, 0xd2, 0xb5, 0x1f,
         0x15, 0x21, 0xf9, 0xe3, 0xe1, 0x61, 0x21, 0x55];

    #[test]
    fn a_mul_a_vs_a_squared_constant() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let asq = FieldElement::from_bytes(&ASQ_BYTES);
        assert_eq!(asq, &a * &a);
    }

    #[test]
    fn a_square_vs_a_squared_constant() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let asq = FieldElement::from_bytes(&ASQ_BYTES);
        assert_eq!(asq, a.square());
    }

    #[test]
    fn a_square2_vs_a_squared_constant() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let asq = FieldElement::from_bytes(&ASQ_BYTES);
        assert_eq!(a.square2(), &asq+&asq);
    }

    #[test]
    fn a_invert_vs_inverse_of_a_constant() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        let should_be_inverse = a.invert();
        assert_eq!(ainv, should_be_inverse);
        assert_eq!(FieldElement::one(), &a * &should_be_inverse);
    }

    #[test]
    fn a_p58_vs_ap58_constant() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ap58 = FieldElement::from_bytes(&AP58_BYTES);
        assert_eq!(ap58, a.pow_p58());
    }

    #[test]
    fn chi_on_square_and_nonsquare() {
        let a = FieldElement::from_bytes(&A_BYTES);
        // a is square
        assert_eq!(a.chi(), FieldElement::one());
        let mut two_bytes = [0u8; 32]; two_bytes[0] = 2;
        let two = FieldElement::from_bytes(&two_bytes);
        // 2 is nonsquare
        assert_eq!(two.chi(), FieldElement::minus_one());
    }

    #[test]
    fn equality() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        assert!(a == a);
        assert!(a != ainv);
    }

    /// Notice that the last element has the high bit set, which
    /// should be ignored
    static B_BYTES: [u8;32] =
        [113, 191, 169, 143,  91, 234, 121,  15,
         241, 131, 217,  36, 230, 101,  92, 234,
           8, 208, 170, 251,  97, 127,  70, 210,
          58,  23, 166,  87, 240, 169, 184, 178];

    #[test]
    fn from_bytes_highbit_is_ignored() {
        let mut cleared_bytes = B_BYTES;
        cleared_bytes[31] &= 127u8;
        let with_highbit_set    = FieldElement::from_bytes(&B_BYTES);
        let without_highbit_set = FieldElement::from_bytes(&cleared_bytes);
        assert_eq!(without_highbit_set, with_highbit_set);
    }

    #[cfg(not(feature="radix_51"))]
    static B_LIMBS_RADIX_25_5: FieldElement32 = FieldElement32(
        [-5652623, 8034020, 8266223, -13556020, -5672552,
         -5582839, -12603138, 15161929, -16418207, 13296296]);

    #[cfg(not(feature="radix_51"))]
    #[test]
    fn from_bytes_vs_radix_25_5_limb_constants() {
        let test_elt = FieldElement::from_bytes(&B_BYTES);
        assert_eq!(test_elt.0, B_LIMBS_RADIX_25_5.0);
    }

    #[cfg(not(feature="radix_51"))]
    #[test]
    fn radix_25_5_limb_constants_to_bytes_vs_byte_constants() {
        let test_bytes = B_LIMBS_RADIX_25_5.to_bytes();
        for i in 0..31 {
            assert!(test_bytes[i] == B_BYTES[i]);
        }
        // Check that high bit is set to zero in to_bytes
        assert!(test_bytes[31] == (B_BYTES[31] & 127u8));
    }

    #[test]
    fn conditional_negate() {
        let       one = FieldElement::one();
        let minus_one = FieldElement::minus_one();
        let mut x = one;
        x.conditional_negate(1u8);
        assert_eq!(x, minus_one);
        x.conditional_negate(0u8);
        assert_eq!(x, minus_one);
        x.conditional_negate(1u8);
        assert_eq!(x, one);
    }
}

#[cfg(all(test, feature = "bench"))]
mod bench {
    use test::Bencher;

    use super::*;
    use super::test::A_BYTES;

    #[bench]
    fn fieldelement_a_mul_a(b: &mut Bencher) {
        let a = FieldElement::from_bytes(&A_BYTES);
        b.iter(|| &a * &a);
    }

    #[bench]
    fn fieldelement_a_sq(b: &mut Bencher) {
        let a = FieldElement::from_bytes(&A_BYTES);
        b.iter(|| a.square());
    }

    #[bench]
    fn fieldelement_a_inv(b: &mut Bencher) {
        let a = FieldElement::from_bytes(&A_BYTES);
        b.iter(|| a.invert());
    }
}
