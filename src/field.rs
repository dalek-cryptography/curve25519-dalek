// -*- mode: rust; coding: utf-8; -*-
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
//! Based on Adam Langley's curve25519-donna and (Golang) ed25519
//! implementations.

use core::clone::Clone;
use core::fmt::Debug;
use core::ops::{Add, AddAssign};
use core::ops::{Sub, SubAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Index, IndexMut};
use core::cmp::{Eq, PartialEq};
use core::ops::Neg;

use util::arrays_equal_ct;
use util::byte_is_nonzero;
use util::CTAssignable;
use util::CTEq;

/// FieldElements are represented as an array of ten "Limbs", which are radix
/// 25.5, that is, each Limb of a FieldElement alternates between being
/// represented as a factor of 2^25 or 2^26 more than the last corresponding
/// integer.
pub type Limb = i32;

/// FieldElement represents an element of the field GF(2^255 - 19).  An element
/// t, entries t[0]...t[9], represents the integer t[0]+2^26 t[1]+2^51 t[2]+2^77
/// t[3]+2^102 t[4]+...+2^230 t[9].  Bounds on each t[i] vary depending on
/// context.
#[derive(Copy, Clone)]
pub struct FieldElement(pub [Limb; 10]);

impl Eq for FieldElement {}
impl PartialEq for FieldElement {
    /// Test equality between two FieldElements by converting them to bytes.
    ///
    /// # Warning
    ///
    /// This comparison is *not* constant time.  It could easily be
    /// made to be, but the main use of an `Eq` implementation is for
    /// branching, so it seems pointless.
    //
    // XXX it would be good to encode constant-time considerations
    // (no data flow from secret information) into Rust's type
    // system.
    fn eq(&self, other: &FieldElement) -> bool {
        let  self_bytes =  self.to_bytes();
        let other_bytes = other.to_bytes();
        let mut are_equal: bool = true;
        for i in 0..32 {
            are_equal &= self_bytes[i] == other_bytes[i];
        }
        return are_equal;
    }
}

impl CTEq for FieldElement {
    /// Test equality between two `FieldElement`s by converting them to bytes.
    ///
    /// # Returns
    ///
    /// `1u8` if the two `FieldElement`s are equal, and `0u8` otherwise.
    fn ct_eq(&self, other: &FieldElement) -> u8 {
        arrays_equal_ct(&self.to_bytes(), &other.to_bytes())
    }
}

impl Debug for FieldElement {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "FieldElement: {:?}", &self.0[..])
    }
}

impl Index<usize> for FieldElement {
    type Output = Limb;

    fn index<'a>(&'a self, _index: usize) -> &'a Limb {
        let ret: &'a Limb = &(self.0[_index]);
        ret
    }
}

impl IndexMut<usize> for FieldElement {
    fn index_mut<'a>(&'a mut self, _index: usize) -> &'a mut Limb {
        let ret: &'a mut Limb = &mut(self.0[_index]);
        ret
    }
}

impl<'b> AddAssign<&'b FieldElement> for FieldElement {
    fn add_assign(&mut self, _rhs: &'b FieldElement) { // fsum()
        for i in 0..10 {
            self[i] += _rhs[i];
        }
    }
}

impl<'a, 'b> Add<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    fn add(self, _rhs: &'b FieldElement) -> FieldElement {
        let mut output = self.clone();
        output += _rhs;
        output
    }
}

impl<'b> SubAssign<&'b FieldElement> for FieldElement {
    fn sub_assign(&mut self, _rhs: &'b FieldElement) { // fdifference()
        for i in 0..10 {
            self[i] -= _rhs[i];
        }
    }
}

impl<'a, 'b> Sub<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    fn sub(self, _rhs: &'b FieldElement) -> FieldElement {
        let mut output = self.clone();
        output -= _rhs;
        output
    }
}

impl<'b> MulAssign<&'b FieldElement> for FieldElement {
    fn mul_assign(&mut self, _rhs: &'b FieldElement) {
        self.0 = self.multiply(_rhs).0;
    }
}

impl<'a, 'b> Mul<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    fn mul(self, _rhs: &'b FieldElement) -> FieldElement {
        self.multiply(_rhs)
    }
}

impl<'a> Neg for &'a FieldElement {
    type Output = FieldElement;
    fn neg(self) -> FieldElement {
        let mut output = self.clone();
        output.negate();
        output
    }
}

impl CTAssignable for FieldElement {
    /// Conditionally assign another FieldElement to this one.
    ///
    /// If `choice == 0`, replace `self` with `self`:
    ///
    /// ```
    /// # use curve25519_dalek::field::FieldElement;
    /// # use curve25519_dalek::util::CTAssignable;
    /// let f     = FieldElement([1,1,1,1,1,1,1,1,1,1]);
    /// let g     = FieldElement([2,2,2,2,2,2,2,2,2,2]);
    /// let mut h = FieldElement([1,1,1,1,1,1,1,1,1,1]);
    /// h.conditional_assign(&g, 0);
    /// assert!(h == f);
    /// ```
    ///
    /// If `choice == 1`, replace `self` with `f`:
    ///
    /// ```
    /// # use curve25519_dalek::field::FieldElement;
    /// # use curve25519_dalek::util::CTAssignable;
    /// # let f     = FieldElement([1,1,1,1,1,1,1,1,1,1]);
    /// # let g     = FieldElement([2,2,2,2,2,2,2,2,2,2]);
    /// # let mut h = FieldElement([1,1,1,1,1,1,1,1,1,1]);
    /// h.conditional_assign(&g, 1);
    /// assert!(h == g);
    /// ```
    ///
    /// # Preconditions
    ///
    /// * `choice` in {0,1}
    fn conditional_assign(&mut self, f: &FieldElement, choice: u8) {
        let mask = -(choice as Limb);
        for i in 0..10 {
            self[i] ^= mask & (self[i] ^ f[i]);
        }
    }
}

/// Convert an array of (at least) three bytes into an i64.
#[inline]
#[allow(dead_code)]
pub fn load3(input: &[u8]) -> i64 {
       (input[0] as i64)
    | ((input[1] as i64) << 8)
    | ((input[2] as i64) << 16)
}

/// Convert an array of (at least) four bytes into an i64.
#[inline]
#[allow(dead_code)]
pub fn load4(input: &[u8]) -> i64 {
       (input[0] as i64)
    | ((input[1] as i64) << 8)
    | ((input[2] as i64) << 16)
    | ((input[3] as i64) << 24)
}

impl FieldElement {
    /// Invert the sign of this field element
    pub fn negate(&mut self) {
        for i in 0..10 {
            self[i] = -self[i];
        }
    }

    /// Construct the additive identity
    pub fn zero() -> FieldElement {
        FieldElement([ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }

    /// Construct the multiplicative identity
    pub fn one() -> FieldElement {
        FieldElement([ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }

    fn combine_coeffs(input: &[i64;10]) -> FieldElement { //FeCombine
        let mut c = [0i64;10];
        let mut h = input.clone();

        /*
          |h[0]| <= (1.1*1.1*2^52*(1+19+19+19+19)+1.1*1.1*2^50*(38+38+38+38+38))
            i.e. |h[0]| <= 1.2*2^59; narrower ranges for h[2], h[4], h[6], h[8]
          |h[1]| <= (1.1*1.1*2^51*(1+1+19+19+19+19+19+19+19+19))
            i.e. |h[1]| <= 1.5*2^58; narrower ranges for h[3], h[5], h[7], h[9]
        */

        c[0] = (h[0] + (1 << 25)) >> 26;
        h[1] += c[0];
        h[0] -= c[0] << 26;
        c[4] = (h[4] + (1 << 25)) >> 26;
        h[5] += c[4];
        h[4] -= c[4] << 26;
        /* |h[0]| <= 2^25 */
        /* |h[4]| <= 2^25 */
        /* |h[1]| <= 1.51*2^58 */
        /* |h[5]| <= 1.51*2^58 */

        c[1] = (h[1] + (1 << 24)) >> 25;
        h[2] += c[1];
        h[1] -= c[1] << 25;
        c[5] = (h[5] + (1 << 24)) >> 25;
        h[6] += c[5];
        h[5] -= c[5] << 25;
        /* |h[1]| <= 2^24; from now on fits into int32 */
        /* |h[5]| <= 2^24; from now on fits into int32 */
        /* |h[2]| <= 1.21*2^59 */
        /* |h[6]| <= 1.21*2^59 */

        c[2] = (h[2] + (1 << 25)) >> 26;
        h[3] += c[2];
        h[2] -= c[2] << 26;
        c[6] = (h[6] + (1 << 25)) >> 26;
        h[7] += c[6];
        h[6] -= c[6] << 26;
        /* |h[2]| <= 2^25; from now on fits into int32 unchanged */
        /* |h[6]| <= 2^25; from now on fits into int32 unchanged */
        /* |h[3]| <= 1.51*2^58 */
        /* |h[7]| <= 1.51*2^58 */

        c[3] = (h[3] + (1 << 24)) >> 25;
        h[4] += c[3];
        h[3] -= c[3] << 25;
        c[7] = (h[7] + (1 << 24)) >> 25;
        h[8] += c[7];
        h[7] -= c[7] << 25;
        /* |h[3]| <= 2^24; from now on fits into int32 unchanged */
        /* |h[7]| <= 2^24; from now on fits into int32 unchanged */
        /* |h[4]| <= 1.52*2^33 */
        /* |h[8]| <= 1.52*2^33 */

        c[4] = (h[4] + (1 << 25)) >> 26;
        h[5] += c[4];
        h[4] -= c[4] << 26;
        c[8] = (h[8] + (1 << 25)) >> 26;
        h[9] += c[8];
        h[8] -= c[8] << 26;
        /* |h[4]| <= 2^25; from now on fits into int32 unchanged */
        /* |h[8]| <= 2^25; from now on fits into int32 unchanged */
        /* |h[5]| <= 1.01*2^24 */
        /* |h[9]| <= 1.51*2^58 */

        c[9] = (h[9] + (1 << 24)) >> 25;
        h[0] += c[9] * 19;
        h[9] -= c[9] << 25;
        /* |h[9]| <= 2^24; from now on fits into int32 unchanged */
        /* |h[0]| <= 1.8*2^37 */

        c[0] = (h[0] + (1 << 25)) >> 26;
        h[1] += c[0];
        h[0] -= c[0] << 26;
        /* |h[0]| <= 2^25; from now on fits into int32 unchanged */
        /* |h[1]| <= 1.01*2^24 */

        let mut output = FieldElement([0i32;10]);
        output[0] = h[0] as i32;
        output[1] = h[1] as i32;
        output[2] = h[2] as i32;
        output[3] = h[3] as i32;
        output[4] = h[4] as i32;
        output[5] = h[5] as i32;
        output[6] = h[6] as i32;
        output[7] = h[7] as i32;
        output[8] = h[8] as i32;
        output[9] = h[9] as i32;
        output
    }

    /// Create a FieldElement by demarshalling an array of 32 bytes.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::field::FieldElement;
    /// let data: [u8; 32] = [ 1,  2,  3,  4,  5,  6,  7,  8,
    ///                        9, 10, 11, 12, 13, 14, 15, 16,
    ///                       17, 18, 19, 20, 21, 22, 23, 24,
    ///                       25, 26, 27, 28, 29, 30, 31, 32 ];
    /// let fe: FieldElement = FieldElement::from_bytes(&data);
    /// assert_eq!(fe,
    ///            FieldElement([ 197121, -4095679,  21045505,  6840408, 4209720,
    ///                          1249809, -7665014, -12377341, 30523826, 8420472]))
    /// ```
    ///
    /// # Return
    ///
    /// Returns a new FieldElement.
    pub fn from_bytes(data: &[u8;32]) -> FieldElement { //FeFromBytes
        let mut h = [0i64;10];
        h[0] =  load4(&data[ 0..]);
        h[1] =  load3(&data[ 4..]) << 6;
        h[2] =  load3(&data[ 7..]) << 5;
        h[3] =  load3(&data[10..]) << 3;
        h[4] =  load3(&data[13..]) << 2;
        h[5] =  load4(&data[16..]);
        h[6] =  load3(&data[20..]) << 7;
        h[7] =  load3(&data[23..]) << 5;
        h[8] =  load3(&data[26..]) << 4;
        h[9] = (load3(&data[29..]) & 8388607) << 2;

        FieldElement::combine_coeffs(&h)
    }

    /// Marshal this FieldElement into a 32-byte array.
    ///
    /// # Preconditions
    ///
    /// * `|h[i]|` bounded by 1.1*2^25, 1.1*2^24, 1.1*2^25, 1.1*2^24, etc.
    ///
    /// # Lemma
    ///
    /// Write p = 2^255 - 19 and q = floor(h/p).
    ///
    /// Basic claim: q = floor(2^(-255)(h + 19 * 2^-25 h9 + 2^-1)).
    ///
    /// # Proof
    ///
    /// Have |h|<=p so |q|<=1 so |19^2 * 2^-255 * q| < 1/4.
    ///
    /// Also have |h-2^230 * h9| < 2^230 so |19 * 2^-255 * (h-2^230 * h9)| < 1/4.
    ///
    /// Write y=2^(-1)-19^2 2^(-255)q-19 2^(-255)(h-2^230 h9), then 0<y<1.
    ///
    /// Write r = h - pq.
    ///
    /// Have 0 <= r< = p-1 = 2^255 - 20.
    ///
    /// Thus 0 <= r + 19 * 2^-255 * r < r + 19 * 2^-255 * 2^255 <= 2^255 - 1.
    ///
    /// Write x = r + 19 * 2^-255 * r + y.
    ///
    /// Then 0 < x < 2^255 so floor(2^(-255)x) = 0 so floor(q+2^(-255)x) = q.
    ///
    /// Have q+2^(-255)x = 2^-255 * (h + 19 * 2^-25 * h9 + 2^-1),
    /// so floor(2^-255 * (h + 19 * 2^-25 * h9 + 2^-1)) = q.
    ///
    /// # Example
    ///
    /// Continuing from the previous example in `FieldElement::from_bytes`:
    ///
    /// ```
    /// # use curve25519_dalek::field::FieldElement;
    /// let data: [u8; 32] = [ 1,  2,  3,  4,  5,  6,  7,  8,
    ///                        9, 10, 11, 12, 13, 14, 15, 16,
    ///                       17, 18, 19, 20, 21, 22, 23, 24,
    ///                       25, 26, 27, 28, 29, 30, 31, 32 ];
    /// let fe: FieldElement = FieldElement([ 197121, -4095679,  21045505,  6840408, 4209720,
    ///                                      1249809, -7665014, -12377341, 30523826, 8420472]);
    /// let bytes: [u8; 32] = fe.to_bytes();
    /// assert!(data == bytes);
    /// ```
    pub fn to_bytes(&self) -> [u8;32] { //FeToBytes
        let mut carry = [0i32; 10];
        let mut h = self.clone();

        let mut q:i32 = (19*h[9] + (1 << 24)) >> 25;
        q = (h[0] + q) >> 26;
        q = (h[1] + q) >> 25;
        q = (h[2] + q) >> 26;
        q = (h[3] + q) >> 25;
        q = (h[4] + q) >> 26;
        q = (h[5] + q) >> 25;
        q = (h[6] + q) >> 26;
        q = (h[7] + q) >> 25;
        q = (h[8] + q) >> 26;
        q = (h[9] + q) >> 25;

        // Goal: Output h-(2^255-19)q, which is between 0 and 2^255-20.
        h[0] += 19 * q;
        // Goal: Output h-2^255 q, which is between 0 and 2^255-20.

        carry[0] = h[0] >> 26;
        h[1] += carry[0];
        h[0] -= carry[0] << 26;
        carry[1] = h[1] >> 25;
        h[2] += carry[1];
        h[1] -= carry[1] << 25;
        carry[2] = h[2] >> 26;
        h[3] += carry[2];
        h[2] -= carry[2] << 26;
        carry[3] = h[3] >> 25;
        h[4] += carry[3];
        h[3] -= carry[3] << 25;
        carry[4] = h[4] >> 26;
        h[5] += carry[4];
        h[4] -= carry[4] << 26;
        carry[5] = h[5] >> 25;
        h[6] += carry[5];
        h[5] -= carry[5] << 25;
        carry[6] = h[6] >> 26;
        h[7] += carry[6];
        h[6] -= carry[6] << 26;
        carry[7] = h[7] >> 25;
        h[8] += carry[7];
        h[7] -= carry[7] << 25;
        carry[8] = h[8] >> 26;
        h[9] += carry[8];
        h[8] -= carry[8] << 26;
        carry[9] = h[9] >> 25;
        h[9] -= carry[9] << 25;
        // h10 = carry9

        // Goal: Output h[0]+...+2^255 h10-2^255 q, which is between 0 and 2^255-20.
        // Have h[0]+...+2^230 h[9] between 0 and 2^255-1;
        // evidently 2^255 h10-2^255 q = 0.
        // Goal: Output h[0]+...+2^230 h[9].

        let mut s = [0u8;32];
        s[0] = (h[0] >> 0) as u8;
        s[1] = (h[0] >> 8) as u8;
        s[2] = (h[0] >> 16) as u8;
        s[3] = ((h[0] >> 24) | (h[1] << 2)) as u8;
        s[4] = (h[1] >> 6) as u8;
        s[5] = (h[1] >> 14) as u8;
        s[6] = ((h[1] >> 22) | (h[2] << 3)) as u8;
        s[7] = (h[2] >> 5) as u8;
        s[8] = (h[2] >> 13) as u8;
        s[9] = ((h[2] >> 21) | (h[3] << 5)) as u8;
        s[10] = (h[3] >> 3) as u8;
        s[11] = (h[3] >> 11) as u8;
        s[12] = ((h[3] >> 19) | (h[4] << 6)) as u8;
        s[13] = (h[4] >> 2) as u8;
        s[14] = (h[4] >> 10) as u8;
        s[15] = (h[4] >> 18) as u8;
        s[16] = (h[5] >> 0) as u8;
        s[17] = (h[5] >> 8) as u8;
        s[18] = (h[5] >> 16) as u8;
        s[19] = ((h[5] >> 24) | (h[6] << 1)) as u8;
        s[20] = (h[6] >> 7) as u8;
        s[21] = (h[6] >> 15) as u8;
        s[22] = ((h[6] >> 23) | (h[7] << 3)) as u8;
        s[23] = (h[7] >> 5) as u8;
        s[24] = (h[7] >> 13) as u8;
        s[25] = ((h[7] >> 21) | (h[8] << 4)) as u8;
        s[26] = (h[8] >> 4) as u8;
        s[27] = (h[8] >> 12) as u8;
        s[28] = ((h[8] >> 20) | (h[9] << 6)) as u8;
        s[29] = (h[9] >> 2) as u8;
        s[30] = (h[9] >> 10) as u8;
        s[31] = (h[9] >> 18) as u8;

        //Clear high bit
        s[31] &= 127u8;

        s
    }

    /// XXX clarify documentation
    /// Determine if this field element, represented as a byte array,
    /// is less than or equal to another field element represented as
    /// a byte array.
    ///
    /// # Returns
    ///
    /// Returns `1u8` if `self.to_bytes() <= other.to_bytes()`, and `0u8` otherwise.
    pub fn bytes_equal_less_than(&self, other: &[u8; 32]) -> u8 { // feBytesLess
        // XXX cleanup
	    let mut equal_so_far: i32 = -1i32;
	    let mut greater:      i32 =  0i32;

        let this: [u8; 32] = self.to_bytes();

        for i in 32 .. 0 {
            let x: i32 =  this[i-1] as i32;
            let y: i32 = other[i-1] as i32;

            greater      = (!equal_so_far & greater) | (equal_so_far & ((x - y) >> 31));
            equal_so_far = equal_so_far & (((x ^ y) - 1) >> 31);
        }

        (!equal_so_far & 1 & greater) as u8
    }

    /// Determine if this `FieldElement` is negative.
    ///
    /// # Return
    ///
    /// If negative, return `1i32`.  Otherwise, return `0i32`.
    // XXX should return u8
    pub fn is_negative(&self) -> i32 { //FeIsNegative
        let bytes = self.to_bytes();
        (bytes[0] & 1) as i32
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
        return byte_is_nonzero(x);
    }

    /// Calculates h = f * g. Can overlap h with f or g.
    ///
    /// # Preconditions
    ///
    /// * |f[i]| bounded by 1.1*2^26, 1.1*2^25, 1.1*2^26, 1.1*2^25, etc.
    /// * |g[i]| bounded by 1.1*2^26, 1.1*2^25, 1.1*2^26, 1.1*2^25, etc.
    ///
    /// # Postconditions
    ///
    /// * |h| bounded by 1.1*2^25, 1.1*2^24, 1.1*2^25, 1.1*2^24, etc.
    ///
    /// ## Notes on implementation strategy
    ///
    /// * Using schoolbook multiplication.
    /// * Karatsuba would save a little in some cost models.
    ///
    /// * Most multiplications by 2 and 19 are 32-bit precomputations;
    ///   cheaper than 64-bit postcomputations.
    ///
    /// * There is one remaining multiplication by 19 in the carry chain;
    ///   one *19 precomputation can be merged into this,
    ///   but the resulting data flow is considerably less clean.
    ///
    /// * There are 12 carries below.
    ///   10 of them are 2-way parallelizable and vectorizable.
    ///   Can get away with 11 carries, but then data flow is much deeper.
    ///
    /// * With tighter constraints on inputs can squeeze carries into int32.
    pub fn multiply(&self, _rhs: &FieldElement) -> FieldElement {
        let f0 = self[0] as i64;
        let f1 = self[1] as i64;
        let f2 = self[2] as i64;
        let f3 = self[3] as i64;
        let f4 = self[4] as i64;
        let f5 = self[5] as i64;
        let f6 = self[6] as i64;
        let f7 = self[7] as i64;
        let f8 = self[8] as i64;
        let f9 = self[9] as i64;

        let f1_2 = (2 * self[1]) as i64;
        let f3_2 = (2 * self[3]) as i64;
        let f5_2 = (2 * self[5]) as i64;
        let f7_2 = (2 * self[7]) as i64;
        let f9_2 = (2 * self[9]) as i64;

        let g0 = _rhs[0] as i64;
        let g1 = _rhs[1] as i64;
        let g2 = _rhs[2] as i64;
        let g3 = _rhs[3] as i64;
        let g4 = _rhs[4] as i64;
        let g5 = _rhs[5] as i64;
        let g6 = _rhs[6] as i64;
        let g7 = _rhs[7] as i64;
        let g8 = _rhs[8] as i64;
        let g9 = _rhs[9] as i64;

        let g1_19 = (19 * _rhs[1]) as i64; /* 1.4*2^29 */
        let g2_19 = (19 * _rhs[2]) as i64; /* 1.4*2^30; still ok */
        let g3_19 = (19 * _rhs[3]) as i64;
        let g4_19 = (19 * _rhs[4]) as i64;
        let g5_19 = (19 * _rhs[5]) as i64;
        let g6_19 = (19 * _rhs[6]) as i64;
        let g7_19 = (19 * _rhs[7]) as i64;
        let g8_19 = (19 * _rhs[8]) as i64;
        let g9_19 = (19 * _rhs[9]) as i64;

        let h0 = f0*g0 + f1_2*g9_19 + f2*g8_19 + f3_2*g7_19 + f4*g6_19 + f5_2*g5_19 + f6*g4_19 + f7_2*g3_19 + f8*g2_19 + f9_2*g1_19;
        let h1 = f0*g1 + f1*g0 + f2*g9_19 + f3*g8_19 + f4*g7_19 + f5*g6_19 + f6*g5_19 + f7*g4_19 + f8*g3_19 + f9*g2_19;
        let h2 = f0*g2 + f1_2*g1 + f2*g0 + f3_2*g9_19 + f4*g8_19 + f5_2*g7_19 + f6*g6_19 + f7_2*g5_19 + f8*g4_19 + f9_2*g3_19;
        let h3 = f0*g3 + f1*g2 + f2*g1 + f3*g0 + f4*g9_19 + f5*g8_19 + f6*g7_19 + f7*g6_19 + f8*g5_19 + f9*g4_19;
        let h4 = f0*g4 + f1_2*g3 + f2*g2 + f3_2*g1 + f4*g0 + f5_2*g9_19 + f6*g8_19 + f7_2*g7_19 + f8*g6_19 + f9_2*g5_19;
        let h5 = f0*g5 + f1*g4 + f2*g3 + f3*g2 + f4*g1 + f5*g0 + f6*g9_19 + f7*g8_19 + f8*g7_19 + f9*g6_19;
        let h6 = f0*g6 + f1_2*g5 + f2*g4 + f3_2*g3 + f4*g2 + f5_2*g1 + f6*g0 + f7_2*g9_19 + f8*g8_19 + f9_2*g7_19;
        let h7 = f0*g7 + f1*g6 + f2*g5 + f3*g4 + f4*g3 + f5*g2 + f6*g1 + f7*g0 + f8*g9_19 + f9*g8_19;
        let h8 = f0*g8 + f1_2*g7 + f2*g6 + f3_2*g5 + f4*g4 + f5_2*g3 + f6*g2 + f7_2*g1 + f8*g0 + f9_2*g9_19;
        let h9 = f0*g9 + f1*g8 + f2*g7 + f3*g6 + f4*g5 + f5*g4 + f6*g3 + f7*g2 + f8*g1 + f9*g0;

        FieldElement::combine_coeffs(&[h0, h1, h2, h3, h4, h5, h6, h7, h8, h9])
    }

    fn square_inner(&self) -> [i64;10] {
        let f0     = self[0]       as i64;
        let f1     = self[1]       as i64;
        let f2     = self[2]       as i64;
        let f3     = self[3]       as i64;
        let f4     = self[4]       as i64;
        let f5     = self[5]       as i64;
        let f6     = self[6]       as i64;
        let f7     = self[7]       as i64;
        let f8     = self[8]       as i64;
        let f9     = self[9]       as i64;
        let f0_2   = (2 * self[0]) as i64;
        let f1_2   = (2 * self[1]) as i64;
        let f2_2   = (2 * self[2]) as i64;
        let f3_2   = (2 * self[3]) as i64;
        let f4_2   = (2 * self[4]) as i64;
        let f5_2   = (2 * self[5]) as i64;
        let f6_2   = (2 * self[6]) as i64;
        let f7_2   = (2 * self[7]) as i64;
        let f5_38  = 38 * f5; // 1.31*2^30
        let f6_19  = 19 * f6; // 1.31*2^30
        let f7_38  = 38 * f7; // 1.31*2^30
        let f8_19  = 19 * f8; // 1.31*2^30
        let f9_38  = 38 * f9; // 1.31*2^30

        let mut h = [0i64;10];
        h[0] =   f0*f0 + f1_2*f9_38 + f2_2*f8_19 + f3_2*f7_38 + f4_2*f6_19 + f5*f5_38;
        h[1] = f0_2*f1 +   f2*f9_38 + f3_2*f8_19 +   f4*f7_38 + f5_2*f6_19;
        h[2] = f0_2*f2 + f1_2*f1    + f3_2*f9_38 + f4_2*f8_19 + f5_2*f7_38 + f6*f6_19;
        h[3] = f0_2*f3 + f1_2*f2    +   f4*f9_38 + f5_2*f8_19 +   f6*f7_38;
        h[4] = f0_2*f4 + f1_2*f3_2  +   f2*f2    + f5_2*f9_38 + f6_2*f8_19 + f7*f7_38;
        h[5] = f0_2*f5 + f1_2*f4    +   f2_2*f3  +   f6*f9_38 + f7_2*f8_19;
        h[6] = f0_2*f6 + f1_2*f5_2  +   f2_2*f4  + f3_2*f3    + f7_2*f9_38 + f8*f8_19;
        h[7] = f0_2*f7 + f1_2*f6    +   f2_2*f5  + f3_2*f4    +   f8*f9_38;
        h[8] = f0_2*f8 + f1_2*f7_2  +   f2_2*f6  + f3_2*f5_2  +   f4*f4    + f9*f9_38;
        h[9] = f0_2*f9 + f1_2*f8    +   f2_2*f7  + f3_2*f6    + f4_2*f5;

        h
    }

    /// Calculates h = f*f. Can overlap h with f.
    ///
    /// # Preconditions
    ///
    /// * |f[i]| bounded by 1.1*2^26, 1.1*2^25, 1.1*2^26, 1.1*2^25, etc.
    ///
    /// # Postconditions
    ///
    /// * |h[i]| bounded by 1.1*2^25, 1.1*2^24, 1.1*2^25, 1.1*2^24, etc.
    pub fn square(&self) -> FieldElement {
        FieldElement::combine_coeffs(&self.square_inner())
    }

    /// Square this field element and multiply the result by 2.
    ///
    /// # Preconditions
    ///
    /// * |f[i]| bounded by 1.65*2^26, 1.65*2^25, 1.65*2^26, 1.65*2^25, etc.
    ///
    /// # Postconditions
    ///
    /// * |h[i]| bounded by 1.01*2^25, 1.01*2^24, 1.01*2^25, 1.01*2^24, etc.
    ///
    /// # Notes
    ///
    /// See fe_mul.c in ref10 implementation for discussion of implementation
    /// strategy.
    pub fn square2(&self) -> FieldElement {
        let mut coeffs = self.square_inner();
        for i in 0..10 {
            coeffs[i] += coeffs[i];
        }
        FieldElement::combine_coeffs(&coeffs)
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
    use test::Bencher;
    use util::CTNegatable;

    #[bench]
    fn bench_fieldelement_a_mul_a(b: &mut Bencher) {
        let a = FieldElement::from_bytes(&A_BYTES);
        b.iter(|| &a*&a);
    }

    #[bench]
    fn bench_fieldelement_a_sq(b: &mut Bencher) {
        let a = FieldElement::from_bytes(&A_BYTES);
        b.iter(|| a.square());
    }

    #[bench]
    fn bench_fieldelement_a_inv(b: &mut Bencher) {
        let a = FieldElement::from_bytes(&A_BYTES);
        b.iter(|| a.invert());
    }

    /// Random element a of GF(2^255-19), from Sage
    /// a = 1070314506888354081329385823235218444233221\
    ///     2228051251926706380353716438957572
    static A_BYTES: [u8;32] =
        [ 0x04, 0xfe, 0xdf, 0x98, 0xa7, 0xfa, 0x0a, 0x68,
          0x84, 0x92, 0xbd, 0x59, 0x08, 0x07, 0xa7, 0x03,
          0x9e, 0xd1, 0xf6, 0xf2, 0xe1, 0xd9, 0xe2, 0xa4,
          0xa4, 0x51, 0x47, 0x36, 0xf3, 0xc3, 0xa9, 0x17];

    /// Byte representation of a**2
    static ASQ_BYTES: [u8;32] =
        [ 0x75, 0x97, 0x24, 0x9e, 0xe6, 0x06, 0xfe, 0xab,
          0x24, 0x04, 0x56, 0x68, 0x07, 0x91, 0x2d, 0x5d,
          0x0b, 0x0f, 0x3f, 0x1c, 0xb2, 0x6e, 0xf2, 0xe2,
          0x63, 0x9c, 0x12, 0xba, 0x73, 0x0b, 0xe3, 0x62];

    /// Byte representation of 1/a
    static AINV_BYTES: [u8;32] =
        [0x96, 0x1b, 0xcd, 0x8d, 0x4d, 0x5e, 0xa2, 0x3a,
         0xe9, 0x36, 0x37, 0x93, 0xdb, 0x7b, 0x4d, 0x70,
         0xb8, 0x0d, 0xc0, 0x55, 0xd0, 0x4c, 0x1d, 0x7b,
         0x90, 0x71, 0xd8, 0xe9, 0xb6, 0x18, 0xe6, 0x30];

    /// Byte representation of a^((p-5)/8)
    static AP58_BYTES: [u8;32] =
        [0x6a, 0x4f, 0x24, 0x89, 0x1f, 0x57, 0x60, 0x36,
         0xd0, 0xbe, 0x12, 0x3c, 0x8f, 0xf5, 0xb1, 0x59,
         0xe0, 0xf0, 0xb8, 0x1b, 0x20, 0xd2, 0xb5, 0x1f,
         0x15, 0x21, 0xf9, 0xe3, 0xe1, 0x61, 0x21, 0x55];

    #[test]
    fn test_fieldelement_a_mul_a() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let asq = FieldElement::from_bytes(&ASQ_BYTES);
        assert_eq!(asq, &a*&a);
        assert_eq!(asq, a.square());
    }

    #[test]
    fn test_fieldelement_a_square2() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let asq = FieldElement::from_bytes(&ASQ_BYTES);
        assert_eq!(a.square2(), &asq+&asq);
    }

    #[test]
    fn test_fieldelement_a_inv() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        assert_eq!(ainv, a.invert());
    }

    #[test]
    fn test_fieldelement_a_p58() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ap58 = FieldElement::from_bytes(&AP58_BYTES);
        assert_eq!(ap58, a.pow_p58());
    }

    #[test]
    fn test_fieldelement_a_chi() {
        let a = FieldElement::from_bytes(&A_BYTES);
        // a is square
        assert_eq!(a.chi(), FieldElement::one());
    }

    #[test]
    fn test_fieldelement_eq() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        assert!(a == a);
        assert!(a != ainv);
    }

    /// Notice that the last element has the high bit set, which
    /// should be ignored
    static B_BYTES: [u8;32] =
        [113, 191, 169, 143, 91, 234, 121, 15, 241, 131, 217, 36, 230, 101, 92, 234, 8, 208, 170, 251, 97, 127, 70, 210, 58, 23, 166, 87, 240, 169, 184, 178];

    static B_LIMBS: FieldElement = FieldElement(
        [-5652623, 8034020, 8266223, -13556020, -5672552, -5582839, -12603138, 15161929, -16418207, 13296296]);

    #[test]
    fn test_fieldelement_frombytes_highbit_is_ignored() {
        let mut cleared_bytes = B_BYTES.clone();
        cleared_bytes[31] &= 127u8;
        let orig_elt = FieldElement::from_bytes(&B_BYTES);
        let cleared_elt = FieldElement::from_bytes(&cleared_bytes);
        for i in 0..10 {
            assert!(orig_elt[i] == cleared_elt[i]);
        }
    }

    #[test]
    fn test_fieldelement_to_bytes() {
        let test_elt = FieldElement::from_bytes(&B_BYTES);
        for i in 0..10 {
            assert!(test_elt[i] == B_LIMBS[i]);
        }
    }

    #[test]
    fn test_fieldelement_from_bytes() {
        let test_bytes = B_LIMBS.to_bytes();
        for i in 0..31 {
            assert!(test_bytes[i] == B_BYTES[i]);
        }
        // high bit is set to zero in to_bytes
        assert!(test_bytes[31] == (B_BYTES[31] & 127u8));
    }

    #[test]
    fn test_conditional_negate() {
        let       one = FieldElement([ 1,0,0,0,0,0,0,0,0,0]);
        let minus_one = FieldElement([-1,0,0,0,0,0,0,0,0,0]);
        let mut x = one;
        x.conditional_negate(1u8);
        assert_eq!(x, minus_one);
        x.conditional_negate(0u8);
        assert_eq!(x, minus_one);
        x.conditional_negate(1u8);
        assert_eq!(x, one);
    }
}
