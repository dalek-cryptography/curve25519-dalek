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

use core::fmt::Debug;
use core::ops::{Add, AddAssign};
use core::ops::{Sub, SubAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Index, IndexMut};
use core::cmp::{Eq, PartialEq};
use core::ops::Neg;

use subtle::arrays_equal;
use subtle::byte_is_nonzero;
use subtle::CTAssignable;
use subtle::CTEq;

#[cfg(not(feature="radix_51"))]
use utils::{load3, load4};
#[cfg(feature="radix_51")]
use utils::load8;

use constants;

/// With the `radix51` feature enabled, `FieldElements` are represented
/// in radix 2^51 as five `u64`s.
#[cfg(feature="radix_51")]
pub type Limb = u64;

/// A `FieldElement` represents an element of the field GF(2^255 - 19).
///
/// With the `radix_51` feature, a `FieldElement` is represented in
/// radix 2^51 as five `u64`s; the coefficients are allowed to grow up
/// to 2^54 between reductions mod `p`.
#[cfg(feature="radix_51")]
#[derive(Copy, Clone)]
pub struct FieldElement(pub [u64; 5]);

/// Without the `radix51` feature enabled, `FieldElements` are represented
/// in radix 2^25.5 as ten `i32`s.
#[cfg(not(feature="radix_51"))]
pub type Limb = i32;

/// A `FieldElement` represents an element of the field GF(2^255 - 19).
///
/// With the `radix_51` feature, a `FieldElement` is represented in
/// radix 2^25.5 as ten `i32`s, so that an element t, entries
/// t[0],...,t[9], represents the integer t[0]+2^26 t[1]+2^51
/// t[2]+2^77 t[3]+2^102 t[4]+...+2^230 t[9].  Bounds on each t[i]
/// vary depending on context.
#[cfg(not(feature="radix_51"))]
#[derive(Copy, Clone)]
pub struct FieldElement(pub [i32; 10]);

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
        are_equal
    }
}

impl CTEq for FieldElement {
    /// Test equality between two `FieldElement`s by converting them to bytes.
    ///
    /// # Returns
    ///
    /// `1u8` if the two `FieldElement`s are equal, and `0u8` otherwise.
    fn ct_eq(&self, other: &FieldElement) -> u8 {
        arrays_equal(&self.to_bytes(), &other.to_bytes())
    }
}

impl Debug for FieldElement {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "FieldElement: {:?}", &self.0[..])
    }
}

impl Index<usize> for FieldElement {
    type Output = Limb;

    fn index(&self, _index: usize) -> &Limb {
        &(self.0[_index])
    }
}

impl IndexMut<usize> for FieldElement {
    fn index_mut(&mut self, _index: usize) -> &mut Limb {
        &mut (self.0[_index])
    }
}

impl<'b> AddAssign<&'b FieldElement> for FieldElement {
    fn add_assign(&mut self, _rhs: &'b FieldElement) { // fsum()
        for i in 0..self.0.len() {
            self[i] += _rhs[i];
        }
    }
}

impl<'a, 'b> Add<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    fn add(self, _rhs: &'b FieldElement) -> FieldElement {
        let mut output = *self;
        output += _rhs;
        output
    }
}

impl<'b> SubAssign<&'b FieldElement> for FieldElement {
    #[cfg(not(feature="radix_51"))]
    fn sub_assign(&mut self, _rhs: &'b FieldElement) { // fdifference()
        for i in 0..10 {
            self[i] -= _rhs[i];
        }
    }
    #[cfg(feature="radix_51")]
    fn sub_assign(&mut self, _rhs: &'b FieldElement) {
        let result = (self as &FieldElement) - _rhs;
        for i in 0..5 {
            self.0[i] = result.0[i];
        }
    }
}

impl<'a, 'b> Sub<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    #[cfg(not(feature="radix_51"))]
    fn sub(self, _rhs: &'b FieldElement) -> FieldElement {
        let mut output = *self;
        output -= _rhs;
        output
    }
    #[cfg(feature="radix_51")]
    fn sub(self, _rhs: &'b FieldElement) -> FieldElement {
        // To avoid underflow, first add a multiple of p.
        // Choose 16*p = p << 4 to be larger than 54-bit _rhs.
        //
        // If we could statically track the bitlengths of the limbs
        // of every FieldElement, we could choose a multiple of p
        // just bigger than _rhs and avoid having to do a reduction.
        //
        // Since we don't yet have type-level integers to do this, we
        // have to add an explicit reduction call here, which is a
        // significant cost.
        FieldElement::reduce([
            (self.0[0] + 36028797018963664u64) - _rhs.0[0],
            (self.0[1] + 36028797018963952u64) - _rhs.0[1],
            (self.0[2] + 36028797018963952u64) - _rhs.0[2],
            (self.0[3] + 36028797018963952u64) - _rhs.0[3],
            (self.0[4] + 36028797018963952u64) - _rhs.0[4],
        ])
    }
}

impl<'b> MulAssign<&'b FieldElement> for FieldElement {
    fn mul_assign(&mut self, _rhs: &'b FieldElement) {
        let result = (self as &FieldElement) * _rhs;
        self.0 = result.0;
    }
}

impl<'a, 'b> Mul<&'b FieldElement> for &'a FieldElement {
    type Output = FieldElement;
    #[cfg(feature="radix_51")]
    fn mul(self, _rhs: &'b FieldElement) -> FieldElement {
        /// Multiply two 64-bit integers with 128 bits of output.
        #[inline(always)]
        fn m(x: u64, y: u64) -> u128 { (x as u128) * (y as u128) }

        // Alias self, _rhs for more readable formulas
        let a: &[u64; 5] = &self.0;
        let b: &[u64; 5] = &_rhs.0;

        // Multiply to get 128-bit coefficients of output
        let     c0: u128 = m(a[0],b[0]) + ( m(a[4],b[1]) +   m(a[3],b[2]) +   m(a[2],b[3]) +   m(a[1],b[4]) )*19;
        let mut c1: u128 = m(a[1],b[0]) +   m(a[0],b[1]) + ( m(a[4],b[2]) +   m(a[3],b[3]) +   m(a[2],b[4]) )*19;
        let mut c2: u128 = m(a[2],b[0]) +   m(a[1],b[1]) +   m(a[0],b[2]) + ( m(a[4],b[3]) +   m(a[3],b[4]) )*19;
        let mut c3: u128 = m(a[3],b[0]) +   m(a[2],b[1]) +   m(a[1],b[2]) +   m(a[0],b[3]) + ( m(a[4],b[4]) )*19;
        let mut c4: u128 = m(a[4],b[0]) +   m(a[3],b[1]) +   m(a[2],b[2]) +   m(a[1],b[3]) +   m(a[0],b[4]);

        // Now c[i] < 2^2b * (1+i + (4-i)*19) < 2^(2b + lg(1+4*19)) < 2^(2b + 6.27)
        // where b is the bitlength of the input limbs.

        // The carry (c[i] >> 51) fits into a u64 iff 2b+6.27 < 64+51 iff b <= 54.
        // After the first carry pass, all c[i] fit into u64.
        debug_assert!(a[0] < (1 << 54)); debug_assert!(b[0] < (1 << 54));
        debug_assert!(a[1] < (1 << 54)); debug_assert!(b[1] < (1 << 54));
        debug_assert!(a[2] < (1 << 54)); debug_assert!(b[2] < (1 << 54));
        debug_assert!(a[3] < (1 << 54)); debug_assert!(b[3] < (1 << 54));
        debug_assert!(a[4] < (1 << 54)); debug_assert!(b[4] < (1 << 54));

        // The 128-bit output limbs are stored in two 64-bit registers (low/high part).
        // By rebinding the names after carrying, we free the upper registers for reuse.
        let low_51_bit_mask = (1u64 << 51) - 1;
        c1 +=  (c0 >> 51) as u128;
        let mut c0: u64 = (c0 as u64) & low_51_bit_mask;
        c2 +=  (c1 >> 51) as u128;
        let c1: u64 = (c1 as u64) & low_51_bit_mask;
        c3 +=  (c2 >> 51) as u128;
        let c2: u64 = (c2 as u64) & low_51_bit_mask;
        c4 +=  (c3 >> 51) as u128;
        let c3: u64 = (c3 as u64) & low_51_bit_mask;
        c0 += ((c4 >> 51) as u64) * 19;
        let c4: u64 = (c4 as u64) & low_51_bit_mask;

        FieldElement::reduce([c0,c1,c2,c3,c4])
    }

    #[cfg(not(feature="radix_51"))]
    fn mul(self, _rhs: &'b FieldElement) -> FieldElement {
        // Notes preserved from ed25519.go (presumably originally from ref10):
        //
        // Calculates h = f * g. Can overlap h with f or g.
        //
        // # Preconditions
        //
        // * |f[i]| bounded by 1.1*2^26, 1.1*2^25, 1.1*2^26, 1.1*2^25, etc.
        // * |g[i]| bounded by 1.1*2^26, 1.1*2^25, 1.1*2^26, 1.1*2^25, etc.
        //
        // # Postconditions
        //
        // * |h| bounded by 1.1*2^25, 1.1*2^24, 1.1*2^25, 1.1*2^24, etc.
        //
        // ## Notes on implementation strategy
        //
        // * Using schoolbook multiplication.
        // * Karatsuba would save a little in some cost models.
        //
        // * Most multiplications by 2 and 19 are 32-bit precomputations;
        //   cheaper than 64-bit postcomputations.
        //
        // * There is one remaining multiplication by 19 in the carry chain;
        //   one *19 precomputation can be merged into this,
        //   but the resulting data flow is considerably less clean.
        //
        // * There are 12 carries below.
        //   10 of them are 2-way parallelizable and vectorizable.
        //   Can get away with 11 carries, but then data flow is much deeper.
        //
        // * With tighter constraints on inputs can squeeze carries into int32.
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

        FieldElement::reduce([h0, h1, h2, h3, h4, h5, h6, h7, h8, h9])
    }
}

impl<'a> Neg for &'a FieldElement {
    type Output = FieldElement;
    fn neg(self) -> FieldElement {
        let mut output = *self;
        output.negate();
        output
    }
}

impl CTAssignable for FieldElement {
    /// Conditionally assign another FieldElement to this one.
    ///
    /// XXX fixup tests to avoid limb specs
    /// XXX_radix_51
    ///
    /// If `choice == 0`, replace `self` with `self`:
    ///
    /// ```
    /// # extern crate subtle;
    /// # extern crate curve25519_dalek;
    /// # use curve25519_dalek::field::FieldElement;
    /// # use subtle::CTAssignable;
    /// # fn main() {
    /// let f     = FieldElement([1,1,1,1,1,1,1,1,1,1]);
    /// let g     = FieldElement([2,2,2,2,2,2,2,2,2,2]);
    /// let mut h = FieldElement([1,1,1,1,1,1,1,1,1,1]);
    /// h.conditional_assign(&g, 0);
    /// assert!(h == f);
    /// # }
    /// ```
    ///
    /// If `choice == 1`, replace `self` with `f`:
    ///
    /// ```
    /// # extern crate subtle;
    /// # extern crate curve25519_dalek;
    /// # use curve25519_dalek::field::FieldElement;
    /// # use subtle::CTAssignable;
    /// # fn main() {
    /// # let f     = FieldElement([1,1,1,1,1,1,1,1,1,1]);
    /// # let g     = FieldElement([2,2,2,2,2,2,2,2,2,2]);
    /// # let mut h = FieldElement([1,1,1,1,1,1,1,1,1,1]);
    /// h.conditional_assign(&g, 1);
    /// assert!(h == g);
    /// # }
    /// ```
    ///
    /// # Preconditions
    ///
    /// * `choice` in {0,1}
    #[cfg(not(feature="radix_51"))]
    fn conditional_assign(&mut self, f: &FieldElement, choice: u8) {
        let mask = -(choice as Limb);
        for i in 0..10 {
            self[i] ^= mask & (self[i] ^ f[i]);
        }
    }
    #[cfg(feature="radix_51")]
    fn conditional_assign(&mut self, f: &FieldElement, choice: u8) {
        let mask = (-(choice as i64)) as u64;
        for i in 0..5 {
            self.0[i] ^= mask & (self.0[i] ^ f.0[i]);
        }
    }
}

impl FieldElement {
    /// Invert the sign of this field element
    #[cfg(not(feature="radix_51"))]
    pub fn negate(&mut self) {
        for i in 0..10 {
            self[i] = -self[i];
        }
    }
    /// Invert the sign of this field element
    #[cfg(feature="radix_51")]
    pub fn negate(&mut self) {
        // See commentary in the Sub impl
        let neg = FieldElement::reduce([
            36028797018963664u64 - self.0[0],
            36028797018963952u64 - self.0[1],
            36028797018963952u64 - self.0[2],
            36028797018963952u64 - self.0[3],
            36028797018963952u64 - self.0[4],
        ]);
        self.0 = neg.0;
    }

    /// Construct zero.
    #[cfg(not(feature="radix_51"))]
    pub fn zero() -> FieldElement {
        FieldElement([ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }
    /// Construct zero.
    #[cfg(feature="radix_51")]
    pub fn zero() -> FieldElement {
        FieldElement([ 0, 0, 0, 0, 0 ])
    }

    /// Construct one.
    #[cfg(not(feature="radix_51"))]
    pub fn one() -> FieldElement {
        FieldElement([ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }
    /// Construct one.
    #[cfg(feature="radix_51")]
    pub fn one() -> FieldElement {
        FieldElement([ 1, 0, 0, 0, 0 ])
    }

    /// Construct -1.
    #[cfg(not(feature="radix_51"))]
    pub fn minus_one() -> FieldElement {
        FieldElement([-1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }
    /// Construct -1.
    #[cfg(feature="radix_51")]
    pub fn minus_one() -> FieldElement {
        FieldElement([2251799813685228, 2251799813685247, 2251799813685247, 2251799813685247, 2251799813685247])
    }

    /// Given 64-bit limbs, reduce to enforce the bound c_i < 2^51.
    #[cfg(feature="radix_51")]
    #[inline(always)]
    fn reduce(mut limbs: [u64; 5]) -> FieldElement {
        let low_51_bit_mask = (1u64 << 51) - 1;
        limbs[1] +=  limbs[0] >> 51;
        limbs[0] = limbs[0] & low_51_bit_mask;
        limbs[2] +=  limbs[1] >> 51;
        limbs[1] = limbs[1] & low_51_bit_mask;
        limbs[3] +=  limbs[2] >> 51;
        limbs[2] = limbs[2] & low_51_bit_mask;
        limbs[4] +=  limbs[3] >> 51;
        limbs[3] = limbs[3] & low_51_bit_mask;
        limbs[0] += (limbs[4] >> 51) * 19;
        limbs[4] = limbs[4] & low_51_bit_mask;

        FieldElement(limbs)
    }

    #[cfg(not(feature="radix_51"))]
    fn reduce(mut h: [i64; 10]) -> FieldElement { //FeCombine
        let mut c = [0i64; 10];

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

        let mut output = FieldElement([0i32; 10]);
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
    /// XXX eliminate limbs
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
    #[cfg(not(feature="radix_51"))]
    pub fn from_bytes(data: &[u8; 32]) -> FieldElement { //FeFromBytes
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

        FieldElement::reduce(h)
    }
    /// Parse a `FieldElement` from 32 bytes.
    #[cfg(feature="radix_51")]
    pub fn from_bytes(bytes: &[u8; 32]) -> FieldElement {
        let low_51_bit_mask = (1u64 << 51) - 1;
        FieldElement(
        // load bits [  0, 64), no shift
        [  load8(&bytes[ 0..])        & low_51_bit_mask
        // load bits [ 48,112), shift to [ 51,112)
        , (load8(&bytes[ 6..]) >>  3) & low_51_bit_mask
        // load bits [ 96,160), shift to [102,160)
        , (load8(&bytes[12..]) >>  6) & low_51_bit_mask
        // load bits [152,216), shift to [153,216)
        , (load8(&bytes[19..]) >>  1) & low_51_bit_mask
        // load bits [192,256), shift to [204,112)
        , (load8(&bytes[24..]) >> 12) & low_51_bit_mask
        ])
    }

    /// Marshal this FieldElement into a 32-byte array.
    ///
    /// XXX eliminate limbs
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
    #[cfg(not(feature="radix_51"))]
    pub fn to_bytes(&self) -> [u8; 32] { //FeToBytes
        // Comment preserved from ed25519.go (presumably originally from ref10):
        //
        // # Preconditions
        //
        // * `|h[i]|` bounded by 1.1*2^25, 1.1*2^24, 1.1*2^25, 1.1*2^24, etc.
        //
        // # Lemma
        //
        // Write p = 2^255 - 19 and q = floor(h/p).
        //
        // Basic claim: q = floor(2^(-255)(h + 19 * 2^-25 h9 + 2^-1)).
        //
        // # Proof
        //
        // Have |h|<=p so |q|<=1 so |19^2 * 2^-255 * q| < 1/4.
        //
        // Also have |h-2^230 * h9| < 2^230 so |19 * 2^-255 * (h-2^230 * h9)| < 1/4.
        //
        // Write y=2^(-1)-19^2 2^(-255)q-19 2^(-255)(h-2^230 h9), then 0<y<1.
        //
        // Write r = h - pq.
        //
        // Have 0 <= r< = p-1 = 2^255 - 20.
        //
        // Thus 0 <= r + 19 * 2^-255 * r < r + 19 * 2^-255 * 2^255 <= 2^255 - 1.
        //
        // Write x = r + 19 * 2^-255 * r + y.
        //
        // Then 0 < x < 2^255 so floor(2^(-255)x) = 0 so floor(q+2^(-255)x) = q.
        //
        // Have q+2^(-255)x = 2^-255 * (h + 19 * 2^-25 * h9 + 2^-1),
        // so floor(2^-255 * (h + 19 * 2^-25 * h9 + 2^-1)) = q.
        //
        let mut carry = [0i32; 10];
        let mut h: [i32; 10] = self.0;

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

        let mut s = [0u8; 32];
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
        debug_assert!((s[31] & 0b1000_0000u8) == 0u8);
        s[31] &= 127u8;

        s
    }
    /// Serialize this `FieldElement` to bytes.
    #[cfg(feature="radix_51")]
    pub fn to_bytes(&self) -> [u8; 32] {
        // This reduces to the range [0,2^255), but we need [0,2^255-19)
        let mut limbs = FieldElement::reduce(self.0).0;
        // Let h = limbs[0] + limbs[1]*2^51 + ... + limbs[4]*2^204.
        //
        // Write h = pq + r with 0 <= r < p.  We want to compute r = h mod p.
        //
        // Since h < 2^255, q = 0 or 1, with q = 0 when h < p and q = 1 when h >= p.
        //
        // Notice that h >= p <==> h + 19 >= p + 19 <==> h + 19 >= 2^255.
        // Therefore q can be computed as the carry bit of h + 19.

        let mut q = (limbs[0] + 19) >> 51;
        q = (limbs[1] + q) >> 51;
        q = (limbs[2] + q) >> 51;
        q = (limbs[3] + q) >> 51;
        q = (limbs[4] + q) >> 51;

        // Now we can compute r as r = h - pq = r - (2^255-19)q = r + 19q - 2^255q

        limbs[0] += 19*q;

        // Now carry the result to compute r + 19q ...
        let low_51_bit_mask = (1u64 << 51) - 1;
        limbs[1] +=  limbs[0] >> 51;
        limbs[0] = limbs[0] & low_51_bit_mask;
        limbs[2] +=  limbs[1] >> 51;
        limbs[1] = limbs[1] & low_51_bit_mask;
        limbs[3] +=  limbs[2] >> 51;
        limbs[2] = limbs[2] & low_51_bit_mask;
        limbs[4] +=  limbs[3] >> 51;
        limbs[3] = limbs[3] & low_51_bit_mask;
        // ... but instead of carrying (limbs[4] >> 51) = 2^255q
        // into another limb, discard it, subtracting the value
        limbs[4] = limbs[4] & low_51_bit_mask;

        // Now arrange the bits of the limbs.
        let mut s = [0u8;32];
        s[ 0] =   limbs[0]        as u8;
        s[ 1] =  (limbs[0] >>  8) as u8;
        s[ 2] =  (limbs[0] >> 16) as u8;
        s[ 3] =  (limbs[0] >> 24) as u8;
        s[ 4] =  (limbs[0] >> 32) as u8;
        s[ 5] =  (limbs[0] >> 40) as u8;
        s[ 6] = ((limbs[0] >> 48) | (limbs[1] << 3)) as u8;
        s[ 7] =  (limbs[1] >>  5) as u8;
        s[ 8] =  (limbs[1] >> 13) as u8;
        s[ 9] =  (limbs[1] >> 21) as u8;
        s[10] =  (limbs[1] >> 29) as u8;
        s[11] =  (limbs[1] >> 37) as u8;
        s[12] = ((limbs[1] >> 45) | (limbs[2] << 6)) as u8;
        s[13] =  (limbs[2] >>  2) as u8;
        s[14] =  (limbs[2] >> 10) as u8;
        s[15] =  (limbs[2] >> 18) as u8;
        s[16] =  (limbs[2] >> 26) as u8;
        s[17] =  (limbs[2] >> 34) as u8;
        s[18] =  (limbs[2] >> 42) as u8;
        s[19] = ((limbs[2] >> 50) | (limbs[3] << 1)) as u8;
        s[20] =  (limbs[3] >>  7) as u8;
        s[21] =  (limbs[3] >> 15) as u8;
        s[22] =  (limbs[3] >> 23) as u8;
        s[23] =  (limbs[3] >> 31) as u8;
        s[24] =  (limbs[3] >> 39) as u8;
        s[25] = ((limbs[3] >> 47) | (limbs[4] << 4)) as u8;
        s[26] =  (limbs[4] >>  4) as u8;
        s[27] =  (limbs[4] >> 12) as u8;
        s[28] =  (limbs[4] >> 20) as u8;
        s[29] =  (limbs[4] >> 28) as u8;
        s[30] =  (limbs[4] >> 36) as u8;
        s[31] =  (limbs[4] >> 44) as u8;

        //Clear high bit
        debug_assert!((s[31] & 0b1000_0000u8) == 0u8);
        s[31] &= 127u8;

        s
    }

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

    #[cfg(not(feature="radix_51"))]
    fn square_inner(&self) -> [i64; 10] {
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

    #[cfg(feature="radix_51")]
    #[inline(always)]
    fn square_inner(&self) -> [u64; 5] {
        /// Multiply two 64-bit integers with 128 bits of output.
        #[inline(always)]
        fn m(x: u64, y: u64) -> u128 { (x as u128) * (y as u128) }

        // Alias self, _rhs for more readable formulas
        let a: &[u64; 5] = &self.0;

        // Precomputation: 64-bit multiply by 19
        let a3_19 = 19 * a[3];
        let a4_19 = 19 * a[4];

        // Multiply to get 128-bit coefficients of output
        let     c0: u128 = m(a[0],  a[0]) + 2*( m(a[1], a4_19) + m(a[2], a3_19) );
        let mut c1: u128 = m(a[3], a3_19) + 2*( m(a[0],  a[1]) + m(a[2], a4_19) );
        let mut c2: u128 = m(a[1],  a[1]) + 2*( m(a[0],  a[2]) + m(a[4], a3_19) );
        let mut c3: u128 = m(a[4], a4_19) + 2*( m(a[0],  a[3]) + m(a[1],  a[2]) );
        let mut c4: u128 = m(a[2],  a[2]) + 2*( m(a[0],  a[4]) + m(a[1],  a[3]) );

        // Same bound as in multiply:
        //    c[i] < 2^2b * (1+i + (4-i)*19) < 2^(2b + lg(1+4*19)) < 2^(2b + 6.27)
        // where b is the bitlength of the input limbs.
        //
        // The carry (c[i] >> 51) fits into a u64 iff 2b+6.27 < 64+51 iff b <= 54.
        // After the first carry pass, all c[i] fit into u64.
        debug_assert!(a[0] < (1 << 54));
        debug_assert!(a[1] < (1 << 54));
        debug_assert!(a[2] < (1 << 54));
        debug_assert!(a[3] < (1 << 54));
        debug_assert!(a[4] < (1 << 54));

        // The 128-bit output limbs are stored in two 64-bit registers (low/high part).
        // By rebinding the names after carrying, we free the upper registers for reuse.
        let low_51_bit_mask = (1u64 << 51) - 1;
        c1 +=  (c0 >> 51) as u128;
        let mut c0: u64 = (c0 as u64) & low_51_bit_mask;
        c2 +=  (c1 >> 51) as u128;
        let c1: u64 = (c1 as u64) & low_51_bit_mask;
        c3 +=  (c2 >> 51) as u128;
        let c2: u64 = (c2 as u64) & low_51_bit_mask;
        c4 +=  (c3 >> 51) as u128;
        let c3: u64 = (c3 as u64) & low_51_bit_mask;
        c0 += ((c4 >> 51) as u64) * 19;
        let c4: u64 = (c4 as u64) & low_51_bit_mask;

        // Now c_i all fit into u64, but are not yet bounded by 2^51.
        [c0,c1,c2,c3,c4]
    }

    /// Calculates h = f*f. Can overlap h with f.
    ///
    /// XXX limbs: better to talk about headroom?
    ///
    /// # Preconditions
    ///
    /// * |f[i]| bounded by 1.1*2^26, 1.1*2^25, 1.1*2^26, 1.1*2^25, etc.
    ///
    /// # Postconditions
    ///
    /// * |h[i]| bounded by 1.1*2^25, 1.1*2^24, 1.1*2^25, 1.1*2^24, etc.
    #[cfg(not(feature="radix_51"))]
    pub fn square(&self) -> FieldElement {
        FieldElement::reduce(self.square_inner())
    }
    /// Compute `self^2`.
    #[cfg(feature="radix_51")]
    pub fn square(&self) -> FieldElement {
        FieldElement::reduce(self.square_inner())
    }

    /// Square this field element and multiply the result by 2.
    ///
    /// XXX explain why square2 exists vs square (overflow)
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
    #[cfg(not(feature="radix_51"))]
    pub fn square2(&self) -> FieldElement {
        let mut coeffs = self.square_inner();
        for i in 0..self.0.len() {
            coeffs[i] += coeffs[i];
        }
        FieldElement::reduce(coeffs)
    }
    /// Compute `2 * self^2`.
    #[cfg(feature="radix_51")]
    pub fn square2(&self) -> FieldElement {
        let mut limbs = self.square_inner();
        // For this to work, need to have 1 extra bit of headroom after carry
        // --> max 53 bit inputs, not 54
        limbs[0] *= 2;
        limbs[1] *= 2;
        limbs[2] *= 2;
        limbs[3] *= 2;
        limbs[4] *= 2;
        FieldElement::reduce(limbs)
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
    use subtle::CTNegatable;

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
    static B_LIMBS_RADIX_25_5: FieldElement = FieldElement(
        [-5652623, 8034020, 8266223, -13556020, -5672552,
         -5582839, -12603138, 15161929, -16418207, 13296296]);

    #[cfg(not(feature="radix_51"))]
    #[test]
    fn from_bytes_vs_radix_25_5_limb_constants() {
        let test_elt = FieldElement::from_bytes(&B_BYTES);
        for i in 0..10 {
            assert!(test_elt[i] == B_LIMBS_RADIX_25_5[i]);
        }
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
