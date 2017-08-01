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

//! Field arithmetic for ℤ/(2²⁵⁵-19), using 64-bit arithmetic wuth
//! 128-bit products.
//!
//! On x86_64, the multiplications lower to `MUL` instructions taking
//! 64-bit inputs and producing 128-bit outputs.  On other platforms,
//! this implementation is not recommended.  On Haswell and newer, the
//! BMI2 instruction set provides `MULX` and friends, which gives even
//! better performance.

use core::fmt::Debug;
use core::ops::{Add, AddAssign};
use core::ops::{Sub, SubAssign};
use core::ops::{Mul, MulAssign};
use core::ops::Neg;

use subtle::ConditionallyAssignable;

use utils::load8;

/// In the 64-bit implementation, field elements are represented in
/// radix 2^51 as five `u64`s.
pub type Limb = u64;

/// A `FieldElement64` represents an element of the field GF(2^255 - 19).
///
/// In the 64-bit implementation, a `FieldElement` is represented in
/// radix 2^51 as five `u64`s; the coefficients are allowed to grow up
/// to 2^54 between reductions mod `p`.
#[derive(Copy, Clone)]
pub struct FieldElement64(pub [u64; 5]);

impl Debug for FieldElement64 {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "FieldElement64: {:?}", &self.0[..])
    }
}

impl<'b> AddAssign<&'b FieldElement64> for FieldElement64 {
    fn add_assign(&mut self, _rhs: &'b FieldElement64) {
        for i in 0..5 {
            self.0[i] += _rhs.0[i];
        }
    }
}

impl<'a, 'b> Add<&'b FieldElement64> for &'a FieldElement64 {
    type Output = FieldElement64;
    fn add(self, _rhs: &'b FieldElement64) -> FieldElement64 {
        let mut output = *self;
        output += _rhs;
        output
    }
}

impl<'b> SubAssign<&'b FieldElement64> for FieldElement64 {
    fn sub_assign(&mut self, _rhs: &'b FieldElement64) {
        let result = (self as &FieldElement64) - _rhs;
        self.0 = result.0;
    }
}

impl<'a, 'b> Sub<&'b FieldElement64> for &'a FieldElement64 {
    type Output = FieldElement64;
    fn sub(self, _rhs: &'b FieldElement64) -> FieldElement64 {
        // To avoid underflow, first add a multiple of p.
        // Choose 16*p = p << 4 to be larger than 54-bit _rhs.
        //
        // If we could statically track the bitlengths of the limbs
        // of every FieldElement64, we could choose a multiple of p
        // just bigger than _rhs and avoid having to do a reduction.
        //
        // Since we don't yet have type-level integers to do this, we
        // have to add an explicit reduction call here, which is a
        // somewhat significant cost.
        FieldElement64::reduce([
            (self.0[0] + 36028797018963664u64) - _rhs.0[0],
            (self.0[1] + 36028797018963952u64) - _rhs.0[1],
            (self.0[2] + 36028797018963952u64) - _rhs.0[2],
            (self.0[3] + 36028797018963952u64) - _rhs.0[3],
            (self.0[4] + 36028797018963952u64) - _rhs.0[4],
        ])
    }
}

impl<'b> MulAssign<&'b FieldElement64> for FieldElement64 {
    fn mul_assign(&mut self, _rhs: &'b FieldElement64) {
        let result = (self as &FieldElement64) * _rhs;
        self.0 = result.0;
    }
}

impl<'a, 'b> Mul<&'b FieldElement64> for &'a FieldElement64 {
    type Output = FieldElement64;
    fn mul(self, _rhs: &'b FieldElement64) -> FieldElement64 {
        /// Helper function to multiply two 64-bit integers with 128
        /// bits of output.
        #[inline(always)]
        fn m(x: u64, y: u64) -> u128 { (x as u128) * (y as u128) }

        // Alias self, _rhs for more readable formulas
        let a: &[u64; 5] = &self.0;
        let b: &[u64; 5] = &_rhs.0;

        // 64-bit precomputations to avoid 128-bit multiplications
        let b1_19 = b[1] * 19;
        let b2_19 = b[2] * 19;
        let b3_19 = b[3] * 19;
        let b4_19 = b[4] * 19;

        // Multiply to get 128-bit coefficients of output
        let     c0: u128 = m(a[0],b[0]) + m(a[4],b1_19) + m(a[3],b2_19) + m(a[2],b3_19) + m(a[1],b4_19);
        let mut c1: u128 = m(a[1],b[0]) + m(a[0],b[1])  + m(a[4],b2_19) + m(a[3],b3_19) + m(a[2],b4_19);
        let mut c2: u128 = m(a[2],b[0]) + m(a[1],b[1])  + m(a[0],b[2])  + m(a[4],b3_19) + m(a[3],b4_19);
        let mut c3: u128 = m(a[3],b[0]) + m(a[2],b[1])  + m(a[1],b[2])  + m(a[0],b[3])  + m(a[4],b4_19);
        let mut c4: u128 = m(a[4],b[0]) + m(a[3],b[1])  + m(a[2],b[2])  + m(a[1],b[3])  + m(a[0],b[4]);

        // Now c[i] < 2^2b * (1+i + (4-i)*19) < 2^(2b + lg(1+4*19)) < 2^(2b + 6.27)
        // where b is the bitlength of the input limbs.

        // The carry (c[i] >> 51) fits into a u64 iff 2b+6.27 < 64+51 iff b <= 54.
        // After the first carry pass, all c[i] fit into u64.
        debug_assert!(a[0] < (1 << 54)); debug_assert!(b[0] < (1 << 54));
        debug_assert!(a[1] < (1 << 54)); debug_assert!(b[1] < (1 << 54));
        debug_assert!(a[2] < (1 << 54)); debug_assert!(b[2] < (1 << 54));
        debug_assert!(a[3] < (1 << 54)); debug_assert!(b[3] < (1 << 54));
        debug_assert!(a[4] < (1 << 54)); debug_assert!(b[4] < (1 << 54));

        // The 128-bit output limbs are stored in two 64-bit registers
        // (low/high part).  By rebinding the names after carrying, we
        // inform LLVM that the values have shrunk, so it can
        // efficiently allocate registers.
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

        FieldElement64::reduce([c0,c1,c2,c3,c4])
    }
}

impl<'a> Neg for &'a FieldElement64 {
    type Output = FieldElement64;
    fn neg(self) -> FieldElement64 {
        let mut output = *self;
        output.negate();
        output
    }
}

impl ConditionallyAssignable for FieldElement64 {
    fn conditional_assign(&mut self, f: &FieldElement64, choice: u8) {
        let mask = (-(choice as i64)) as u64;
        for i in 0..5 {
            self.0[i] ^= mask & (self.0[i] ^ f.0[i]);
        }
    }
}

impl FieldElement64 {
    /// Invert the sign of this field element
    pub fn negate(&mut self) {
        // See commentary in the Sub impl
        let neg = FieldElement64::reduce([
            36028797018963664u64 - self.0[0],
            36028797018963952u64 - self.0[1],
            36028797018963952u64 - self.0[2],
            36028797018963952u64 - self.0[3],
            36028797018963952u64 - self.0[4],
        ]);
        self.0 = neg.0;
    }

    /// Construct zero.
    pub fn zero() -> FieldElement64 {
        FieldElement64([ 0, 0, 0, 0, 0 ])
    }

    /// Construct one.
    pub fn one() -> FieldElement64 {
        FieldElement64([ 1, 0, 0, 0, 0 ])
    }

    /// Construct -1.
    pub fn minus_one() -> FieldElement64 {
        FieldElement64([2251799813685228, 2251799813685247, 2251799813685247, 2251799813685247, 2251799813685247])
    }

    /// Given 64-bit limbs, reduce to enforce the bound c_i < 2^51.
    #[inline(always)]
    fn reduce(mut limbs: [u64; 5]) -> FieldElement64 {
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

        FieldElement64(limbs)
    }

    /// Load a `FieldElement64` from the low 255 bits of a 256-bit
    /// input.
    ///
    /// # Warning
    ///
    /// This function does not check that the input used the canonical
    /// representative.  It masks the high bit, but it will happily
    /// decode 2^255 - 18 to 1.  Applications that require a canonical
    /// encoding of every field element should decode, re-encode to
    /// the canonical encoding, and check that the input was
    /// canonical.
    ///
    pub fn from_bytes(bytes: &[u8; 32]) -> FieldElement64 {
        let low_51_bit_mask = (1u64 << 51) - 1;
        FieldElement64(
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

    /// Serialize this `FieldElement64` to a 32-byte array.  The
    /// encoding is canonical.
    pub fn to_bytes(&self) -> [u8; 32] {
        // This reduces to the range [0,2^255), but we need [0,2^255-19).
        let mut limbs = FieldElement64::reduce(self.0).0;

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

        // High bit should be zero.
        debug_assert!((s[31] & 0b1000_0000u8) == 0u8);

        s
    }

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

    /// Returns the square of this field element.
    pub fn square(&self) -> FieldElement64 {
        FieldElement64::reduce(self.square_inner())
    }

    /// Returns 2 times the square of this field element.
    pub fn square2(&self) -> FieldElement64 {
        let mut limbs = self.square_inner();
        // For this to work, need to have 1 extra bit of headroom after carry
        // --> max 53 bit inputs, not 54
        //
        // XXX check that this is correct; I think it isn't -- hdevalence
        limbs[0] *= 2;
        limbs[1] *= 2;
        limbs[2] *= 2;
        limbs[3] *= 2;
        limbs[4] *= 2;
        FieldElement64::reduce(limbs)
    }
}
