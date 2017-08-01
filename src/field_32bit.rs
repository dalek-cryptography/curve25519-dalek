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

//! Field arithmetic for ℤ/(2²⁵⁵-19), using 32-bit arithmetic with
//! 64-bit products.
//!
//! Based on Adam Langley's curve25519-donna and (Golang) ed25519
//! implementations.
//!
//! This implementation is intended for platforms that can multiply
//! 32-bit inputs to produce 64-bit outputs.
//!
//! This implementation is not preferred for use on x86_64, since the
//! 64-bit implementation is both much simpler and much faster.
//! However, that implementation requires Rust's `u128`, which is not
//! yet stable.

use core::fmt::Debug;
use core::ops::{Add, AddAssign};
use core::ops::{Sub, SubAssign};
use core::ops::{Mul, MulAssign};
use core::ops::Neg;

use subtle::ConditionallyAssignable;

use utils::{load3, load4};

/// A `FieldElement32` represents an element of the field GF(2^255 - 19).
///
/// In the 32-bit implementation, a `FieldElement32` is represented in
/// radix 2^25.5 as ten `i32`s, so that an element t, entries
/// t[0],...,t[9], represents the integer t[0]+2^26 t[1]+2^51
/// t[2]+2^77 t[3]+2^102 t[4]+...+2^230 t[9].
///
/// The coefficients t[i] are allowed to grow between multiplications.
///
/// XXX document by how much
#[derive(Copy, Clone)]
pub struct FieldElement32(pub [i32; 10]);

impl Debug for FieldElement32 {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "FieldElement32: {:?}", &self.0[..])
    }
}

impl<'b> AddAssign<&'b FieldElement32> for FieldElement32 {
    fn add_assign(&mut self, _rhs: &'b FieldElement32) {
        for i in 0..10 {
            self.0[i] += _rhs.0[i];
        }
    }
}

impl<'a, 'b> Add<&'b FieldElement32> for &'a FieldElement32 {
    type Output = FieldElement32;
    fn add(self, _rhs: &'b FieldElement32) -> FieldElement32 {
        let mut output = *self;
        output += _rhs;
        output
    }
}

impl<'b> SubAssign<&'b FieldElement32> for FieldElement32 {
    fn sub_assign(&mut self, _rhs: &'b FieldElement32) {
        for i in 0..10 {
            self.0[i] -= _rhs.0[i];
        }
    }
}

impl<'a, 'b> Sub<&'b FieldElement32> for &'a FieldElement32 {
    type Output = FieldElement32;
    fn sub(self, _rhs: &'b FieldElement32) -> FieldElement32 {
        let mut output = *self;
        output -= _rhs;
        output
    }
}

impl<'b> MulAssign<&'b FieldElement32> for FieldElement32 {
    fn mul_assign(&mut self, _rhs: &'b FieldElement32) {
        let result = (self as &FieldElement32) * _rhs;
        self.0 = result.0;
    }
}

impl<'a, 'b> Mul<&'b FieldElement32> for &'a FieldElement32 {
    type Output = FieldElement32;
    fn mul(self, _rhs: &'b FieldElement32) -> FieldElement32 {
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
        let f0 = self.0[0] as i64;
        let f1 = self.0[1] as i64;
        let f2 = self.0[2] as i64;
        let f3 = self.0[3] as i64;
        let f4 = self.0[4] as i64;
        let f5 = self.0[5] as i64;
        let f6 = self.0[6] as i64;
        let f7 = self.0[7] as i64;
        let f8 = self.0[8] as i64;
        let f9 = self.0[9] as i64;

        let f1_2 = (2 * self.0[1]) as i64;
        let f3_2 = (2 * self.0[3]) as i64;
        let f5_2 = (2 * self.0[5]) as i64;
        let f7_2 = (2 * self.0[7]) as i64;
        let f9_2 = (2 * self.0[9]) as i64;

        let g0 = _rhs.0[0] as i64;
        let g1 = _rhs.0[1] as i64;
        let g2 = _rhs.0[2] as i64;
        let g3 = _rhs.0[3] as i64;
        let g4 = _rhs.0[4] as i64;
        let g5 = _rhs.0[5] as i64;
        let g6 = _rhs.0[6] as i64;
        let g7 = _rhs.0[7] as i64;
        let g8 = _rhs.0[8] as i64;
        let g9 = _rhs.0[9] as i64;

        let g1_19 = (19 * _rhs.0[1]) as i64; /* 1.4*2^29 */
        let g2_19 = (19 * _rhs.0[2]) as i64; /* 1.4*2^30; still ok */
        let g3_19 = (19 * _rhs.0[3]) as i64;
        let g4_19 = (19 * _rhs.0[4]) as i64;
        let g5_19 = (19 * _rhs.0[5]) as i64;
        let g6_19 = (19 * _rhs.0[6]) as i64;
        let g7_19 = (19 * _rhs.0[7]) as i64;
        let g8_19 = (19 * _rhs.0[8]) as i64;
        let g9_19 = (19 * _rhs.0[9]) as i64;

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

        FieldElement32::reduce([h0, h1, h2, h3, h4, h5, h6, h7, h8, h9])
    }
}

impl<'a> Neg for &'a FieldElement32 {
    type Output = FieldElement32;
    fn neg(self) -> FieldElement32 {
        let mut output = *self;
        output.negate();
        output
    }
}

impl ConditionallyAssignable for FieldElement32 {
    fn conditional_assign(&mut self, f: &FieldElement32, choice: u8) {
        let mask = -(choice as i32);
        for i in 0..10 {
            self.0[i] ^= mask & (self.0[i] ^ f.0[i]);
        }
    }
}

impl FieldElement32 {
    /// Invert the sign of this field element
    pub fn negate(&mut self) {
        for i in 0..10 {
            self.0[i] = -self.0[i];
        }
    }

    /// Construct zero.
    pub fn zero() -> FieldElement32 {
        FieldElement32([ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }

    /// Construct one.
    pub fn one() -> FieldElement32 {
        FieldElement32([ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }

    /// Construct -1.
    pub fn minus_one() -> FieldElement32 {
        FieldElement32([-1, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }

    fn reduce(mut h: [i64; 10]) -> FieldElement32 { //FeCombine
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

        let mut output = FieldElement32([0i32; 10]);
        output.0[0] = h[0] as i32;
        output.0[1] = h[1] as i32;
        output.0[2] = h[2] as i32;
        output.0[3] = h[3] as i32;
        output.0[4] = h[4] as i32;
        output.0[5] = h[5] as i32;
        output.0[6] = h[6] as i32;
        output.0[7] = h[7] as i32;
        output.0[8] = h[8] as i32;
        output.0[9] = h[9] as i32;
        output
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
    /// XXX the above applies to the 64-bit implementation; check that
    /// it applies here too.
    pub fn from_bytes(data: &[u8; 32]) -> FieldElement32 { //FeFromBytes
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

        FieldElement32::reduce(h)
    }

    /// Serialize this `FieldElement64` to a 32-byte array.  The
    /// encoding is canonical.
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

        // Check that high bit is cleared
        debug_assert!((s[31] & 0b1000_0000u8) == 0u8);

        s
    }

    fn square_inner(&self) -> [i64; 10] {
        let f0     = self.0[0]       as i64;
        let f1     = self.0[1]       as i64;
        let f2     = self.0[2]       as i64;
        let f3     = self.0[3]       as i64;
        let f4     = self.0[4]       as i64;
        let f5     = self.0[5]       as i64;
        let f6     = self.0[6]       as i64;
        let f7     = self.0[7]       as i64;
        let f8     = self.0[8]       as i64;
        let f9     = self.0[9]       as i64;
        let f0_2   = (2 * self.0[0]) as i64;
        let f1_2   = (2 * self.0[1]) as i64;
        let f2_2   = (2 * self.0[2]) as i64;
        let f3_2   = (2 * self.0[3]) as i64;
        let f4_2   = (2 * self.0[4]) as i64;
        let f5_2   = (2 * self.0[5]) as i64;
        let f6_2   = (2 * self.0[6]) as i64;
        let f7_2   = (2 * self.0[7]) as i64;
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
    /// XXX limbs: better to talk about headroom?
    ///
    /// # Preconditions
    ///
    /// * |f[i]| bounded by 1.1*2^26, 1.1*2^25, 1.1*2^26, 1.1*2^25, etc.
    ///
    /// # Postconditions
    ///
    /// * |h[i]| bounded by 1.1*2^25, 1.1*2^24, 1.1*2^25, 1.1*2^24, etc.
    pub fn square(&self) -> FieldElement32 {
        FieldElement32::reduce(self.square_inner())
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
    pub fn square2(&self) -> FieldElement32 {
        let mut coeffs = self.square_inner();
        for i in 0..self.0.len() {
            coeffs[i] += coeffs[i];
        }
        FieldElement32::reduce(coeffs)
    }
}
