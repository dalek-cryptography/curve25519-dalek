// -*- mode: rust; -*-
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

//! Arithmetic for scalar multiplication.
//!
//! The Ed25519 basepoint P has prime order
//!
//! l = 2^252 + 27742317777372353535851937790883648493.
//!
//! Thus a multiple `aP` of the basepoint (with a ∈ ℤ) depends only
//! on the value of `a (mod l)`, or equivalently, the image of `a` in
//! the quotient ℤ/lℤ.
//!
//! The `Scalar` struct represents an element in ℤ/lℤ.
//!
//! Arithmetic operations on `Scalar`s are done using 12 21-bit limbs.
//! However, in contrast to `FieldElement`s, `Scalar`s are stored in
//! memory as bytes, allowing easy access to the bits of the `Scalar`.

use std::clone::Clone;
use std::ops::{Index, IndexMut};

use rand::Rng;

use field::{load3, load4};

/// The `Scalar` struct represents an element in ℤ/lℤ, where
///
/// l = 2^252 + 27742317777372353535851937790883648493
///
/// is the order of the basepoint.
#[derive(Copy)]
pub struct Scalar(pub [u8; 32]);

impl Clone for Scalar {
    fn clone(&self) -> Scalar { *self }
}

impl Index<usize> for Scalar {
    type Output = u8;

    fn index<'a>(&'a self, _index: usize) -> &'a u8 {
        let ret: &'a u8 = &(self.0[_index]);
        ret
    }
}

impl IndexMut<usize> for Scalar {
    fn index_mut<'a>(&'a mut self, _index: usize) -> &'a mut u8 {
        let ret: &'a mut u8 = &mut(self.0[_index]);
        ret
    }
}

impl Scalar {
    /// Return a `Scalar` chosen uniformly at random using a CSPRNG.
    /// Panics if the operating system's CSPRNG is unavailable.
    ///
    /// # Inputs
    ///
    /// * `cspring`: any cryptographically secure PRNG which
    ///   implements the `rand::Rng` interface.
    ///
    /// # Returns
    ///
    /// A random scalar within ℤ/lℤ.
    pub fn random<T: Rng>(csprng: &mut T) -> Self {
        let mut scalar_bytes = [0u8; 64];
        csprng.fill_bytes(&mut scalar_bytes);
        Scalar::reduce(&scalar_bytes)
    }

    /// Construct the additive identity
    pub fn zero() -> Self {
        Scalar([0u8; 32])
    }

    /// Construct the multiplicative identity
    pub fn one() -> Self {
        Scalar([ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }

    /// Compute a width-5 "Non-Adjacent Form" of this scalar.
    ///
    /// A width-`w` NAF of a positive integer `k` is an expression
    /// `k = sum(k[i]*2^i for i in range(l))`, where each nonzero
    /// coefficient `k[i]` is odd and bounded by `|k[i]| < 2^(w-1)`,
    /// `k[l-1]` is nonzero, and at most one of any `w` consecutive
    /// coefficients is nonzero.  (Hankerson, Menezes, Vanstone; def 3.32).
    ///
    /// Intuitively, this is like a binary expansion, except that we
    /// allow some coefficients to grow up to `2^(w-1)` so that the
    /// nonzero coefficients are as sparse as possible.
    pub fn non_adjacent_form(&self) -> [i8;256] {
        // Step 1: write out bits of the scalar
        let mut naf = [0i8; 256];
        for i in 0..256 {
            // As i runs from 0..256, the bottom 3 bits index the bit,
            // while the upper bits index the byte.
            naf[i] = ((self.0[i>>3] >> (i&7)) & 1u8) as i8;
        }

        // Step 2: zero coefficients by carrying them upwards or downwards 
        'bits: for i in 0..256 {
            if naf[i] == 0 { continue 'bits; }
            'window: for b in 1..6 {
                if     i+b  >= 256  { break 'window; }
                if naf[i+b] == 0    { continue 'window; }
                let potential_carry = naf[i+b] << b;
                if  naf[i+b] + potential_carry <= 15 {
                    // Eliminate naf[i+b] by carrying its value onto naf[i]
                    naf[i] += potential_carry;
                    naf[i+b] = 0;
                } else if naf[i+b] - potential_carry >= -15 {
                    // Eliminate naf[i+b] by carrying its value upwards.
                    naf[i] -= potential_carry; // Subtract 2^(i+b)
                    'carry: for k in i+b..256 {
                        if naf[k] != 0 {
                            // Since naf[k] = 0 or 1 for k > i, naf[k] == 1.
                            naf[k] = 0; // Subtract 2^k
                        } else {
                            // By now we have subtracted 2^k = 
                            // 2^(i+b) + 2^(i+b) + 2^(i+b+1) + ... + 2^(k-1).
                            naf[k] = 1; // Add back 2^k.
                            break 'carry;
                        }
                    }
                }
            }
        }

        naf
    }

    /// Create a scalar by packing 12 21-bit limbs into bytes.
    fn pack_limbs(limbs: &[i64;12]) -> Scalar {
        let mut s = Scalar::zero();
        s[0]  =  (limbs[ 0] >>  0)                     as u8;
        s[1]  =  (limbs[ 0] >>  8)                     as u8;
        s[2]  = ((limbs[ 0] >> 16) | (limbs[ 1] << 5)) as u8;
        s[3]  =  (limbs[ 1] >>  3)                     as u8;
        s[4]  =  (limbs[ 1] >> 11)                     as u8;
        s[5]  = ((limbs[ 1] >> 19) | (limbs[ 2] << 2)) as u8;
        s[6]  =  (limbs[ 2] >>  6)                     as u8;
        s[7]  = ((limbs[ 2] >> 14) | (limbs[ 3] << 7)) as u8;
        s[8]  =  (limbs[ 3] >>  1)                     as u8;
        s[9]  =  (limbs[ 3] >>  9)                     as u8;
        s[10] = ((limbs[ 3] >> 17) | (limbs[ 4] << 4)) as u8;
        s[11] =  (limbs[ 4] >>  4)                     as u8;
        s[12] =  (limbs[ 4] >> 12)                     as u8;
        s[13] = ((limbs[ 4] >> 20) | (limbs[ 5] << 1)) as u8;
        s[14] =  (limbs[ 5] >>  7)                     as u8;
        s[15] = ((limbs[ 5] >> 15) | (limbs[ 6] << 6)) as u8;
        s[16] =  (limbs[ 6] >>  2)                     as u8;
        s[17] =  (limbs[ 6] >> 10)                     as u8;
        s[18] = ((limbs[ 6] >> 18) | (limbs[ 7] << 3)) as u8;
        s[19] =  (limbs[ 7] >>  5)                     as u8;
        s[20] =  (limbs[ 7] >> 13)                     as u8;
        s[21] =  (limbs[ 8] >>  0)                     as u8;
        s[22] =  (limbs[ 8] >>  8)                     as u8;
        s[23] = ((limbs[ 8] >> 16) | (limbs[ 9] << 5)) as u8;
        s[24] =  (limbs[ 9] >>  3)                     as u8;
        s[25] =  (limbs[ 9] >> 11)                     as u8;
        s[26] = ((limbs[ 9] >> 19) | (limbs[10] << 2)) as u8;
        s[27] =  (limbs[10] >>  6)                     as u8;
        s[28] = ((limbs[10] >> 14) | (limbs[11] << 7)) as u8;
        s[29] =  (limbs[11] >>  1)                     as u8;
        s[30] =  (limbs[11] >>  9)                     as u8;
        s[31] =  (limbs[11] >> 17)                     as u8;

        s
    }

    // Unpack a scalar into 12 21-bit limbs.
    fn unpack_limbs(&self) -> [i64;12] {
        let mask_21bits: i64 = (1 << 21) -1;
        let mut a = [0i64;12];
        a[ 0]  = mask_21bits &  load3(&self.0[ 0..])      ;
        a[ 1]  = mask_21bits & (load4(&self.0[ 2..]) >> 5);
        a[ 2]  = mask_21bits & (load3(&self.0[ 5..]) >> 2);
        a[ 3]  = mask_21bits & (load4(&self.0[ 7..]) >> 7);
        a[ 4]  = mask_21bits & (load4(&self.0[10..]) >> 4);
        a[ 5]  = mask_21bits & (load3(&self.0[13..]) >> 1);
        a[ 6]  = mask_21bits & (load4(&self.0[15..]) >> 6);
        a[ 7]  = mask_21bits & (load3(&self.0[18..]) >> 3);
        a[ 8]  = mask_21bits &  load3(&self.0[21..])      ;
        a[ 9]  = mask_21bits & (load4(&self.0[23..]) >> 5);
        a[10]  = mask_21bits & (load3(&self.0[26..]) >> 2);
        a[11]  =                load4(&self.0[28..]) >> 7 ;

        a
    }

    /// Write this scalar in radix 16, with coefficients in `[-8,8)`,
    /// i.e., compute `a_i` such that
    ///
    ///    a = a_0 + a_1*16^1 + ... + a_63*16^63,
    ///
    /// with `-8 ≤ a_i < 8` for `0 ≤ i < 63` and `-8 ≤ a_63 ≤ 8`.
    ///
    /// Precondition: self[31] <= 127.  This is the case whenever
    /// `self` is reduced.
    pub fn to_radix_16(&self) -> [i8;64] {
        debug_assert!(self[31] <= 127);
        let mut output = [0i8; 64];

        // Step 1: change radix.
        // Convert from radix 256 (bytes) to radix 16 (nibbles)
        #[inline(always)]
        fn bot_half(x: u8) -> u8 { (x >> 0) & 15 }
        #[inline(always)]
        fn top_half(x: u8) -> u8 { (x >> 4) & 15 }

        for i in 0..32 {
            output[2*i  ] = bot_half(self[i]) as i8;
            output[2*i+1] = top_half(self[i]) as i8;
        }
        // Precondition note: since self[31] <= 127, output[63] <= 7

        // Step 2: recenter coefficients from [0,16) to [-8,8)
        for i in 0..63 {
            let carry    = (output[i] + 8) >> 4;
            output[i  ] -= carry << 4;
            output[i+1] += carry;
        }
        // Precondition note: output[63] is not recentered.  It
        // increases by carry <= 1.  Thus output[63] <= 8.

        output
    }

    /// Reduce limbs in-place.  Reduction is mod
    ///
    ///   l = 2^252 + 27742317777372353535851937790883648493,
    ///
    /// so
    ///
    ///   2^252 = -27742317777372353535851937790883648493 (mod l).
    ///
    /// We can write the right-hand side in 21-bit limbs as
    /// 
    /// rhs =    666643 * 2^0
    ///        + 470296 * 2^21
    ///        + 654183 * 2^42
    ///        - 997805 * 2^63
    ///        + 136657 * 2^84
    ///        - 683901 * 2^105
    ///
    /// The (12+k)-th limb of `limbs` is the coefficient of
    ///
    ///    2^(252 + 21*k)
    ///
    /// since 12*21 = 252.  By the above, we have that
    ///
    ///    c * 2^(252 + 21*k) =   c * 666643 * 2^(21*k)
    ///                         + c * 470296 * 2^(42*k) + ...
    ///
    /// so we can eliminate it by adding those values to the lower
    /// limbs.  Reduction mod l amounts to eliminating all of the
    /// high limbs while carrying as appropriate to prevent
    /// overflows in the lower limbs.
    fn reduce_limbs(mut limbs: &mut [i64;24]) {
        #[inline]
        #[allow(dead_code)]
        fn do_reduction(limbs: &mut [i64;24], i:usize) {
            limbs[i - 12] += limbs[i] * 666643;
            limbs[i - 11] += limbs[i] * 470296;
            limbs[i - 10] += limbs[i] * 654183;
            limbs[i -  9] -= limbs[i] * 997805;
            limbs[i -  8] += limbs[i] * 136657;
            limbs[i -  7] -= limbs[i] * 683901;
            limbs[i] = 0;
        }
        /// Carry excess from the `i`-th limb into the `(i+1)`-th limb.
        /// Postcondition: `0 <= limbs[i] < 2^21`.
        #[inline]
        #[allow(dead_code)]
        fn do_carry_uncentered(limbs: &mut [i64; 24], i: usize) {
            let carry: i64 = limbs[i] >> 21;
            limbs[i+1] += carry;
            limbs[i  ] -= carry << 21;
        }
        #[inline]
        #[allow(dead_code)]
        /// Carry excess from the `i`-th limb into the `(i+1)`-th limb.
        /// Postcondition: `-2^20 <= limbs[i] < 2^20`.
        fn do_carry_centered(limbs: &mut [i64;24], i:usize) {
            let carry: i64 = (limbs[i] + (1<<20)) >> 21;
            limbs[i+1] += carry;
            limbs[i  ] -= carry << 21;
        }

        for i in 0..23 {
            do_carry_centered(&mut limbs, i);
        }
        for i in (0..23).filter(|x| x % 2 == 1) {
            do_carry_centered(&mut limbs, i);
        }

        do_reduction(&mut limbs, 23);
        do_reduction(&mut limbs, 22);
        do_reduction(&mut limbs, 21);
        do_reduction(&mut limbs, 20);
        do_reduction(&mut limbs, 19);
        do_reduction(&mut limbs, 18);

        for i in (6..18).filter(|x| x % 2 == 0) {
            do_carry_centered(&mut limbs, i);
        }
        for i in (6..16).filter(|x| x % 2 == 1) {
            do_carry_centered(&mut limbs, i);
        }

        do_reduction(&mut limbs, 17);
        do_reduction(&mut limbs, 16);
        do_reduction(&mut limbs, 15);
        do_reduction(&mut limbs, 14);
        do_reduction(&mut limbs, 13);
        do_reduction(&mut limbs, 12);

        for i in (0..12).filter(|x| x % 2 == 0) {
            do_carry_centered(&mut limbs, i);
        }
        for i in (0..12).filter(|x| x % 2 == 1) {
            do_carry_centered(&mut limbs, i);
        }

        do_reduction(&mut limbs, 12);

        for i in 0..12 {
            do_carry_uncentered(&mut limbs, i);
        }

        do_reduction(&mut limbs, 12);

        for i in 0..11 {
            do_carry_uncentered(&mut limbs, i);
        }
    }

    /// Compute `ab+c (mod l)`.
    pub fn multiply_add(a: &Scalar, b: &Scalar, c: &Scalar) -> Scalar {
        // Unpack scalars into limbs
        let al = a.unpack_limbs();
        let bl = b.unpack_limbs();
        let cl = c.unpack_limbs();

        let mut result = [0i64;24];

        // Multiply a and b, and add c
        result[0]  =         cl[0] +  al[0]*bl[0];
        result[1]  =         cl[1] +  al[0]*bl[1]  +  al[1]*bl[0];
        result[2]  =         cl[2] +  al[0]*bl[2]  +  al[1]*bl[1] +  al[2]*bl[0];
        result[3]  =         cl[3] +  al[0]*bl[3]  +  al[1]*bl[2] +  al[2]*bl[1] +  al[3]*bl[0];
        result[4]  =         cl[4] +  al[0]*bl[4]  +  al[1]*bl[3] +  al[2]*bl[2] +  al[3]*bl[1] +  al[4]*bl[0];
        result[5]  =         cl[5] +  al[0]*bl[5]  +  al[1]*bl[4] +  al[2]*bl[3] +  al[3]*bl[2] +  al[4]*bl[1] +  al[5]*bl[0];
        result[6]  =         cl[6] +  al[0]*bl[6]  +  al[1]*bl[5] +  al[2]*bl[4] +  al[3]*bl[3] +  al[4]*bl[2] +  al[5]*bl[1] +  al[6]*bl[0];
        result[7]  =         cl[7] +  al[0]*bl[7]  +  al[1]*bl[6] +  al[2]*bl[5] +  al[3]*bl[4] +  al[4]*bl[3] +  al[5]*bl[2] +  al[6]*bl[1] +  al[7]*bl[0];
        result[8]  =         cl[8] +  al[0]*bl[8]  +  al[1]*bl[7] +  al[2]*bl[6] +  al[3]*bl[5] +  al[4]*bl[4] +  al[5]*bl[3] +  al[6]*bl[2] +  al[7]*bl[1] +  al[8]*bl[0];
        result[9]  =         cl[9] +  al[0]*bl[9]  +  al[1]*bl[8] +  al[2]*bl[7] +  al[3]*bl[6] +  al[4]*bl[5] +  al[5]*bl[4] +  al[6]*bl[3] +  al[7]*bl[2] +  al[8]*bl[1] +  al[9]*bl[0];
        result[10] =        cl[10] +  al[0]*bl[10] +  al[1]*bl[9] +  al[2]*bl[8] +  al[3]*bl[7] +  al[4]*bl[6] +  al[5]*bl[5] +  al[6]*bl[4] +  al[7]*bl[3] +  al[8]*bl[2] +  al[9]*bl[1] + al[10]*bl[0];
        result[11] =        cl[11] +  al[0]*bl[11] + al[1]*bl[10] +  al[2]*bl[9] +  al[3]*bl[8] +  al[4]*bl[7] +  al[5]*bl[6] +  al[6]*bl[5] +  al[7]*bl[4] +  al[8]*bl[3] +  al[9]*bl[2] + al[10]*bl[1] + al[11]*bl[0];
        result[12] =  al[1]*bl[11] +  al[2]*bl[10] +  al[3]*bl[9] +  al[4]*bl[8] +  al[5]*bl[7] +  al[6]*bl[6] +  al[7]*bl[5] +  al[8]*bl[4] +  al[9]*bl[3] + al[10]*bl[2] + al[11]*bl[1];
        result[13] =  al[2]*bl[11] +  al[3]*bl[10] +  al[4]*bl[9] +  al[5]*bl[8] +  al[6]*bl[7] +  al[7]*bl[6] +  al[8]*bl[5] +  al[9]*bl[4] + al[10]*bl[3] + al[11]*bl[2];
        result[14] =  al[3]*bl[11] +  al[4]*bl[10] +  al[5]*bl[9] +  al[6]*bl[8] +  al[7]*bl[7] +  al[8]*bl[6] +  al[9]*bl[5] + al[10]*bl[4] + al[11]*bl[3];
        result[15] =  al[4]*bl[11] +  al[5]*bl[10] +  al[6]*bl[9] +  al[7]*bl[8] +  al[8]*bl[7] +  al[9]*bl[6] + al[10]*bl[5] + al[11]*bl[4];
        result[16] =  al[5]*bl[11] +  al[6]*bl[10] +  al[7]*bl[9] +  al[8]*bl[8] +  al[9]*bl[7] + al[10]*bl[6] + al[11]*bl[5];
        result[17] =  al[6]*bl[11] +  al[7]*bl[10] +  al[8]*bl[9] +  al[9]*bl[8] + al[10]*bl[7] + al[11]*bl[6];
        result[18] =  al[7]*bl[11] +  al[8]*bl[10] +  al[9]*bl[9] + al[10]*bl[8] + al[11]*bl[7];
        result[19] =  al[8]*bl[11] +  al[9]*bl[10] + al[10]*bl[9] + al[11]*bl[8];
        result[20] =  al[9]*bl[11] + al[10]*bl[10] + al[11]*bl[9];
        result[21] = al[10]*bl[11] + al[11]*bl[10];
        result[22] = al[11]*bl[11];
        result[23] =          0i64;

        // reduce limbs and pack into output
        Scalar::reduce_limbs(&mut result);
        Scalar::pack_limbs(array_ref!(result, 0, 12))
    }

    /// Reduce a 512-bit little endian number mod l
    pub fn reduce(input: &[u8;64]) -> Scalar {
        let mut s = [0i64;24];

        // XXX express this as two unpack_limbs
        // some issues re: masking with the top byte of the 32byte input
        let mask_21bits: i64 = (1 << 21) -1;
        s[0]  = mask_21bits &  load3(&input[ 0..])      ;
        s[1]  = mask_21bits & (load4(&input[ 2..]) >> 5);
        s[2]  = mask_21bits & (load3(&input[ 5..]) >> 2);
        s[3]  = mask_21bits & (load4(&input[ 7..]) >> 7);
        s[4]  = mask_21bits & (load4(&input[10..]) >> 4);
        s[5]  = mask_21bits & (load3(&input[13..]) >> 1);
        s[6]  = mask_21bits & (load4(&input[15..]) >> 6);
        s[7]  = mask_21bits & (load3(&input[18..]) >> 3);
        s[8]  = mask_21bits &  load3(&input[21..])      ;
        s[9]  = mask_21bits & (load4(&input[23..]) >> 5);
        s[10] = mask_21bits & (load3(&input[26..]) >> 2);
        s[11] = mask_21bits & (load4(&input[28..]) >> 7);
        s[12] = mask_21bits & (load4(&input[31..]) >> 4);
        s[13] = mask_21bits & (load3(&input[34..]) >> 1);
        s[14] = mask_21bits & (load4(&input[36..]) >> 6);
        s[15] = mask_21bits & (load3(&input[39..]) >> 3);
        s[16] = mask_21bits &  load3(&input[42..])      ;
        s[17] = mask_21bits & (load4(&input[44..]) >> 5);
        s[18] = mask_21bits & (load3(&input[47..]) >> 2);
        s[19] = mask_21bits & (load4(&input[49..]) >> 7);
        s[20] = mask_21bits & (load4(&input[52..]) >> 4);
        s[21] = mask_21bits & (load3(&input[55..]) >> 1);
        s[22] = mask_21bits & (load4(&input[57..]) >> 6);
        s[23] =                load4(&input[60..]) >> 3 ;

        // XXX replacing the previous code in this function with the
        // call to reduce_limbs adds two extra carry passes (the ones
        // at the top of the reduce_limbs function).  Otherwise they
        // are identical.  The test seems to work OK but it would be
        // good to check that this really is OK to add.
        Scalar::reduce_limbs(&mut s);

        Scalar::pack_limbs(array_ref!(s,0,12))
    }
}

#[cfg(test)]
mod test {
    use rand::Rng;
    use rand::OsRng;
    use super::*;
    use test::Bencher;

    #[bench]
    fn bench_scalar_random(b: &mut Bencher) {
        let mut csprng: OsRng = OsRng::new().unwrap();

        b.iter(|| Scalar::random(&mut csprng));
    }

    #[bench]
    fn bench_scalar_multiply_add(b: &mut Bencher) {
        b.iter(|| Scalar::multiply_add(&X, &Y, &Z) );
    }

    /// x = 2238329342913194256032495932344128051776374960164957527413114840482143558222
    static X: Scalar = Scalar(
        [0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84,
         0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2, 0x7d, 0x52,
         0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44,
         0xd4, 0x49, 0xf4, 0xa8, 0x79, 0xd9, 0xf2, 0x04]);
    /// y = 2592331292931086675770238855846338635550719849568364935475441891787804997264
    static Y: Scalar = Scalar(
        [0x90, 0x76, 0x33, 0xfe, 0x1c, 0x4b, 0x66, 0xa4,
         0xa2, 0x8d, 0x2d, 0xd7, 0x67, 0x83, 0x86, 0xc3,
         0x53, 0xd0, 0xde, 0x54, 0x55, 0xd4, 0xfc, 0x9d,
         0xe8, 0xef, 0x7a, 0xc3, 0x1f, 0x35, 0xbb, 0x05]);
    /// z = 5033871415930814945849241457262266927579821285980625165479289807629491019013
    static Z: Scalar = Scalar(
        [0x05, 0x9d, 0x3e, 0x0b, 0x09, 0x26, 0x50, 0x3d,
         0xa3, 0x84, 0xa1, 0x3c, 0x92, 0x7a, 0xc2, 0x06,
         0x41, 0x98, 0xcf, 0x34, 0x3a, 0x24, 0xd5, 0xb7,
         0xeb, 0x33, 0x6a, 0x2d, 0xfc, 0x11, 0x21, 0x0b]);
    /// w = 3486911242272497535104403593250518247409663771668155364040899665266216860804
    static W: Scalar = Scalar(
        [0x84, 0xfc, 0xbc, 0x4f, 0x78, 0x12, 0xa0, 0x06,
         0xd7, 0x91, 0xd9, 0x7a, 0x3a, 0x27, 0xdd, 0x1e,
         0x21, 0x43, 0x45, 0xf7, 0xb1, 0xb9, 0x56, 0x7a,
         0x81, 0x30, 0x73, 0x44, 0x96, 0x85, 0xb5, 0x07]);

    /// x*y = 5690045403673944803228348699031245560686958845067437804563560795922180092780
    static X_TIMES_Y: Scalar = Scalar(
        [0x6c, 0x33, 0x74, 0xa1, 0x89, 0x4f, 0x62, 0x21,
         0x0a, 0xaa, 0x2f, 0xe1, 0x86, 0xa6, 0xf9, 0x2c,
         0xe0, 0xaa, 0x75, 0xc2, 0x77, 0x95, 0x81, 0xc2,
         0x95, 0xfc, 0x08, 0x17, 0x9a, 0x73, 0x94, 0x0c]);

    static A_SCALAR: Scalar = Scalar([
        0x1a, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d,
        0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8, 0x26, 0x4d,
        0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1,
        0x58, 0x9e, 0x7b, 0x7f, 0x23, 0x76, 0xef, 0x09]);

    static A_NAF: [i8;256] =
        [0,13,0,0,0,0,0,0,0,7,0,0,0,0,0,0,-9,0,0,0,0,-11,0,0,0,0,3,0,0,0,0,1,
         0,0,0,0,9,0,0,0,0,-5,0,0,0,0,0,0,3,0,0,0,0,11,0,0,0,0,11,0,0,0,0,0,
         -9,0,0,0,0,0,-3,0,0,0,0,9,0,0,0,0,0,1,0,0,0,0,0,0,-1,0,0,0,0,0,9,0,
         0,0,0,-15,0,0,0,0,-7,0,0,0,0,-9,0,0,0,0,0,5,0,0,0,0,13,0,0,0,0,0,-3,0,
         0,0,0,-11,0,0,0,0,-7,0,0,0,0,-13,0,0,0,0,11,0,0,0,0,-9,0,0,0,0,0,1,0,0,
         0,0,0,-15,0,0,0,0,1,0,0,0,0,7,0,0,0,0,0,0,0,0,5,0,0,0,0,0,13,0,0,0,
         0,0,0,11,0,0,0,0,0,15,0,0,0,0,0,-9,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,7,
         0,0,0,0,0,-15,0,0,0,0,0,15,0,0,0,0,15,0,0,0,0,15,0,0,0,0,0,1,0,0,0,0];

    #[test]
    fn test_non_adjacent_form() {
        let naf = A_SCALAR.non_adjacent_form();
        for i in 0..256 {
            assert_eq!(naf[i], A_NAF[i]);
        }
    }

    #[test]
    fn test_scalar_multiply_by_one() {
        let one = Scalar::one();
        let zero = Scalar::zero();
        let test_scalar = Scalar::multiply_add(&X, &one, &zero);
        for i in 0..32 {
            assert!(test_scalar[i] == X[i]);
        }
    }

    #[test]
    fn test_scalar_multiply_only() {
        let zero = Scalar::zero();
        let test_scalar = Scalar::multiply_add(&X, &Y, &zero);
        for i in 0..32 {
            assert!(test_scalar[i] == X_TIMES_Y[i]);
        }
    }

    #[test]
    fn test_scalar_multiply_add() {
        let test_scalar = Scalar::multiply_add(&X, &Y, &Z);
        for i in 0..32 {
            assert!(test_scalar[i] == W[i]);
        }
    }

    #[test]
    fn test_scalar_reduce() {
        let mut bignum = [0u8;64];
        // set bignum = x + 2^256x
        for i in 0..32 {
            bignum[   i] = X[i];
            bignum[32+i] = X[i];
        }
        // 3958878930004874126169954872055634648693766179881526445624823978500314864344
        // = x + 2^256x (mod l)
        let reduced = Scalar([216, 154, 179, 139, 210, 121,   2,  71,
                               69,  99, 158, 216,  23, 173,  63, 100,
                              204,   0,  91,  50, 219, 153,  57, 249,
                               28,  82,  31, 197, 100, 165, 192,   8]);
        let test_red = Scalar::reduce(&bignum);
        for i in 0..32 {
            assert!(test_red[i] == reduced[i]);
        }
    }
}
