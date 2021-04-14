// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2020 Jack Grigg
// See LICENSE for licensing information.
//
// Author:
// Jack Grigg <thestr4d@gmail.com>
#![allow(non_snake_case)]

use core::cmp::Ordering;
use core::convert::TryInto;
use core::mem;
use core::ops::{Add, AddAssign, Shl, Sub, SubAssign};

use constants::BASEPOINT_ORDER;
use scalar::Scalar;

/// The low 127 bits of \\( \ell \\).
const ELL_LOWER_HALF: i128 = 0x14de_f9de_a2f7_9cd6_5812_631a_5cf5_d3ed;

/// Finds a short non-zero vector \\((d_0, d_1)\\) such that \\(d_0 = d_1 k \mod \ell\\).
/// \\(d_0\\) and \\(d_1)\\) may be negative.
///
/// Implements Algorithm 4 from [Pornin 2020](https://eprint.iacr.org/2020/454).
pub(crate) fn find_short_vector(k: &Scalar) -> (i128, i128) {
    let mut N_u = BigInt::ell_squared();
    let mut N_v = BigInt::mul(k, k) + BigInt::one();
    let mut p = BigInt::mul(&BASEPOINT_ORDER, k);

    /// The target bit length of `N_v` for the vector to be considered short.
    const T: usize = 254; // len(\ell) + 1

    let (mut u_0, mut u_1) = (ELL_LOWER_HALF, 0);
    let (mut v_0, mut v_1) = (
        i128::from_le_bytes(k.to_bytes()[..16].try_into().unwrap()),
        1,
    );

    loop {
        if &N_u < &N_v {
            mem::swap(&mut u_0, &mut v_0);
            mem::swap(&mut u_1, &mut v_1);
            mem::swap(&mut N_u, &mut N_v);
        }

        let len_N_v = N_v.bit_len();
        if len_N_v <= T {
            return (v_0, v_1);
        }

        let s = p.bit_len().saturating_sub(len_N_v);
        if p > BigInt::zero() {
            u_0 = u_0.wrapping_sub(v_0.wrapping_shl(s as u32));
            u_1 = u_1.wrapping_sub(v_1.wrapping_shl(s as u32));
            N_u += (N_v << (2 * s)) - (p << (s + 1));
            p -= N_v << s;
        } else {
            u_0 = u_0.wrapping_add(v_0.wrapping_shl(s as u32));
            u_1 = u_1.wrapping_add(v_1.wrapping_shl(s as u32));
            N_u += (N_v << (2 * s)) + (p << (s + 1));
            p += N_v << s;
        }
    }
}

/// Represents a signed two's complement 512-bit integer in eight 64-bit limbs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BigInt([u64; 8]);

impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> Ordering {
        // If the signs differ, we can quickly determine ordering.
        let a_is_neg = self.is_negative();
        let b_is_neg = other.is_negative();
        match (a_is_neg, b_is_neg) {
            (true, false) => return Ordering::Less,
            (false, true) => return Ordering::Greater,
            _ => (),
        }

        // Compare the integers ignoring sign. Because we use two's complement, and the
        // integers have the same sign, this is guaranteed to give the correct result.
        self.0
            .iter()
            .zip(other.0.iter())
            .rev()
            .find_map(|(a, b)| match a.cmp(b) {
                Ordering::Equal => None,
                ord => Some(ord),
            })
            .unwrap_or(Ordering::Equal)
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &BigInt) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl BigInt {
    const fn zero() -> BigInt {
        BigInt([0; 8])
    }

    const fn one() -> BigInt {
        BigInt([1, 0, 0, 0, 0, 0, 0, 0])
    }

    /// \\( \ell^2 \\)
    const fn ell_squared() -> BigInt {
        BigInt([
            0xe2ed_f685_ab12_8969,
            0x6803_9276_2298_a31d,
            0x3dce_ec73_d217_f5be,
            0xa1b3_9941_1b7c_309a,
            0xcb02_4c63_4b9e_ba7d,
            0x029b_df3b_d45e_f39a,
            0x0000_0000_0000_0000,
            0x0100_0000_0000_0000,
        ])
    }

    /// Returns `true` if the sign bit is set.
    fn is_negative(&self) -> bool {
        self.0[7] >> 63 != 0
    }

    /// Returns the minimal size (in bits) of the binary representation of this value, in
    /// two's complement, excluding the sign bit.
    fn bit_len(&self) -> usize {
        // The implementation starts with two observations:
        // - In two's complement, positive integers are padded above the most significant
        //   bit with 0-bits, and negative integers are padded above the MSB with 1-bits.
        // - We can efficiently count the number of leading zeroes in any limb.

        // Create a mask from the sign bit that matches the padding:
        // - All zeroes if positive.
        // - All ones if positive.
        let sign_mask = -((self.0[7] >> 63) as i64) as u64;

        self.0
            .iter()
            .enumerate()
            // Find the most significant limb that does not match the mask (and therefore
            // contains the most significant bit).
            .rev()
            .skip_while(|(_, w)| **w == sign_mask)
            .next()
            // XOR the limb with the mask, resulting in a word that has leading zeroes
            // followed by the most significant bit as a 1.
            .map(|(i, w)| (i, w ^ sign_mask))
            // Compute the position of the most significant bit.
            .map(|(i, w)| ((i + 1) * 64) - w.leading_zeros() as usize)
            // If all limbs were padding, the bit length is zero.
            .unwrap_or(0)
    }

    /// Returns `a * b` as an unreduced 512-bit integer.
    fn mul(a: &Scalar, b: &Scalar) -> BigInt {
        /// Converts a [`Scalar`] into a set of little-endian 64-bit limbs.
        fn to_limbs(s: &Scalar) -> [u64; 4] {
            let mut limbs = [0; 4];
            for (i, l) in s
                .as_bytes()
                .chunks(8)
                .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
                .enumerate()
            {
                limbs[i] = l;
            }
            limbs
        }

        /// Computes a + (b * c) + carry, returning the result along with the new carry.
        #[inline(always)]
        const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
            let ret = (a as u128) + ((b as u128) * (c as u128)) + (carry as u128);
            (ret as u64, (ret >> 64) as u64)
        }

        let a = to_limbs(a);
        let b = to_limbs(b);

        let (w0, carry) = mac(0, a[0], b[0], 0);
        let (w1, carry) = mac(0, a[0], b[1], carry);
        let (w2, carry) = mac(0, a[0], b[2], carry);
        let (w3, w4) = mac(0, a[0], b[3], carry);

        let (w1, carry) = mac(w1, a[1], b[0], 0);
        let (w2, carry) = mac(w2, a[1], b[1], carry);
        let (w3, carry) = mac(w3, a[1], b[2], carry);
        let (w4, w5) = mac(w4, a[1], b[3], carry);

        let (w2, carry) = mac(w2, a[2], b[0], 0);
        let (w3, carry) = mac(w3, a[2], b[1], carry);
        let (w4, carry) = mac(w4, a[2], b[2], carry);
        let (w5, w6) = mac(w5, a[2], b[3], carry);

        let (w3, carry) = mac(w3, a[3], b[0], 0);
        let (w4, carry) = mac(w4, a[3], b[1], carry);
        let (w5, carry) = mac(w5, a[3], b[2], carry);
        let (w6, w7) = mac(w6, a[3], b[3], carry);

        // The top 7 bits of the top limb should be zero. This includes the sign bit;
        // Scalars are always unsigned, so we don't need to apply a correction here.
        debug_assert_eq!(w7 >> 57, 0);

        BigInt([w0, w1, w2, w3, w4, w5, w6, w7])
    }
}

impl Add for BigInt {
    type Output = BigInt;

    fn add(mut self, rhs: BigInt) -> Self::Output {
        self += rhs;
        self
    }
}

impl AddAssign for BigInt {
    fn add_assign(&mut self, rhs: BigInt) {
        /// Computes a + b + carry, returning the result along with the new carry.
        #[inline(always)]
        const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
            let ret = (a as u128) + (b as u128) + (carry as u128);
            (ret as u64, (ret >> 64) as u64)
        }

        // a + b
        let mut carry: u64 = 0;
        for i in 0..8 {
            let (res, new_carry) = adc(self.0[i], rhs.0[i], carry);
            self.0[i] = res;
            carry = new_carry;
        }
    }
}

impl Sub for BigInt {
    type Output = BigInt;

    fn sub(mut self, rhs: BigInt) -> Self::Output {
        self -= rhs;
        self
    }
}

impl SubAssign for BigInt {
    fn sub_assign(&mut self, rhs: BigInt) {
        /// Computes a - (b + borrow), returning the result along with the new borrow.
        #[inline(always)]
        const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
            let ret = (a as u128).wrapping_sub((b as u128) + ((borrow >> 63) as u128));
            (ret as u64, (ret >> 64) as u64)
        }

        // a - b
        let mut borrow: u64 = 0;
        for i in 0..8 {
            let (res, new_borrow) = sbb(self.0[i], rhs.0[i], borrow);
            self.0[i] = res;
            borrow = new_borrow;
        }
    }
}

impl Shl<usize> for BigInt {
    type Output = BigInt;

    fn shl(mut self, s: usize) -> Self::Output {
        let (k, s) = if s >= 64 {
            let k = s / 64;
            self.0.rotate_right(k);
            for w in &mut self.0[..k] {
                *w = 0;
            }
            (k, s - (k * 64))
        } else {
            (0, s)
        };

        /// Computes (a << b) | carry, returning the result along with the new carry.
        #[inline(always)]
        const fn slc(a: u64, b: usize, carry: u64) -> (u64, u64) {
            let ret = ((a as u128) << b) | (carry as u128);
            (ret as u64, (ret >> 64) as u64)
        }

        let mut carry: u64 = 0;
        for i in k..8 {
            let (res, new_carry) = slc(self.0[i], s, carry);
            self.0[i] = res;
            carry = new_carry;
        }

        self
    }
}

#[cfg(test)]
mod tests {
    use super::{find_short_vector, BigInt};
    use scalar::Scalar;

    #[test]
    fn test_find_short_vector() {
        let mut rng = rand::thread_rng();

        for _ in 0..500 {
            let k = Scalar::random(&mut rng);

            let (d_0, d_1) = find_short_vector(&k);

            let d_0 = if d_0.is_negative() {
                -Scalar::from(d_0.abs() as u128)
            } else {
                Scalar::from(d_0.abs() as u128)
            };

            let d_1 = if d_1.is_negative() {
                -Scalar::from(d_1.abs() as u128)
            } else {
                Scalar::from(d_1.abs() as u128)
            };

            assert_eq!(d_0, d_1 * k);
        }
    }

    #[test]
    fn ord() {
        let zero = BigInt::zero();
        let one = BigInt::one();
        let neg_one = zero - one;
        let neg_ell_sq = zero - BigInt::ell_squared();

        assert!(zero < one);
        assert!(one < BigInt::ell_squared());
        assert!(neg_one < zero);
        assert!(neg_one < one);
        assert!(neg_ell_sq < neg_one);
    }

    #[test]
    fn bit_len() {
        let zero = BigInt::zero();
        let one = BigInt::one();
        let neg_one = zero - one;

        assert_eq!(zero.bit_len(), 0);
        assert_eq!(one.bit_len(), 1);
        assert_eq!(neg_one.bit_len(), 0);
        assert_eq!(BigInt::ell_squared().bit_len(), 505);
    }

    #[test]
    fn addition() {
        assert_eq!(BigInt::zero() + BigInt::one(), BigInt::one());
    }

    #[test]
    fn subtraction() {
        assert_eq!(BigInt::one() - BigInt::one(), BigInt::zero());
    }

    #[test]
    fn shl() {
        assert_eq!(BigInt::one() << 1, BigInt([2, 0, 0, 0, 0, 0, 0, 0]));
        assert_eq!(
            BigInt([
                0xffff_ffff_ffff_ffff,
                0x0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff,
                0x0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff,
                0x0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff,
                0x0000_0000_0000_0000,
            ]) << 24,
            BigInt([
                0xffff_ffff_ff00_0000,
                0x0000_0000_00ff_ffff,
                0xffff_ffff_ff00_0000,
                0x0000_0000_00ff_ffff,
                0xffff_ffff_ff00_0000,
                0x0000_0000_00ff_ffff,
                0xffff_ffff_ff00_0000,
                0x0000_0000_00ff_ffff,
            ])
        );
        assert_eq!(
            BigInt([
                0xffff_ffff_ffff_ffff,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x01ff_ffff_ffff_ffff,
            ]) << 48,
            BigInt([
                0xffff_0000_0000_0000,
                0x0000_ffff_ffff_ffff,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0x0000_0000_0000_0000,
                0xffff_0000_0000_0000,
            ])
        );
    }
}
