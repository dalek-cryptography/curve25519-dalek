// -*- mode: rust; coding: utf-8; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! 4-way vectorized 32bit field arithmetic using AVX2.
//!

#![allow(bad_style)]

use std::ops::Mul;

use stdsimd::simd::{u32x8, i32x8, u64x4};

use backend::u32::field::FieldElement32;

static P_TIMES_2: FieldElement32x4 = FieldElement32x4([
    u32x8::new(134217690, 134217690, 67108862, 67108862, 134217690, 134217690, 67108862, 67108862),
    u32x8::new(134217726, 134217726, 67108862, 67108862, 134217726, 134217726, 67108862, 67108862),
    u32x8::new(134217726, 134217726, 67108862, 67108862, 134217726, 134217726, 67108862, 67108862),
    u32x8::new(134217726, 134217726, 67108862, 67108862, 134217726, 134217726, 67108862, 67108862),
    u32x8::new(134217726, 134217726, 67108862, 67108862, 134217726, 134217726, 67108862, 67108862)
]);

/// A vector of four `FieldElements`, implemented using AVX2.
#[derive(Clone, Copy)]
pub(crate) struct FieldElement32x4(pub(crate) [u32x8; 5]);

impl FieldElement32x4 {
    pub(crate) fn split(&self) -> [FieldElement32; 4] {
        let mut out = [FieldElement32::zero(); 4];
        for i in 0..5 {
            out[0].0[2*i  ] = self.0[i].extract(0); //
            out[1].0[2*i  ] = self.0[i].extract(1); //
            out[0].0[2*i+1] = self.0[i].extract(2); // `.
            out[1].0[2*i+1] = self.0[i].extract(3); //  | pre-swapped to avoid
            out[2].0[2*i  ] = self.0[i].extract(4); //  | a cross lane shuffle
            out[3].0[2*i  ] = self.0[i].extract(5); // .'
            out[2].0[2*i+1] = self.0[i].extract(6); //
            out[3].0[2*i+1] = self.0[i].extract(7); //
        }
        
        out
    }

    pub fn zero() -> FieldElement32x4 {
        FieldElement32x4([u32x8::splat(0);5])
    }

    pub fn splat(x: &FieldElement32) -> FieldElement32x4 {
        FieldElement32x4::new(x,x,x,x)
    }

    pub fn new(
        x0: &FieldElement32,
        x1: &FieldElement32,
        x2: &FieldElement32,
        x3: &FieldElement32,
    ) -> FieldElement32x4 {
        let mut buf = [u32x8::splat(0); 5];
        for i in 0..5 {
            buf[i] = u32x8::new(x0.0[2*i  ], x1.0[2*i  ], x0.0[2*i+1], x1.0[2*i+1],
                                x2.0[2*i  ], x3.0[2*i  ], x2.0[2*i+1], x3.0[2*i+1]);
        }

        FieldElement32x4(buf)
    }

    // Given `self = (A,B,C,D)`, compute `(B - A, B + A, D - C, D + C)`.
    pub fn diff_sum(&self) -> FieldElement32x4 {
        /// (v0 v1 v2 v3 v4 v5 v6 v7) -> (v1 v0 v3 v2 v5 v4 v7 v6)
        #[inline(always)]
        fn alternate_32bit_lanes(v: u32x8) -> u32x8 {
            unsafe {
                use stdsimd::vendor::_mm256_shuffle_epi32;
                _mm256_shuffle_epi32(v.as_i32x8(), 0b10_11_00_01).as_u32x8()
            }
        }

        /// (v0 XX v2 XX v4 XX v6 XX)
        /// (XX v1 XX v3 XX v5 XX v7) -> (v0 v1 v2 v3 v4 v5 v6 v7)
        #[inline(always)]
        fn blend_alternating_32bit_lanes(v1: u32x8, v2: u32x8) -> u32x8 {
            unsafe {
                use stdsimd::vendor::_mm256_blend_epi32;
                _mm256_blend_epi32(v1.into(), v2.into(), 0b10101010).as_u32x8()
            }
        }

        let mut out = [u32x8::splat(0); 5];

        for i in 0..5 {
            let x = self.0[i];
            let p = P_TIMES_2.0[i] ;
            let x_shuf = alternate_32bit_lanes(x);

            let diff = (x_shuf + p) - x;
            let sum  =  x + x_shuf;
            let diff_sum = blend_alternating_32bit_lanes(diff, sum);

            out[i] = diff_sum;
        }

        FieldElement32x4(out)
    }

    // Given `self = (A,B,C,D)`, compute `(B + A, B - A, D + C, D - C)`.
    pub fn sum_diff(&self) -> FieldElement32x4 {
        /// (v0 v1 v2 v3 v4 v5 v6 v7) -> (v1 v0 v3 v2 v5 v4 v7 v6)
        #[inline(always)]
        #[allow(dead_code)] // XXX
        fn alternate_32bit_lanes(v: u32x8) -> u32x8 {
            unsafe {
                use stdsimd::vendor::_mm256_shuffle_epi32;
                _mm256_shuffle_epi32(v.as_i32x8(), 0b10_11_00_01).as_u32x8()
            }
        }

        /// (v0 XX v2 XX v4 XX v6 XX)
        /// (XX v1 XX v3 XX v5 XX v7) -> (v0 v1 v2 v3 v4 v5 v6 v7)
        #[inline(always)]
        #[allow(dead_code)] // XXX
        fn blend_alternating_32bit_lanes(v1: u32x8, v2: u32x8) -> u32x8 {
            unsafe {
                use stdsimd::vendor::_mm256_blend_epi32;
                _mm256_blend_epi32(v1.into(), v2.into(), 0b10101010).as_u32x8()
            }
        }

        let mut out = [u32x8::splat(0); 5];

        for i in 0..5 {
            let x = self.0[i];
            let p = P_TIMES_2.0[i];
            let x_shuf = alternate_32bit_lanes(x);

            let sum  =  x      + x_shuf;
            let diff = (x + p) - x_shuf;
            let sum_diff = blend_alternating_32bit_lanes(sum, diff);

            out[i] = sum_diff;
        }

        FieldElement32x4(out)
    }

    pub fn scale_by_curve_constants(&mut self) {
        let mut b = [u64x4::splat(0); 10];

        let consts   = u32x8::new(121666, 0, 121666, 0, 2*121666, 0, 2*121665, 0);
        let low__p20 = u64x4::splat(0x3ffffed << 20);
        let even_p20 = u64x4::splat(0x3ffffff << 20);
        let odd__p20 = u64x4::splat(0x1ffffff << 20);

        unsafe {
            use stdsimd::vendor::_mm256_mul_epu32;
            use stdsimd::vendor::_mm256_blend_epi32;

            let (b0, b1) = unpack_pair(self.0[0]);
            let b0 = _mm256_mul_epu32(b0, consts); // need a new binding since now
            let b1 = _mm256_mul_epu32(b1, consts); // b0 has type u64x4
            b[0] = _mm256_blend_epi32(b0.into(), (low__p20 - b0).into(), 0b11_00_00_00).into();
            b[1] = _mm256_blend_epi32(b1.into(), (odd__p20 - b1).into(), 0b11_00_00_00).into();

            let (b2, b3) = unpack_pair(self.0[1]);
            let b2 = _mm256_mul_epu32(b2, consts);
            let b3 = _mm256_mul_epu32(b3, consts);
            b[2] = _mm256_blend_epi32(b2.into(), (even_p20 - b2).into(), 0b11_00_00_00).into();
            b[3] = _mm256_blend_epi32(b3.into(), (odd__p20 - b3).into(), 0b11_00_00_00).into();

            let (b4, b5) = unpack_pair(self.0[2]);
            let b4 = _mm256_mul_epu32(b4, consts);
            let b5 = _mm256_mul_epu32(b5, consts);
            b[4] = _mm256_blend_epi32(b4.into(), (even_p20 - b4).into(), 0b11_00_00_00).into();
            b[5] = _mm256_blend_epi32(b5.into(), (odd__p20 - b5).into(), 0b11_00_00_00).into();

            let (b6, b7) = unpack_pair(self.0[3]);
            let b6 = _mm256_mul_epu32(b6, consts);
            let b7 = _mm256_mul_epu32(b7, consts);
            b[6] = _mm256_blend_epi32(b6.into(), (even_p20 - b6).into(), 0b11_00_00_00).into();
            b[7] = _mm256_blend_epi32(b7.into(), (odd__p20 - b7).into(), 0b11_00_00_00).into();

            let (b8, b9) = unpack_pair(self.0[4]);
            let b8 = _mm256_mul_epu32(b8, consts);
            let b9 = _mm256_mul_epu32(b9, consts);
            b[8] = _mm256_blend_epi32(b8.into(), (even_p20 - b8).into(), 0b11_00_00_00).into();
            b[9] = _mm256_blend_epi32(b9.into(), (odd__p20 - b9).into(), 0b11_00_00_00).into();
        }

        *self = FieldElement32x4::reduce64(b);
    }

    pub fn reduce32(&mut self) {
        let mut b = [u64x4::splat(0); 10];

        let (b0, b1) = unpack_pair(self.0[0]);
        b[0] = b0.into(); b[1] = b1.into();
        let (b2, b3) = unpack_pair(self.0[1]);
        b[2] = b2.into(); b[3] = b3.into();
        let (b4, b5) = unpack_pair(self.0[2]);
        b[4] = b4.into(); b[5] = b5.into();
        let (b6, b7) = unpack_pair(self.0[3]);
        b[6] = b6.into(); b[7] = b7.into();
        let (b8, b9) = unpack_pair(self.0[4]);
        b[8] = b8.into(); b[9] = b9.into();

        *self = FieldElement32x4::reduce64(b);
    }

    pub fn reduce64(mut z: [u64x4; 10]) -> FieldElement32x4 {
        // These aren't const because splat isn't a const fn
        let LOW_25_BITS: u64x4 = u64x4::splat((1<<25)-1);
        let LOW_26_BITS: u64x4 = u64x4::splat((1<<26)-1);

        /// XXX check whether u64x4 >> is this already
        #[inline(always)]
        fn shift_right(x: u64x4, s: i32) -> u64x4 {
            unsafe {
                use stdsimd::vendor::_mm256_srli_epi64;
                _mm256_srli_epi64(x.into(), s).as_u64x4()
            }
        }

        // Carry the value from limb i = 0..8 to limb i+1
        let carry = |z: &mut [u64x4; 10], i: usize| {
            debug_assert!(i < 9);
            if i % 2 == 0 {
                // Even limbs have 26 bits
                z[i+1] = z[i+1] + shift_right(z[i], 26);
                z[i] = z[i] & LOW_26_BITS;
            } else {
                // Odd limbs have 25 bits
                z[i+1] = z[i+1] + shift_right(z[i], 25);
                z[i] = z[i] & LOW_25_BITS;
            }
        };

        // Perform two halves of the carry chain in parallel.
        carry(&mut z, 0); carry(&mut z, 4);
        carry(&mut z, 1); carry(&mut z, 5);
        carry(&mut z, 2); carry(&mut z, 6);
        carry(&mut z, 3); carry(&mut z, 7);
        // Since z[3] < 2^64, c < 2^(64-25) = 2^39,
        // so    z[4] < 2^26 + 2^39 < 2^39.0002
        carry(&mut z, 4); carry(&mut z, 8);
        // Now z[4] < 2^26 
        // and z[5] < 2^25 + 2^13.0002 < 2^25.0004 (good enough)

        // Last carry has a multiplication by 19.  In the serial case we
        // do a 64-bit multiplication by 19, but here we want to do a
        // 32-bit multiplication.  However, if we only know z[9] < 2^64,
        // the carry is bounded as c < 2^(64-25) = 2^39, which is too
        // big.  To ensure c < 2^32, we would need z[9] < 2^57.
        // Instead, we split the carry in two, with c = c_0 + c_1*2^26.

        let c = shift_right(z[9], 25);
        z[9] = z[9] & LOW_25_BITS;
        let mut c0 = c & LOW_26_BITS;     // c0 < 2^26;
        let mut c1 = shift_right(c, 26);  // c1 < 2^(39-26) = 2^13;

        unsafe {
            use stdsimd::vendor::_mm256_mul_epu32;
            let x19 = u32x8::from(u64x4::splat(19));
            c0 = _mm256_mul_epu32(u32x8::from(c0), x19); // c0 < 2^30.25
            c1 = _mm256_mul_epu32(u32x8::from(c1), x19); // c1 < 2^17.25
        }

        z[0] = z[0] + c0; // z0 < 2^26 + 2^30.25 < 2^30.33
        z[1] = z[1] + c1; // z1 < 2^25 + 2^17.25 < 2^25.0067
        carry(&mut z, 0); // z0 < 2^26, z1 < 2^25.0067 + 2^4.33 = 2^25.007

        // Now repack the [u64x4; 10] into a FieldElement32x4

        FieldElement32x4([
            repack_pair(z[0].into(), z[1].into()),
            repack_pair(z[2].into(), z[3].into()),
            repack_pair(z[4].into(), z[5].into()),
            repack_pair(z[6].into(), z[7].into()),
            repack_pair(z[8].into(), z[9].into()),
        ])
    }
}

#[inline(always)]
pub fn unpack_pair(src: u32x8) -> (u32x8, u32x8) {
    let a: u32x8;
    let b: u32x8;
    let zero = i32x8::new(0,0,0,0,0,0,0,0);
    unsafe {
        use stdsimd::vendor::_mm256_unpackhi_epi32;
        use stdsimd::vendor::_mm256_unpacklo_epi32;
        a = _mm256_unpacklo_epi32(src.as_i32x8(), zero).as_u32x8();
        b = _mm256_unpackhi_epi32(src.as_i32x8(), zero).as_u32x8();
    }
    (a,b)
}

#[inline(always)]
pub fn repack_pair(x: u32x8, y: u32x8) -> u32x8 {
    unsafe {
        use stdsimd::vendor::_mm256_shuffle_epi32;
        use stdsimd::vendor::_mm256_blend_epi32;

        // Input: x = (a0, 0, b0, 0, c0, 0, d0)
        // Input: y = (a1, 0, b1, 0, c1, 0, d1)

        let x_shuffled = _mm256_shuffle_epi32(x.into(), 0b11_01_10_00);
        let y_shuffled = _mm256_shuffle_epi32(y.into(), 0b10_00_11_01);

        // x' = (a0, b0,  0,  0, c0, d0,  0,  0)
        // y' = ( 0,  0, a1, b1,  0,  0, c1, d1)

        return _mm256_blend_epi32(x_shuffled, y_shuffled, 0b11001100).as_u32x8();
    }
}

impl<'a, 'b> Mul<&'b FieldElement32x4> for &'a FieldElement32x4 {
    type Output = FieldElement32x4;
    fn mul(self, _rhs: &'b FieldElement32x4) -> FieldElement32x4 {
        let mut b = [u32x8::splat(0); 10];
        let mut c = [u64x4::splat(0); 10];

        let (b0, b1) = unpack_pair(_rhs.0[0]);
        b[0] = b0; b[1] = b1;
        let (b2, b3) = unpack_pair(_rhs.0[1]);
        b[2] = b2; b[3] = b3;
        let (b4, b5) = unpack_pair(_rhs.0[2]);
        b[4] = b4; b[5] = b5;
        let (b6, b7) = unpack_pair(_rhs.0[3]);
        b[6] = b6; b[7] = b7;
        let (b8, b9) = unpack_pair(_rhs.0[4]);
        b[8] = b8; b[9] = b9;

        #[inline(always)]
        fn m(x: u32x8, y: u32x8) -> u64x4 {
            use stdsimd::vendor::_mm256_mul_epu32;
            unsafe { _mm256_mul_epu32(x,y) }
        }
        
        #[inline(always)]
        fn m_lo(x: u32x8, y: u32x8) -> u32x8 {
            use stdsimd::vendor::_mm256_mul_epu32;
            unsafe { u32x8::from(_mm256_mul_epu32(x,y)) }
        }

        let x19 = u32x8::new(19,0,19,0,19,0,19,0);

        macro_rules! loop_body {
            ($i:expr) => {
                let (ai, ai1) = unpack_pair(self.0[$i/2]);

                c[9] = c[9] + m(ai, b[(100 + 9-$i) % 10]);
                b[(100 + 9-$i) % 10] = m_lo(b[(100 + 9-$i) % 10], x19);
                c[8] = c[8] + m(ai, b[(100 + 8-$i) % 10]);
                c[7] = c[7] + m(ai, b[(100 + 7-$i) % 10]);
                c[6] = c[6] + m(ai, b[(100 + 6-$i) % 10]);
                c[5] = c[5] + m(ai, b[(100 + 5-$i) % 10]);
                c[4] = c[4] + m(ai, b[(100 + 4-$i) % 10]);
                c[3] = c[3] + m(ai, b[(100 + 3-$i) % 10]);
                c[2] = c[2] + m(ai, b[(100 + 2-$i) % 10]);
                c[1] = c[1] + m(ai, b[(100 + 1-$i) % 10]);
                c[0] = c[0] + m(ai, b[(100 + 0-$i) % 10]);

                let ai1_2 = ai1 + ai1;
                c[9] = c[9] + m(ai1,   b[(100 + 9-($i+1)) % 10]);
                b[(100 + 9-($i+1)) % 10] = m_lo(b[(100 + 9-($i+1)) % 10], x19);
                c[8] = c[8] + m(ai1_2, b[(100 + 8-($i+1)) % 10]);
                c[7] = c[7] + m(ai1,   b[(100 + 7-($i+1)) % 10]);
                c[6] = c[6] + m(ai1_2, b[(100 + 6-($i+1)) % 10]);
                c[5] = c[5] + m(ai1,   b[(100 + 5-($i+1)) % 10]);
                c[4] = c[4] + m(ai1_2, b[(100 + 4-($i+1)) % 10]);
                c[3] = c[3] + m(ai1,   b[(100 + 3-($i+1)) % 10]);
                c[2] = c[2] + m(ai1_2, b[(100 + 2-($i+1)) % 10]);
                c[1] = c[1] + m(ai1,   b[(100 + 1-($i+1)) % 10]);
                c[0] = c[0] + m(ai1_2, b[(100 + 0-($i+1)) % 10]);
            };
        }

        loop_body!(0);
        loop_body!(2);
        loop_body!(4);
        loop_body!(6);
        loop_body!(8);

        return FieldElement32x4::reduce64(c);
    }
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn scale_by_curve_constants() {
        let mut x = FieldElement32x4::splat(&FieldElement32::one());
        x.scale_by_curve_constants();

        let xs = x.split();
        assert_eq!(xs[0],   FieldElement32([  121666,0,0,0,0,0,0,0,0,0]));
        assert_eq!(xs[1],   FieldElement32([  121666,0,0,0,0,0,0,0,0,0]));
        assert_eq!(xs[2],   FieldElement32([2*121666,0,0,0,0,0,0,0,0,0]));
        assert_eq!(xs[3], -&FieldElement32([2*121665,0,0,0,0,0,0,0,0,0]));
    }

    #[test]
    fn diff_sum_vs_serial() {
        let x0 = FieldElement32([10000, 10001, 10002, 10003, 10004, 10005, 10006, 10007, 10008, 10009]);
        let x1 = FieldElement32([10100, 10101, 10102, 10103, 10104, 10105, 10106, 10107, 10108, 10109]);
        let x2 = FieldElement32([10200, 10201, 10202, 10203, 10204, 10205, 10206, 10207, 10208, 10209]);
        let x3 = FieldElement32([10300, 10301, 10302, 10303, 10304, 10305, 10306, 10307, 10308, 10309]);

        let vec = FieldElement32x4::new(&x0, &x1, &x2, &x3);

        let result = vec.diff_sum().split();

        assert_eq!(result[0], &x1 - &x0);
        assert_eq!(result[1], &x1 + &x0);
        assert_eq!(result[2], &x3 - &x2);
        assert_eq!(result[3], &x3 + &x2);
    }

    #[test]
    fn multiply_vs_serial() {
        let x0 = FieldElement32([10000, 10001, 10002, 10003, 10004, 10005, 10006, 10007, 10008, 10009]);
        let x1 = FieldElement32([10100, 10101, 10102, 10103, 10104, 10105, 10106, 10107, 10108, 10109]);
        let x2 = FieldElement32([10200, 10201, 10202, 10203, 10204, 10205, 10206, 10207, 10208, 10209]);
        let x3 = FieldElement32([10300, 10301, 10302, 10303, 10304, 10305, 10306, 10307, 10308, 10309]);

        let vec = FieldElement32x4::new(&x0, &x1, &x2, &x3);
        let vecprime = vec.clone();

        let result = (&vec * &vecprime).split();

        assert_eq!(result[0], &x0 * &x0);
        assert_eq!(result[1], &x1 * &x1);
        assert_eq!(result[2], &x2 * &x2);
        assert_eq!(result[3], &x3 * &x3);
    }

    #[test]
    fn test_unpack_repack_pair() {
        let x0 = FieldElement32([10000, 10001, 10002, 10003, 10004, 10005, 10006, 10007, 10008, 10009]);
        let x1 = FieldElement32([10100, 10101, 10102, 10103, 10104, 10105, 10106, 10107, 10108, 10109]);
        let x2 = FieldElement32([10200, 10201, 10202, 10203, 10204, 10205, 10206, 10207, 10208, 10209]);
        let x3 = FieldElement32([10300, 10301, 10302, 10303, 10304, 10305, 10306, 10307, 10308, 10309]);

        let vec = FieldElement32x4::new(&x0, &x1, &x2, &x3);

        let src = vec.0[0];

        let (a,b) = unpack_pair(src);

        let expected_a = u32x8::new(10000, 0, 10100, 0, 10200, 0, 10300, 0);
        let expected_b = u32x8::new(10001, 0, 10101, 0, 10201, 0, 10301, 0);

        assert_eq!(a, expected_a);
        assert_eq!(b, expected_b);

        let expected_src = repack_pair(a,b);

        assert_eq!(src, expected_src);
    }

    #[test]
    fn new_split_roundtrips() {
        let x0 = FieldElement32::from_bytes(&[0x10; 32]);
        let x1 = FieldElement32::from_bytes(&[0x11; 32]);
        let x2 = FieldElement32::from_bytes(&[0x12; 32]);
        let x3 = FieldElement32::from_bytes(&[0x13; 32]);

        let vec = FieldElement32x4::new(&x0, &x1, &x2, &x3);

        let splits = vec.split();

        assert_eq!(x0, splits[0]);
        assert_eq!(x1, splits[1]);
        assert_eq!(x2, splits[2]);
        assert_eq!(x3, splits[3]);
    }

}

#[cfg(all(test, feature = "bench"))]
mod bench {
    use test::Bencher;
    use super::*;

    #[bench]
    fn multiply(b: &mut Bencher) {
        let vec = FieldElement32x4::splat(&FieldElement::zero());
        let vecprime = vec.clone();

        b.iter(|| &vec * &vecprime );
    }
}

