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

pub const A_LANES: u8 = 0b0000_0101;
pub const B_LANES: u8 = 0b0000_1010;
pub const C_LANES: u8 = 0b0101_0000;
pub const D_LANES: u8 = 0b1010_0000;

pub const A_LANES64: u8 = 0b00_00_00_11;
pub const B_LANES64: u8 = 0b00_00_11_00;
pub const C_LANES64: u8 = 0b00_11_00_00;
pub const D_LANES64: u8 = 0b11_00_00_00;

pub const ALL_LANES: u8 = A_LANES | B_LANES | C_LANES | D_LANES;

use core::ops::Mul;

use stdsimd::simd::{u32x8, i32x8, u64x4};

use backend::u64::field::FieldElement64;

use backend::avx2::constants::{P_TIMES_2_LO, P_TIMES_2_HI, P_TIMES_16_LO, P_TIMES_16_HI};

/// A vector of four `FieldElements`, implemented using AVX2.
#[derive(Clone, Copy, Debug)]
pub(crate) struct FieldElement32x4(pub(crate) [u32x8; 5]);

use subtle::ConditionallyAssignable;
use subtle::Choice;

impl ConditionallyAssignable for FieldElement32x4 {
    fn conditional_assign(&mut self, other: &FieldElement32x4, choice: Choice) {
        let mask = (-(choice.unwrap_u8() as i32)) as u32;
        let mask_vec = u32x8::splat(mask);
        for i in 0..5 {
            self.0[i] = self.0[i] ^ (mask_vec & (self.0[i] ^ other.0[i]));
        }
    }
}


impl FieldElement32x4 {
    pub(crate) fn split(&self) -> [FieldElement64; 4] {
        let mut out = [FieldElement64::zero(); 4];
        for i in 0..5 {

            let a_2i   = self.0[i].extract(0) as u64; //
            let b_2i   = self.0[i].extract(1) as u64; //
            let a_2i_1 = self.0[i].extract(2) as u64; // `.
            let b_2i_1 = self.0[i].extract(3) as u64; //  | pre-swapped to avoid
            let c_2i   = self.0[i].extract(4) as u64; //  | a cross lane shuffle
            let d_2i   = self.0[i].extract(5) as u64; // .'
            let c_2i_1 = self.0[i].extract(6) as u64; //
            let d_2i_1 = self.0[i].extract(7) as u64; //

            out[0].0[i] = a_2i + (a_2i_1 << 26);
            out[1].0[i] = b_2i + (b_2i_1 << 26);
            out[2].0[i] = c_2i + (c_2i_1 << 26);
            out[3].0[i] = d_2i + (d_2i_1 << 26);
        }

        out
    }

    pub fn zero() -> FieldElement32x4 {
        FieldElement32x4([u32x8::splat(0);5])
    }

    pub fn splat(x: &FieldElement64) -> FieldElement32x4 {
        FieldElement32x4::new(x,x,x,x)
    }

    pub fn new(
        x0: &FieldElement64,
        x1: &FieldElement64,
        x2: &FieldElement64,
        x3: &FieldElement64,
    ) -> FieldElement32x4 {
        let mut buf = [u32x8::splat(0); 5];
        let low_26_bits = (1 << 26) - 1;
        for i in 0..5 {
            let a_2i   = (x0.0[i] & low_26_bits) as u32;
            let a_2i_1 = (x0.0[i] >> 26) as u32;
            let b_2i   = (x1.0[i] & low_26_bits) as u32;
            let b_2i_1 = (x1.0[i] >> 26) as u32;
            let c_2i   = (x2.0[i] & low_26_bits) as u32;
            let c_2i_1 = (x2.0[i] >> 26) as u32;
            let d_2i   = (x3.0[i] & low_26_bits) as u32;
            let d_2i_1 = (x3.0[i] >> 26) as u32;

            buf[i] = u32x8::new(a_2i, b_2i, a_2i_1, b_2i_1, c_2i, d_2i, c_2i_1, d_2i_1);
        }

        let mut out = FieldElement32x4(buf);
        out.reduce32();
        return out;
    }

    pub fn negate_lazy(&mut self, mask: u8) {
        let mask = mask as i32;
        unsafe {
            use stdsimd::vendor::_mm256_blend_epi32;
            self.0[0] = _mm256_blend_epi32(self.0[0].into(), (P_TIMES_2_LO - self.0[0]).into(), mask).into();
            self.0[1] = _mm256_blend_epi32(self.0[1].into(), (P_TIMES_2_HI - self.0[1]).into(), mask).into();
            self.0[2] = _mm256_blend_epi32(self.0[2].into(), (P_TIMES_2_HI - self.0[2]).into(), mask).into();
            self.0[3] = _mm256_blend_epi32(self.0[3].into(), (P_TIMES_2_HI - self.0[3]).into(), mask).into();
            self.0[4] = _mm256_blend_epi32(self.0[4].into(), (P_TIMES_2_HI - self.0[4]).into(), mask).into();
        }
    }

    /// Negate variables in lanes where mask is set
    pub fn negate(&mut self, mask: u8) {
        let mask = mask as i32;
        unsafe {
            use stdsimd::vendor::_mm256_blend_epi32;
            self.0[0] = _mm256_blend_epi32(self.0[0].into(), (P_TIMES_16_LO - self.0[0]).into(), mask).into();
            self.0[1] = _mm256_blend_epi32(self.0[1].into(), (P_TIMES_16_HI - self.0[1]).into(), mask).into();
            self.0[2] = _mm256_blend_epi32(self.0[2].into(), (P_TIMES_16_HI - self.0[2]).into(), mask).into();
            self.0[3] = _mm256_blend_epi32(self.0[3].into(), (P_TIMES_16_HI - self.0[3]).into(), mask).into();
            self.0[4] = _mm256_blend_epi32(self.0[4].into(), (P_TIMES_16_HI - self.0[4]).into(), mask).into();
        }
        self.reduce32();
    }

    /// Given `self = (A,B,C,D)`, set `self = (B,A,C,D)`
    pub fn swap_AB(&mut self) {
        unsafe {
            use stdsimd::vendor::_mm256_shuffle_epi32;
            use stdsimd::vendor::_mm256_blend_epi32;
            for i in 0..5 {
                let swapped = _mm256_shuffle_epi32(self.0[i].into(), 0b10_11_00_01);
                self.0[i] = _mm256_blend_epi32(self.0[i].into(), swapped, 0b00001111).into();
            }
        }
    }

    /// Given `self = (A,B,C,D)`, set `self = (A,B,D,C)`
    pub fn swap_CD(&mut self) {
        unsafe {
            use stdsimd::vendor::_mm256_shuffle_epi32;
            use stdsimd::vendor::_mm256_blend_epi32;
            for i in 0..5 {
                let swapped = _mm256_shuffle_epi32(self.0[i].into(), 0b10_11_00_01);
                self.0[i] = _mm256_blend_epi32(self.0[i].into(), swapped, 0b11110000).into();
            }
        }
    }

    /// Given `self = (A,B,C,D)`, set `self = (B - A, B + A, D - C, D + C)` according to `mask`.
    pub fn diff_sum(&mut self, mask: u8) {
        let mask = mask as i32;
        unsafe {
            use stdsimd::vendor::{_mm256_shuffle_epi32, _mm256_blend_epi32};

            let x01 = self.0[0];
            let x01_shuf = _mm256_shuffle_epi32(x01.as_i32x8(), 0b10_11_00_01).as_u32x8();
            let v1 = (x01_shuf + P_TIMES_2_LO) - x01;
            let v2 =  x01_shuf + x01;
            let diffsum01 = _mm256_blend_epi32(v1.into(), v2.into(), 0b10101010).as_u32x8();
            self.0[0] = _mm256_blend_epi32(x01.into(), diffsum01.into(), mask).into();

            let x23 = self.0[1];
            let x23_shuf = _mm256_shuffle_epi32(x23.as_i32x8(), 0b10_11_00_01).as_u32x8();
            let v1 = (x23_shuf + P_TIMES_2_HI) - x23;
            let v2 =  x23_shuf + x23;
            let diffsum23 = _mm256_blend_epi32(v1.into(), v2.into(), 0b10101010).as_u32x8();
            self.0[1] = _mm256_blend_epi32(x23.into(), diffsum23.into(), mask).into();

            let x45 = self.0[2];
            let x45_shuf = _mm256_shuffle_epi32(x45.as_i32x8(), 0b10_11_00_01).as_u32x8();
            let v1 = (x45_shuf + P_TIMES_2_HI) - x45;
            let v2 =  x45_shuf + x45;
            let diffsum45 = _mm256_blend_epi32(v1.into(), v2.into(), 0b10101010).as_u32x8();
            self.0[2] = _mm256_blend_epi32(x45.into(), diffsum45.into(), mask).into();

            let x67 = self.0[3];
            let x67_shuf = _mm256_shuffle_epi32(x67.as_i32x8(), 0b10_11_00_01).as_u32x8();
            let v1 = (x67_shuf + P_TIMES_2_HI) - x67;
            let v2 =  x67_shuf + x67;
            let diffsum67 = _mm256_blend_epi32(v1.into(), v2.into(), 0b10101010).as_u32x8();
            self.0[3] = _mm256_blend_epi32(x67.into(), diffsum67.into(), mask).into();

            let x89 = self.0[4];
            let x89_shuf = _mm256_shuffle_epi32(x89.as_i32x8(), 0b10_11_00_01).as_u32x8();
            let v1 = (x89_shuf + P_TIMES_2_HI) - x89;
            let v2 =  x89_shuf + x89;
            let diffsum89 = _mm256_blend_epi32(v1.into(), v2.into(), 0b10101010).as_u32x8();
            self.0[4] = _mm256_blend_epi32(x89.into(), diffsum89.into(), mask).into();
        }
    }

    /// Let `self` \\(= (A, B, C, D) \\).
    ///
    /// Compute
    /// $$( 121666A, 121666B, 2\cdot 121666C, 2\cdot 121665 D).$$
    pub fn scale_by_curve_constants(&mut self) {
        let mut b = [u64x4::splat(0); 10];

        let consts   = u32x8::new(121666, 0, 121666, 0, 2*121666, 0, 2*121665, 0);

        unsafe {
            use stdsimd::vendor::_mm256_mul_epu32;

            let (b0, b1) = unpack_pair(self.0[0]);
            b[0] = _mm256_mul_epu32(b0, consts);
            b[1] = _mm256_mul_epu32(b1, consts);

            let (b2, b3) = unpack_pair(self.0[1]);
            b[2] = _mm256_mul_epu32(b2, consts);
            b[3] = _mm256_mul_epu32(b3, consts);

            let (b4, b5) = unpack_pair(self.0[2]);
            b[4] = _mm256_mul_epu32(b4, consts);
            b[5] = _mm256_mul_epu32(b5, consts);

            let (b6, b7) = unpack_pair(self.0[3]);
            b[6] = _mm256_mul_epu32(b6, consts);
            b[7] = _mm256_mul_epu32(b7, consts);

            let (b8, b9) = unpack_pair(self.0[4]);
            b[8] = _mm256_mul_epu32(b8, consts);
            b[9] = _mm256_mul_epu32(b9, consts);
        }

        *self = FieldElement32x4::reduce64(b);
    }

    pub fn reduce32(&mut self) {

        let shifts = i32x8::new(26,26,25,25,26,26,25,25);
        let masks  = u32x8::new((1<<26)-1, (1<<26)-1, (1<<25)-1, (1<<25)-1,
                                (1<<26)-1, (1<<26)-1, (1<<25)-1, (1<<25)-1);

        let carry = |v: u32x8| -> u32x8 {
            unsafe {
                use stdsimd::vendor::_mm256_srlv_epi32;
                _mm256_srlv_epi32(v.into(), shifts).into()
            }
        };

        let swap_lanes = |v: u32x8| -> u32x8 {
            unsafe {
                use stdsimd::vendor::_mm256_shuffle_epi32;
                _mm256_shuffle_epi32(v.into(), 0b01_00_11_10).into()
            }
        };

        let combine = |v_lo: u32x8, v_hi: u32x8| -> u32x8 {
            unsafe {
                use stdsimd::vendor::_mm256_blend_epi32;
                _mm256_blend_epi32(v_lo.into(), v_hi.into(), 0b11_00_11_00).into()
            }
        };

        let v = &mut self.0;

        let c10 = swap_lanes(carry(v[0]));
        v[0] = (v[0] & masks) + combine(u32x8::splat(0), c10);
        let c32 = swap_lanes(carry(v[1]));
        v[1] = (v[1] & masks) + combine(c10, c32);
        let c54 = swap_lanes(carry(v[2]));
        v[2] = (v[2] & masks) + combine(c32, c54);
        let c76 = swap_lanes(carry(v[3]));
        v[3] = (v[3] & masks) + combine(c54, c76);
        let c98 = swap_lanes(carry(v[4]));
        v[4] = (v[4] & masks) + combine(c76, c98);

        // Still need to account for c9
        // c98 = (c9, c9, c8, c8, c9, c9, c8, c8)
        //
        let c9_19: u32x8;
        unsafe {
            use stdsimd::vendor::_mm256_mul_epu32;
            use stdsimd::vendor::_mm256_shuffle_epi32;
            let c9_spread: u32x8 = _mm256_shuffle_epi32(c98.into(), 0b11_01_10_00).into();
            let c9_19_spread: u32x8 = _mm256_mul_epu32(c9_spread, u64x4::splat(19).into()).into();
            c9_19 = _mm256_shuffle_epi32(c9_19_spread.into(), 0b11_01_10_00).into();
        }

        v[0] = v[0] + c9_19;
    }

    pub fn reduce64(mut z: [u64x4; 10]) -> FieldElement32x4 {
        // These aren't const because splat isn't a const fn
        let LOW_25_BITS: u64x4 = u64x4::splat((1<<25)-1);
        let LOW_26_BITS: u64x4 = u64x4::splat((1<<26)-1);

        // Carry the value from limb i = 0..8 to limb i+1
        let carry = |z: &mut [u64x4; 10], i: usize| {
            debug_assert!(i < 9);
            if i % 2 == 0 {
                // Even limbs have 26 bits
                z[i+1] = z[i+1] + (z[i] >> 26);
                z[i] = z[i] & LOW_26_BITS;
            } else {
                // Odd limbs have 25 bits
                z[i+1] = z[i+1] + (z[i] >> 25);
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

        let c = z[9] >> 25;
        z[9] = z[9] & LOW_25_BITS;
        let mut c0 = c & LOW_26_BITS; // c0 < 2^26;
        let mut c1 = c >> 26;         // c1 < 2^(39-26) = 2^13;

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

impl FieldElement32x4 {
    /// Square this field element, then conditionally negate according to `neg_mask`; for instance,
    /// `neg_mask = 0b11_00_00_00` negates the \\( D \\) value.
    ///
    /// # Precondition
    ///
    /// Limbs must be bounded by bit-excess \\( b < 2.0 \\).
    pub fn square(&self, neg_mask: u8) -> FieldElement32x4 {
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

        let v19 = u32x8::new(19,0,19,0,19,0,19,0);

        let (x0, x1) = unpack_pair(self.0[0]);
        let (x2, x3) = unpack_pair(self.0[1]);
        let (x4, x5) = unpack_pair(self.0[2]);
        let (x6, x7) = unpack_pair(self.0[3]);
        let (x8, x9) = unpack_pair(self.0[4]);

        let x0_2   = x0 << 1;
        let x1_2   = x1 << 1;
        let x2_2   = x2 << 1;
        let x3_2   = x3 << 1;
        let x4_2   = x4 << 1;
        let x5_2   = x5 << 1;
        let x6_2   = x6 << 1;
        let x7_2   = x7 << 1;

        let x5_19  = m_lo(v19, x5);
        let x6_19  = m_lo(v19, x6);
        let x7_19  = m_lo(v19, x7);
        let x8_19  = m_lo(v19, x8);
        let x9_19  = m_lo(v19, x9);

        let mut z0 = m(x0,  x0) + m(x2_2,x8_19) + m(x4_2,x6_19) + ((m(x1_2,x9_19) +  m(x3_2,x7_19) +    m(x5,x5_19)) << 1);
        let mut z1 = m(x0_2,x1) + m(x3_2,x8_19) + m(x5_2,x6_19) +                  ((m(x2,x9_19)   +    m(x4,x7_19)) << 1);
        let mut z2 = m(x0_2,x2) + m(x1_2,x1)    + m(x4_2,x8_19) + m(x6,x6_19)    + ((m(x3_2,x9_19) +  m(x5_2,x7_19)) << 1);
        let mut z3 = m(x0_2,x3) + m(x1_2,x2)    + m(x5_2,x8_19) +                  ((m(x4,x9_19)   +    m(x6,x7_19)) << 1);
        let mut z4 = m(x0_2,x4) + m(x1_2,x3_2)  + m(x2,  x2)    + m(x6_2,x8_19)  + ((m(x5_2,x9_19) +    m(x7,x7_19)) << 1);
        let mut z5 = m(x0_2,x5) + m(x1_2,x4)    + m(x2_2,x3)    + m(x7_2,x8_19)                    +  ((m(x6,x9_19)) << 1);
        let mut z6 = m(x0_2,x6) + m(x1_2,x5_2)  + m(x2_2,x4)    + m(x3_2,x3) + m(x8,x8_19)        + ((m(x7_2,x9_19)) << 1);
        let mut z7 = m(x0_2,x7) + m(x1_2,x6)    + m(x2_2,x5)    + m(x3_2,x4)                      +   ((m(x8,x9_19)) << 1);
        let mut z8 = m(x0_2,x8) + m(x1_2,x7_2)  + m(x2_2,x6)    + m(x3_2,x5_2) + m(x4,x4)         +   ((m(x9,x9_19)) << 1);
        let mut z9 = m(x0_2,x9) + m(x1_2,x8)    + m(x2_2,x7)    + m(x3_2,x6) + m(x4_2,x5);

        #[inline(always)]
        fn mask_neg(x: u64x4, p: u64x4, mask: u8) -> u64x4 {
            unsafe {
                use stdsimd::vendor::_mm256_blend_epi32;
                _mm256_blend_epi32(x.into(), (p - x).into(), mask as i32).into()
            }
        }

        // The biggest z_i is bounded as z_i < 249*2^(51 + 2*b);
        // if b < 1.5 we get z_i < 4485585228861014016.
        //
        // The limbs of the multiples of p are bounded above by
        //
        // 0x3fffffff << 37 = 9223371899415822336 < 2^63
        //
        // and below by
        //
        // 0x1fffffff << 37 = 4611685880988434432
        //                  > 4485585228861014016
        //
        // So these multiples of p are big enough to avoid underflow
        // in subtraction, and small enough to fit within u64
        // with room for a carry.

        let low__p37 = u64x4::splat(0x3ffffed << 37);
        let even_p37 = u64x4::splat(0x3ffffff << 37);
        let odd__p37 = u64x4::splat(0x1ffffff << 37);

        z0 = mask_neg(z0, low__p37, neg_mask);
        z1 = mask_neg(z1, odd__p37, neg_mask);
        z2 = mask_neg(z2, even_p37, neg_mask);
        z3 = mask_neg(z3, odd__p37, neg_mask);
        z4 = mask_neg(z4, even_p37, neg_mask);
        z5 = mask_neg(z5, odd__p37, neg_mask);
        z6 = mask_neg(z6, even_p37, neg_mask);
        z7 = mask_neg(z7, odd__p37, neg_mask);
        z8 = mask_neg(z8, even_p37, neg_mask);
        z9 = mask_neg(z9, odd__p37, neg_mask);

        FieldElement32x4::reduce64([z0, z1, z2, z3, z4, z5, z6, z7, z8, z9])
    }
}

impl<'a, 'b> Mul<&'b FieldElement32x4> for &'a FieldElement32x4 {
    type Output = FieldElement32x4;
    fn mul(self, _rhs: &'b FieldElement32x4) -> FieldElement32x4 {

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

        let (x0, x1) = unpack_pair(self.0[0]);
        let (x2, x3) = unpack_pair(self.0[1]);
        let (x4, x5) = unpack_pair(self.0[2]);
        let (x6, x7) = unpack_pair(self.0[3]);
        let (x8, x9) = unpack_pair(self.0[4]);

        let (y0, y1) = unpack_pair(_rhs.0[0]);
        let (y2, y3) = unpack_pair(_rhs.0[1]);
        let (y4, y5) = unpack_pair(_rhs.0[2]);
        let (y6, y7) = unpack_pair(_rhs.0[3]);
        let (y8, y9) = unpack_pair(_rhs.0[4]);

        let v19 = u32x8::new(19,0,19,0,19,0,19,0);

        let y1_19 = m_lo(v19, y1); // This fits in a u32
        let y2_19 = m_lo(v19, y2); // iff 26 + b + lg(19) < 32
        let y3_19 = m_lo(v19, y3); // if  b < 32 - 26 - 4.248 = 1.752
        let y4_19 = m_lo(v19, y4);
        let y5_19 = m_lo(v19, y5); // below, b<2.5: this is a bottleneck,
        let y6_19 = m_lo(v19, y6); // could be avoided by promoting to
        let y7_19 = m_lo(v19, y7); // u64 here instead of in m()
        let y8_19 = m_lo(v19, y8);
        let y9_19 = m_lo(v19, y9);

        let x1_2 = x1 + x1; // This fits in a u32 iff 25 + b + 1 < 32
        let x3_2 = x3 + x3; //                    iff b < 6
        let x5_2 = x5 + x5;
        let x7_2 = x7 + x7;
        let x9_2 = x9 + x9;

        let z0 = m(x0,y0) + m(x1_2,y9_19) + m(x2,y8_19) + m(x3_2,y7_19) + m(x4,y6_19) + m(x5_2,y5_19) + m(x6,y4_19) + m(x7_2,y3_19) + m(x8,y2_19) + m(x9_2,y1_19);
        let z1 = m(x0,y1) +   m(x1,y0)    + m(x2,y9_19) +   m(x3,y8_19) + m(x4,y7_19) +   m(x5,y6_19) + m(x6,y5_19) +   m(x7,y4_19) + m(x8,y3_19) + m(x9,y2_19);
        let z2 = m(x0,y2) + m(x1_2,y1)    + m(x2,y0)    + m(x3_2,y9_19) + m(x4,y8_19) + m(x5_2,y7_19) + m(x6,y6_19) + m(x7_2,y5_19) + m(x8,y4_19) + m(x9_2,y3_19);
        let z3 = m(x0,y3) +   m(x1,y2)    + m(x2,y1)    +   m(x3,y0)    + m(x4,y9_19) +   m(x5,y8_19) + m(x6,y7_19) +   m(x7,y6_19) + m(x8,y5_19) + m(x9,y4_19);
        let z4 = m(x0,y4) + m(x1_2,y3)    + m(x2,y2)    + m(x3_2,y1)    + m(x4,y0)    + m(x5_2,y9_19) + m(x6,y8_19) + m(x7_2,y7_19) + m(x8,y6_19) + m(x9_2,y5_19);
        let z5 = m(x0,y5) +   m(x1,y4)    + m(x2,y3)    +   m(x3,y2)    + m(x4,y1)    +   m(x5,y0)    + m(x6,y9_19) +   m(x7,y8_19) + m(x8,y7_19) + m(x9,y6_19);
        let z6 = m(x0,y6) + m(x1_2,y5)    + m(x2,y4)    + m(x3_2,y3)    + m(x4,y2)    + m(x5_2,y1)    + m(x6,y0)    + m(x7_2,y9_19) + m(x8,y8_19) + m(x9_2,y7_19);
        let z7 = m(x0,y7) +   m(x1,y6)    + m(x2,y5)    +   m(x3,y4)    + m(x4,y3)    +   m(x5,y2)    + m(x6,y1)    +   m(x7,y0)    + m(x8,y9_19) + m(x9,y8_19);
        let z8 = m(x0,y8) + m(x1_2,y7)    + m(x2,y6)    + m(x3_2,y5)    + m(x4,y4)    + m(x5_2,y3)    + m(x6,y2)    + m(x7_2,y1)    + m(x8,y0)    + m(x9_2,y9_19);
        let z9 = m(x0,y9) +   m(x1,y8)    + m(x2,y7)    +   m(x3,y6)    + m(x4,y5)    +   m(x5,y4)    + m(x6,y3)    +   m(x7,y2)    + m(x8,y1)    + m(x9,y0);

        FieldElement32x4::reduce64([z0, z1, z2, z3, z4, z5, z6, z7, z8, z9])
    }
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn scale_by_curve_constants() {
        let mut x = FieldElement32x4::splat(&FieldElement64::one());
        x.scale_by_curve_constants();

        let xs = x.split();
        assert_eq!(xs[0],   FieldElement64([  121666,0,0,0,0]));
        assert_eq!(xs[1],   FieldElement64([  121666,0,0,0,0]));
        assert_eq!(xs[2],   FieldElement64([2*121666,0,0,0,0]));
        assert_eq!(xs[3],   FieldElement64([2*121665,0,0,0,0]));
    }

    #[test]
    fn diff_sum_vs_serial() {
        let x0 = FieldElement64([10000, 10001, 10002, 10003, 10004]);
        let x1 = FieldElement64([10100, 10101, 10102, 10103, 10104]);
        let x2 = FieldElement64([10200, 10201, 10202, 10203, 10204]);
        let x3 = FieldElement64([10300, 10301, 10302, 10303, 10304]);

        let mut vec = FieldElement32x4::new(&x0, &x1, &x2, &x3);
        vec.diff_sum(0xff);

        let result = vec.split();

        assert_eq!(result[0], &x1 - &x0);
        assert_eq!(result[1], &x1 + &x0);
        assert_eq!(result[2], &x3 - &x2);
        assert_eq!(result[3], &x3 + &x2);

        let mut vec = FieldElement32x4::new(&x0, &x1, &x2, &x3);
        vec.diff_sum(0b01011111); // leave D unchanged

        let result = vec.split();

        assert_eq!(result[0], &x1 - &x0);
        assert_eq!(result[1], &x1 + &x0);
        assert_eq!(result[2], &x3 - &x2);
        assert_eq!(result[3], x3);
    }

    #[test]
    fn square_vs_serial() {
        let x0 = FieldElement64([10000, 10001, 10002, 10003, 10004]);
        let x1 = FieldElement64([10100, 10101, 10102, 10103, 10104]);
        let x2 = FieldElement64([10200, 10201, 10202, 10203, 10204]);
        let x3 = FieldElement64([10300, 10301, 10302, 10303, 10304]);

        let vec = FieldElement32x4::new(&x0, &x1, &x2, &x3);

        let neg_mask = 0b11_00_00_00;

        let result = vec.square(neg_mask).split();

        assert_eq!(result[0], &x0 * &x0);
        assert_eq!(result[1], &x1 * &x1);
        assert_eq!(result[2], &x2 * &x2);
        assert_eq!(result[3], -&(&x3 * &x3));
    }


    #[test]
    fn multiply_vs_serial() {
        let x0 = FieldElement64([10000, 10001, 10002, 10003, 10004]);
        let x1 = FieldElement64([10100, 10101, 10102, 10103, 10104]);
        let x2 = FieldElement64([10200, 10201, 10202, 10203, 10204]);
        let x3 = FieldElement64([10300, 10301, 10302, 10303, 10304]);

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
        let x0 = FieldElement64([10000 + (10001 << 26), 0, 0, 0, 0]);
        let x1 = FieldElement64([10100 + (10101 << 26), 0, 0, 0, 0]);
        let x2 = FieldElement64([10200 + (10201 << 26), 0, 0, 0, 0]);
        let x3 = FieldElement64([10300 + (10301 << 26), 0, 0, 0, 0]);

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
        let x0 = FieldElement64::from_bytes(&[0x10; 32]);
        let x1 = FieldElement64::from_bytes(&[0x11; 32]);
        let x2 = FieldElement64::from_bytes(&[0x12; 32]);
        let x3 = FieldElement64::from_bytes(&[0x13; 32]);

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
        let vec = FieldElement32x4::splat(&FieldElement64::zero());
        let vecprime = vec.clone();

        b.iter(|| &vec * &vecprime );
    }
}

