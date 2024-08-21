// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2019 Isis Lovecruft, Henry de Valence
//               2021-2022 Robrecht Blancquaert
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
// - Robrecht Blancquaert <Robrecht.Simon.Blancquaert@vub.be>

//! More details on the algorithms can be found in the `avx2`
//! module. Here comments are mostly added only when needed
//! to explain differenes between the 'base' avx2 version and
//! this re-implementation for arm neon.

//! The most major difference is the split of one vector of 8
//! limbs into to vectors holding 4 limbs each. For the rest
//! changes where made to account for different structure in
//! arm instructions.

use core::ops::{Add, Mul, Neg};

use super::packed_simd::{i32x4, u32x2, u32x2x2, u32x4, u32x4x2, u64x2, u64x2x2};
use crate::backend::serial::u64::field::FieldElement51;
use crate::backend::vector::neon::constants::{
    P_TIMES_16_HI, P_TIMES_16_LO, P_TIMES_2_HI, P_TIMES_2_LO,
};

#[cfg(all(target_arch = "aarch64"))]
#[inline(always)]
fn vget_high_u32(v: core::arch::aarch64::uint32x4_t) -> core::arch::aarch64::uint32x2_t {
    use core::arch::asm;
    let o;
    unsafe {
        asm! (
            "DUP {o:d}, {v}.D[1]",
            v = in(vreg) v,
            o = out(vreg) o,
        )
    }
    o
}

#[cfg(all(target_arch = "aarch64"))]
#[inline(always)]
fn vget_low_u32(v: core::arch::aarch64::uint32x4_t) -> core::arch::aarch64::uint32x2_t {
    use core::arch::asm;
    let o;
    unsafe {
        asm! (
            "DUP {o:d}, {v}.D[0]",
            v = in(vreg) v,
            o = out(vreg) o,
        )
    }
    o
}
#[cfg(not(target_arch = "aarch64"))]
use core::arch::aarch64::vget_high_u32;
#[cfg(not(target_arch = "aarch64"))]
use core::arch::aarch64::vget_low_u32;

// Shuffle the lanes in a u32x4x2
macro_rules! shuffle {
    ($vec:expr , $index:expr) => {
        unsafe {
            let v_n: [u32; 8] = [
                $vec.extract::<0>(),
                $vec.extract::<1>(),
                $vec.extract::<2>(),
                $vec.extract::<3>(),
                $vec.extract::<4>(),
                $vec.extract::<5>(),
                $vec.extract::<6>(),
                $vec.extract::<7>(),
            ];
            u32x4x2::new(
                core::mem::transmute::<[u32; 4], u32x4>([
                    v_n[$index[0]],
                    v_n[$index[1]],
                    v_n[$index[2]],
                    v_n[$index[3]],
                ]),
                core::mem::transmute::<[u32; 4], u32x4>([
                    v_n[$index[4]],
                    v_n[$index[5]],
                    v_n[$index[6]],
                    v_n[$index[7]],
                ]),
            )
        }
    };
}

// Blend the lanes of two u32x4
macro_rules! blend {
    ($vec0: expr, $vec1: expr, $index:expr) => {
        unsafe {
            let v_n: [u32; 8] = [
                $vec0.extract::<0>(),
                $vec0.extract::<1>(),
                $vec0.extract::<2>(),
                $vec0.extract::<3>(),
                $vec1.extract::<0>(),
                $vec1.extract::<1>(),
                $vec1.extract::<2>(),
                $vec1.extract::<3>(),
            ];
            core::mem::transmute::<[u32; 4], u32x4>([
                v_n[$index[0]],
                v_n[$index[1]],
                v_n[$index[2]],
                v_n[$index[3]],
            ])
        }
    };
}

/// Unpack 32-bit lanes:
/// ((a0, b0, a1, b1) ,(c0, d0, c1, d1))
/// into
/// ((a0, b0), (c0, d0))
/// ((a1, b1), (c1, d1))
#[inline(always)]
fn unpack_pair(src: u32x4x2) -> (u32x2x2, u32x2x2) {
    let a0: u32x2;
    let a1: u32x2;
    let b0: u32x2;
    let b1: u32x2;
    unsafe {
        a0 = vget_low_u32(src.0 .0).into();
        a1 = vget_low_u32(src.0 .1).into();
        b0 = vget_high_u32(src.0 .0).into();
        b1 = vget_high_u32(src.0 .1).into();
    }
    return (u32x2x2::new(a0, a1), u32x2x2::new(b0, b1));
}

/// ((a0, 0, b0, 0), (c0, 0, d0, 0))
/// ((a1, 0, b1, 0), (c1, 0, d1, 0))
/// into
/// ((a0, b0, a1, b1), (c0, d0, c1, d1))
#[inline(always)]
#[rustfmt::skip] // Retain formatting of the return tuples
fn repack_pair(x: u32x4x2, y: u32x4x2) -> u32x4x2 {
    unsafe {
        use core::arch::aarch64::vcombine_u32;
        use core::arch::aarch64::vtrn1_u32;

        u32x4x2::new(
            vcombine_u32(
                vtrn1_u32(vget_low_u32(x.0.0), vget_high_u32(x.0.0)),
                vtrn1_u32(vget_low_u32(y.0.0), vget_high_u32(y.0.0))).into(),
            vcombine_u32(
                vtrn1_u32(vget_low_u32(x.0.1), vget_high_u32(x.0.1)),
                vtrn1_u32(vget_low_u32(y.0.1), vget_high_u32(y.0.1))).into(),
        )
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Lanes {
    C,
    D,
    AB,
    AC,
    CD,
    AD,
    BC,
    ABCD,
}

#[derive(Copy, Clone, Debug)]
pub enum Shuffle {
    AAAA,
    BBBB,
    CACA,
    DBBD,
    ADDA,
    CBCB,
    ABAB,
    BADC,
    BACD,
    ABDC,
}

#[derive(Clone, Copy, Debug)]
pub struct FieldElement2625x4(pub(crate) [u32x4x2; 5]);

use subtle::Choice;
use subtle::ConditionallySelectable;

impl ConditionallySelectable for FieldElement2625x4 {
    fn conditional_select(
        a: &FieldElement2625x4,
        b: &FieldElement2625x4,
        choice: Choice,
    ) -> FieldElement2625x4 {
        let mask = (-(choice.unwrap_u8() as i32)) as u32;
        let mask_vec = u32x4x2::splat(mask);
        FieldElement2625x4([
            a.0[0] ^ (mask_vec & (a.0[0] ^ b.0[0])),
            a.0[1] ^ (mask_vec & (a.0[1] ^ b.0[1])),
            a.0[2] ^ (mask_vec & (a.0[2] ^ b.0[2])),
            a.0[3] ^ (mask_vec & (a.0[3] ^ b.0[3])),
            a.0[4] ^ (mask_vec & (a.0[4] ^ b.0[4])),
        ])
    }

    fn conditional_assign(&mut self, other: &FieldElement2625x4, choice: Choice) {
        let mask = (-(choice.unwrap_u8() as i32)) as u32;
        let mask_vec = u32x4x2::splat(mask);
        self.0[0] ^= mask_vec & (self.0[0] ^ other.0[0]);
        self.0[1] ^= mask_vec & (self.0[1] ^ other.0[1]);
        self.0[2] ^= mask_vec & (self.0[2] ^ other.0[2]);
        self.0[3] ^= mask_vec & (self.0[3] ^ other.0[3]);
        self.0[4] ^= mask_vec & (self.0[4] ^ other.0[4]);
    }
}

impl FieldElement2625x4 {
    pub fn split(&self) -> [FieldElement51; 4] {
        let mut out = [FieldElement51::ZERO; 4];
        for i in 0..5 {
            let a_2i = self.0[i].extract::<0>() as u64;
            let b_2i = self.0[i].extract::<1>() as u64;
            let a_2i_1 = self.0[i].extract::<2>() as u64;
            let b_2i_1 = self.0[i].extract::<3>() as u64;
            let c_2i = self.0[i].extract::<4>() as u64;
            let d_2i = self.0[i].extract::<5>() as u64;
            let c_2i_1 = self.0[i].extract::<6>() as u64;
            let d_2i_1 = self.0[i].extract::<7>() as u64;

            out[0].0[i] = a_2i + (a_2i_1 << 26);
            out[1].0[i] = b_2i + (b_2i_1 << 26);
            out[2].0[i] = c_2i + (c_2i_1 << 26);
            out[3].0[i] = d_2i + (d_2i_1 << 26);
        }

        out
    }

    #[inline]
    pub fn shuffle(&self, control: Shuffle) -> FieldElement2625x4 {
        #[inline(always)]
        #[rustfmt::skip] // Retain format of the return tuples
        fn shuffle_lanes(x: u32x4x2, control: Shuffle) -> u32x4x2 {
            match control {
                Shuffle::AAAA => shuffle!(x, [0, 0, 2, 2, 0, 0, 2, 2]),
                Shuffle::BBBB => shuffle!(x, [1, 1, 3, 3, 1, 1, 3, 3]),
                Shuffle::CACA => shuffle!(x, [4, 0, 6, 2, 4, 0, 6, 2]),
                Shuffle::DBBD => shuffle!(x, [5, 1, 7, 3, 1, 5, 3, 7]),
                Shuffle::ADDA => shuffle!(x, [0, 5, 2, 7, 5, 0, 7, 2]),
                Shuffle::CBCB => shuffle!(x, [4, 1, 6, 3, 4, 1, 6, 3]),
                Shuffle::ABAB => shuffle!(x, [0, 1, 2, 3, 0, 1, 2, 3]),
                Shuffle::BADC => shuffle!(x, [1, 0, 3, 2, 5, 4, 7, 6]),
                Shuffle::BACD => shuffle!(x, [1, 0, 3, 2, 4, 5, 6, 7]),
                Shuffle::ABDC => shuffle!(x, [0, 1, 2, 3, 5, 4, 7, 6]),
            }
        }

        FieldElement2625x4([
            shuffle_lanes(self.0[0], control),
            shuffle_lanes(self.0[1], control),
            shuffle_lanes(self.0[2], control),
            shuffle_lanes(self.0[3], control),
            shuffle_lanes(self.0[4], control),
        ])
    }

    pub fn shuffleABAB(&self) -> FieldElement2625x4 {
        self.shuffle(Shuffle::ABAB)
    }

    pub fn shuffleBACD(&self) -> FieldElement2625x4 {
        self.shuffle(Shuffle::BACD)
    }

    // Can probably be sped up using multiple vset/vget instead of table
    #[inline]
    pub fn blend(&self, other: FieldElement2625x4, control: Lanes) -> FieldElement2625x4 {
        #[inline(always)]
        #[rustfmt::skip] // Retain format of the return tuples
        fn blend_lanes(x: u32x4x2, y: u32x4x2, control: Lanes) -> u32x4x2 {
            let x0 = u32x4::from(x.0.0);
            let x1 = u32x4::from(x.0.1);
            let y0 = u32x4::from(y.0.0);
            let y1 = u32x4::from(y.0.1);
            match control {
                Lanes::C  => u32x4x2::new(x0, blend!(y1, x1, [0, 5, 2, 7])),
                Lanes::D  => u32x4x2::new(x0, blend!(y1, x1, [4, 1, 6, 3])),
                Lanes::AD => u32x4x2::new(blend!(y0, x0, [0, 5, 2, 7]), blend!(y1, x1, [4, 1, 6, 3])),
                Lanes::AB => u32x4x2::new(y0, x1),
                Lanes::AC => u32x4x2::new(blend!(y0, x0, [0, 5, 2, 7]), blend!(y1, x1, [0, 5, 2, 7])),
                Lanes::CD => u32x4x2::new(x0, y1),
                Lanes::BC => u32x4x2::new(blend!(y0, x0, [4, 1, 6, 3]), blend!(y1, x1, [0, 5, 2, 7])),
                Lanes::ABCD => y,
            }
        }

        FieldElement2625x4([
            blend_lanes(self.0[0], other.0[0], control),
            blend_lanes(self.0[1], other.0[1], control),
            blend_lanes(self.0[2], other.0[2], control),
            blend_lanes(self.0[3], other.0[3], control),
            blend_lanes(self.0[4], other.0[4], control),
        ])
    }

    pub fn zero() -> FieldElement2625x4 {
        FieldElement2625x4([u32x4x2::splat(0); 5])
    }

    pub fn splat(x: &FieldElement51) -> FieldElement2625x4 {
        FieldElement2625x4::new(x, x, x, x)
    }

    pub fn new(
        x0: &FieldElement51,
        x1: &FieldElement51,
        x2: &FieldElement51,
        x3: &FieldElement51,
    ) -> FieldElement2625x4 {
        let mut buf = [u32x4x2::splat(0); 5];
        let low_26_bits = (1 << 26) - 1;
        for i in 0..5 {
            let a_2i = (x0.0[i] & low_26_bits) as u32;
            let a_2i_1 = (x0.0[i] >> 26) as u32;
            let b_2i = (x1.0[i] & low_26_bits) as u32;
            let b_2i_1 = (x1.0[i] >> 26) as u32;
            let c_2i = (x2.0[i] & low_26_bits) as u32;
            let c_2i_1 = (x2.0[i] >> 26) as u32;
            let d_2i = (x3.0[i] & low_26_bits) as u32;
            let d_2i_1 = (x3.0[i] >> 26) as u32;

            buf[i] = u32x4x2::new(
                u32x4::new(a_2i, b_2i, a_2i_1, b_2i_1),
                u32x4::new(c_2i, d_2i, c_2i_1, d_2i_1),
            );
        }
        return FieldElement2625x4(buf).reduce();
    }

    #[inline]
    pub fn negate_lazy(&self) -> FieldElement2625x4 {
        FieldElement2625x4([
            P_TIMES_2_LO - self.0[0],
            P_TIMES_2_HI - self.0[1],
            P_TIMES_2_HI - self.0[2],
            P_TIMES_2_HI - self.0[3],
            P_TIMES_2_HI - self.0[4],
        ])
    }

    #[inline]
    pub fn diff_sum(&self) -> FieldElement2625x4 {
        let tmp1 = self.shuffle(Shuffle::BADC);
        let tmp2 = self.blend(self.negate_lazy(), Lanes::AC);
        tmp1 + tmp2
    }

    pub fn reduce(&self) -> FieldElement2625x4 {
        // Negated for shift right instead of left
        let shifts = (
            i32x4::new(-26, -26, -25, -25),
            i32x4::new(-26, -26, -25, -25),
        );
        let masks = u32x4x2::new(
            u32x4::new((1 << 26) - 1, (1 << 26) - 1, (1 << 25) - 1, (1 << 25) - 1),
            u32x4::new((1 << 26) - 1, (1 << 26) - 1, (1 << 25) - 1, (1 << 25) - 1),
        );

        // Use mutliple transposes instead of table lookup?
        let rotated_carryout = |v: u32x4x2| -> u32x4x2 {
            unsafe {
                use core::arch::aarch64::vcombine_u32;
                use core::arch::aarch64::vqshlq_u32;

                let c: u32x4x2 = u32x4x2::new(
                    vqshlq_u32(v.0 .0, shifts.0.into()).into(),
                    vqshlq_u32(v.0 .1, shifts.1.into()).into(),
                );
                u32x4x2::new(
                    vcombine_u32(vget_high_u32(c.0 .0), vget_low_u32(c.0 .0)).into(),
                    vcombine_u32(vget_high_u32(c.0 .1), vget_low_u32(c.0 .1)).into(),
                )
            }
        };

        let combine = |v_lo: u32x4x2, v_hi: u32x4x2| -> u32x4x2 {
            unsafe {
                use core::arch::aarch64::vcombine_u32;
                u32x4x2::new(
                    vcombine_u32(vget_low_u32(v_lo.0 .0), vget_high_u32(v_hi.0 .0)).into(),
                    vcombine_u32(vget_low_u32(v_lo.0 .1), vget_high_u32(v_hi.0 .1)).into(),
                )
            }
        };

        let mut v = self.0;

        let c10 = rotated_carryout(v[0]);
        let mut com = combine(u32x4x2::splat(0), c10);
        v[0] = (v[0] & masks) + com;

        let c32 = rotated_carryout(v[1]);
        com = combine(c10, c32);
        v[1] = (v[1] & masks) + com;

        let c54 = rotated_carryout(v[2]);
        com = combine(c32, c54);
        v[2] = (v[2] & masks) + com;

        let c76 = rotated_carryout(v[3]);
        com = combine(c54, c76);
        v[3] = (v[3] & masks) + com;

        let c98 = rotated_carryout(v[4]);
        com = combine(c76, c98);
        v[4] = (v[4] & masks) + com;

        #[rustfmt::skip] // Retain formatting of return tuple
        let c9_19: u32x4x2 = unsafe {
            use core::arch::aarch64::vcombine_u32;
            use core::arch::aarch64::vmulq_n_u32;

            let c9_19_spread: u32x4x2 = u32x4x2::new(
                vmulq_n_u32(c98.0.0, 19).into(),
                vmulq_n_u32(c98.0.1, 19).into(),
            );

            u32x4x2::new(
                vcombine_u32(vget_low_u32(c9_19_spread.0.0), u32x2::splat(0).into()).into(),
                vcombine_u32(vget_low_u32(c9_19_spread.0.1), u32x2::splat(0).into()).into())
        };
        v[0] = v[0] + c9_19;

        FieldElement2625x4(v)
    }

    #[inline]
    #[rustfmt::skip] // Retain formatting of carry and repacking
    fn reduce64(mut z: [u64x2x2; 10]) -> FieldElement2625x4 {
        #[allow(non_snake_case)]
        let LOW_25_BITS: u64x2x2 = u64x2x2::splat((1 << 25) - 1);
        #[allow(non_snake_case)]
        let LOW_26_BITS: u64x2x2 = u64x2x2::splat((1 << 26) - 1);

        let carry = |z: &mut [u64x2x2; 10], i: usize| {
            debug_assert!(i < 9);
            if i % 2 == 0 {
                z[i + 1] = z[i + 1] + (z[i].shr::<26>());
                z[i] = z[i] & LOW_26_BITS;
            } else {
                z[i + 1] = z[i + 1] + (z[i].shr::<25>());
                z[i] = z[i] & LOW_25_BITS;
            }
        };

        carry(&mut z, 0); carry(&mut z, 4);
        carry(&mut z, 1); carry(&mut z, 5);
        carry(&mut z, 2); carry(&mut z, 6);
        carry(&mut z, 3); carry(&mut z, 7);
        carry(&mut z, 4); carry(&mut z, 8);

        let c = z[9].shr::<25>();
        z[9] = z[9] & LOW_25_BITS;
        let mut c0: u64x2x2 = c & LOW_26_BITS;
        let mut c1: u64x2x2 = c.shr::<26>();

        unsafe {
            use core::arch::aarch64::vmulq_n_u32;
            use core::arch::aarch64::vreinterpretq_u32_u64;

            c0 = u64x2x2::new(
                vmulq_n_u32(vreinterpretq_u32_u64(c0.0.0), 19).into(),
                vmulq_n_u32(vreinterpretq_u32_u64(c0.0.1), 19).into());
            c1 = u64x2x2::new(
                vmulq_n_u32(vreinterpretq_u32_u64(c1.0.0), 19).into(),
                vmulq_n_u32(vreinterpretq_u32_u64(c1.0.1), 19).into());
        }

        z[0] = z[0] + c0;
        z[1] = z[1] + c1;
        carry(&mut z, 0);

        FieldElement2625x4([
            repack_pair(u32x4x2::new(z[0].0.0.into(), z[0].0.1.into()), u32x4x2::new(z[1].0.0.into(), z[1].0.1.into())),
            repack_pair(u32x4x2::new(z[2].0.0.into(), z[2].0.1.into()), u32x4x2::new(z[3].0.0.into(), z[3].0.1.into())),
            repack_pair(u32x4x2::new(z[4].0.0.into(), z[4].0.1.into()), u32x4x2::new(z[5].0.0.into(), z[5].0.1.into())),
            repack_pair(u32x4x2::new(z[6].0.0.into(), z[6].0.1.into()), u32x4x2::new(z[7].0.0.into(), z[7].0.1.into())),
            repack_pair(u32x4x2::new(z[8].0.0.into(), z[8].0.1.into()), u32x4x2::new(z[9].0.0.into(), z[9].0.1.into())),
        ])
    }

    #[allow(non_snake_case)]
    #[rustfmt::skip] // keep alignment of formulas
    pub fn square_and_negate_D(&self) -> FieldElement2625x4 {
        #[inline(always)]
        fn m(x: u32x2x2, y: u32x2x2) -> u64x2x2 {
            use core::arch::aarch64::vmull_u32;
            unsafe {
                let z0: u64x2 = vmull_u32(x.0.0, y.0.0).into();
                let z1: u64x2 = vmull_u32(x.0.1, y.0.1).into();
                u64x2x2::new(z0, z1)
            }
        }

        #[inline(always)]
        fn m_lo(x: u32x2x2, y: u32x2x2) -> u32x2x2 {
            use core::arch::aarch64::vmull_u32;
            use core::arch::aarch64::vuzp1_u32;
            unsafe {
                let x: u32x4x2 = u32x4x2::new(
                    vmull_u32(x.0.0, y.0.0).into(),
                    vmull_u32(x.0.1, y.0.1).into(),
                );
                u32x2x2::new(
                    vuzp1_u32(vget_low_u32(x.0.0), vget_high_u32(x.0.0)).into(),
                    vuzp1_u32(vget_low_u32(x.0.1), vget_high_u32(x.0.1)).into()
                )
            }
        }

        let v19 = u32x2x2::new(u32x2::new(19, 19), u32x2::new(19, 19));

        let (x0, x1) = unpack_pair(self.0[0]);
        let (x2, x3) = unpack_pair(self.0[1]);
        let (x4, x5) = unpack_pair(self.0[2]);
        let (x6, x7) = unpack_pair(self.0[3]);
        let (x8, x9) = unpack_pair(self.0[4]);

        let x0_2   = x0.shl::<1>();
        let x1_2   = x1.shl::<1>();
        let x2_2   = x2.shl::<1>();
        let x3_2   = x3.shl::<1>();
        let x4_2   = x4.shl::<1>();
        let x5_2   = x5.shl::<1>();
        let x6_2   = x6.shl::<1>();
        let x7_2   = x7.shl::<1>();

        let x5_19  = m_lo(v19, x5);
        let x6_19  = m_lo(v19, x6);
        let x7_19  = m_lo(v19, x7);
        let x8_19  = m_lo(v19, x8);
        let x9_19  = m_lo(v19, x9);

        let z0 = m(x0,  x0) + m(x2_2,x8_19) + m(x4_2,x6_19) + ((m(x1_2,x9_19) +  m(x3_2,x7_19) +     m(x5,x5_19)).shl::<1>());
        let z1 = m(x0_2,x1) + m(x3_2,x8_19) + m(x5_2,x6_19) +                  ((m(x2,x9_19)   +     m(x4,x7_19)).shl::<1>());
        let z2 = m(x0_2,x2) + m(x1_2,x1)    + m(x4_2,x8_19) + m(x6,x6_19)    + ((m(x3_2,x9_19) +   m(x5_2,x7_19)).shl::<1>());
        let z3 = m(x0_2,x3) + m(x1_2,x2)    + m(x5_2,x8_19) +                  ((m(x4,x9_19)   +     m(x6,x7_19)).shl::<1>());
        let z4 = m(x0_2,x4) + m(x1_2,x3_2)  + m(x2,  x2)    + m(x6_2,x8_19)  + ((m(x5_2,x9_19) +     m(x7,x7_19)).shl::<1>());
        let z5 = m(x0_2,x5) + m(x1_2,x4)    + m(x2_2,x3)    + m(x7_2,x8_19)                    +   ((m(x6,x9_19)).shl::<1>());
        let z6 = m(x0_2,x6) + m(x1_2,x5_2)  + m(x2_2,x4)    + m(x3_2,x3) + m(x8,x8_19)         + ((m(x7_2,x9_19)).shl::<1>());
        let z7 = m(x0_2,x7) + m(x1_2,x6)    + m(x2_2,x5)    + m(x3_2,x4)                       +   ((m(x8,x9_19)).shl::<1>());
        let z8 = m(x0_2,x8) + m(x1_2,x7_2)  + m(x2_2,x6)    + m(x3_2,x5_2) + m(x4,x4)          +   ((m(x9,x9_19)).shl::<1>());
        let z9 = m(x0_2,x9) + m(x1_2,x8)    + m(x2_2,x7)    + m(x3_2,x6) + m(x4_2,x5);


        let low__p37 = u64x2x2::splat(0x3ffffed << 37);
        let even_p37 = u64x2x2::splat(0x3ffffff << 37);
        let odd__p37 = u64x2x2::splat(0x1ffffff << 37);

        let negate_D = |x_01: u64x2x2, p_01: u64x2x2| -> u64x2x2 {
            unsafe {
                use core::arch::aarch64::vcombine_u32;
                use core::arch::aarch64::vreinterpretq_u32_u64;
                use core::arch::aarch64::vsubq_u64;

                u64x2x2::new(u64x2(x_01.0.0),
                 vcombine_u32(
                     vget_low_u32(vreinterpretq_u32_u64(x_01.0.1)),
                     vget_high_u32(vreinterpretq_u32_u64(vsubq_u64(p_01.0.1, x_01.0.1)))).into())
            }
        };

        let z0s = negate_D(z0, low__p37);
        let z1s = negate_D(z1, odd__p37);
        let z2s = negate_D(z2, even_p37);
        let z3s = negate_D(z3, odd__p37);
        let z4s = negate_D(z4, even_p37);
        let z5s = negate_D(z5, odd__p37);
        let z6s = negate_D(z6, even_p37);
        let z7s = negate_D(z7, odd__p37);
        let z8s = negate_D(z8, even_p37);
        let z9s = negate_D(z9, odd__p37);

        FieldElement2625x4::reduce64([z0s, z1s, z2s, z3s, z4s, z5s, z6s, z7s, z8s, z9s])
    }
}

impl Neg for FieldElement2625x4 {
    type Output = FieldElement2625x4;
    #[inline]
    fn neg(self) -> FieldElement2625x4 {
        FieldElement2625x4([
            P_TIMES_16_LO - self.0[0],
            P_TIMES_16_HI - self.0[1],
            P_TIMES_16_HI - self.0[2],
            P_TIMES_16_HI - self.0[3],
            P_TIMES_16_HI - self.0[4],
        ])
        .reduce()
    }
}

impl Add<FieldElement2625x4> for FieldElement2625x4 {
    type Output = FieldElement2625x4;
    #[inline]
    fn add(self, rhs: FieldElement2625x4) -> FieldElement2625x4 {
        FieldElement2625x4([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
            self.0[4] + rhs.0[4],
        ])
    }
}

impl Mul<(u32, u32, u32, u32)> for FieldElement2625x4 {
    type Output = FieldElement2625x4;
    #[inline]
    #[rustfmt::skip] // Retain formatting of packing
    fn mul(self, scalars: (u32, u32, u32, u32)) -> FieldElement2625x4 {
        unsafe {
            use core::arch::aarch64::vmull_u32;

            let consts = (
                u32x2::new(scalars.0, scalars.1),
                u32x2::new(scalars.2, scalars.3),
            );

            let (b0, b1) = unpack_pair(self.0[0]);
            let (b2, b3) = unpack_pair(self.0[1]);
            let (b4, b5) = unpack_pair(self.0[2]);
            let (b6, b7) = unpack_pair(self.0[3]);
            let (b8, b9) = unpack_pair(self.0[4]);

            FieldElement2625x4::reduce64([
                u64x2x2::new(vmull_u32(b0.0.0, consts.0.into()).into(), vmull_u32(b0.0.1, consts.1.into()).into()),
                u64x2x2::new(vmull_u32(b1.0.0, consts.0.into()).into(), vmull_u32(b1.0.1, consts.1.into()).into()),
                u64x2x2::new(vmull_u32(b2.0.0, consts.0.into()).into(), vmull_u32(b2.0.1, consts.1.into()).into()),
                u64x2x2::new(vmull_u32(b3.0.0, consts.0.into()).into(), vmull_u32(b3.0.1, consts.1.into()).into()),
                u64x2x2::new(vmull_u32(b4.0.0, consts.0.into()).into(), vmull_u32(b4.0.1, consts.1.into()).into()),
                u64x2x2::new(vmull_u32(b5.0.0, consts.0.into()).into(), vmull_u32(b5.0.1, consts.1.into()).into()),
                u64x2x2::new(vmull_u32(b6.0.0, consts.0.into()).into(), vmull_u32(b6.0.1, consts.1.into()).into()),
                u64x2x2::new(vmull_u32(b7.0.0, consts.0.into()).into(), vmull_u32(b7.0.1, consts.1.into()).into()),
                u64x2x2::new(vmull_u32(b8.0.0, consts.0.into()).into(), vmull_u32(b8.0.1, consts.1.into()).into()),
                u64x2x2::new(vmull_u32(b9.0.0, consts.0.into()).into(), vmull_u32(b9.0.1, consts.1.into()).into())
            ])
        }
    }
}

impl<'a, 'b> Mul<&'b FieldElement2625x4> for &'a FieldElement2625x4 {
    type Output = FieldElement2625x4;

    #[rustfmt::skip] // Retain formatting of z_i computation
    fn mul(self, rhs: &'b FieldElement2625x4) -> FieldElement2625x4 {
        #[inline(always)]
        fn m(x: u32x2x2, y: u32x2x2) -> u64x2x2 {
            use core::arch::aarch64::vmull_u32;
            unsafe {
                let z0: u64x2 = vmull_u32(x.0.0, y.0.0).into();
                let z1: u64x2 = vmull_u32(x.0.1, y.0.1).into();
                u64x2x2::new(z0, z1)
            }
        }

        #[inline(always)]
        fn m_lo(x: u32x2x2, y: u32x2x2) -> u32x2x2 {
            use core::arch::aarch64::vmull_u32;
            use core::arch::aarch64::vuzp1_u32;
            unsafe {
                let x: u32x4x2 = u32x4x2::new(
                    vmull_u32(x.0.0, y.0.0).into(),
                    vmull_u32(x.0.1, y.0.1).into(),
                );
                u32x2x2::new(
                    vuzp1_u32(vget_low_u32(x.0.0), vget_high_u32(x.0.0)).into(),
                    vuzp1_u32(vget_low_u32(x.0.1), vget_high_u32(x.0.1)).into()
                )
            }
        }


        let (x0, x1) = unpack_pair(self.0[0]);
        let (x2, x3) = unpack_pair(self.0[1]);
        let (x4, x5) = unpack_pair(self.0[2]);
        let (x6, x7) = unpack_pair(self.0[3]);
        let (x8, x9) = unpack_pair(self.0[4]);

        let (y0, y1) = unpack_pair(rhs.0[0]);
        let (y2, y3) = unpack_pair(rhs.0[1]);
        let (y4, y5) = unpack_pair(rhs.0[2]);
        let (y6, y7) = unpack_pair(rhs.0[3]);
        let (y8, y9) = unpack_pair(rhs.0[4]);

        let v19 = u32x2x2::new(u32x2::new(19, 19), u32x2::new(19, 19));

        let y1_19 = m_lo(v19, y1);
        let y2_19 = m_lo(v19, y2);
        let y3_19 = m_lo(v19, y3);
        let y4_19 = m_lo(v19, y4);
        let y5_19 = m_lo(v19, y5);
        let y6_19 = m_lo(v19, y6);
        let y7_19 = m_lo(v19, y7);
        let y8_19 = m_lo(v19, y8);
        let y9_19 = m_lo(v19, y9);

        let x1_2 = x1 + x1;
        let x3_2 = x3 + x3;
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

        let f = |x: u64x2x2| -> u64x2x2 {
            u64x2x2::new(
                x.0.0.into(),
                x.0.1.into()
            )
        };

        FieldElement2625x4::reduce64([
            f(z0),
            f(z1),
            f(z2),
            f(z3),
            f(z4),
            f(z5),
            f(z6),
            f(z7),
            f(z8),
            f(z9),
        ])
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_unpack_repack_pair() {
        let x0 = FieldElement51([10000 + (10001 << 26), 0, 0, 0, 0]);
        let x1 = FieldElement51([10100 + (10101 << 26), 0, 0, 0, 0]);
        let x2 = FieldElement51([10200 + (10201 << 26), 0, 0, 0, 0]);
        let x3 = FieldElement51([10300 + (10301 << 26), 0, 0, 0, 0]);

        let vec = FieldElement2625x4::new(&x0, &x1, &x2, &x3);

        let src = vec.0[0];

        let (a, b) = unpack_pair(src);

        let expected_a = u32x2x2::new(u32x2::new(10000, 10100), u32x2::new(10200, 10300));
        let expected_b = u32x2x2::new(u32x2::new(10001, 10101), u32x2::new(10201, 10301));

        assert_eq!(a, expected_a);
        assert_eq!(b, expected_b);

        let expected_src = repack_pair(
            u32x4x2::new(
                u32x4::new(a.extract::<0>(), 0, a.extract::<1>(), 0),
                u32x4::new(a.extract::<2>(), 0, a.extract::<3>(), 0),
            ),
            u32x4x2::new(
                u32x4::new(b.extract::<0>(), 0, b.extract::<1>(), 0),
                u32x4::new(b.extract::<2>(), 0, b.extract::<3>(), 0),
            ),
        );

        assert_eq!(src, expected_src);
    }

    #[test]
    fn scale_by_curve_constants() {
        let mut x = FieldElement2625x4::splat(&FieldElement51::ONE);

        x = x * (121666, 121666, 2 * 121666, 2 * 121665);

        let xs = x.split();
        assert_eq!(xs[0], FieldElement51([121666, 0, 0, 0, 0]));
        assert_eq!(xs[1], FieldElement51([121666, 0, 0, 0, 0]));
        assert_eq!(xs[2], FieldElement51([2 * 121666, 0, 0, 0, 0]));
        assert_eq!(xs[3], FieldElement51([2 * 121665, 0, 0, 0, 0]));
    }

    #[test]
    fn diff_sum_vs_serial() {
        let x0 = FieldElement51([10000, 10001, 10002, 10003, 10004]);
        let x1 = FieldElement51([10100, 10101, 10102, 10103, 10104]);
        let x2 = FieldElement51([10200, 10201, 10202, 10203, 10204]);
        let x3 = FieldElement51([10300, 10301, 10302, 10303, 10304]);

        let vec = FieldElement2625x4::new(&x0, &x1, &x2, &x3).diff_sum();

        let result = vec.split();

        assert_eq!(result[0], &x1 - &x0);
        assert_eq!(result[1], &x1 + &x0);
        assert_eq!(result[2], &x3 - &x2);
        assert_eq!(result[3], &x3 + &x2);
    }

    #[test]
    fn square_vs_serial() {
        let x0 = FieldElement51([10000, 10001, 10002, 10003, 10004]);
        let x1 = FieldElement51([10100, 10101, 10102, 10103, 10104]);
        let x2 = FieldElement51([10200, 10201, 10202, 10203, 10204]);
        let x3 = FieldElement51([10300, 10301, 10302, 10303, 10304]);

        let vec = FieldElement2625x4::new(&x0, &x1, &x2, &x3);

        let result = vec.square_and_negate_D().split();

        assert_eq!(result[0], &x0 * &x0);
        assert_eq!(result[1], &x1 * &x1);
        assert_eq!(result[2], &x2 * &x2);
        assert_eq!(result[3], -&(&x3 * &x3));
    }

    #[test]
    fn multiply_vs_serial() {
        let x0 = FieldElement51([10000, 10001, 10002, 10003, 10004]);
        let x1 = FieldElement51([10100, 10101, 10102, 10103, 10104]);
        let x2 = FieldElement51([10200, 10201, 10202, 10203, 10204]);
        let x3 = FieldElement51([10300, 10301, 10302, 10303, 10304]);

        let vec = FieldElement2625x4::new(&x0, &x1, &x2, &x3);
        let vecprime = vec.clone();

        let result = (&vec * &vecprime).split();

        assert_eq!(result[0], &x0 * &x0);
        assert_eq!(result[1], &x1 * &x1);
        assert_eq!(result[2], &x2 * &x2);
        assert_eq!(result[3], &x3 * &x3);
    }

    #[test]
    fn new_split_roundtrips() {
        let x0 = FieldElement51::from_bytes(&[0x10; 32]);
        let x1 = FieldElement51::from_bytes(&[0x11; 32]);
        let x2 = FieldElement51::from_bytes(&[0x12; 32]);
        let x3 = FieldElement51::from_bytes(&[0x13; 32]);

        let vec = FieldElement2625x4::new(&x0, &x1, &x2, &x3);

        let splits = vec.split();

        assert_eq!(x0, splits[0]);
        assert_eq!(x1, splits[1]);
        assert_eq!(x2, splits[2]);
        assert_eq!(x3, splits[3]);
    }
}
