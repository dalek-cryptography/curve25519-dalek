// -*- mode: rust; coding: utf-8; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2018 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Henry de Valence <hdevalence@hdevalence.ca>

use core::ops::{Add, Mul, Neg};
use packed_simd::{u64x4, FromBits, IntoBits};

use backend::serial::u64::field::FieldElement51;

#[allow(improper_ctypes)]
extern "C" {
    #[link_name = "llvm.x86.avx512.vpmadd52l.uq.256"]
    fn madd52lo(z: u64x4, x: u64x4, y: u64x4) -> u64x4;
    #[link_name = "llvm.x86.avx512.vpmadd52h.uq.256"]
    fn madd52hi(z: u64x4, x: u64x4, y: u64x4) -> u64x4;
}

/// A vector of four field elements in radix 2^51, with unreduced coefficients.
#[derive(Copy, Clone, Debug)]
pub struct F51x4Unreduced(pub(crate) [u64x4; 5]);

/// A vector of four field elements in radix 2^51, with reduced coefficients.
#[derive(Copy, Clone, Debug)]
pub struct F51x4Reduced(pub(crate) [u64x4; 5]);

#[derive(Copy, Clone)]
pub enum Lanes {
    D,
    AB,
    AC,
}

#[derive(Copy, Clone)]
pub enum Shuffle {
    AAAA,
    BADC,
    ADDA,
    CBCB,
    ABDC,
}

#[inline(always)]
fn shuffle_lanes(x: u64x4, control: Shuffle) -> u64x4 {
    unsafe {
        use core::arch::x86_64::_mm256_permute4x64_epi64 as perm;

        match control {
            Shuffle::AAAA => perm(x.into_bits(), 0b00_00_00_00).into_bits(),
            Shuffle::BADC => perm(x.into_bits(), 0b10_11_00_01).into_bits(),
            Shuffle::ADDA => perm(x.into_bits(), 0b00_11_11_00).into_bits(),
            Shuffle::CBCB => perm(x.into_bits(), 0b01_10_01_10).into_bits(),
            Shuffle::ABDC => perm(x.into_bits(), 0b10_11_01_00).into_bits(),
        }
    }
}

#[inline]
fn blend_lanes(x: u64x4, y: u64x4, control: Lanes) -> u64x4 {
    unsafe {
        use core::arch::x86_64::_mm256_blend_epi32 as blend;

        match control {
            Lanes::D => blend(x.into_bits(), y.into_bits(), 0b11_00_00_00).into_bits(),
            Lanes::AB => blend(x.into_bits(), y.into_bits(), 0b00_00_11_11).into_bits(),
            Lanes::AC => blend(x.into_bits(), y.into_bits(), 0b00_11_00_11).into_bits(),
        }
    }
}

impl F51x4Unreduced {
    pub fn new(
        x0: &FieldElement51,
        x1: &FieldElement51,
        x2: &FieldElement51,
        x3: &FieldElement51,
    ) -> F51x4Unreduced {
        F51x4Unreduced([
            u64x4::new(x0.0[0], x1.0[0], x2.0[0], x3.0[0]),
            u64x4::new(x0.0[1], x1.0[1], x2.0[1], x3.0[1]),
            u64x4::new(x0.0[2], x1.0[2], x2.0[2], x3.0[2]),
            u64x4::new(x0.0[3], x1.0[3], x2.0[3], x3.0[3]),
            u64x4::new(x0.0[4], x1.0[4], x2.0[4], x3.0[4]),
        ])
    }

    pub fn split(&self) -> [FieldElement51; 4] {
        let x = &self.0;
        [
            FieldElement51([
                x[0].extract(0),
                x[1].extract(0),
                x[2].extract(0),
                x[3].extract(0),
                x[4].extract(0),
            ]),
            FieldElement51([
                x[0].extract(1),
                x[1].extract(1),
                x[2].extract(1),
                x[3].extract(1),
                x[4].extract(1),
            ]),
            FieldElement51([
                x[0].extract(2),
                x[1].extract(2),
                x[2].extract(2),
                x[3].extract(2),
                x[4].extract(2),
            ]),
            FieldElement51([
                x[0].extract(3),
                x[1].extract(3),
                x[2].extract(3),
                x[3].extract(3),
                x[4].extract(3),
            ]),
        ]
    }

    #[inline]
    pub fn diff_sum(&self) -> F51x4Unreduced {
        // tmp1 = (B, A, D, C)
        let tmp1 = self.shuffle(Shuffle::BADC);
        // tmp2 = (-A, B, -C, D)
        let tmp2 = self.blend(&self.negate_lazy(), Lanes::AC);
        // (B - A, B + A, D - C, D + C)
        tmp1 + tmp2
    }

    #[inline]
    pub fn negate_lazy(&self) -> F51x4Unreduced {
        let lo = u64x4::splat(36028797018963664u64);
        let hi = u64x4::splat(36028797018963952u64);
        F51x4Unreduced([
            lo - self.0[0],
            hi - self.0[1],
            hi - self.0[2],
            hi - self.0[3],
            hi - self.0[4],
        ])
    }

    #[inline]
    pub fn shuffle(&self, control: Shuffle) -> F51x4Unreduced {
        F51x4Unreduced([
            shuffle_lanes(self.0[0], control),
            shuffle_lanes(self.0[1], control),
            shuffle_lanes(self.0[2], control),
            shuffle_lanes(self.0[3], control),
            shuffle_lanes(self.0[4], control),
        ])
    }

    #[inline]
    pub fn blend(&self, other: &F51x4Unreduced, control: Lanes) -> F51x4Unreduced {
        F51x4Unreduced([
            blend_lanes(self.0[0], other.0[0], control),
            blend_lanes(self.0[1], other.0[1], control),
            blend_lanes(self.0[2], other.0[2], control),
            blend_lanes(self.0[3], other.0[3], control),
            blend_lanes(self.0[4], other.0[4], control),
        ])
    }
}

impl F51x4Reduced {
    #[inline]
    pub fn shuffle(&self, control: Shuffle) -> F51x4Reduced {
        F51x4Reduced([
            shuffle_lanes(self.0[0], control),
            shuffle_lanes(self.0[1], control),
            shuffle_lanes(self.0[2], control),
            shuffle_lanes(self.0[3], control),
            shuffle_lanes(self.0[4], control),
        ])
    }

    #[inline]
    pub fn blend(&self, other: &F51x4Reduced, control: Lanes) -> F51x4Reduced {
        F51x4Reduced([
            blend_lanes(self.0[0], other.0[0], control),
            blend_lanes(self.0[1], other.0[1], control),
            blend_lanes(self.0[2], other.0[2], control),
            blend_lanes(self.0[3], other.0[3], control),
            blend_lanes(self.0[4], other.0[4], control),
        ])
    }
}

impl From<F51x4Reduced> for F51x4Unreduced {
    #[inline]
    fn from(x: F51x4Reduced) -> F51x4Unreduced {
        F51x4Unreduced(x.0)
    }
}

impl From<F51x4Unreduced> for F51x4Reduced {
    #[inline]
    fn from(x: F51x4Unreduced) -> F51x4Reduced {
        let mask = u64x4::splat((1 << 51) - 1);
        let r19 = u64x4::splat(19);

        // Compute carryouts in parallel
        let c0 = x.0[0] >> 51;
        let c1 = x.0[1] >> 51;
        let c2 = x.0[2] >> 51;
        let c3 = x.0[3] >> 51;
        let c4 = x.0[4] >> 51;

        unsafe {
            F51x4Reduced([
                madd52lo(x.0[0] & mask, c4, r19),
                (x.0[1] & mask) + c0,
                (x.0[2] & mask) + c1,
                (x.0[3] & mask) + c2,
                (x.0[4] & mask) + c3,
            ])
        }
    }
}

impl Add<F51x4Unreduced> for F51x4Unreduced {
    type Output = F51x4Unreduced;
    #[inline]
    fn add(self, rhs: F51x4Unreduced) -> F51x4Unreduced {
        F51x4Unreduced([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
            self.0[4] + rhs.0[4],
        ])
    }
}

impl<'a> Mul<(u32, u32, u32, u32)> for &'a F51x4Reduced {
    type Output = F51x4Unreduced;
    #[inline]
    fn mul(self, scalars: (u32, u32, u32, u32)) -> F51x4Unreduced {
        unsafe {
            let x = &self.0;
            let y = u64x4::new(
                scalars.0 as u64,
                scalars.1 as u64,
                scalars.2 as u64,
                scalars.3 as u64,
            );
            let mask = u64x4::splat((1 << 51) - 1);
            let r19 = u64x4::splat(19);

            let mut z0lo = u64x4::splat(0);
            let mut z1lo = u64x4::splat(0);
            let mut z2lo = u64x4::splat(0);
            let mut z3lo = u64x4::splat(0);
            let mut z4lo = u64x4::splat(0);
            let mut z1hi = u64x4::splat(0);
            let mut z2hi = u64x4::splat(0);
            let mut z3hi = u64x4::splat(0);
            let mut z4hi = u64x4::splat(0);
            let mut z5hi = u64x4::splat(0);

            // Wave 0
            z4hi = madd52hi(z4hi, y, x[3]);
            z5hi = madd52hi(z5hi, y, x[4]);
            z4lo = madd52lo(z4lo, y, x[4]);
            z0lo = madd52lo(z0lo, y, x[0]);
            z3lo = madd52lo(z3lo, y, x[3]);
            z2lo = madd52lo(z2lo, y, x[2]);
            z1lo = madd52lo(z1lo, y, x[1]);
            z3hi = madd52hi(z3hi, y, x[2]);

            // Wave 2
            z2hi = madd52hi(z2hi, y, x[1]);
            z1hi = madd52hi(z1hi, y, x[0]);
            z0lo = madd52lo(z0lo, z5hi + z5hi, r19);

            F51x4Unreduced([
                z0lo,
                z1hi + z1hi + z1lo,
                z2hi + z2hi + z2lo,
                z3hi + z3hi + z3lo,
                z4hi + z4hi + z4lo,
            ])
        }
    }
}

impl<'a, 'b> Mul<&'b F51x4Reduced> for &'a F51x4Reduced {
    type Output = F51x4Unreduced;
    #[inline]
    fn mul(self, rhs: &'b F51x4Reduced) -> F51x4Unreduced {
        unsafe {
            // Inputs
            let x = &self.0;
            let y = &rhs.0;

            // Accumulators for lo-sourced terms
            let mut z0lo = u64x4::splat(0);
            let mut z1lo = u64x4::splat(0);
            let mut z2lo = u64x4::splat(0);
            let mut z3lo = u64x4::splat(0);
            let mut z4lo = u64x4::splat(0);
            let mut z5lo = u64x4::splat(0);
            let mut z6lo = u64x4::splat(0);
            let mut z7lo = u64x4::splat(0);
            let mut z8lo = u64x4::splat(0);

            // Accumulators for hi-sourced terms
            // Need to be doubled before adding
            let mut z0hi = u64x4::splat(0);
            let mut z1hi = u64x4::splat(0);
            let mut z2hi = u64x4::splat(0);
            let mut z3hi = u64x4::splat(0);
            let mut z4hi = u64x4::splat(0);
            let mut z5hi = u64x4::splat(0);
            let mut z6hi = u64x4::splat(0);
            let mut z7hi = u64x4::splat(0);
            let mut z8hi = u64x4::splat(0);
            let mut z9hi = u64x4::splat(0);

            // Wave 0
            z4lo = madd52lo(z4lo, x[2], y[2]);
            z5hi = madd52hi(z5hi, x[2], y[2]);
            z5lo = madd52lo(z5lo, x[4], y[1]);
            z6hi = madd52hi(z6hi, x[4], y[1]);
            z6lo = madd52lo(z6lo, x[4], y[2]);
            z7hi = madd52hi(z7hi, x[4], y[2]);
            z7lo = madd52lo(z7lo, x[4], y[3]);
            z8hi = madd52hi(z8hi, x[4], y[3]);

            // Wave 1
            z4lo = madd52lo(z4lo, x[3], y[1]);
            z5hi = madd52hi(z5hi, x[3], y[1]);
            z5lo = madd52lo(z5lo, x[3], y[2]);
            z6hi = madd52hi(z6hi, x[3], y[2]);
            z6lo = madd52lo(z6lo, x[3], y[3]);
            z7hi = madd52hi(z7hi, x[3], y[3]);
            z7lo = madd52lo(z7lo, x[3], y[4]);
            z8hi = madd52hi(z8hi, x[3], y[4]);

            // Wave 2
            z8lo = madd52lo(z8lo, x[4], y[4]);
            z9hi = madd52hi(z9hi, x[4], y[4]);
            z4lo = madd52lo(z4lo, x[4], y[0]);
            z5hi = madd52hi(z5hi, x[4], y[0]);
            z5lo = madd52lo(z5lo, x[2], y[3]);
            z6hi = madd52hi(z6hi, x[2], y[3]);
            z6lo = madd52lo(z6lo, x[2], y[4]);
            z7hi = madd52hi(z7hi, x[2], y[4]);

            let z8 = z8lo + z8hi + z8hi;
            let z9 = z9hi + z9hi;

            // Wave 3
            z3lo = madd52lo(z3lo, x[3], y[0]);
            z4hi = madd52hi(z4hi, x[3], y[0]);
            z4lo = madd52lo(z4lo, x[1], y[3]);
            z5hi = madd52hi(z5hi, x[1], y[3]);
            z5lo = madd52lo(z5lo, x[1], y[4]);
            z6hi = madd52hi(z6hi, x[1], y[4]);
            z2lo = madd52lo(z2lo, x[2], y[0]);
            z3hi = madd52hi(z3hi, x[2], y[0]);

            let z6 = z6lo + z6hi + z6hi;
            let z7 = z7lo + z7hi + z7hi;

            // Wave 4
            z3lo = madd52lo(z3lo, x[2], y[1]);
            z4hi = madd52hi(z4hi, x[2], y[1]);
            z4lo = madd52lo(z4lo, x[0], y[4]);
            z5hi = madd52hi(z5hi, x[0], y[4]);
            z1lo = madd52lo(z1lo, x[1], y[0]);
            z2hi = madd52hi(z2hi, x[1], y[0]);
            z2lo = madd52lo(z2lo, x[1], y[1]);
            z3hi = madd52hi(z3hi, x[1], y[1]);

            let z5 = z5lo + z5hi + z5hi;

            // Wave 5
            z3lo = madd52lo(z3lo, x[1], y[2]);
            z4hi = madd52hi(z4hi, x[1], y[2]);
            z0lo = madd52lo(z0lo, x[0], y[0]);
            z1hi = madd52hi(z1hi, x[0], y[0]);
            z1lo = madd52lo(z1lo, x[0], y[1]);
            z2lo = madd52lo(z2lo, x[0], y[2]);
            z2hi = madd52hi(z2hi, x[0], y[1]);
            z3hi = madd52hi(z3hi, x[0], y[2]);

            let mut t0 = u64x4::splat(0);
            let mut t1 = u64x4::splat(0);
            let r19 = u64x4::splat(19);

            // Wave 6
            t0 = madd52hi(t0, r19, z9);
            t1 = madd52lo(t1, r19, z9 >> 52);
            z3lo = madd52lo(z3lo, x[0], y[3]);
            z4hi = madd52hi(z4hi, x[0], y[3]);
            z1hi = madd52lo(z1hi, r19, z5 >> 52);
            z2hi = madd52lo(z2hi, r19, z6 >> 52);
            z3hi = madd52lo(z3hi, r19, z7 >> 52);
            z0lo = madd52lo(z0lo, r19, z5);

            // Wave 7
            z4lo = madd52lo(z4lo, r19, z9);
            z1lo = madd52lo(z1lo, r19, z6);
            z0hi = madd52lo(z0hi, r19, t0 + t1);
            z4hi = madd52hi(z4hi, r19, z8);
            z2lo = madd52lo(z2lo, r19, z7);
            z1hi = madd52hi(z1hi, r19, z5);
            z2hi = madd52hi(z2hi, r19, z6);
            z3hi = madd52hi(z3hi, r19, z7);

            // Wave 8
            z3lo = madd52lo(z3lo, r19, z8);
            z4hi = madd52lo(z4hi, r19, z8 >> 52);

            F51x4Unreduced([
                z0lo + z0hi + z0hi,
                z1lo + z1hi + z1hi,
                z2lo + z2hi + z2hi,
                z3lo + z3hi + z3hi,
                z4lo + z4hi + z4hi,
            ])
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn vpmadd52luq() {
        let x = u64x4::splat(2);
        let y = u64x4::splat(3);
        let mut z = u64x4::splat(5);

        z = unsafe { madd52lo(z, x, y) };

        assert_eq!(z, u64x4::splat(5 + 2 * 3));
    }

    #[test]
    fn new_split_round_trip_on_reduced_input() {
        // Invert a small field element to get a big one
        let a = FieldElement51([2438, 24, 243, 0, 0]).invert();

        let ax4 = F51x4Unreduced::new(&a, &a, &a, &a);
        let splits = ax4.split();

        for i in 0..4 {
            assert_eq!(a, splits[i]);
        }
    }

    #[test]
    fn new_split_round_trip_on_unreduced_input() {
        // Invert a small field element to get a big one
        let a = FieldElement51([2438, 24, 243, 0, 0]).invert();
        // ... but now multiply it by 16 without reducing coeffs
        let a16 = FieldElement51([
            a.0[0] << 4,
            a.0[1] << 4,
            a.0[2] << 4,
            a.0[3] << 4,
            a.0[4] << 4,
        ]);

        let a16x4 = F51x4Unreduced::new(&a16, &a16, &a16, &a16);
        let splits = a16x4.split();

        for i in 0..4 {
            assert_eq!(a16, splits[i]);
        }
    }

    #[test]
    fn test_reduction() {
        // Invert a small field element to get a big one
        let a = FieldElement51([2438, 24, 243, 0, 0]).invert();
        // ... but now multiply it by 128 without reducing coeffs
        let abig = FieldElement51([
            a.0[0] << 4,
            a.0[1] << 4,
            a.0[2] << 4,
            a.0[3] << 4,
            a.0[4] << 4,
        ]);

        let abigx4: F51x4Reduced = F51x4Unreduced::new(&abig, &abig, &abig, &abig).into();

        let splits = F51x4Unreduced::from(abigx4).split();
        let c = &a * &FieldElement51([(1 << 4), 0, 0, 0, 0]);

        for i in 0..4 {
            assert_eq!(c, splits[i]);
        }
    }

    #[test]
    fn mul_matches_serial() {
        // Invert a small field element to get a big one
        let a = FieldElement51([2438, 24, 243, 0, 0]).invert();
        let b = FieldElement51([98098, 87987897, 0, 1, 0]).invert();
        let c = &a * &b;

        let ax4: F51x4Reduced = F51x4Unreduced::new(&a, &a, &a, &a).into();
        let bx4: F51x4Reduced = F51x4Unreduced::new(&b, &b, &b, &b).into();
        let cx4 = &ax4 * &bx4;

        let splits = cx4.split();

        for i in 0..4 {
            assert_eq!(c, splits[i]);
        }
    }

    #[test]
    fn iterated_mul_matches_serial() {
        // Invert a small field element to get a big one
        let a = FieldElement51([2438, 24, 243, 0, 0]).invert();
        let b = FieldElement51([98098, 87987897, 0, 1, 0]).invert();
        let mut c = &a * &b;
        for i in 0..1024 {
            c = &a * &c;
            c = &b * &c;
        }

        let ax4: F51x4Reduced = F51x4Unreduced::new(&a, &a, &a, &a).into();
        let bx4: F51x4Reduced = F51x4Unreduced::new(&b, &b, &b, &b).into();
        let mut cx4 = &ax4 * &bx4;
        for i in 0..1024 {
            cx4 = &ax4 * &F51x4Reduced::from(cx4);
            cx4 = &bx4 * &F51x4Reduced::from(cx4);
        }

        let splits = cx4.split();

        for i in 0..4 {
            assert_eq!(c, splits[i]);
        }
    }

    #[test]
    fn iterated_u32_mul_matches_serial() {
        // Invert a small field element to get a big one
        let a = FieldElement51([2438, 24, 243, 0, 0]).invert();
        let b = FieldElement51([121665, 0, 0, 0, 0]);
        let mut c = &a * &b;
        for i in 0..1024 {
            c = &b * &c;
        }

        let ax4 = F51x4Unreduced::new(&a, &a, &a, &a);
        let bx4 = (121665u32, 121665u32, 121665u32, 121665u32);
        let mut cx4 = &F51x4Reduced::from(ax4) * bx4;
        for i in 0..1024 {
            cx4 = &F51x4Reduced::from(cx4) * bx4;
        }

        let splits = cx4.split();

        for i in 0..4 {
            assert_eq!(c, splits[i]);
        }
    }

    #[test]
    fn shuffle_AAAA() {
        let x0 = FieldElement51::from_bytes(&[0x10; 32]);
        let x1 = FieldElement51::from_bytes(&[0x11; 32]);
        let x2 = FieldElement51::from_bytes(&[0x12; 32]);
        let x3 = FieldElement51::from_bytes(&[0x13; 32]);

        let x = F51x4Unreduced::new(&x0, &x1, &x2, &x3);

        let y = x.shuffle(Shuffle::AAAA);
        let splits = y.split();

        assert_eq!(splits[0], x0);
        assert_eq!(splits[1], x0);
        assert_eq!(splits[2], x0);
        assert_eq!(splits[3], x0);
    }

    #[test]
    fn blend_AB() {
        let x0 = FieldElement51::from_bytes(&[0x10; 32]);
        let x1 = FieldElement51::from_bytes(&[0x11; 32]);
        let x2 = FieldElement51::from_bytes(&[0x12; 32]);
        let x3 = FieldElement51::from_bytes(&[0x13; 32]);

        let x = F51x4Unreduced::new(&x0, &x1, &x2, &x3);
        let z = F51x4Unreduced::new(&x3, &x2, &x1, &x0);

        let y = x.blend(&z, Lanes::AB);
        let splits = y.split();

        assert_eq!(splits[0], x3);
        assert_eq!(splits[1], x2);
        assert_eq!(splits[2], x2);
        assert_eq!(splits[3], x3);
    }
}
