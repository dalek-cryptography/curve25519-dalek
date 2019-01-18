// -*- mode: rust; coding: utf-8; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2018 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Henry de Valence <hdevalence@hdevalence.ca>

use core::ops::{Add, Mul, Neg};
use packed_simd::{i32x8, u32x8, u64x4, IntoBits};

use backend::serial::u64::field::FieldElement51;

#[allow(improper_ctypes)]
extern "C" {
    #[link_name = "llvm.x86.avx512.vpmadd52l.uq.256"]
    fn madd52lo(z: u64x4, x: u64x4, y: u64x4) -> u64x4;
    #[link_name = "llvm.x86.avx512.vpmadd52h.uq.256"]
    fn madd52hi(z: u64x4, x: u64x4, y: u64x4) -> u64x4;
}

#[derive(Copy, Clone)]
pub struct FieldElement51x4([u64x4; 5]);

impl FieldElement51x4 {
    pub fn new(
        x0: &FieldElement51,
        x1: &FieldElement51,
        x2: &FieldElement51,
        x3: &FieldElement51,
    ) -> FieldElement51x4 {
        FieldElement51x4([
            u64x4::new(x0.0[0], x1.0[0], x2.0[0], x3.0[0]),
            u64x4::new(x0.0[1], x1.0[1], x2.0[1], x3.0[1]),
            u64x4::new(x0.0[2], x1.0[2], x2.0[2], x3.0[2]),
            u64x4::new(x0.0[3], x1.0[3], x2.0[3], x3.0[3]),
            u64x4::new(x0.0[4], x1.0[4], x2.0[4], x3.0[4]),
        ])
        .reduce()
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
    pub fn reduce(&self) -> FieldElement51x4 {
        let mask = u64x4::splat((1 << 51) - 1);
        let r19 = u64x4::splat(19);

        // Compute carryouts in parallel
        let c0 = self.0[0] >> 51;
        let c1 = self.0[1] >> 51;
        let c2 = self.0[2] >> 51;
        let c3 = self.0[3] >> 51;
        let c4 = self.0[4] >> 51;

        unsafe {
            FieldElement51x4([
                madd52lo(self.0[0] & mask, c4, r19),
                (self.0[1] & mask) + c0,
                (self.0[2] & mask) + c1,
                (self.0[3] & mask) + c2,
                (self.0[4] & mask) + c3,
            ])
        }
    }
}

impl<'a, 'b> Mul<&'b FieldElement51x4> for &'a FieldElement51x4 {
    type Output = FieldElement51x4;
    fn mul(self, rhs: &'b FieldElement51x4) -> FieldElement51x4 {
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
            z4lo = madd52lo(z4lo, x[4], y[0]);
            z5hi = madd52hi(z5hi, x[4], y[0]);
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
            z4lo = madd52lo(z4lo, x[2], y[2]);
            z5hi = madd52hi(z5hi, x[2], y[2]);
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

            let r19 = u64x4::splat(19);
            let r38 = u64x4::splat(38);
            let r1938 = u64x4::splat(19 * 38);
            let mut z919hi = u64x4::splat(0);

            // Wave 6
            z3lo = madd52lo(z3lo, x[0], y[3]);
            z919hi = madd52hi(z919hi, r19, z9);
            z0lo = madd52lo(z0lo, r19, z5);
            z4lo = madd52lo(z4lo, r19, z9);
            z1lo = madd52lo(z1lo, r19, z6);
            z2lo = madd52lo(z2lo, r19, z7);
            z1hi = madd52hi(z1hi, r19, z5);
            z4hi = madd52hi(z4hi, x[0], y[3]);

            // Wave 7
            z3lo = madd52lo(z3lo, r19, z8);
            z2hi = madd52hi(z2hi, r19, z6);
            z0lo = madd52lo(z0lo, r38, z919hi);
            z4lo = madd52lo(z4lo, r38, z8 >> 52);
            z1lo = madd52lo(z1lo, r38, z5 >> 52);
            z2lo = madd52lo(z2lo, r38, z6 >> 52);
            z3hi = madd52hi(z3hi, r19, z7);
            z4hi = madd52hi(z4hi, r19, z8);

            // Wave 8
            z3lo = madd52lo(z3lo, r38, z7 >> 52);
            z0lo = madd52lo(z0lo, r1938, z9 >> 52);

            FieldElement51x4([
                z0lo,
                z1lo + z1hi + z1hi,
                z2lo + z2hi + z2hi,
                z3lo + z3hi + z3hi,
                z4lo + z4hi + z4hi,
            ])
            .reduce()
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

        let ax4 = FieldElement51x4::new(&a, &a, &a, &a);
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

        let a16x4 = FieldElement51x4::new(&a16, &a16, &a16, &a16);
        let splits = a16x4.split();

        for i in 0..4 {
            assert_eq!(a16, splits[i]);
        }
    }

    #[test]
    fn mul_matches_serial() {
        // Invert a small field element to get a big one
        let a = FieldElement51([2438, 24, 243, 0, 0]).invert();
        let b = FieldElement51([98098, 87987897, 0, 1, 0]).invert();
        let c = &a * &b;

        let ax4 = FieldElement51x4::new(&a, &a, &a, &a);
        let bx4 = FieldElement51x4::new(&b, &b, &b, &b);
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

        let ax4 = FieldElement51x4::new(&a, &a, &a, &a);
        let bx4 = FieldElement51x4::new(&b, &b, &b, &b);
        let mut cx4 = &ax4 * &bx4;
        for i in 0..1024 {
            cx4 = &ax4 * &cx4;
            cx4 = &bx4 * &cx4;
        }

        let splits = cx4.split();

        for i in 0..4 {
            assert_eq!(c, splits[i]);
        }
    }
}
