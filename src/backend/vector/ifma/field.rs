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

}
