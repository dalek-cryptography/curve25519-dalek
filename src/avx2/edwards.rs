// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Extended Twisted Edwards for Curve25519, using AVX2.

// just going to own it
#![allow(bad_style)]

use std::convert::From;
use std::ops::Add;

use stdsimd::simd::u32x8;

use edwards;

use avx2::field::FieldElement32x4;

/// A point on Curve25519, represented in an AVX2-friendly format.
pub(crate) struct ExtendedPoint(FieldElement32x4);

// XXX need to cfg gate here to handle FieldElement64
impl From<edwards::ExtendedPoint> for ExtendedPoint {
    fn from(P: edwards::ExtendedPoint) -> ExtendedPoint {
        ExtendedPoint(FieldElement32x4::new(&P.X, &P.Y, &P.Z, &P.T))
    }
}

// XXX need to cfg gate here to handle FieldElement64
impl From<ExtendedPoint> for edwards::ExtendedPoint {
    fn from(P: ExtendedPoint) -> edwards::ExtendedPoint {
        let tmp = P.0.split();
        edwards::ExtendedPoint{X: tmp[0], Y: tmp[1], Z: tmp[2], T: tmp[3]}
    }
}

impl<'a, 'b> Add<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    /// Uses a slight tweak of the parallel unified formulas of HWCD'08
    fn add(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        unsafe {
            use stdsimd::vendor::_mm256_permute2x128_si256;
            use stdsimd::vendor::_mm256_permutevar8x32_epi32;
            use stdsimd::vendor::_mm256_blend_epi32;

            let mut P: FieldElement32x4 = self.0;
            let mut Q: FieldElement32x4 = other.0;
            let mut t0: FieldElement32x4 = self.0;

            for i in 0..5 {
                t0.0[i] = _mm256_permute2x128_si256(P.0[i].into(), Q.0[i].into(), 32).into();
            }
            //println!("t0 = (X1, Y1, X2, Y2)");
            //println!("t0 = {:?}\n", t0.split());

            let mut t1 = t0.diff_sum();
            //println!("t1 = (S1 S3 S2 S4)");
            //println!("t1 = {:?}\n", t1.split());

            for i in 0..5 {
                Q.0[i] = _mm256_permute2x128_si256(t1.0[i].into(), Q.0[i].into(), 49).into();
                t1.0[i] = _mm256_blend_epi32(t1.0[i].into(), P.0[i].into(), 0b11110000).into();
            }
            //println!("Q  = (S2 S4 Z2 T2)");
            //println!("Q = {:?}\n", Q.split());
            //println!("t1 = (S1 S3 Z1 T1)");
            //println!("t1 = {:?}\n", t1.split());

            P = &t1 * &Q;
            //println!("P = (S5 S6 S8 S7)");
            //println!("P = {:?}\n", P.split());
            
            P.scale_by_curve_constants();
            //println!("P = (S5' S6' S10 S8)");
            //println!("P = {:?}\n", P.split());

            Q = P.diff_sum();
            //println!("Q = (S11 S14 S12 S13)");
            //println!("Q = {:?}\n", Q.split());

            let c0 = u32x8::new(0,5,2,7,5,0,7,2); // (ABCD) -> (ADDA)
            let c1 = u32x8::new(4,1,6,3,4,1,6,3); // (ABCD) -> (CBBC)

            for i in 0..5 {
                t0.0[i] = _mm256_permutevar8x32_epi32(Q.0[i], c0);
                t1.0[i] = _mm256_permutevar8x32_epi32(Q.0[i], c1);
            }
            //println!("t0 = (S11 S13 S13 S11)");
            //println!("t0 = {:?}\n", t0.split());
            //println!("t1 = (S12 S14 S14 S12)");
            //println!("t1 = {:?}\n", t1.split());

            ExtendedPoint(&t0 * &t1)
        }
    }
}
    
