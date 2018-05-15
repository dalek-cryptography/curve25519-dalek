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

use core::convert::From;
use core::ops::{Add, Sub, Neg};

use core::simd::{IntoBits, u32x8};

use subtle::ConditionallyAssignable;
use subtle::Choice;

use edwards;
use scalar_mul::window::{LookupTable, NafLookupTable5, NafLookupTable8};

use traits::Identity;

use backend::avx2::field::{D_LANES, Lanes, FieldElement32x4};

use backend::avx2;

/// A point on Curve25519, represented in an AVX2-friendly format.
#[derive(Copy, Clone, Debug)]
pub struct ExtendedPoint(pub(super) FieldElement32x4);

impl From<edwards::EdwardsPoint> for ExtendedPoint {
    fn from(P: edwards::EdwardsPoint) -> ExtendedPoint {
        ExtendedPoint(FieldElement32x4::new(&P.X, &P.Y, &P.Z, &P.T))
    }
}

impl From<ExtendedPoint> for edwards::EdwardsPoint {
    fn from(P: ExtendedPoint) -> edwards::EdwardsPoint {
        let tmp = P.0.split();
        edwards::EdwardsPoint{X: tmp[0], Y: tmp[1], Z: tmp[2], T: tmp[3]}
    }
}

impl ConditionallyAssignable for ExtendedPoint {
    fn conditional_assign(&mut self, other: &ExtendedPoint, choice: Choice) {
        self.0.conditional_assign(&other.0, choice);
    }
}

impl Default for ExtendedPoint {
    fn default() -> ExtendedPoint {
        ExtendedPoint::identity()
    }
}

impl Identity for ExtendedPoint {
    fn identity() -> ExtendedPoint {
        ExtendedPoint(FieldElement32x4([
            u32x8::new(0,1,0,0,1,0,0,0),
            u32x8::splat(0),
            u32x8::splat(0),
            u32x8::splat(0),
            u32x8::splat(0),
        ]))
    }
}

impl ExtendedPoint {
    pub fn double(&self) -> ExtendedPoint {
        unsafe {
            use core::arch::x86_64::_mm256_permute2x128_si256;
            use core::arch::x86_64::_mm256_permutevar8x32_epi32;
            use core::arch::x86_64::_mm256_blend_epi32;
            use core::arch::x86_64::_mm256_shuffle_epi32;

            let P = &self.0;

            let mut t0 = FieldElement32x4::zero();
            let mut t1 = FieldElement32x4::zero();

            // Want to compute (X1 Y1 Z1 X1+Y1).
            // Not sure how to do this less expensively than computing
            // (X1 Y1 Z1 T1) --(256bit shuffle)--> (X1 Y1 X1 Y1)
            // (X1 Y1 X1 Y1) --(2x128b shuffle)--> (Y1 X1 Y1 X1)
            // and then adding.

            // Set t0 = (X1 Y1 X1 Y1)
            t0.0[0] = _mm256_permute2x128_si256(P.0[0].into_bits(), P.0[0].into_bits(), 0b0000_0000).into_bits();
            t0.0[1] = _mm256_permute2x128_si256(P.0[1].into_bits(), P.0[1].into_bits(), 0b0000_0000).into_bits();
            t0.0[2] = _mm256_permute2x128_si256(P.0[2].into_bits(), P.0[2].into_bits(), 0b0000_0000).into_bits();
            t0.0[3] = _mm256_permute2x128_si256(P.0[3].into_bits(), P.0[3].into_bits(), 0b0000_0000).into_bits();
            t0.0[4] = _mm256_permute2x128_si256(P.0[4].into_bits(), P.0[4].into_bits(), 0b0000_0000).into_bits();

            // Set t1 = (Y1 X1 Y1 X1)
            t1.0[0] = _mm256_shuffle_epi32(t0.0[0].into_bits(), 0b10_11_00_01).into_bits();
            t1.0[1] = _mm256_shuffle_epi32(t0.0[1].into_bits(), 0b10_11_00_01).into_bits();
            t1.0[2] = _mm256_shuffle_epi32(t0.0[2].into_bits(), 0b10_11_00_01).into_bits();
            t1.0[3] = _mm256_shuffle_epi32(t0.0[3].into_bits(), 0b10_11_00_01).into_bits();
            t1.0[4] = _mm256_shuffle_epi32(t0.0[4].into_bits(), 0b10_11_00_01).into_bits();

            // Set t0 = (X1+Y1 X1+Y1 X1+Y1 X1+Y1)
            t0.0[0] = t0.0[0] + t1.0[0];
            t0.0[1] = t0.0[1] + t1.0[1];
            t0.0[2] = t0.0[2] + t1.0[2];
            t0.0[3] = t0.0[3] + t1.0[3];
            t0.0[4] = t0.0[4] + t1.0[4];

            // Set t0 = (X1 Y1 Z1 X1+Y1)
            // why does this intrinsic take an i32 for the imm8 ???
            t0.0[0] = _mm256_blend_epi32(P.0[0].into_bits(), t0.0[0].into_bits(), D_LANES as i32).into_bits();
            t0.0[1] = _mm256_blend_epi32(P.0[1].into_bits(), t0.0[1].into_bits(), D_LANES as i32).into_bits();
            t0.0[2] = _mm256_blend_epi32(P.0[2].into_bits(), t0.0[2].into_bits(), D_LANES as i32).into_bits();
            t0.0[3] = _mm256_blend_epi32(P.0[3].into_bits(), t0.0[3].into_bits(), D_LANES as i32).into_bits();
            t0.0[4] = _mm256_blend_epi32(P.0[4].into_bits(), t0.0[4].into_bits(), D_LANES as i32).into_bits();

            // Set t1 = t0^2, negating the D values
            t1 = t0.square_and_negate_D();

            // Now t1 = (S1 S2 S3 -S4)

            let c0 = u32x8::new(0,0,2,2,0,0,2,2).into_bits(); // (ABCD) -> (AAAA)
            let c1 = u32x8::new(1,1,3,3,1,1,3,3).into_bits(); // (ABCD) -> (BBBB)

            // See discussion of bounds in the module-level documentation.
            //
            // We want to compute
            //
            //    + | S1 | S1 | S1 | S1 |
            //    + | S2 |    |    | S2 |
            //    + |    |    | S3 |    |
            //    + |    |    | S3 |    |
            //    + |    |    |    |-S4 |
            //    + |    | 2p | 2p |    |
            //    - |    | S2 | S2 |    |
            //    =======================
            //        S5   S6   S8   S9
            //
            for i in 0..5 {
                let zero = u32x8::splat(0).into_bits();
                let S1: u32x8 = _mm256_permutevar8x32_epi32(t1.0[i].into_bits(), c0).into_bits();
                let S2: u32x8 = _mm256_permutevar8x32_epi32(t1.0[i].into_bits(), c1).into_bits();
                let S3_2: u32x8 = _mm256_blend_epi32(zero, (t1.0[i] + t1.0[i]).into_bits(), 0b01010000).into_bits();
                // tmp0 = (0 0 2*S3 -S4)
                let tmp0: u32x8 = _mm256_blend_epi32(S3_2.into_bits(), t1.0[i].into_bits(), 0b10100000).into_bits();
                t0.0[i] = (avx2::constants::P_TIMES_2_MASKED.0[i] + tmp0) + S1;
                let S2_pos: u32x8 = _mm256_blend_epi32(zero, S2.into_bits(), 0b10100101).into_bits();
                let S2_neg: u32x8 = _mm256_blend_epi32(S2.into_bits(), zero, 0b10100101).into_bits();
                t0.0[i] = t0.0[i] + S2_pos;
                t0.0[i] = t0.0[i] - S2_neg;
            }

            let c0 = u32x8::new(4,0,6,2,4,0,6,2).into_bits(); // (ABCD) -> (CACA)
            let c1 = u32x8::new(5,1,7,3,1,5,3,7).into_bits(); // (ABCD) -> (DBBD)

            for i in 0..5 {
                let tmp = t0.0[i];
                t0.0[i] = _mm256_permutevar8x32_epi32(tmp.into_bits(), c0).into_bits();
                t1.0[i] = _mm256_permutevar8x32_epi32(tmp.into_bits(), c1).into_bits();
            }

            ExtendedPoint(&t0 * &t1)
        }
    }

    pub fn mul_by_pow_2(&self, k: u32) -> ExtendedPoint {
        let mut tmp: ExtendedPoint = *self;
        for _ in 0..k {
            tmp = tmp.double();
        }
        tmp
    }
}

/// A cached point with some precomputed variables used for readdition.
#[derive(Copy, Clone, Debug)]
pub struct CachedPoint(pub(super) FieldElement32x4);

impl From<ExtendedPoint> for CachedPoint {
    fn from(P: ExtendedPoint) -> CachedPoint {
        let mut x = P.0;

        // x = (S2 S3 Z2 T2)
        x.diff_sum(Lanes::AB);

        // x = (121666*S2 121666*S3 2*121666*Z2 2*121665*T2)
        x.scale_by_curve_constants();

        // x = (121666*S2 121666*S3 2*121666*Z2 -2*121665*T2)
        x.negate_D();

        CachedPoint(x)
    }
}

impl Default for CachedPoint {
    fn default() -> CachedPoint {
        CachedPoint::identity()
    }
}

impl Identity for CachedPoint {
    fn identity() -> CachedPoint {
        CachedPoint(FieldElement32x4([
            u32x8::new(121647, 121666, 0, 0, 243332, 67108845, 0, 33554431),
            u32x8::new(67108864, 0, 33554431, 0, 0, 67108863, 0, 33554431),
            u32x8::new(67108863, 0, 33554431, 0, 0, 67108863, 0, 33554431),
            u32x8::new(67108863, 0, 33554431, 0, 0, 67108863, 0, 33554431),
            u32x8::new(67108863, 0, 33554431, 0, 0, 67108863, 0, 33554431),
        ]))
    }
}

impl ConditionallyAssignable for CachedPoint {
    fn conditional_assign(&mut self, other: &CachedPoint, choice: Choice) {
        self.0.conditional_assign(&other.0, choice);
    }
}

impl<'a> Neg for &'a CachedPoint {
    type Output = CachedPoint;

    fn neg(self) -> CachedPoint {
        let mut neg = *self;
        neg.0.swap_AB();
        neg.0.negate_D_lazy();
        neg
    }
}

impl<'a, 'b> Add<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;
    fn add(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        self + &CachedPoint::from(*other)
    }
}

impl<'a, 'b> Add<&'b CachedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    /// Uses a slight tweak of the parallel unified formulas of HWCD'08
    fn add(self, other: &'b CachedPoint) -> ExtendedPoint {
        unsafe {
            use core::arch::x86_64::_mm256_permutevar8x32_epi32;

            let mut tmp = self.0;

            // tmp = (Y1-X1 Y1+X1 Z1 T1) = (S0 S1 Z1 T1)
            tmp.diff_sum(Lanes::AB);

            // tmp = (S0*S2' S1*S3' Z1*Z2' T1*T2') = (S8 S9 S10 S11)
            tmp = &tmp * &other.0;

            // tmp = (S8 S9 S11 S10)
            tmp.swap_CD();

            // tmp = (S9-S8 S9+S8 S10-S11 S10+S11) = (S12 S13 S14 S15)
            tmp.diff_sum(Lanes::ALL);

            let c0 = u32x8::new(0,5,2,7,5,0,7,2); // (ABCD) -> (ADDA)
            let c1 = u32x8::new(4,1,6,3,4,1,6,3); // (ABCD) -> (CBCB)

            // set t0 = (S12 S15 S15 S12)
            // set t1 = (S14 S13 S14 S13)
            let mut t0 = FieldElement32x4::zero();
            let mut t1 = FieldElement32x4::zero();
            for i in 0..5 {
                t0.0[i] = _mm256_permutevar8x32_epi32(tmp.0[i].into_bits(), c0.into_bits()).into_bits();
                t1.0[i] = _mm256_permutevar8x32_epi32(tmp.0[i].into_bits(), c1.into_bits()).into_bits();
            }

            // return (S12*S14 S15*S13 S15*S14 S12*S13) = (X3 Y3 Z3 T3)
            ExtendedPoint(&t0 * &t1)
        }
    }
}

impl<'a, 'b> Sub<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;
    fn sub(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        self - &CachedPoint::from(*other)
    }
}

impl<'a, 'b> Sub<&'b CachedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    /// Implement subtraction by negating the point and adding.
    ///
    /// Empirically, this seems about the same cost as a custom subtraction impl (maybe because the
    /// benefit is cancelled by increased code size?)
    fn sub(self, other: &'b CachedPoint) -> ExtendedPoint {
        self + &(-other)
    }
}

impl<'a> From<&'a edwards::EdwardsPoint> for LookupTable<CachedPoint> {
    fn from(point: &'a edwards::EdwardsPoint) -> Self {
        let P = ExtendedPoint::from(*point);
        let mut points = [CachedPoint::from(P); 8];
        for i in 0..7 {
            points[i+1] = (&P + &points[i]).into();
        }
        LookupTable(points)
    }
}

impl<'a> From<&'a edwards::EdwardsPoint> for NafLookupTable5<CachedPoint> {
    fn from(point: &'a edwards::EdwardsPoint) -> Self {
        let A = ExtendedPoint::from(*point);
        let mut Ai = [CachedPoint::from(A); 8];
        let A2 = A.double();
        for i in 0..7 {
            Ai[i + 1] = (&A2 + &Ai[i]).into();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        NafLookupTable5(Ai)
    }
}

impl<'a> From<&'a edwards::EdwardsPoint> for NafLookupTable8<CachedPoint> {
    fn from(point: &'a edwards::EdwardsPoint) -> Self {
        let A = ExtendedPoint::from(*point);
        let mut Ai = [CachedPoint::from(A); 64];
        let A2 = A.double();
        for i in 0..63 {
            Ai[i + 1] = (&A2 + &Ai[i]).into();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
        NafLookupTable8(Ai)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn serial_add(P: edwards::EdwardsPoint, Q: edwards::EdwardsPoint) -> edwards::EdwardsPoint {
        use backend::u64::field::FieldElement64;

        let (X1, Y1, Z1, T1) = (P.X, P.Y, P.Z, P.T);
        let (X2, Y2, Z2, T2) = (Q.X, Q.Y, Q.Z, Q.T);

        macro_rules! print_var {
            ($x:ident) => {
                println!("{} = {:?}", stringify!($x), $x.to_bytes());
            }
        }

        let S0  =  &Y1 - &X1; // R1
        let S1  =  &Y1 + &X1; // R3
        let S2  =  &Y2 - &X2; // R2
        let S3  =  &Y2 + &X2; // R4
        print_var!(S0);
        print_var!(S1);
        print_var!(S2);
        print_var!(S3);
        println!("");

        let S4  =  &S0 * &S2; // R5 = R1 * R2
        let S5  =  &S1 * &S3; // R6 = R3 * R4
        let S6  =  &Z1 * &Z2; // R8
        let S7  =  &T1 * &T2; // R7
        print_var!(S4);
        print_var!(S5);
        print_var!(S6);
        print_var!(S7);
        println!("");

        let S8  =  &S4 *    &FieldElement64([  121666,0,0,0,0]);  // R5
        let S9  =  &S5 *    &FieldElement64([  121666,0,0,0,0]);  // R6
        let S10 =  &S6 *    &FieldElement64([2*121666,0,0,0,0]);  // R8
        let S11 =  &S7 * &(-&FieldElement64([2*121665,0,0,0,0])); // R7
        print_var!(S8 );
        print_var!(S9 );
        print_var!(S10);
        print_var!(S11);
        println!("");

        let S12 =  &S9 - &S8;  // R1
        let S13 =  &S9 + &S8;  // R4
        let S14 = &S10 - &S11; // R2
        let S15 = &S10 + &S11; // R3
        print_var!(S12);
        print_var!(S13);
        print_var!(S14);
        print_var!(S15);
        println!("");

        let X3  = &S12 * &S14; // R1 * R2
        let Y3  = &S15 * &S13; // R3 * R4
        let Z3  = &S15 * &S14; // R2 * R3
        let T3  = &S12 * &S13; // R1 * R4

        edwards::EdwardsPoint{X: X3, Y: Y3, Z: Z3, T: T3}
    }

    fn addition_test_helper(P: edwards::EdwardsPoint, Q: edwards::EdwardsPoint) {
        // Test the serial implementation of the parallel addition formulas
        let R_serial: edwards::EdwardsPoint = serial_add(P.into(), Q.into()).into();

        // Test the vector implementation of the parallel readdition formulas
        let cached_Q = CachedPoint::from(ExtendedPoint::from(Q));
        let R_vector: edwards::EdwardsPoint = (&ExtendedPoint::from(P) + &cached_Q).into();
        let S_vector: edwards::EdwardsPoint = (&ExtendedPoint::from(P) - &cached_Q).into();

        println!("Testing point addition:");
        println!("P = {:?}", P);
        println!("Q = {:?}", Q);
        println!("cached Q = {:?}", cached_Q);
        println!("R = P + Q = {:?}", &P + &Q);
        println!("R_serial = {:?}", R_serial);
        println!("R_vector = {:?}", R_vector);
        println!("S = P - Q = {:?}", &P - &Q);
        println!("S_vector = {:?}", S_vector);
        assert_eq!(R_serial.compress(), (&P + &Q).compress());
        assert_eq!(R_vector.compress(), (&P + &Q).compress());
        assert_eq!(S_vector.compress(), (&P - &Q).compress());
        println!("OK!\n");
    }

    #[test]
    fn vector_addition_vs_serial_addition_vs_edwards_extendedpoint() {
        use constants;
        use scalar::Scalar;

        println!("Testing id +- id");
        let P = edwards::EdwardsPoint::identity();
        let Q = edwards::EdwardsPoint::identity();
        addition_test_helper(P, Q);

        println!("Testing id +- B");
        let P = edwards::EdwardsPoint::identity();
        let Q = constants::ED25519_BASEPOINT_POINT;
        addition_test_helper(P, Q);

        println!("Testing B +- B");
        let P = constants::ED25519_BASEPOINT_POINT;
        let Q = constants::ED25519_BASEPOINT_POINT;
        addition_test_helper(P, Q);

        println!("Testing B +- kB");
        let P = constants::ED25519_BASEPOINT_POINT;
        let Q = &constants::ED25519_BASEPOINT_TABLE * &Scalar::from_u64(8475983829);
        addition_test_helper(P, Q);
    }

    fn serial_double(P: edwards::EdwardsPoint) -> edwards::EdwardsPoint {
        let (X1, Y1, Z1, T1) = (P.X, P.Y, P.Z, P.T);

        macro_rules! print_var {
            ($x:ident) => {
                println!("{} = {:?}", stringify!($x), $x.to_bytes());
            }
        }

        let S0 = &X1 + &Y1;  // R1
        print_var!(S0);
        println!("");

        let S1 = X1.square();
        let S2 = Y1.square();
        let S3 = Z1.square();
        let S4 = S0.square();
        print_var!(S1);
        print_var!(S2);
        print_var!(S3);
        print_var!(S4);
        println!("");

        let S5 = &S1 + &S2;
        let S6 = &S1 - &S2;
        let S7 = &S3 + &S3;
        let S8 = &S7 + &S6;
        let S9 = &S5 - &S4;
        print_var!(S5);
        print_var!(S6);
        print_var!(S7);
        print_var!(S8);
        print_var!(S9);
        println!("");

        let X3 = &S8 * &S9;
        let Y3 = &S5 * &S6;
        let Z3 = &S8 * &S6;
        let T3 = &S5 * &S9;

        edwards::EdwardsPoint{X: X3, Y: Y3, Z: Z3, T: T3}
    }

    fn doubling_test_helper(P: edwards::EdwardsPoint) {
        let R1: edwards::EdwardsPoint = serial_double(P.into()).into();
        let R2: edwards::EdwardsPoint = ExtendedPoint::from(P).double().into();
        println!("Testing point doubling:");
        println!("P = {:?}", P);
        println!("(serial) R1 = {:?}", R1);
        println!("(vector) R2 = {:?}", R2);
        println!("P + P = {:?}", &P + &P);
        assert_eq!(R1.compress(), (&P + &P).compress());
        assert_eq!(R2.compress(), (&P + &P).compress());
        println!("OK!\n");
    }

    #[test]
    fn vector_doubling_vs_serial_doubling_vs_edwards_extendedpoint() {
        use constants;
        use scalar::Scalar;

        println!("Testing [2]id");
        let P = edwards::EdwardsPoint::identity();
        doubling_test_helper(P);

        println!("Testing [2]B");
        let P = constants::ED25519_BASEPOINT_POINT;
        doubling_test_helper(P);

        println!("Testing [2]([k]B)");
        let P = &constants::ED25519_BASEPOINT_TABLE * &Scalar::from_u64(8475983829);
        doubling_test_helper(P);
    }
}
