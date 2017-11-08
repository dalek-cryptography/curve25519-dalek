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
            use stdsimd::vendor::_mm256_shuffle_epi32;

            let P: &FieldElement32x4 = &self.0;
            let Q: &FieldElement32x4 = &other.0;

            let mut t0 = FieldElement32x4::zero();
            let mut t1 = FieldElement32x4::zero();

            macro_rules! print_vec {
                ($x:ident) => {
                    let splits = $x.split();
                    println!("{}[0] = {:?}", stringify!($x), splits[0].to_bytes());
                    println!("{}[1] = {:?}", stringify!($x), splits[1].to_bytes());
                    println!("{}[2] = {:?}", stringify!($x), splits[2].to_bytes());
                    println!("{}[3] = {:?}", stringify!($x), splits[3].to_bytes());
                }
            }

            for i in 0..5 {
                t0.0[i] = _mm256_permute2x128_si256(P.0[i].into(), Q.0[i].into(), 32).into();
            }
            //println!("t0 = (X1, Y1, X2, Y2)");
            //print_vec!(t0);
            //println!("");

            t0.diff_sum();

            //println!("t0 = (S0 S1 S2 S3)");
            //print_vec!(t0);
            //println!("");

            for i in 0..5 {
                t1.0[i] = _mm256_blend_epi32(t0.0[i].into(), P.0[i].into(), 0b11110000).into();
                t0.0[i] = _mm256_permute2x128_si256(t0.0[i].into(), Q.0[i].into(), 49).into();
            }
            //println!("t0 = (S2 S3 Z2 T2)");
            //print_vec!(t0);
            //println!("");

            //println!("t1 = (S0 S1 Z1 T1)");
            //print_vec!(t1);
            //println!("");

            let mut t2 = &t0 * &t1;
            //println!("t2 = (S4 S5 S6 S7)");
            //print_vec!(t2);
            //println!("");
            
            t2.scale_by_curve_constants();
            //println!("t2 = (S8 S9 S10 S11)");
            //print_vec!(t2);
            //println!("");
            
            for i in 0..5 {
                let swapped = _mm256_shuffle_epi32(t2.0[i].into(), 0b10_11_00_01);
                t2.0[i] = _mm256_blend_epi32(t2.0[i].into(), swapped, 0b11110000).into();
            }
            //println!("t2 = (S8 S9 S11 S10)");
            //print_vec!(t2);
            //println!("");

            t2.diff_sum();
            //println!("t2 = (S12 S13 S14 S15)");
            //print_vec!(t2);
            //println!("");

            let c0 = u32x8::new(0,5,2,7,5,0,7,2); // (ABCD) -> (ADDA)
            let c1 = u32x8::new(4,1,6,3,4,1,6,3); // (ABCD) -> (CBCB)

            for i in 0..5 {
                t0.0[i] = _mm256_permutevar8x32_epi32(t2.0[i], c0);
                t1.0[i] = _mm256_permutevar8x32_epi32(t2.0[i], c1);
            }
            //println!("t0 = (S11 S13 S13 S11)");
            //print_vec!(t0);
            //println!("");

            //println!("t1 = (S12 S14 S14 S12)");
            //print_vec!(t1);
            //println!("");

            ExtendedPoint(&t0 * &t1)
        }
    }
}
    
#[cfg(test)]
mod test {
    use super::*;

    fn serial_add(P: edwards::ExtendedPoint, Q: edwards::ExtendedPoint) -> edwards::ExtendedPoint {
        use field_32bit::FieldElement32;

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

        let S8  =  &S4 *    &FieldElement32([  121666,0,0,0,0,0,0,0,0,0]);  // R5
        let S9  =  &S5 *    &FieldElement32([  121666,0,0,0,0,0,0,0,0,0]);  // R6
        let S10 =  &S6 *    &FieldElement32([2*121666,0,0,0,0,0,0,0,0,0]);  // R8
        let S11 =  &S7 * &(-&FieldElement32([2*121665,0,0,0,0,0,0,0,0,0])); // R7
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

        edwards::ExtendedPoint{X: X3, Y: Y3, Z: Z3, T: T3}
    }

    fn addition_test_helper(P: edwards::ExtendedPoint, Q: edwards::ExtendedPoint) {
        let R1: edwards::ExtendedPoint = serial_add(P.into(), Q.into()).into();
        let R2: edwards::ExtendedPoint = (&ExtendedPoint::from(P) + &ExtendedPoint::from(Q)).into();
        println!("Testing point addition:");
        println!("P = {:?}", P);
        println!("Q = {:?}", Q);
        println!("(serial) R1 = {:?}", R1);
        println!("(vector) R2 = {:?}", R2);
        println!("P + Q = {:?}", &P + &Q);
        assert_eq!(R1.compress(), (&P + &Q).compress());
        assert_eq!(R2.compress(), (&P + &Q).compress());
        println!("OK!\n");
    }

    #[test]
    fn addition_vs_serial_add_vs_edwards_extendedpoint() {
        use constants;
        use scalar::Scalar;
        use edwards::Identity;

        println!("Testing id + id");
        let P = edwards::ExtendedPoint::identity();
        let Q = edwards::ExtendedPoint::identity();
        addition_test_helper(P, Q);

        println!("Testing id + B");
        let P = edwards::ExtendedPoint::identity();
        let Q = constants::ED25519_BASEPOINT_POINT;
        addition_test_helper(P, Q);

        println!("Testing B + B");
        let P = constants::ED25519_BASEPOINT_POINT;
        let Q = constants::ED25519_BASEPOINT_POINT;
        addition_test_helper(P, Q);

        println!("Testing B + kB");
        let P = constants::ED25519_BASEPOINT_POINT;
        let Q = &constants::ED25519_BASEPOINT_TABLE * &Scalar::from_u64(8475983829);
        addition_test_helper(P, Q);
    }
}

#[cfg(all(test, feature = "bench"))]
mod bench {
    use test::Bencher;
    use super::*;

    use constants;
    use scalar::Scalar;

    #[bench]
    fn point_addition(b: &mut Bencher) {
        let B = &constants::ED25519_BASEPOINT_TABLE;
        let P = ExtendedPoint::from(B * &Scalar::from_u64(83973422));
        let Q = ExtendedPoint::from(B * &Scalar::from_u64(98932328));

        b.iter(|| &P + &Q );
    }
}

