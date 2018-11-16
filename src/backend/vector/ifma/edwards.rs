// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2018 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Henry de Valence <hdevalence@hdevalence.ca>

use traits::Identity;

use std::ops::Add;

use edwards;

use super::field::{F51x4Reduced, F51x4Unreduced, Lanes, Shuffle};

#[derive(Copy, Clone, Debug)]
pub struct ExtendedPoint(pub(super) F51x4Unreduced);

#[derive(Copy, Clone, Debug)]
pub struct CachedPoint(pub(super) F51x4Reduced);

impl From<edwards::EdwardsPoint> for ExtendedPoint {
    fn from(P: edwards::EdwardsPoint) -> ExtendedPoint {
        ExtendedPoint(F51x4Unreduced::new(&P.X, &P.Y, &P.Z, &P.T))
    }
}

impl From<ExtendedPoint> for edwards::EdwardsPoint {
    fn from(P: ExtendedPoint) -> edwards::EdwardsPoint {
        let tmp = P.0.split();
        edwards::EdwardsPoint {
            X: tmp[0],
            Y: tmp[1],
            Z: tmp[2],
            T: tmp[3],
        }
    }
}

impl From<ExtendedPoint> for CachedPoint {
    fn from(P: ExtendedPoint) -> CachedPoint {
        let mut x = P.0;

        x = x.blend(&x.diff_sum(), Lanes::AB);
        x = &F51x4Reduced::from(x) * (121666, 121666, 2 * 121666, 2 * 121665);
        x = x.blend(&x.negate_lazy(), Lanes::D);

        CachedPoint(F51x4Reduced::from(x))
    }
}
    
impl<'a, 'b> Add<&'b CachedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    /// Add an `ExtendedPoint` and a `CachedPoint`.
    fn add(self, other: &'b CachedPoint) -> ExtendedPoint {
        let mut tmp = self.0;

        tmp = tmp.blend(&tmp.diff_sum(), Lanes::AB);
        // tmp = (Y1-X1 Y1+X1 Z1 T1) = (S0 S1 Z1 T1)

        tmp = &F51x4Reduced::from(tmp) * &other.0;
        // tmp = (S0*S2' S1*S3' Z1*Z2' T1*T2') = (S8 S9 S10 S11)

        tmp = tmp.shuffle(Shuffle::ABDC);
        // tmp = (S8 S9 S11 S10)

        let tmp = F51x4Reduced::from(tmp.diff_sum());
        // tmp = (S9-S8 S9+S8 S10-S11 S10+S11) = (S12 S13 S14 S15)

        let t0 = tmp.shuffle(Shuffle::ADDA);
        // t0 = (S12 S15 S15 S12)
        let t1 = tmp.shuffle(Shuffle::CBCB);
        // t1 = (S14 S13 S14 S13)

        // Return (S12*S14 S15*S13 S15*S14 S12*S13) = (X3 Y3 Z3 T3)
        ExtendedPoint(&t0 * &t1)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn addition_test_helper(P: edwards::EdwardsPoint, Q: edwards::EdwardsPoint) {
        // Test the serial implementation of the parallel addition formulas
        //let R_serial: edwards::EdwardsPoint = serial_add(P.into(), Q.into()).into();

        // Test the vector implementation of the parallel readdition formulas
        let cached_Q = CachedPoint::from(ExtendedPoint::from(Q));
        let R_vector: edwards::EdwardsPoint = (&ExtendedPoint::from(P) + &cached_Q).into();
         //et S_vector: edwards::EdwardsPoint = (&ExtendedPoint::from(P) - &cached_Q).into();

        println!("Testing point addition:");
        println!("P = {:?}", P);
        println!("Q = {:?}", Q);
        println!("cached Q = {:?}", cached_Q);
        println!("R = P + Q = {:?}", &P + &Q);
        //println!("R_serial = {:?}", R_serial);
        println!("R_vector = {:?}", R_vector);
        //println!("S = P - Q = {:?}", &P - &Q);
        //println!("S_vector = {:?}", S_vector);
        //assert_eq!(R_serial.compress(), (&P + &Q).compress());
        assert_eq!(R_vector.compress(), (&P + &Q).compress());
        //assert_eq!(S_vector.compress(), (&P - &Q).compress());
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
        let Q = &constants::ED25519_BASEPOINT_TABLE * &Scalar::from(8475983829u64);
        addition_test_helper(P, Q);
    }
}
