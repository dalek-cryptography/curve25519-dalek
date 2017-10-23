// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! This module contains various constants (such as curve parameters
//! and useful field elements like `sqrt(-1)`), as well as
//! lookup tables of pre-computed points.

#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(missing_docs)]
#![allow(non_snake_case)]

use edwards::CompressedEdwardsY;
use ristretto::{RistrettoPoint, RistrettoBasepointTable};
use montgomery::CompressedMontgomeryU;
use scalar::Scalar;

#[cfg(feature="radix_51")]
pub use constants_64bit::*;
#[cfg(not(feature="radix_51"))]
pub use constants_32bit::*;

/// (p-1)/2, in little-endian bytes.
pub const HALF_P_MINUS_1_BYTES: [u8; 32] =
    [0xf6, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f];

/// `HALF_Q_MINUS_1_BYTES` is (2^255-20)/2 expressed in little endian form.
pub const HALF_Q_MINUS_1_BYTES: [u8; 32] = [ // halfQMinus1Bytes
    0xf6, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f, ];

/// Basepoint has y = 4/5.
///
/// Generated with Sage: these are the bytes of 4/5 in 𝔽_p.  The
/// sign bit is 0 since the basepoint has x chosen to be positive.
pub const BASE_CMPRSSD: CompressedEdwardsY =
    CompressedEdwardsY([0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
                        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
                        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
                        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66]);

/// The X25519 basepoint, in compressed Montgomery form.
pub const BASE_COMPRESSED_MONTGOMERY: CompressedMontgomeryU =
    CompressedMontgomeryU([0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                           0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                           0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                           0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);


/// The Ed25519 basepoint, as a `RistrettoPoint`.  This is called `_POINT` to distinguish it from
/// `_TABLE`, which provides fast scalar multiplication.
pub const RISTRETTO_BASEPOINT_POINT: RistrettoPoint = RistrettoPoint(ED25519_BASEPOINT_POINT);

/// `l` is the order of base point, i.e. 2^252 +
/// 27742317777372353535851937790883648493, in little-endian form
pub const l: Scalar = Scalar([ 0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
                               0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
                               0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                               0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 ]);

/// `l_minus_1` is the order of base point minus one, i.e. 2^252 +
/// 27742317777372353535851937790883648493 - 1, in little-endian form
pub const l_minus_1: Scalar = Scalar([ 0xec, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
                                       0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
                                       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 ]);

/// `lminus1` is the order of base point minus two, i.e. 2^252 +
/// 27742317777372353535851937790883648493 - 2, in little-endian form
pub const l_minus_2: Scalar = Scalar([ 0xeb, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
                                       0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
                                       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 ]);

/// The Ed25519 basepoint, as a RistrettoPoint
pub const RISTRETTO_BASEPOINT_TABLE: RistrettoBasepointTable
    = RistrettoBasepointTable(ED25519_BASEPOINT_TABLE);

#[cfg(test)]
mod test {
    use field::FieldElement;
    use edwards::IsIdentity;
    use edwards::ValidityCheck;
    use constants;

    #[test]
    fn test_eight_torsion() {
        for i in 0..8 {
            let Q = constants::EIGHT_TORSION[i].mult_by_pow_2(3);
            assert!(Q.is_valid());
            assert!(Q.is_identity());
        }
    }

    #[test]
    fn test_four_torsion() {
        for i in (0..8).filter(|i| i % 2 == 0) {
            let Q = constants::EIGHT_TORSION[i].mult_by_pow_2(2);
            assert!(Q.is_valid());
            assert!(Q.is_identity());
        }
    }

    #[test]
    fn test_two_torsion() {
        for i in (0..8).filter(|i| i % 4 == 0) {
            let Q = constants::EIGHT_TORSION[i].mult_by_pow_2(1);
            assert!(Q.is_valid());
            assert!(Q.is_identity());
        }
    }

    #[test]
    fn test_half() {
        let one = FieldElement::one();
        let two = &one + &one;
        assert_eq!(one, &two * &constants::HALF);
    }

    /// Test that the constant for sqrt(-486664) really is a square
    /// root of -486664.
    #[test]
    #[cfg(feature="radix_51")]
    fn sqrt_minus_aplus2() {
        use field_64bit::FieldElement64;
        let minus_aplus2 = -&FieldElement64([486664,0,0,0,0]);
        let sqrt = constants::SQRT_MINUS_APLUS2;
        let sq = &sqrt * &sqrt;
        assert_eq!(sq, minus_aplus2);
    }

    /// Test that the constant for sqrt(-486664) really is a square
    /// root of -486664.
    #[test]
    #[cfg(not(feature="radix_51"))]
    fn sqrt_minus_aplus2() {
        use field_32bit::FieldElement32;
        let minus_aplus2 = FieldElement32([-486664,0,0,0,0,0,0,0,0,0]);
        let sqrt = constants::SQRT_MINUS_APLUS2;
        let sq = &sqrt * &sqrt;
        assert_eq!(sq, minus_aplus2);
    }

    #[test]
    /// Test that SQRT_M1 and MSQRT_M1 are square roots of -1
    fn test_sqrt_minus_one() {
        let minus_one = FieldElement::minus_one();
        let sqrt_m1_sq = &constants::SQRT_M1 * &constants::SQRT_M1;
        let msqrt_m1_sq = &constants::MSQRT_M1 * &constants::MSQRT_M1;
        assert_eq!(minus_one,  sqrt_m1_sq);
        assert_eq!(minus_one, msqrt_m1_sq);
    }

    #[test]
    fn test_sqrt_constants_sign() {
        let one       = FieldElement::one();
        let minus_one = FieldElement::minus_one();
        let (was_nonzero_square, invsqrt_m1) = minus_one.invsqrt();
        assert_eq!(was_nonzero_square, 1u8);
        let sign_test_sqrt  = &invsqrt_m1 * &constants::SQRT_M1;
        let sign_test_msqrt = &invsqrt_m1 * &constants::MSQRT_M1;
        // XXX it seems we have flipped the sign relative to
        // the invsqrt function?
        assert_eq!(sign_test_sqrt, minus_one);
        assert_eq!(sign_test_msqrt, one);
    }

    /// Test that d = -121665/121666
    #[cfg(not(feature="radix_51"))]
    #[test]
    fn test_d_vs_ratio() {
        use field_32bit::FieldElement32;
        let a = FieldElement32([-121665,0,0,0,0,0,0,0,0,0]);
        let b = FieldElement32([ 121666,0,0,0,0,0,0,0,0,0]);
        let d = &a * &b.invert();
        let d2 = &d + &d;
        assert_eq!(d, constants::d);
        assert_eq!(d2, constants::d2);
    }

    /// Test that d = -121665/121666
    #[cfg(feature="radix_51")]
    #[test]
    fn test_d_vs_ratio() {
        use field_64bit::FieldElement64;
        let a = -&FieldElement64([121665,0,0,0,0]);
        let b =   FieldElement64([121666,0,0,0,0]);
        let d = &a * &b.invert();
        let d2 = &d + &d;
        assert_eq!(d, constants::d);
        assert_eq!(d2, constants::d2);
    }

    #[test]
    fn test_d4() {
        let mut four = FieldElement::zero();
        // XXX should have a way to create small field elements
        four.0[0] = 4;
        assert_eq!(&constants::d * &four, constants::d4);
    }

    #[test]
    fn test_sqrt_ad_minus_one() {
        let a = FieldElement::minus_one();
        let ad_minus_one = &(&a * &constants::d) + &a;
        let should_be_ad_minus_one = constants::sqrt_ad_minus_one.square();
        assert_eq!(should_be_ad_minus_one, ad_minus_one);
    }

    #[test]
    fn test_a_minus_d() {
        let a = FieldElement::minus_one();
        let a_minus_d = &a - &constants::d;
        assert_eq!(a_minus_d, constants::a_minus_d);
        let (_, invsqrt_a_minus_d) = constants::a_minus_d.invsqrt();
        assert_eq!(invsqrt_a_minus_d, constants::invsqrt_a_minus_d);
        let inv_a_minus_d = invsqrt_a_minus_d.square();
        assert_eq!(inv_a_minus_d, constants::inv_a_minus_d);
        assert_eq!(&inv_a_minus_d * &a_minus_d, FieldElement::one());
    }
}
