// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
//! Various constants, such as the Ristretto and Ed25519 basepoints.

#![allow(non_snake_case)]

use cfg_if::cfg_if;

use crate::edwards::CompressedEdwardsY;
use crate::montgomery::MontgomeryPoint;
use crate::ristretto::{CompressedRistretto, RistrettoPoint};
use crate::scalar::Scalar;

#[cfg(feature = "precomputed-tables")]
use crate::edwards::EdwardsBasepointTable;

cfg_if! {
    if #[cfg(curve25519_dalek_backend = "fiat")] {
        #[cfg(curve25519_dalek_bits = "32")]
        pub use crate::backend::serial::fiat_u32::constants::*;
        #[cfg(curve25519_dalek_bits = "64")]
        pub use crate::backend::serial::fiat_u64::constants::*;
    } else {
        #[cfg(curve25519_dalek_bits = "32")]
        pub use crate::backend::serial::u32::constants::*;
        #[cfg(curve25519_dalek_bits = "64")]
        pub use crate::backend::serial::u64::constants::*;
    }
}

/// The Ed25519 basepoint, in `CompressedEdwardsY` format.
///
/// This is the little-endian byte encoding of \\( 4/5 \pmod p \\),
/// which is the \\(y\\)-coordinate of the Ed25519 basepoint.
///
/// The sign bit is 0 since the basepoint has \\(x\\) chosen to be positive.
pub const ED25519_BASEPOINT_COMPRESSED: CompressedEdwardsY = CompressedEdwardsY([
    0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
]);

/// The X25519 basepoint, in `MontgomeryPoint` format.
pub const X25519_BASEPOINT: MontgomeryPoint = MontgomeryPoint([
    0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
]);

/// The Ristretto basepoint, in `CompressedRistretto` format.
pub const RISTRETTO_BASEPOINT_COMPRESSED: CompressedRistretto = CompressedRistretto([
    0xe2, 0xf2, 0xae, 0x0a, 0x6a, 0xbc, 0x4e, 0x71, 0xa8, 0x84, 0xa9, 0x61, 0xc5, 0x00, 0x51, 0x5f,
    0x58, 0xe3, 0x0b, 0x6a, 0xa5, 0x82, 0xdd, 0x8d, 0xb6, 0xa6, 0x59, 0x45, 0xe0, 0x8d, 0x2d, 0x76,
]);

/// The Ristretto basepoint, as a `RistrettoPoint`.
///
/// This is called `_POINT` to distinguish it from `_TABLE`, which
/// provides fast scalar multiplication.
pub const RISTRETTO_BASEPOINT_POINT: RistrettoPoint = RistrettoPoint(ED25519_BASEPOINT_POINT);

/// `BASEPOINT_ORDER` is the order of the Ristretto group and of the Ed25519 basepoint, i.e.,
/// $$
/// \ell = 2^\{252\} + 27742317777372353535851937790883648493.
/// $$
pub(crate) const BASEPOINT_ORDER: Scalar = Scalar {
    bytes: [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x10,
    ],
};

#[cfg(feature = "precomputed-tables")]
use crate::ristretto::RistrettoBasepointTable;

/// The Ristretto basepoint, as a `RistrettoBasepointTable` for scalar multiplication.
#[cfg(feature = "precomputed-tables")]
pub static RISTRETTO_BASEPOINT_TABLE: &RistrettoBasepointTable = unsafe {
    // SAFETY: `RistrettoBasepointTable` is a `#[repr(transparent)]` newtype of
    // `EdwardsBasepointTable`
    &*(ED25519_BASEPOINT_TABLE as *const EdwardsBasepointTable as *const RistrettoBasepointTable)
};

/// X25519 low order points.
///
/// The output of any scalar multiplied by these points is zero. Protocols which need to ensure
/// "contributory" behavior should reject these points.
///
/// Table adapted from <https://cr.yp.to/ecdh.html>.
#[rustfmt::skip]
pub static X25519_LOW_ORDER_POINTS: [MontgomeryPoint; 7] = [
    // 0 (order 4)
    MontgomeryPoint([0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),

    // 1 (order 1)
    MontgomeryPoint([0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),

    // 325606250916557431795983626356110631294008115727848805560023387167927233504 (order 8)
    MontgomeryPoint([0xe0, 0xeb, 0x7a, 0x7c, 0x3b, 0x41, 0xb8, 0xae, 0x16, 0x56, 0xe3, 0xfa, 0xf1, 0x9f, 0xc4, 0x6a, 0xda, 0x09, 0x8d, 0xeb, 0x9c, 0x32, 0xb1, 0xfd, 0x86, 0x62, 0x05, 0x16, 0x5f, 0x49, 0xb8, 0x00]),

    // 39382357235489614581723060781553021112529911719440698176882885853963445705823 (order 8)
    MontgomeryPoint([0x5f, 0x9c, 0x95, 0xbc, 0xa3, 0x50, 0x8c, 0x24, 0xb1, 0xd0, 0xb1, 0x55, 0x9c, 0x83, 0xef, 0x5b, 0x04, 0x44, 0x5c, 0xc4, 0x58, 0x1c, 0x8e, 0x86, 0xd8, 0x22, 0x4e, 0xdd, 0xd0, 0x9f, 0x11, 0x57]),

    // p - 1 (order 2)
    MontgomeryPoint([0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),

    // p (order 4)
    MontgomeryPoint([0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),

    // p + 1 (order 1)
    MontgomeryPoint([0xee, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f])
];

#[cfg(test)]
mod test {
    use crate::constants;
    use crate::field::FieldElement;
    use crate::montgomery::MontgomeryPoint;
    use crate::traits::{IsIdentity, ValidityCheck};

    #[test]
    fn test_eight_torsion() {
        for i in 0..8 {
            let Q = constants::EIGHT_TORSION[i].mul_by_pow_2(3);
            assert!(Q.is_valid());
            assert!(Q.is_identity());
        }
    }

    #[test]
    fn test_four_torsion() {
        for i in (0..8).filter(|i| i % 2 == 0) {
            let Q = constants::EIGHT_TORSION[i].mul_by_pow_2(2);
            assert!(Q.is_valid());
            assert!(Q.is_identity());
        }
    }

    #[test]
    fn test_two_torsion() {
        for i in (0..8).filter(|i| i % 4 == 0) {
            let Q = constants::EIGHT_TORSION[i].mul_by_pow_2(1);
            assert!(Q.is_valid());
            assert!(Q.is_identity());
        }
    }

    /// Test that SQRT_M1 is the positive square root of -1
    #[test]
    fn test_sqrt_minus_one() {
        let minus_one = FieldElement::MINUS_ONE;
        let sqrt_m1_sq = &constants::SQRT_M1 * &constants::SQRT_M1;
        assert_eq!(minus_one, sqrt_m1_sq);
        assert!(bool::from(!constants::SQRT_M1.is_negative()));
    }

    #[test]
    fn test_sqrt_constants_sign() {
        let minus_one = FieldElement::MINUS_ONE;
        let (was_nonzero_square, invsqrt_m1) = minus_one.invsqrt();
        assert!(bool::from(was_nonzero_square));
        let sign_test_sqrt = &invsqrt_m1 * &constants::SQRT_M1;
        assert_eq!(sign_test_sqrt, minus_one);
    }

    /// Test that d = -121665/121666
    #[test]
    #[cfg(all(curve25519_dalek_bits = "32", not(curve25519_dalek_backend = "fiat")))]
    fn test_d_vs_ratio() {
        use crate::backend::serial::u32::field::FieldElement2625;
        let a = -&FieldElement2625([121665, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        let b = FieldElement2625([121666, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        let d = &a * &b.invert();
        let d2 = &d + &d;
        assert_eq!(d, constants::EDWARDS_D);
        assert_eq!(d2, constants::EDWARDS_D2);
    }

    /// Test that d = -121665/121666
    #[test]
    #[cfg(all(curve25519_dalek_bits = "64", not(curve25519_dalek_backend = "fiat")))]
    fn test_d_vs_ratio() {
        use crate::backend::serial::u64::field::FieldElement51;
        let a = -&FieldElement51([121665, 0, 0, 0, 0]);
        let b = FieldElement51([121666, 0, 0, 0, 0]);
        let d = &a * &b.invert();
        let d2 = &d + &d;
        assert_eq!(d, constants::EDWARDS_D);
        assert_eq!(d2, constants::EDWARDS_D2);
    }

    #[test]
    fn test_sqrt_ad_minus_one() {
        let a = FieldElement::MINUS_ONE;
        let ad_minus_one = &(&a * &constants::EDWARDS_D) + &a;
        let should_be_ad_minus_one = constants::SQRT_AD_MINUS_ONE.square();
        assert_eq!(should_be_ad_minus_one, ad_minus_one);
    }

    #[test]
    fn low_order_point_scalar_mul() {
        // Example scalar from RFC7748 § 5.2
        let scalar = [
            0xa5, 0x46, 0xe3, 0x6b, 0xf0, 0x52, 0x7c, 0x9d, 0x3b, 0x16, 0x15, 0x4b, 0x82, 0x46,
            0x5e, 0xdd, 0x62, 0x14, 0x4c, 0x0a, 0xc1, 0xfc, 0x5a, 0x18, 0x50, 0x6a, 0x22, 0x44,
            0xba, 0x44, 0x9a, 0xc4,
        ];

        for low_order_point in constants::X25519_LOW_ORDER_POINTS {
            let output = low_order_point.mul_clamped(scalar);
            assert_eq!(output, MontgomeryPoint([0; 32]));
        }
    }

    /// Test that ED25519_SQRTAM2 squared is MONTGOMERY_A_NEG - 2
    #[test]
    #[cfg(feature = "digest")]
    fn test_sqrt_a_minus_2() {
        let one = FieldElement::ONE;
        let a_minus_two = &(&constants::MONTGOMERY_A_NEG - &one) - &one;

        assert_eq!(constants::ED25519_SQRTAM2.square(), a_minus_two)
    }
}
