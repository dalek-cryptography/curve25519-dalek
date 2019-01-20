// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! This module contains backend-specific constant values, such as the 64-bit limbs of curve constants.

use backend::serial::u64::field::FieldElement51;
use backend::serial::u64::scalar::Scalar52;
use edwards::EdwardsPoint;

/// Edwards `d` value, equal to `-121665/121666 mod p`.
pub(crate) const EDWARDS_D: FieldElement51 = FieldElement51([929955233495203, 466365720129213, 1662059464998953, 2033849074728123, 1442794654840575]);

/// Edwards `2*d` value, equal to `2*(-121665/121666) mod p`.
pub(crate) const EDWARDS_D2: FieldElement51 = FieldElement51([1859910466990425, 932731440258426, 1072319116312658, 1815898335770999, 633789495995903]);

/// `= sqrt(a*d - 1)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const SQRT_AD_MINUS_ONE: FieldElement51 = FieldElement51([
    2241493124984347, 425987919032274, 2207028919301688, 1220490630685848, 974799131293748
]);

/// `= 1/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const INVSQRT_A_MINUS_D: FieldElement51 = FieldElement51([
    278908739862762, 821645201101625, 8113234426968, 1777959178193151, 2118520810568447
]);

/// Precomputed value of one of the square roots of -1 (mod p)
pub(crate) const SQRT_M1: FieldElement51 = FieldElement51([1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133]);

/// `APLUS2_OVER_FOUR` is (A+2)/4. (This is used internally within the Montgomery ladder.)
pub(crate) const APLUS2_OVER_FOUR: FieldElement51 = FieldElement51([121666, 0, 0, 0, 0]);

/// `L` is the order of base point, i.e. 2^252 + 27742317777372353535851937790883648493
pub(crate) const L: Scalar52 = Scalar52([ 0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0x0000000000000000, 0x0000100000000000 ]);

/// `L` * `LFACTOR` = -1 (mod 2^52)
pub(crate) const LFACTOR: u64 = 0x51da312547e1b;

/// `R` = R % L where R = 2^260
pub(crate) const R: Scalar52 = Scalar52([ 0x000f48bd6721e6ed, 0x0003bab5ac67e45a, 0x000fffffeb35e51b, 0x000fffffffffffff, 0x00000fffffffffff ]);

/// `RR` = (R^2) % L where R = 2^260
pub(crate) const RR: Scalar52 = Scalar52([ 0x0009d265e952d13b, 0x000d63c715bea69f, 0x0005be65cb687604, 0x0003dceec73d217f, 0x000009411b7c309a ]);

/// The Ed25519 basepoint, as an `EdwardsPoint`.
///
/// This is called `_POINT` to distinguish it from
/// `ED25519_BASEPOINT_TABLE`, which should be used for scalar
/// multiplication (it's much faster).
pub const ED25519_BASEPOINT_POINT: EdwardsPoint = EdwardsPoint{
    X: FieldElement51([1738742601995546, 1146398526822698, 2070867633025821, 562264141797630, 587772402128613]),
    Y: FieldElement51([1801439850948184, 1351079888211148, 450359962737049, 900719925474099, 1801439850948198]),
    Z: FieldElement51([1, 0, 0, 0, 0]),
    T: FieldElement51([1841354044333475, 16398895984059, 755974180946558, 900171276175154, 1821297809914039]),
};

/// The 8-torsion subgroup \\(\mathcal E [8]\\).
///
/// In the case of Curve25519, it is cyclic; the \\(i\\)-th element of
/// the array is \\([i]P\\), where \\(P\\) is a point of order \\(8\\)
/// generating \\(\mathcal E[8]\\).
///
/// Thus \\(\mathcal E[8]\\) is the points indexed by `0,2,4,6`, and
/// \\(\mathcal E[2]\\) is the points indexed by `0,4`.
pub const EIGHT_TORSION: [EdwardsPoint; 8] = EIGHT_TORSION_INNER_DOC_HIDDEN;

/// Inner item used to hide limb constants from cargo doc output.
#[doc(hidden)]
pub const EIGHT_TORSION_INNER_DOC_HIDDEN: [EdwardsPoint; 8] = [
    EdwardsPoint {
        X: FieldElement51([0, 0, 0, 0, 0]),
        Y: FieldElement51([1, 0, 0, 0, 0]),
        Z: FieldElement51([1, 0, 0, 0, 0]),
        T: FieldElement51([0, 0, 0, 0, 0]),
    }
    ,
    EdwardsPoint {
        X: FieldElement51([358744748052810, 1691584618240980, 977650209285361, 1429865912637724, 560044844278676]),
        Y: FieldElement51([84926274344903, 473620666599931, 365590438845504, 1028470286882429, 2146499180330972]),
        Z: FieldElement51([1, 0, 0, 0, 0]),
        T: FieldElement51([1448326834587521, 1857896831960481, 1093722731865333, 1677408490711241, 1915505153018406]),
    }
    ,
    EdwardsPoint {
        X: FieldElement51([533094393274173, 2016890930128738, 18285341111199, 134597186663265, 1486323764102114]),
        Y: FieldElement51([0, 0, 0, 0, 0]),
        Z: FieldElement51([1, 0, 0, 0, 0]),
        T: FieldElement51([0, 0, 0, 0, 0]),
    }
    ,
    EdwardsPoint {
        X: FieldElement51([358744748052810, 1691584618240980, 977650209285361, 1429865912637724, 560044844278676]),
        Y: FieldElement51([2166873539340326, 1778179147085316, 1886209374839743, 1223329526802818, 105300633354275]),
        Z: FieldElement51([1, 0, 0, 0, 0]),
        T: FieldElement51([803472979097708, 393902981724766, 1158077081819914, 574391322974006, 336294660666841]),
    }
    ,
    EdwardsPoint {
        X: FieldElement51([0, 0, 0, 0, 0]),
        Y: FieldElement51([2251799813685228, 2251799813685247, 2251799813685247, 2251799813685247, 2251799813685247]),
        Z: FieldElement51([1, 0, 0, 0, 0]),
        T: FieldElement51([0, 0, 0, 0, 0]),
    }
    ,
    EdwardsPoint {
        X: FieldElement51([1893055065632419, 560215195444267, 1274149604399886, 821933901047523, 1691754969406571]),
        Y: FieldElement51([2166873539340326, 1778179147085316, 1886209374839743, 1223329526802818, 105300633354275]),
        Z: FieldElement51([1, 0, 0, 0, 0]),
        T: FieldElement51([1448326834587521, 1857896831960481, 1093722731865333, 1677408490711241, 1915505153018406]),
    }
    ,
    EdwardsPoint {
        X: FieldElement51([1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133]),
        Y: FieldElement51([0, 0, 0, 0, 0]),
        Z: FieldElement51([1, 0, 0, 0, 0]),
        T: FieldElement51([0, 0, 0, 0, 0]),
    }
    ,
    EdwardsPoint {
        X: FieldElement51([1893055065632419, 560215195444267, 1274149604399886, 821933901047523, 1691754969406571]),
        Y: FieldElement51([84926274344903, 473620666599931, 365590438845504, 1028470286882429, 2146499180330972]),
        Z: FieldElement51([1, 0, 0, 0, 0]),
        T: FieldElement51([803472979097708, 393902981724766, 1158077081819914, 574391322974006, 336294660666841]),
    }
];
