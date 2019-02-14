// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! This module contains various constants (such as curve parameters
//! and useful field elements like `sqrt(-1)`), as well as
//! lookup tables of pre-computed points.

use backend::serial::u32::field::FieldElement2625;
use backend::serial::u32::scalar::Scalar29;
use edwards::EdwardsPoint;

/// Edwards `d` value, equal to `-121665/121666 mod p`.
pub(crate) const EDWARDS_D: FieldElement2625       = FieldElement2625([
    56195235, 13857412, 51736253,  6949390,   114729,
    24766616, 60832955, 30306712, 48412415, 21499315,
]);

/// Edwards `2*d` value, equal to `2*(-121665/121666) mod p`.
pub(crate) const EDWARDS_D2: FieldElement2625      = FieldElement2625([
    45281625, 27714825, 36363642, 13898781,  229458,
    15978800, 54557047, 27058993, 29715967, 9444199,
]);

/// `= sqrt(a*d - 1)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const SQRT_AD_MINUS_ONE: FieldElement2625 = FieldElement2625([
    24849947, 33400850, 43495378,  6347714, 46036536,
    32887293, 41837720, 18186727, 66238516, 14525638,
]);

/// `= 1/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const INVSQRT_A_MINUS_D: FieldElement2625 = FieldElement2625([
    6111466,  4156064, 39310137, 12243467, 41204824,
     120896, 20826367, 26493656,  6093567, 31568420,
]);

/// Precomputed value of one of the square roots of -1 (mod p)
pub(crate) const SQRT_M1: FieldElement2625 = FieldElement2625([
    34513072, 25610706,  9377949, 3500415, 12389472,
    33281959, 41962654, 31548777,  326685, 11406482,
]);

/// `APLUS2_OVER_FOUR` is (A+2)/4. (This is used internally within the Montgomery ladder.)
pub(crate) const APLUS2_OVER_FOUR: FieldElement2625 = FieldElement2625([
    121666, 0, 0, 0, 0, 0, 0, 0, 0, 0
]);

/// `L` is the order of base point, i.e. 2^252 +
/// 27742317777372353535851937790883648493
pub(crate) const L: Scalar29 = Scalar29([ 0x1cf5d3ed, 0x009318d2, 0x1de73596, 0x1df3bd45,
                                          0x0000014d, 0x00000000, 0x00000000, 0x00000000,
                                          0x00100000 ]);

/// `L` * `LFACTOR` = -1 (mod 2^29)
pub(crate) const LFACTOR: u32 = 0x12547e1b;

/// `R` = R % L where R = 2^261
pub(crate) const R: Scalar29 = Scalar29([ 0x114df9ed, 0x1a617303, 0x0f7c098c, 0x16793167,
                                          0x1ffd656e, 0x1fffffff, 0x1fffffff, 0x1fffffff,
                                          0x000fffff ]);

/// `RR` = (R^2) % L where R = 2^261
pub(crate) const RR: Scalar29 = Scalar29([ 0x0b5f9d12, 0x1e141b17, 0x158d7f3d, 0x143f3757,
                                           0x1972d781, 0x042feb7c, 0x1ceec73d, 0x1e184d1e,
                                           0x0005046d ]);

/// The Ed25519 basepoint, as an `EdwardsPoint`.
///
/// This is called `_POINT` to distinguish it from
/// `ED25519_BASEPOINT_TABLE`, which should be used for scalar
/// multiplication (it's much faster).
pub const ED25519_BASEPOINT_POINT: EdwardsPoint = EdwardsPoint{
    X: FieldElement2625([52811034, 25909283, 16144682, 17082669, 27570973, 30858332, 40966398, 8378388, 20764389, 8758491]),
    Y: FieldElement2625([40265304, 26843545, 13421772, 20132659, 26843545, 6710886, 53687091, 13421772, 40265318, 26843545]),
    Z: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    T: FieldElement2625([28827043, 27438313, 39759291, 244362, 8635006, 11264893, 19351346, 13413597, 16611511, 27139452]),
};

/// The 8-torsion subgroup \\(\mathcal E [8]\\).
///
/// In the case of Curve25519, it is cyclic; the \\(i\\)-th element of
/// the array is \\([i]P\\), where \\(P\\) is a point of order \\(8\\)
/// generating \\(\mathcal E[8]\\).
///
/// Thus \\(\mathcal E[8]\\) is the points indexed by `0,2,4,6`, and
/// \\(\mathcal E[2]\\) is the points indexed by `0,4`.
/// The Ed25519 basepoint has y = 4/5.  This is called `_POINT` to
/// distinguish it from `_TABLE`, which should be used for scalar
/// multiplication (it's much faster).
pub const EIGHT_TORSION: [EdwardsPoint; 8] = EIGHT_TORSION_INNER_DOC_HIDDEN;

/// Inner item used to hide limb constants from cargo doc output.
#[doc(hidden)]
pub const EIGHT_TORSION_INNER_DOC_HIDDEN: [EdwardsPoint; 8] = [
    EdwardsPoint{
        X: FieldElement2625([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Y: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Z: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement2625([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    EdwardsPoint{
        X: FieldElement2625([21352778, 5345713, 4660180, 25206575, 24143089, 14568123, 30185756, 21306662, 33579924, 8345318]),
        Y: FieldElement2625([6952903, 1265500, 60246523, 7057497, 4037696, 5447722, 35427965, 15325401, 19365852, 31985330]),
        Z: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement2625([41846657, 21581751, 11716001, 27684820, 48915701, 16297738, 20670665, 24995334, 3541542, 28543251])
    },
    EdwardsPoint{
        X: FieldElement2625([32595773, 7943725, 57730914, 30054016, 54719391, 272472, 25146209, 2005654, 66782178, 22147949]),
        Y: FieldElement2625([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Z: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement2625([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    EdwardsPoint{
        X: FieldElement2625([21352778, 5345713, 4660180, 25206575, 24143089, 14568123, 30185756, 21306662, 33579924, 8345318]),
        Y: FieldElement2625([60155942, 32288931, 6862340, 26496934, 63071167, 28106709, 31680898, 18229030, 47743011, 1569101]),
        Z: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement2625([25262188, 11972680, 55392862, 5869611, 18193162, 17256693, 46438198, 8559097, 63567321, 5011180])
    },
    EdwardsPoint{
        X: FieldElement2625([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Y: FieldElement2625([67108844, 33554431, 67108863, 33554431, 67108863, 33554431, 67108863, 33554431, 67108863, 33554431]),
        Z: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement2625([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    EdwardsPoint{
        X: FieldElement2625([45756067, 28208718, 62448683, 8347856, 42965774, 18986308, 36923107, 12247769, 33528939, 25209113]),
        Y: FieldElement2625([60155942, 32288931, 6862340, 26496934, 63071167, 28106709, 31680898, 18229030, 47743011, 1569101]),
        Z: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement2625([41846657, 21581751, 11716001, 27684820, 48915701, 16297738, 20670665, 24995334, 3541542, 28543251])
    },
    EdwardsPoint{
        X: FieldElement2625([34513072, 25610706, 9377949, 3500415, 12389472, 33281959, 41962654, 31548777, 326685, 11406482]),
        Y: FieldElement2625([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Z: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement2625([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    EdwardsPoint{
        X: FieldElement2625([45756067, 28208718, 62448683, 8347856, 42965774, 18986308, 36923107, 12247769, 33528939, 25209113]),
        Y: FieldElement2625([6952903, 1265500, 60246523, 7057497, 4037696, 5447722, 35427965, 15325401, 19365852, 31985330]),
        Z: FieldElement2625([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement2625([25262188, 11972680, 55392862, 5869611, 18193162, 17256693, 46438198, 8559097, 63567321, 5011180])
    },
];
