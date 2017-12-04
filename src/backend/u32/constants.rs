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

use backend::u32::field::FieldElement32;
use backend::u32::scalar::Scalar32;
use edwards::ExtendedPoint;

/// Edwards `d` value, equal to `-121665/121666 mod p`.
pub(crate) const EDWARDS_D: FieldElement32       = FieldElement32([
    56195235, 13857412, 51736253,  6949390,   114729,
    24766616, 60832955, 30306712, 48412415, 21499315,
]);

/// Edwards `2*d` value, equal to `2*(-121665/121666) mod p`.
pub(crate) const EDWARDS_D2: FieldElement32      = FieldElement32([
    45281625, 27714825, 36363642, 13898781,  229458,
    15978800, 54557047, 27058993, 29715967, 9444199,
]);

/// `= sqrt(a*d - 1)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const SQRT_AD_MINUS_ONE: FieldElement32 = FieldElement32([
    24849947, 33400850, 43495378,  6347714, 46036536,
    32887293, 41837720, 18186727, 66238516, 14525638,
]);

/// `= 1/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const INVSQRT_A_MINUS_D: FieldElement32 = FieldElement32([
    6111466,  4156064, 39310137, 12243467, 41204824,
     120896, 20826367, 26493656,  6093567, 31568420,
]);

/// Precomputed value of one of the square roots of -1 (mod p)
pub(crate) const SQRT_M1: FieldElement32 = FieldElement32([
    34513072, 25610706,  9377949, 3500415, 12389472,
    33281959, 41962654, 31548777,  326685, 11406482,
]);

/// In Montgomery form y² = x³+Ax²+x, Curve25519 has A=486662.
pub(crate) const MONTGOMERY_A: FieldElement32 = FieldElement32([
    486662, 0, 0, 0, 0, 0, 0, 0, 0, 0,
]);

/// `APLUS2_OVER_FOUR` is (A+2)/4. (This is used internally within the Montgomery ladder.)
pub(crate) const APLUS2_OVER_FOUR: FieldElement32 = FieldElement32([
    121666, 0, 0, 0, 0, 0, 0, 0, 0, 0
]);

/// `SQRT_MINUS_APLUS2` is sqrt(-486664)
pub(crate) const SQRT_MINUS_APLUS2: FieldElement32 = FieldElement32([
    54885894, 25242303, 55597453,  9067496, 51808079,
    33312638, 25456129, 14121551, 54921728,  3972023,
]);

/// `L` is the order of base point, i.e. 2^252 +
/// 27742317777372353535851937790883648493
pub(crate) const L: Scalar32 = Scalar32([ 0x1cf5d3ed, 0x009318d2, 0x1de73596, 0x1df3bd45,
                                          0x0000014d, 0x00000000, 0x00000000, 0x00000000,
                                          0x00100000 ]);

/// `L` * `LFACTOR` = -1 (mod 2^29)
pub(crate) const LFACTOR: u32 = 0x12547e1b;

/// `R` = R % L where R = 2^261
pub(crate) const R: Scalar32 = Scalar32([ 0x114df9ed, 0x1a617303, 0x0f7c098c, 0x16793167,
                                          0x1ffd656e, 0x1fffffff, 0x1fffffff, 0x1fffffff,
                                          0x000fffff ]);

/// `RR` = (R^2) % L where R = 2^261
pub(crate) const RR: Scalar32 = Scalar32([ 0x0b5f9d12, 0x1e141b17, 0x158d7f3d, 0x143f3757,
                                           0x1972d781, 0x042feb7c, 0x1ceec73d, 0x1e184d1e,
                                           0x0005046d ]);

/// The Ed25519 basepoint has y = 4/5.  This is called `_POINT` to
/// distinguish it from `_TABLE`, which should be used for scalar
/// multiplication (it's much faster).
pub const ED25519_BASEPOINT_POINT: ExtendedPoint = ExtendedPoint{
        X: FieldElement32([52811034, 25909283, 16144682, 17082669, 27570973, 30858332, 40966398, 8378388, 20764389, 8758491]),
        Y: FieldElement32([40265304, 26843545, 13421772, 20132659, 26843545, 6710886, 53687091, 13421772, 40265318, 26843545]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([28827043, 27438313, 39759291, 244362, 8635006, 11264893, 19351346, 13413597, 16611511, 27139452]),
};

/// The 8-torsion subgroup Ɛ[8].
///
/// In the case of Curve25519, it is cyclic; the `i`th element of the
/// array is `i*P`, where `P` is a point of order 8 generating Ɛ[8].
///
/// Thus Ɛ[4] is the points indexed by 0,2,4,6 and Ɛ[2] is the points
/// indexed by 0,4.
pub const EIGHT_TORSION: [ExtendedPoint; 8] = [
    ExtendedPoint{
        X: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Y: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    ExtendedPoint{
        X: FieldElement32([21352778, 5345713, 4660180, 25206575, 24143089, 14568123, 30185756, 21306662, 33579924, 8345318]),
        Y: FieldElement32([6952903, 1265500, 60246523, 7057497, 4037696, 5447722, 35427965, 15325401, 19365852, 31985330]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([41846657, 21581751, 11716001, 27684820, 48915701, 16297738, 20670665, 24995334, 3541542, 28543251])
    },
    ExtendedPoint{
        X: FieldElement32([32595773, 7943725, 57730914, 30054016, 54719391, 272472, 25146209, 2005654, 66782178, 22147949]),
        Y: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    ExtendedPoint{
        X: FieldElement32([21352778, 5345713, 4660180, 25206575, 24143089, 14568123, 30185756, 21306662, 33579924, 8345318]),
        Y: FieldElement32([60155942, 32288931, 6862340, 26496934, 63071167, 28106709, 31680898, 18229030, 47743011, 1569101]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([25262188, 11972680, 55392862, 5869611, 18193162, 17256693, 46438198, 8559097, 63567321, 5011180])
    },
    ExtendedPoint{
        X: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Y: FieldElement32([67108844, 33554431, 67108863, 33554431, 67108863, 33554431, 67108863, 33554431, 67108863, 33554431]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    ExtendedPoint{
        X: FieldElement32([45756067, 28208718, 62448683, 8347856, 42965774, 18986308, 36923107, 12247769, 33528939, 25209113]),
        Y: FieldElement32([60155942, 32288931, 6862340, 26496934, 63071167, 28106709, 31680898, 18229030, 47743011, 1569101]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([41846657, 21581751, 11716001, 27684820, 48915701, 16297738, 20670665, 24995334, 3541542, 28543251])
    },
    ExtendedPoint{
        X: FieldElement32([34513072, 25610706, 9377949, 3500415, 12389472, 33281959, 41962654, 31548777, 326685, 11406482]),
        Y: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    ExtendedPoint{
        X: FieldElement32([45756067, 28208718, 62448683, 8347856, 42965774, 18986308, 36923107, 12247769, 33528939, 25209113]),
        Y: FieldElement32([6952903, 1265500, 60246523, 7057497, 4037696, 5447722, 35427965, 15325401, 19365852, 31985330]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([25262188, 11972680, 55392862, 5869611, 18193162, 17256693, 46438198, 8559097, 63567321, 5011180])
    },
];
