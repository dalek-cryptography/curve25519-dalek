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

use field_32bit::FieldElement32;
use scalar_32bit::Scalar32;
use edwards::ExtendedPoint;

/// Edwards `d` value, equal to `-121665/121666 mod p`.
pub(crate) const EDWARDS_D: FieldElement32       = FieldElement32([
    -10913610,  13857413, -15372611,   6949391,    114729,
    -8787816,   -6275908,  -3247719, -18696448, -12055116, ]);

/// Edwards `2*d` value, equal to `2*(-121665/121666) mod p`.
pub(crate) const EDWARDS_D2: FieldElement32      = FieldElement32([
    -21827239,  -5839606, -30745221,  13898782,    229458,
    15978800,  -12551817,  -6495438,  29715968,   9444199, ]);

/// `= sqrt(a*d - 1)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const SQRT_AD_MINUS_ONE: FieldElement32 = FieldElement32([
    24849947, -153582, -23613485, 6347715, -21072328, -667138, -25271143, -15367704, -870347, 14525639
]);

/// `= 1/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const INVSQRT_A_MINUS_D: FieldElement32 = FieldElement32([
    6111485, 4156064, -27798727, 12243468, -25904040,
    120897, 20826367, -7060776, 6093568, -1986012
]);

/// Precomputed value of one of the square roots of -1 (mod p)
pub(crate) const SQRT_M1: FieldElement32 = FieldElement32([
    -32595792,  -7943725,   9377950,   3500415,  12389472,
    -272473,   -25146209,  -2005654,    326686,  11406482, ]);

/// In Montgomery form y² = x³+Ax²+x, Curve25519 has A=486662.
pub(crate) const MONTGOMERY_A: FieldElement32       = FieldElement32([
    486662, 0, 0, 0, 0, 0, 0, 0, 0, 0, ]);

/// `APLUS2_OVER_FOUR` is (A+2)/4. (This is used internally within the Montgomery ladder.)
pub(crate) const APLUS2_OVER_FOUR: FieldElement32 = FieldElement32([121666, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

/// `SQRT_MINUS_APLUS2` is sqrt(-486664)
pub(crate) const SQRT_MINUS_APLUS2: FieldElement32 = FieldElement32([
    -12222970, -8312128, -11511410, 9067497, -15300785,
    -241793, 25456130, 14121551, -12187136, 3972024]);

/// `SQRT_MINUS_HALF` is sqrt(-1/2)
pub const SQRT_MINUS_HALF: FieldElement32 = FieldElement32([ // sqrtMinusHalf
    -17256545,   3971863,  28865457,  -1750208,  27359696,
    -16640980,  12573105,   1002827,   -163343,  11073975, ]);

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
        X: FieldElement32([-14297830, -7645148, 16144683, -16471763, 27570974, -2696100, -26142465, 8378389, 20764389, 8758491]),
        Y: FieldElement32([-26843541, -6710886, 13421773, -13421773, 26843546, 6710886, -13421773, 13421773, -26843546, -6710886]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([28827062, -6116119, -27349572, 244363, 8635006, 11264893, 19351346, 13413597, 16611511, -6414980]),
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
        X: FieldElement32([21352778, 5345713, 4660180, -8347857, 24143090, 14568123, 30185756, -12247770, -33528939, 8345319]),
        Y: FieldElement32([6952922, 1265500, -6862341, 7057498, 4037696, 5447722, -31680899, 15325402, 19365852, -1569102]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([-25262188, -11972680, 11716002, -5869612, -18193162, 16297739, 20670665, -8559098, 3541543, -5011181])
    },
    ExtendedPoint{
        X: FieldElement32([32595792, 7943725, -9377950, -3500415, -12389472, 272473, 25146209, 2005654, -326686, -11406482]),
        Y: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    ExtendedPoint{
        X: FieldElement32([21352778, 5345713, 4660180, -8347857, 24143090, 14568123, 30185756, -12247770, -33528939, 8345319]),
        Y: FieldElement32([-6952922, -1265500, 6862341, -7057498, -4037696, -5447722, 31680899, -15325402, -19365852, 1569102]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([25262188, 11972680, -11716002, 5869612, 18193162, -16297739, -20670665, 8559098, -3541543, 5011181])
    },
    ExtendedPoint{
        X: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Y: FieldElement32([-1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    ExtendedPoint{
        X: FieldElement32([-21352778, -5345713, -4660180, 8347857, -24143090, -14568123, -30185756, 12247770, 33528939, -8345319]),
        Y: FieldElement32([-6952922, -1265500, 6862341, -7057498, -4037696, -5447722, 31680899, -15325402, -19365852, 1569102]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([-25262188, -11972680, 11716002, -5869612, -18193162, 16297739, 20670665, -8559098, 3541543, -5011181])
    },
    ExtendedPoint{
        X: FieldElement32([-32595792, -7943725, 9377950, 3500415, 12389472, -272473, -25146209, -2005654, 326686, 11406482]),
        Y: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    },
    ExtendedPoint{
        X: FieldElement32([-21352778, -5345713, -4660180, 8347857, -24143090, -14568123, -30185756, 12247770, 33528939, -8345319]),
        Y: FieldElement32([6952922, 1265500, -6862341, 7057498, 4037696, 5447722, -31680899, 15325402, 19365852, -1569102]),
        Z: FieldElement32([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        T: FieldElement32([25262188, 11972680, -11716002, 5869612, 18193162, -16297739, -20670665, 8559098, -3541543, 5011181])
    },
];
