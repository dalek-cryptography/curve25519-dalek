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

#![allow(non_snake_case)]

use field_64bit::FieldElement64;
use scalar_64bit::Scalar64;
use edwards::ExtendedPoint;
use edwards::AffineNielsPoint;
use edwards::EdwardsBasepointTable;

/// Edwards `d` value, equal to `-121665/121666 mod p`.
pub(crate) const EDWARDS_D: FieldElement64 = FieldElement64([929955233495203, 466365720129213, 1662059464998953, 2033849074728123, 1442794654840575]);

/// Edwards `2*d` value, equal to `2*(-121665/121666) mod p`.
pub(crate) const EDWARDS_D2: FieldElement64 = FieldElement64([1859910466990425, 932731440258426, 1072319116312658, 1815898335770999, 633789495995903]);

/// `= sqrt(a*d - 1)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const SQRT_AD_MINUS_ONE: FieldElement64 = FieldElement64([
    2241493124984347, 425987919032274, 2207028919301688, 1220490630685848, 974799131293748
]);

/// `= 1/sqrt(a-d)`, where `a = -1 (mod p)`, `d` are the Edwards curve parameters.
pub(crate) const INVSQRT_A_MINUS_D: FieldElement64 = FieldElement64([
    278908739862762, 821645201101625, 8113234426968, 1777959178193151, 2118520810568447
]);

/// Precomputed value of one of the square roots of -1 (mod p)
pub(crate) const SQRT_M1: FieldElement64 = FieldElement64([1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133]);

/// In Montgomery form y² = x³+Ax²+x, Curve25519 has A=486662.
pub(crate) const MONTGOMERY_A: FieldElement64 = FieldElement64([486662, 0, 0, 0, 0]);

/// `APLUS2_OVER_FOUR` is (A+2)/4. (This is used internally within the Montgomery ladder.)
pub(crate) const APLUS2_OVER_FOUR: FieldElement64 = FieldElement64([121666, 0, 0, 0, 0]);

/// `SQRT_MINUS_APLUS2` is sqrt(-486664)
pub(crate) const SQRT_MINUS_APLUS2: FieldElement64 = FieldElement64([1693982333959686, 608509411481997, 2235573344831311, 947681270984193, 266558006233600]);

/// `L` is the order of base point, i.e. 2^252 + 27742317777372353535851937790883648493
pub(crate) const L: Scalar64 = Scalar64([ 0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0x0000000000000000, 0x0000100000000000 ]);

/// `L` * `LFACTOR` = -1 (mod 2^51)
pub(crate) const LFACTOR: u64 = 0x51da312547e1b;

/// `R` = R % L where R = 2^260
pub(crate) const R: Scalar64 = Scalar64([ 0x000f48bd6721e6ed, 0x0003bab5ac67e45a, 0x000fffffeb35e51b, 0x000fffffffffffff, 0x00000fffffffffff ]);

/// `RR` = (R^2) % L where R = 2^260
pub(crate) const RR: Scalar64 = Scalar64([ 0x0009d265e952d13b, 0x000d63c715bea69f, 0x0005be65cb687604, 0x0003dceec73d217f, 0x000009411b7c309a ]);

/// The Ed25519 basepoint has y = 4/5.  This is called `_POINT` to
/// distinguish it from `_TABLE`, which should be used for scalar
/// multiplication (it's much faster).
pub const ED25519_BASEPOINT_POINT: ExtendedPoint = ExtendedPoint{
    X: FieldElement64([1738742601995546, 1146398526822698, 2070867633025821, 562264141797630, 587772402128613]),
    Y: FieldElement64([1801439850948184, 1351079888211148, 450359962737049, 900719925474099, 1801439850948198]),
    Z: FieldElement64([1, 0, 0, 0, 0]),
    T: FieldElement64([1841354044333475, 16398895984059, 755974180946558, 900171276175154, 1821297809914039]),
};

/// The 8-torsion subgroup Ɛ[8].
///
/// In the case of Curve25519, it is cyclic; the `i`th element of the
/// array is `i*P`, where `P` is a point of order 8 generating Ɛ[8].
///
/// Thus Ɛ[4] is the points indexed by 0,2,4,6 and Ɛ[2] is the points
/// indexed by 0,4. 
pub const EIGHT_TORSION: [ExtendedPoint; 8] = [
    ExtendedPoint {
        X: FieldElement64([0, 0, 0, 0, 0]),
        Y: FieldElement64([1, 0, 0, 0, 0]),
        Z: FieldElement64([1, 0, 0, 0, 0]),
        T: FieldElement64([0, 0, 0, 0, 0]),
    }
    ,
    ExtendedPoint {
        X: FieldElement64([358744748052810, 1691584618240980, 977650209285361, 1429865912637724, 560044844278676]),
        Y: FieldElement64([84926274344903, 473620666599931, 365590438845504, 1028470286882429, 2146499180330972]),
        Z: FieldElement64([1, 0, 0, 0, 0]),
        T: FieldElement64([1448326834587521, 1857896831960481, 1093722731865333, 1677408490711241, 1915505153018406]),
    }
    ,
    ExtendedPoint {
        X: FieldElement64([533094393274173, 2016890930128738, 18285341111199, 134597186663265, 1486323764102114]),
        Y: FieldElement64([0, 0, 0, 0, 0]),
        Z: FieldElement64([1, 0, 0, 0, 0]),
        T: FieldElement64([0, 0, 0, 0, 0]),
    }
    ,
    ExtendedPoint {
        X: FieldElement64([358744748052810, 1691584618240980, 977650209285361, 1429865912637724, 560044844278676]),
        Y: FieldElement64([2166873539340326, 1778179147085316, 1886209374839743, 1223329526802818, 105300633354275]),
        Z: FieldElement64([1, 0, 0, 0, 0]),
        T: FieldElement64([803472979097708, 393902981724766, 1158077081819914, 574391322974006, 336294660666841]),
    }
    ,
    ExtendedPoint {
        X: FieldElement64([0, 0, 0, 0, 0]),
        Y: FieldElement64([2251799813685228, 2251799813685247, 2251799813685247, 2251799813685247, 2251799813685247]),
        Z: FieldElement64([1, 0, 0, 0, 0]),
        T: FieldElement64([0, 0, 0, 0, 0]),
    }
    ,
    ExtendedPoint {
        X: FieldElement64([1893055065632419, 560215195444267, 1274149604399886, 821933901047523, 1691754969406571]),
        Y: FieldElement64([2166873539340326, 1778179147085316, 1886209374839743, 1223329526802818, 105300633354275]),
        Z: FieldElement64([1, 0, 0, 0, 0]),
        T: FieldElement64([1448326834587521, 1857896831960481, 1093722731865333, 1677408490711241, 1915505153018406]),
    }
    ,
    ExtendedPoint {
        X: FieldElement64([1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133]),
        Y: FieldElement64([0, 0, 0, 0, 0]),
        Z: FieldElement64([1, 0, 0, 0, 0]),
        T: FieldElement64([0, 0, 0, 0, 0]),
    }
    ,
    ExtendedPoint {
        X: FieldElement64([1893055065632419, 560215195444267, 1274149604399886, 821933901047523, 1691754969406571]),
        Y: FieldElement64([84926274344903, 473620666599931, 365590438845504, 1028470286882429, 2146499180330972]),
        Z: FieldElement64([1, 0, 0, 0, 0]),
        T: FieldElement64([803472979097708, 393902981724766, 1158077081819914, 574391322974006, 336294660666841]),
    }
];

/// Odd multiples of the basepoint `[B, 3B, 5B, 7B, 9B, 11B, 13B, 15B]`.
pub(crate) const AFFINE_ODD_MULTIPLES_OF_BASEPOINT: [AffineNielsPoint; 8] = [
    AffineNielsPoint {
        y_plus_x: FieldElement64([1288382639258501, 245678601348599, 269427782077623, 1462984067271730, 137412439391563]),
        y_minus_x: FieldElement64([62697248952638, 204681361388450, 631292143396476, 338455783676468, 1213667448819585]),
        xy2d: FieldElement64([301289933810280, 1259582250014073, 1422107436869536, 796239922652654, 1953934009299142]),
    }
    ,
    AffineNielsPoint {
        y_plus_x: FieldElement64([1601611775252272, 1720807796594148, 1132070835939856, 1260455018889551, 2147779492816911]),
        y_minus_x: FieldElement64([316559037616741, 2177824224946892, 1459442586438991, 1461528397712656, 751590696113597]),
        xy2d: FieldElement64([1850748884277385, 1200145853858453, 1068094770532492, 672251375690438, 1586055907191707]),
    }
    ,
    AffineNielsPoint {
        y_plus_x: FieldElement64([769950342298419, 132954430919746, 844085933195555, 974092374476333, 726076285546016]),
        y_minus_x: FieldElement64([425251763115706, 608463272472562, 442562545713235, 837766094556764, 374555092627893]),
        xy2d: FieldElement64([1086255230780037, 274979815921559, 1960002765731872, 929474102396301, 1190409889297339]),
    }
    ,
    AffineNielsPoint {
        y_plus_x: FieldElement64([665000864555967, 2065379846933859, 370231110385876, 350988370788628, 1233371373142985]),
        y_minus_x: FieldElement64([2019367628972465, 676711900706637, 110710997811333, 1108646842542025, 517791959672113]),
        xy2d: FieldElement64([965130719900578, 247011430587952, 526356006571389, 91986625355052, 2157223321444601]),
    }
    ,
    AffineNielsPoint {
        y_plus_x: FieldElement64([1802695059465007, 1664899123557221, 593559490740857, 2160434469266659, 927570450755031]),
        y_minus_x: FieldElement64([1725674970513508, 1933645953859181, 1542344539275782, 1767788773573747, 1297447965928905]),
        xy2d: FieldElement64([1381809363726107, 1430341051343062, 2061843536018959, 1551778050872521, 2036394857967624]),
    }
    ,
    AffineNielsPoint {
        y_plus_x: FieldElement64([1970894096313054, 528066325833207, 1619374932191227, 2207306624415883, 1169170329061080]),
        y_minus_x: FieldElement64([2070390218572616, 1458919061857835, 624171843017421, 1055332792707765, 433987520732508]),
        xy2d: FieldElement64([893653801273833, 1168026499324677, 1242553501121234, 1306366254304474, 1086752658510815]),
    }
    ,
    AffineNielsPoint {
        y_plus_x: FieldElement64([213454002618221, 939771523987438, 1159882208056014, 317388369627517, 621213314200687]),
        y_minus_x: FieldElement64([1971678598905747, 338026507889165, 762398079972271, 655096486107477, 42299032696322]),
        xy2d: FieldElement64([177130678690680, 1754759263300204, 1864311296286618, 1180675631479880, 1292726903152791]),
    }
    ,
    AffineNielsPoint {
        y_plus_x: FieldElement64([1913163449625248, 460779200291993, 2193883288642314, 1008900146920800, 1721983679009502]),
        y_minus_x: FieldElement64([1070401523076875, 1272492007800961, 1910153608563310, 2075579521696771, 1191169788841221]),
        xy2d: FieldElement64([692896803108118, 500174642072499, 2068223309439677, 1162190621851337, 1426986007309901]),
    }
];

