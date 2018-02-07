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
use core::ops::{Index, Add, Sub, Mul, Neg};
use core::borrow::Borrow;

use stdsimd::simd::{u32x8, i32x8};

use subtle::ConditionallyAssignable;
use subtle::Choice;

use edwards;
use scalar::Scalar;
use curve_models::window::LookupTable;

use traits::Identity;

use backend::avx2::field::FieldElement32x4;

use backend::avx2::field::{A_LANES, B_LANES, C_LANES, D_LANES, ALL_LANES};
use backend::avx2::field::D_LANES64;

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

/// A cached point with some precomputed variables used for readdition.
#[derive(Copy, Clone, Debug)]
pub struct CachedPoint(pub(super) FieldElement32x4);

impl From<ExtendedPoint> for CachedPoint {
    fn from(P: ExtendedPoint) -> CachedPoint {
        let mut x = P.0;

        // x = (S2 S3 Z2 T2)
        x.diff_sum(0b00001111);

        // x = (121666*S2 121666*S3 2*121666*Z2 2*121665*T2)
        x.scale_by_curve_constants();

        // x = (121666*S2 121666*S3 2*121666*Z2 -2*121665*T2)
        x.negate(D_LANES);

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
        neg.0.negate_lazy(D_LANES);
        neg
    }
}

impl<'a> Neg for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    fn neg(self) -> ExtendedPoint {
        let mut neg = *self;
        // (X Y Z T) -> (-X Y Z -T)
        neg.0.negate(A_LANES | D_LANES);
        neg
    }
}

impl ExtendedPoint {
    fn double(&self) -> ExtendedPoint {
        unsafe {
            use stdsimd::vendor::_mm256_permute2x128_si256;
            use stdsimd::vendor::_mm256_permutevar8x32_epi32;
            use stdsimd::vendor::_mm256_blend_epi32;
            use stdsimd::vendor::_mm256_shuffle_epi32;

            let P = &self.0;

            let mut t0 = FieldElement32x4::zero();
            let mut t1 = FieldElement32x4::zero();

            // Want to compute (X1 Y1 Z1 X1+Y1).
            // Not sure how to do this less expensively than computing
            // (X1 Y1 Z1 T1) --(256bit shuffle)--> (X1 Y1 X1 Y1)
            // (X1 Y1 X1 Y1) --(2x128b shuffle)--> (Y1 X1 Y1 X1)
            // and then adding.

            // Set t0 = (X1 Y1 X1 Y1)
            t0.0[0] = _mm256_permute2x128_si256(P.0[0].into(), P.0[0].into(), 0b0000_0000).into();
            t0.0[1] = _mm256_permute2x128_si256(P.0[1].into(), P.0[1].into(), 0b0000_0000).into();
            t0.0[2] = _mm256_permute2x128_si256(P.0[2].into(), P.0[2].into(), 0b0000_0000).into();
            t0.0[3] = _mm256_permute2x128_si256(P.0[3].into(), P.0[3].into(), 0b0000_0000).into();
            t0.0[4] = _mm256_permute2x128_si256(P.0[4].into(), P.0[4].into(), 0b0000_0000).into();

            // Set t1 = (Y1 X1 Y1 X1)
            t1.0[0] = _mm256_shuffle_epi32(t0.0[0].into(), 0b10_11_00_01).into();
            t1.0[1] = _mm256_shuffle_epi32(t0.0[1].into(), 0b10_11_00_01).into();
            t1.0[2] = _mm256_shuffle_epi32(t0.0[2].into(), 0b10_11_00_01).into();
            t1.0[3] = _mm256_shuffle_epi32(t0.0[3].into(), 0b10_11_00_01).into();
            t1.0[4] = _mm256_shuffle_epi32(t0.0[4].into(), 0b10_11_00_01).into();

            // Set t0 = (X1+Y1 X1+Y1 X1+Y1 X1+Y1)
            t0.0[0] = t0.0[0] + t1.0[0];
            t0.0[1] = t0.0[1] + t1.0[1];
            t0.0[2] = t0.0[2] + t1.0[2];
            t0.0[3] = t0.0[3] + t1.0[3];
            t0.0[4] = t0.0[4] + t1.0[4];

            // Set t0 = (X1 Y1 Z1 X1+Y1)
            // why does this intrinsic take an i32 for the imm8 ???
            t0.0[0] = _mm256_blend_epi32(P.0[0].into(), t0.0[0].into(), D_LANES as i32).into();
            t0.0[1] = _mm256_blend_epi32(P.0[1].into(), t0.0[1].into(), D_LANES as i32).into();
            t0.0[2] = _mm256_blend_epi32(P.0[2].into(), t0.0[2].into(), D_LANES as i32).into();
            t0.0[3] = _mm256_blend_epi32(P.0[3].into(), t0.0[3].into(), D_LANES as i32).into();
            t0.0[4] = _mm256_blend_epi32(P.0[4].into(), t0.0[4].into(), D_LANES as i32).into();

            // Set t1 = t0^2, negating the D values
            t1 = t0.square(D_LANES64);

            // Now t1 = (S1 S2 S3 -S4)

            let c0 = u32x8::new(0,0,2,2,0,0,2,2); // (ABCD) -> (AAAA)
            let c1 = u32x8::new(1,1,3,3,1,1,3,3); // (ABCD) -> (BBBB)

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
                let zero = i32x8::splat(0);
                let S1 = _mm256_permutevar8x32_epi32(t1.0[i], c0);
                let S2 = _mm256_permutevar8x32_epi32(t1.0[i], c1);
                let S3_2: u32x8 = _mm256_blend_epi32(zero, (t1.0[i] + t1.0[i]).into(), 0b01010000).into();
                // tmp0 = (0 0 2*S3 -S4)
                let tmp0: u32x8 = _mm256_blend_epi32(S3_2.into(), t1.0[i].into(), 0b10100000).into();
                t0.0[i] = (avx2::constants::P_TIMES_2_MASKED.0[i] + tmp0) + S1;
                t0.0[i] = t0.0[i] + _mm256_blend_epi32(zero, S2.into(), 0b10100101).into();
                t0.0[i] = t0.0[i] - _mm256_blend_epi32(S2.into(), zero, 0b10100101).into();
            }

            let c0 = u32x8::new(4,0,6,2,4,0,6,2); // (ABCD) -> (CACA)
            let c1 = u32x8::new(5,1,7,3,1,5,3,7); // (ABCD) -> (DBBD)

            for i in 0..5 {
                let tmp = t0.0[i];
                t0.0[i] = _mm256_permutevar8x32_epi32(tmp, c0);
                t1.0[i] = _mm256_permutevar8x32_epi32(tmp, c1);
            }

            ExtendedPoint(&t0 * &t1)
        }
    }

    pub fn mult_by_pow_2(&self, k: u32) -> ExtendedPoint {
        let mut tmp: ExtendedPoint = *self;
        for _ in 0..k {
            tmp = tmp.double();
        }
        tmp
    }
}

impl<'a, 'b> Add<&'b CachedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    /// Uses a slight tweak of the parallel unified formulas of HWCD'08
    fn add(self, other: &'b CachedPoint) -> ExtendedPoint {
        unsafe {
            use stdsimd::vendor::_mm256_permutevar8x32_epi32;

            let mut tmp = self.0;

            // tmp = (Y1-X1 Y1+X1 Z1 T1) = (S0 S1 Z1 T1)
            tmp.diff_sum(A_LANES | B_LANES);

            // tmp = (S0*S2' S1*S3' Z1*Z2' T1*T2') = (S8 S9 S10 S11)
            tmp = &tmp * &other.0;

            // tmp = (S8 S9 S11 S10)
            tmp.swap_CD();

            // tmp = (S9-S8 S9+S8 S10-S11 S10+S11) = (S12 S13 S14 S15)
            tmp.diff_sum(ALL_LANES);

            let c0 = u32x8::new(0,5,2,7,5,0,7,2); // (ABCD) -> (ADDA)
            let c1 = u32x8::new(4,1,6,3,4,1,6,3); // (ABCD) -> (CBCB)

            // set t0 = (S12 S15 S15 S12)
            // set t1 = (S14 S13 S14 S13)
            let mut t0 = FieldElement32x4::zero();
            let mut t1 = FieldElement32x4::zero();
            for i in 0..5 {
                t0.0[i] = _mm256_permutevar8x32_epi32(tmp.0[i], c0);
                t1.0[i] = _mm256_permutevar8x32_epi32(tmp.0[i], c1);
            }

            // return (S12*S14 S15*S13 S15*S14 S12*S13) = (X3 Y3 Z3 T3)
            ExtendedPoint(&t0 * &t1)
        }
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

            let P: &FieldElement32x4 = &self.0;
            let Q: &FieldElement32x4 = &other.0;

            let mut t0 = FieldElement32x4::zero();
            let mut t1 = FieldElement32x4::zero();

            // set t0 = (X1 Y1 X2 Y2)
            for i in 0..5 {
                t0.0[i] = _mm256_permute2x128_si256(P.0[i].into(), Q.0[i].into(), 32).into();
            }

            // set t0 = (Y1-X1 Y1+X1 Y2-X2 Y2+X2) = (S0 S1 S2 S3)
            t0.diff_sum(0xff);

            // set t1 = (S0 S1 Z1 T1)
            // set t0 = (S2 S3 Z2 T2)
            for i in 0..5 {
                // why does this intrinsic take an i32 for the imm8 ???
                t1.0[i] = _mm256_blend_epi32(t0.0[i].into(), P.0[i].into(), (C_LANES | D_LANES) as i32).into();
                t0.0[i] = _mm256_permute2x128_si256(t0.0[i].into(), Q.0[i].into(), 49).into();
            }

            // set t2 = (S0*S2 S1*S3 Z1*Z2 T1*T2) = (S4 S5 S6 S7)
            let mut t2 = &t0 * &t1;

            //// set t2 = (S8 S9 S10 S11)
            // set t2 = (121666*S4  121666*S5 2*121666*S6 2*121665*S7)
            //        = (       S8         S9         S10        -S11)
            t2.scale_by_curve_constants();

            // set t2 = (S8 S9 -S11 S10)
            t2.swap_CD();

            // set t2 = (S9-S8 S9+S8 S10+S11 S10-S11) = (S12 S13 S15 S14)
            t2.diff_sum(0xff);

            let c0 = u32x8::new(0,4,2,6,4,0,6,2); // (ABCD) -> (ACCA)
            let c1 = u32x8::new(5,1,7,3,5,1,7,3); // (ABCD) -> (DBDB)

            // set t0 = (S12 S15 S15 S12)
            // set t1 = (S14 S13 S14 S13)
            for i in 0..5 {
                t0.0[i] = _mm256_permutevar8x32_epi32(t2.0[i], c0);
                t1.0[i] = _mm256_permutevar8x32_epi32(t2.0[i], c1);
            }

            // return (S12*S14 S15*S13 S15*S14 S12*S13) = (X3 Y3 Z3 T3)
            ExtendedPoint(&t0 * &t1)
        }
    }
}

impl<'a, 'b> Sub<&'b ExtendedPoint> for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    /// Implement subtraction by negating the point and adding.
    ///
    /// Empirically, this seems about the same cost as a custom subtraction impl (maybe because the
    /// benefit is cancelled by increased code size?)
    fn sub(self, other: &'b ExtendedPoint) -> ExtendedPoint {
        self + &(-other)
    }
}

impl From<ExtendedPoint> for LookupTable<CachedPoint> {
    fn from(P: ExtendedPoint) -> Self {
        let mut points = [CachedPoint::from(P); 8];
        for i in 0..7 {
            points[i+1] = (&P + &points[i]).into();
        }
        LookupTable(points)
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a ExtendedPoint {
    type Output = ExtendedPoint;
    /// Scalar multiplication: compute `scalar * self`.
    ///
    /// Uses a window of size 4.
    fn mul(self, scalar: &'b Scalar) -> ExtendedPoint {
        // Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]
        let lookup_table = LookupTable::<CachedPoint>::from(*self);

        // Setting s = scalar, compute
        //
        //    s = s_0 + s_1*16^1 + ... + s_63*16^63,
        //
        // with `-8 ≤ s_i < 8` for `0 ≤ i < 63` and `-8 ≤ s_63 ≤ 8`.
        let scalar_digits = scalar.to_radix_16();

        // Compute s*P as
        //
        //    s*P = P*(s_0 +   s_1*16^1 +   s_2*16^2 + ... +   s_63*16^63)
        //    s*P =  P*s_0 + P*s_1*16^1 + P*s_2*16^2 + ... + P*s_63*16^63
        //    s*P = P*s_0 + 16*(P*s_1 + 16*(P*s_2 + 16*( ... + P*s_63)...))
        //
        // We sum right-to-left.
        let mut Q = ExtendedPoint::identity();
        for i in (0..64).rev() {
            // Q = 16*Q
            Q = Q.mult_by_pow_2(4);
            // Q += P*s_i
            Q = &Q + &lookup_table.select(scalar_digits[i]);
        }
        Q
    }
}

#[derive(Clone)]
pub struct EdwardsBasepointTable(pub [LookupTable<CachedPoint>; 32]);

impl<'a, 'b> Mul<&'b Scalar> for &'a EdwardsBasepointTable {
    type Output = ExtendedPoint;

    fn mul(self, scalar: &'b Scalar) -> ExtendedPoint {
        let a = scalar.to_radix_16();

        let tables = &self.0;
        let mut P = ExtendedPoint::identity();

        for i in (0..64).filter(|x| x % 2 == 1) {
            P = &P + &tables[i/2].select(a[i]);
        }

        P = P.mult_by_pow_2(4);

        for i in (0..64).filter(|x| x % 2 == 0) {
            P = &P + &tables[i/2].select(a[i]);
        }

        P
    }
}

impl<'a, 'b> Mul<&'a EdwardsBasepointTable> for &'b Scalar {
    type Output = ExtendedPoint;

    /// Given `self` a table of precomputed multiples of the point `B`, compute `B * s`.
    fn mul(self, basepoint_table: &'a EdwardsBasepointTable) -> ExtendedPoint {
        basepoint_table * &self
    }
}

impl EdwardsBasepointTable {
    /// Create a table of precomputed multiples of `basepoint`.
    pub fn create(basepoint: &ExtendedPoint) -> EdwardsBasepointTable {
        // XXX use init_with
        let mut table = EdwardsBasepointTable([LookupTable::default(); 32]);
        let mut P = *basepoint;
        for i in 0..32 {
            // P = (16^2)^i * B
            table.0[i] = LookupTable::from(P);
            P = P.mult_by_pow_2(8);
        }
        table
    }
}

/// Internal multiscalar code.
#[cfg(any(feature = "alloc", feature = "std"))]
pub fn multiscalar_mult<I, J>(scalars: I, points: J) -> edwards::EdwardsPoint
    where I: IntoIterator,
          I::Item: Borrow<Scalar>,
          J: IntoIterator,
          J::Item: Borrow<edwards::EdwardsPoint>,
{
    //assert_eq!(scalars.len(), points.len());

    use clear_on_drop::ClearOnDrop;
    let lookup_tables_vec: Vec<_> = points.into_iter()
        .map(|P| LookupTable::from(ExtendedPoint::from(*P.borrow())) )
        .collect();

    let lookup_tables = ClearOnDrop::new(lookup_tables_vec);

    // Setting s_i = i-th scalar, compute
    //
    //    s_i = s_{i,0} + s_{i,1}*16^1 + ... + s_{i,63}*16^63,
    //
    // with `-8 ≤ s_{i,j} < 8` for `0 ≤ j < 63` and `-8 ≤ s_{i,63} ≤ 8`.
    let scalar_digits_vec: Vec<_> = scalars.into_iter()
        .map(|c| c.borrow().to_radix_16())
        .collect();

    // The above puts the scalar digits into a heap-allocated Vec.
    // To ensure that these are erased, pass ownership of the Vec into a
    // ClearOnDrop wrapper.
    let scalar_digits = ClearOnDrop::new(scalar_digits_vec);

    // Compute s_1*P_1 + ... + s_n*P_n: since
    //
    //    s_i*P_i = P_i*(s_{i,0} +     s_{i,1}*16^1 + ... +     s_{i,63}*16^63)
    //    s_i*P_i =  P_i*s_{i,0} + P_i*s_{i,1}*16^1 + ... + P_i*s_{i,63}*16^63
    //    s_i*P_i =  P_i*s_{i,0} + 16*(P_i*s_{i,1} + 16*( ... + 16*P_i*s_{i,63})...)
    //
    // we have the two-dimensional sum
    //
    //    s_1*P_1 =   P_1*s_{1,0} + 16*(P_1*s_{1,1} + 16*( ... + 16*P_1*s_{1,63})...)
    //  + s_2*P_2 = + P_2*s_{2,0} + 16*(P_2*s_{2,1} + 16*( ... + 16*P_2*s_{2,63})...)
    //      ...
    //  + s_n*P_n = + P_n*s_{n,0} + 16*(P_n*s_{n,1} + 16*( ... + 16*P_n*s_{n,63})...)
    //
    // We sum column-wise top-to-bottom, then right-to-left,
    // multiplying by 16 only once per column.
    //
    // This provides the speedup over doing n independent scalar
    // mults: we perform 63 multiplications by 16 instead of 63*n
    // multiplications, saving 252*(n-1) doublings.
    let mut Q = ExtendedPoint::identity();
    // XXX this algorithm makes no effort to be cache-aware; maybe it could be improved?
    for j in (0..64).rev() {
        Q = Q.mult_by_pow_2(4);
        let it = scalar_digits.iter().zip(lookup_tables.iter());
        for (s_i, lookup_table_i) in it {
            // Q = Q + s_{i,j} * P_i
            Q = &Q + &lookup_table_i.select(s_i[j]);
        }
    }
    Q.into()
}

pub mod vartime {
    //! Variable-time operations on curve points, useful for non-secret data.
    use super::*;

    /// Holds odd multiples 1A, 3A, ..., 15A of a point A.
    struct OddMultiples([ExtendedPoint; 8]);

    impl OddMultiples {
        fn create(A: ExtendedPoint) -> OddMultiples {
            // XXX would be great to skip this initialization
            let mut Ai = [A; 8];
            let A2 = A.double();
            for i in 0..7 {
                Ai[i+1] = &A2 + &Ai[i];
            }
            // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
            OddMultiples(Ai)
        }
    }

    impl Index<usize> for OddMultiples {
        type Output = ExtendedPoint;

        fn index(&self, _index: usize) -> &ExtendedPoint {
            &(self.0[_index])
        }
    }

    /// Given a point `A` and scalars `a` and `b`, compute the point
    /// `aA+bB`, where `B` is the Ed25519 basepoint (i.e., `B = (x,4/5)`
    /// with x positive).
    ///
    /// This is the same as calling the iterator-based function, but slightly faster.
    pub fn double_scalar_mult_basepoint(a: &Scalar,
                                        A: &edwards::EdwardsPoint,
                                        b: &Scalar) -> edwards::EdwardsPoint {
        let a_naf = a.non_adjacent_form();
        let b_naf = b.non_adjacent_form();

        // Find starting index
        let mut i: usize = 255;
        for j in (0..255).rev() {
            i = j;
            if a_naf[i] != 0 || b_naf[i] != 0 {
                break;
            }
        }

        let odd_multiples_of_A = OddMultiples::create((*A).into());
        let odd_multiples_of_B = &avx2::constants::ODD_MULTIPLES_OF_BASEPOINT;

        let mut Q = ExtendedPoint::identity();

        loop {
            Q = Q.double();

            if a_naf[i] > 0 {
                Q = &Q + &odd_multiples_of_A[( a_naf[i]/2) as usize];
            } else if a_naf[i] < 0 {
                Q = &Q - &odd_multiples_of_A[(-a_naf[i]/2) as usize];
            }

            if b_naf[i] > 0 {
                Q = &Q + &odd_multiples_of_B[( b_naf[i]/2) as usize];
            } else if b_naf[i] < 0 {
                Q = &Q - &odd_multiples_of_B[(-b_naf[i]/2) as usize];
            }

            if i == 0 {
                break;
            }
            i -= 1;
        }

        Q.into()
    }

    /// Internal multiscalar function
    #[cfg(any(feature = "alloc", feature = "std"))]
    pub fn multiscalar_mult<I, J>(scalars: I, points: J) -> edwards::EdwardsPoint
        where I: IntoIterator,
              I::Item: Borrow<Scalar>,
              J: IntoIterator,
              J::Item: Borrow<edwards::EdwardsPoint>,
    {
        //assert_eq!(scalars.len(), points.len());

        let nafs: Vec<_> = scalars.into_iter()
            .map(|c| c.borrow().non_adjacent_form()).collect();

        let odd_multiples: Vec<_> = points.into_iter()
            .map(|P| OddMultiples::create((*P.borrow()).into()) ).collect();

        let mut Q = ExtendedPoint::identity();

        for i in (0..255).rev() {
            Q = Q.double();

            for (naf, odd_multiple) in nafs.iter().zip(odd_multiples.iter()) {
                if naf[i] > 0 {
                    Q = &Q + &odd_multiple[( naf[i]/2) as usize];
                } else if naf[i] < 0 {
                    Q = &Q - &odd_multiple[(-naf[i]/2) as usize];
                }
            }
        }
        Q.into()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use constants;

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
        // Test the vector implementation of the parallel addition formulas
        let R_vector: edwards::EdwardsPoint = (&ExtendedPoint::from(P) + &ExtendedPoint::from(Q)).into();
        // Test the vector implementation of the parallel subtraction formulas
        let S_vector: edwards::EdwardsPoint = (&ExtendedPoint::from(P) - &ExtendedPoint::from(Q)).into();

        // Test the vector implementation of the parallel readdition formulas
        let cached_Q = CachedPoint::from(ExtendedPoint::from(Q));
        let T_vector: edwards::EdwardsPoint = (&ExtendedPoint::from(P) + &cached_Q).into();

        println!("Testing point addition:");
        println!("P = {:?}", P);
        println!("Q = {:?}", Q);
        println!("cached Q = {:?}", cached_Q);
        println!("R = P + Q = {:?}", &P + &Q);
        println!("R_serial = {:?}", R_serial);
        println!("R_vector = {:?}", R_vector);
        println!("T_vector = {:?}", T_vector);
        println!("S = P - Q = {:?}", &P - &Q);
        println!("S_vector = {:?}", S_vector);
        assert_eq!(R_serial.compress(), (&P + &Q).compress());
        assert_eq!(R_vector.compress(), (&P + &Q).compress());
        assert_eq!(T_vector.compress(), (&P + &Q).compress());
        assert_eq!(S_vector.compress(), (&P - &Q).compress());
        println!("OK!\n");
    }

    #[test]
    fn sub_vs_add_minus() {
        let P: ExtendedPoint = edwards::EdwardsPoint::identity().into();
        let Q: ExtendedPoint = edwards::EdwardsPoint::identity().into();

        let mQ = -&Q;

        println!("sub");
        let R1: edwards::EdwardsPoint = (&P - &Q).into();
        println!("add neg");
        let R2: edwards::EdwardsPoint = (&P + &mQ).into();

        assert_eq!(R2.compress(), edwards::EdwardsPoint::identity().compress());
        assert_eq!(R1.compress(), edwards::EdwardsPoint::identity().compress());
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

    #[test]
    fn identity_trait_vs_edwards_identity() {
        let id1: edwards::EdwardsPoint = ExtendedPoint::identity().into();
        let id2: edwards::EdwardsPoint = edwards::EdwardsPoint::identity();
        assert_eq!(id1.compress(), id2.compress());
    }

    #[test]
    fn neg_vs_edwards_neg() {
        let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
        let Bneg = -&B;
        assert_eq!(edwards::EdwardsPoint::from(Bneg).compress(),
                   (-&constants::ED25519_BASEPOINT_POINT).compress());
    }

    #[test]
    fn scalar_mult_vs_edwards_scalar_mult() {
        let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
        // some random bytes
        let s = Scalar::from_bits([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);

        let R1 = edwards::EdwardsPoint::from(&B * &s);
        let R2 = &constants::ED25519_BASEPOINT_TABLE * &s;

        assert_eq!(R1.compress(), R2.compress());
    }

    #[test]
    fn scalar_mult_vs_basepoint_table_scalar_mult() {
        let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
        let B_table = EdwardsBasepointTable::create(&B);
        // some random bytes
        let s = Scalar::from_bits([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);

        let P1 = &B * &s;
        let P2 = &B_table * &s;

        assert_eq!(edwards::EdwardsPoint::from(P1).compress(),
                   edwards::EdwardsPoint::from(P2).compress());
    }

    #[test]
    fn multiscalar_mult_vs_adding_scalar_mults() {
        let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
        let s1 = Scalar::from_bits([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);
        let s2 = Scalar::from_bits([165, 30, 79, 89, 58, 24, 195, 245, 248, 146, 203, 236, 119, 43, 64, 119, 196, 111, 188, 251, 248, 53, 234, 59, 215, 28, 218, 13, 59, 120, 14, 4]);

        let P1 = &B * &s2;
        let P2 = &B * &s1;

        let R = &(&P1 * &s1) + &(&P2 * &s2);

        let R_multiscalar = multiscalar_mult(&[s1, s2], &[P1.into(), P2.into()]);

        assert_eq!(edwards::EdwardsPoint::from(R).compress(),
                   R_multiscalar.compress());
    }

    mod vartime {
        use super::*;

        #[test]
        fn multiscalar_mult_vs_adding_scalar_mults() {
            let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
            let s1 = Scalar::from_bits([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);
            let s2 = Scalar::from_bits([165, 30, 79, 89, 58, 24, 195, 245, 248, 146, 203, 236, 119, 43, 64, 119, 196, 111, 188, 251, 248, 53, 234, 59, 215, 28, 218, 13, 59, 120, 14, 4]);

            let P1 = &B * &s2;
            let P2 = &B * &s1;

            let R = &(&P1 * &s1) + &(&P2 * &s2);

            let R_multiscalar = vartime::multiscalar_mult(&[s1, s2], &[P1.into(), P2.into()]);

            assert_eq!(edwards::EdwardsPoint::from(R).compress(),
                       R_multiscalar.compress());
        }
    }
}

#[cfg(all(test, feature = "bench"))]
mod bench {
    use test::Bencher;
    use rand::OsRng;
    use super::*;

    use constants;
    use scalar::Scalar;

    #[bench]
    fn conversion_into__avx2_format(b: &mut Bencher) {
        let B = constants::ED25519_BASEPOINT_POINT;

        b.iter(|| ExtendedPoint::from(B));
    }

    #[bench]
    fn conversion_outof_avx2_format(b: &mut Bencher) {
        let B = constants::ED25519_BASEPOINT_POINT;
        let B_avx2 = ExtendedPoint::from(B);

        b.iter(|| edwards::EdwardsPoint::from(B_avx2));
    }

    #[bench]
    fn point_readdition(b: &mut Bencher) {
        let B = &constants::ED25519_BASEPOINT_TABLE;
        let P = ExtendedPoint::from(B * &Scalar::from_u64(83973422));
        let Q = ExtendedPoint::from(B * &Scalar::from_u64(98932328));
        let Q_cached = CachedPoint::from(Q);

        b.iter(|| &P + &Q_cached );
    }

    #[bench]
    fn point_addition(b: &mut Bencher) {
        let B = &constants::ED25519_BASEPOINT_TABLE;
        let P = ExtendedPoint::from(B * &Scalar::from_u64(83973422));
        let Q = ExtendedPoint::from(B * &Scalar::from_u64(98932328));

        b.iter(|| &P + &Q );
    }

    #[bench]
    fn point_doubling(b: &mut Bencher) {
        let B = &constants::ED25519_BASEPOINT_TABLE;
        let P = ExtendedPoint::from(B * &Scalar::from_u64(83973422));

        b.iter(|| P.double() );
    }

    #[bench]
    fn scalar_mult(b: &mut Bencher) {
        let B = &constants::ED25519_BASEPOINT_TABLE;
        let P = ExtendedPoint::from(B * &Scalar::from_u64(83973422));
        let s = Scalar::from_bits([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);

        b.iter(|| &P * &s );
    }

    #[bench]
    fn basepoint_table_creation(b: &mut Bencher) {
        let B = ExtendedPoint::from(constants::ED25519_BASEPOINT_POINT);

        b.iter(|| EdwardsBasepointTable::create(&B) );
    }

    #[bench]
    fn basepoint_mult(b: &mut Bencher) {
        let B = ExtendedPoint::from(constants::ED25519_BASEPOINT_POINT);
        let table = EdwardsBasepointTable::create(&B);
        let s = Scalar::from_bits([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);

        b.iter(|| &table * &s );
    }

    #[bench]
    fn ten_fold_scalar_mult(b: &mut Bencher) {
        let mut csprng: OsRng = OsRng::new().unwrap();
        // Create 10 random scalars
        let scalars: Vec<_> = (0..10).map(|_| Scalar::random(&mut csprng)).collect();
        // Create 10 points (by doing scalar mults)
        let B = &constants::ED25519_BASEPOINT_TABLE;
        let points: Vec<_> = scalars.iter().map(|s| B * s).collect();

        b.iter(|| multiscalar_mult(&scalars, &points));
    }

    mod vartime {
        use super::super::*;
        use super::{constants, Bencher, OsRng};

        #[bench]
        fn double_scalar_mult(b: &mut Bencher) {
            let mut csprng: OsRng = OsRng::new().unwrap();
            // Create 2 random scalars
            let s1 = Scalar::random(&mut csprng);
            let s2 = Scalar::random(&mut csprng);
            let P = &s1 * &constants::ED25519_BASEPOINT_TABLE;

            b.iter(|| vartime::double_scalar_mult_basepoint(&s2, &P, &s1) );
        }

        #[bench]
        fn ten_fold_scalar_mult(b: &mut Bencher) {
            let mut csprng: OsRng = OsRng::new().unwrap();
            // Create 10 random scalars
            let scalars: Vec<_> = (0..10).map(|_| Scalar::random(&mut csprng)).collect();
            // Create 10 points (by doing scalar mults)
            let B = &constants::ED25519_BASEPOINT_TABLE;
            let points: Vec<_> = scalars.iter().map(|s| B * s).collect();

            b.iter(|| vartime::multiscalar_mult(&scalars, &points));
        }
    }
}

