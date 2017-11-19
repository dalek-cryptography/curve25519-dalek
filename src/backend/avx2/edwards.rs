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
use std::ops::{Add, Mul, Neg};

use stdsimd::simd::{u32x8, i32x8};

use subtle::ConditionallyAssignable;

use edwards;
use scalar::Scalar;

use traits::Identity;

use backend::avx2::field::FieldElement32x4;
use backend::avx2::field::P_TIMES_2;

/// A point on Curve25519, represented in an AVX2-friendly format.
#[derive(Copy, Clone, Debug)]
pub struct ExtendedPoint(FieldElement32x4);

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

impl ConditionallyAssignable for ExtendedPoint {
    fn conditional_assign(&mut self, other: &ExtendedPoint, choice: u8) {
        self.0.conditional_assign(&other.0, choice);
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

impl<'a> Neg for &'a ExtendedPoint {
    type Output = ExtendedPoint;

    fn neg(self) -> ExtendedPoint {
        let mut neg = *self;
        neg.0.mask_negate(0b10100101);
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
            t0.0[0] = _mm256_blend_epi32(t0.0[0].into(), P.0[0].into(), 0b01011111).into();
            t0.0[1] = _mm256_blend_epi32(t0.0[1].into(), P.0[1].into(), 0b01011111).into();
            t0.0[2] = _mm256_blend_epi32(t0.0[2].into(), P.0[2].into(), 0b01011111).into();
            t0.0[3] = _mm256_blend_epi32(t0.0[3].into(), P.0[3].into(), 0b01011111).into();
            t0.0[4] = _mm256_blend_epi32(t0.0[4].into(), P.0[4].into(), 0b01011111).into();

            t1 = t0.square();

            // Now t1 = (S1 S2 S3 S4)

            let c0 = u32x8::new(0,0,2,2,0,0,2,2); // (ABCD) -> (AAAA)
            let c1 = u32x8::new(1,1,3,3,1,1,3,3); // (ABCD) -> (BBBB)

            // Horror block goes here: we want to compute the following table:
            // We know that the bit-excess b is bounded by eps, since S1 S2 S3 S4
            // are the outputs of a squaring, so they're freshly reduced.
            // 
            //    + | S1 | S1 | S1 | S1 |  
            //    + | S2 |    |    | S2 |  
            //    + |    |    | S3 |    |  
            //    + |    |    | S3 |    |  
            //    + |    | 2p | 2p | 2p |  
            //    - |    | S2 | S2 |    |  
            //    - |    |    |    | S4 |  
            //    =======================  
            //        S5   S6   S8   S9    
            //
            // Bounds for even / odd limbs:
            //
            //    + |  2^26 |  2^26 |  2^26 |  2^26 |    + |  2^25 |  2^25 |  2^25 |  2^25 |  
            //    + |  2^26 |       |       |  2^26 |    + |  2^25 |       |       |  2^25 |  
            //    + |       |       |  2^26 |       |    + |       |       |  2^25 |       |  
            //    + |       |       |  2^26 |       |    + |       |       |  2^25 |       |  
            //    + |       |  2^27 |  2^27 |  2^27 |    + |       |  2^26 |  2^26 |  2^26 |  
            //    - |       |   0   |    0  |       |    - |       |    0  |    0  |       |  
            //    - |       |       |       |    0  |    - |       |       |       |    0  |  
            //    ===================================    ===================================
            //    <   2^27   2^27.59 2^28.33   2^28           2^26  2^26.59 2^27.33  2^27
            //
            // So, the bit-excess for (S5 S6 S8 S9) is (1, 1.59, 2.33, 2).
            //
            // However the multiplication routine only allows (1.75, 1.75, 1.75, 1.75).
            //
            // This is because we need to have 19*y[i] < 2^32.  Otherwise I think we could get b < 2.5.
            //
            // Can we tighten these bounds to avoid a reduction? Alternately, can we do better than
            // the 64-bit reduction that reduce32() calls internally?
            // 
            // Or, could we do the arithmetic on the intermediate [u64x4;10], then do
            // the reduction we'd need to do for the squaring?
            //
            // Also, can we do better than the mess below?
            for i in 0..5 {
                let zero = i32x8::splat(0);
                let S1 = _mm256_permutevar8x32_epi32(t1.0[i], c0);
                let S2 = _mm256_permutevar8x32_epi32(t1.0[i], c1);
                let S3_2 = _mm256_blend_epi32(zero, (t1.0[i] + t1.0[i]).into(), 0b01010000).into();
                t0.0[i] = (P_TIMES_2.0[i] + S3_2) + S1;
                t0.0[i] = t0.0[i] + _mm256_blend_epi32(zero, S2.into(), 0b10100101).into();
                let S4 = _mm256_blend_epi32(zero, t1.0[i].into(), 0b10100000);
                let sub = _mm256_blend_epi32(S2.into(), S4, 0b10100101).into();
                t0.0[i] = t0.0[i] - sub;
            }

            // This is really sad, see above
            t0.reduce32();

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

            for i in 0..5 {
                t0.0[i] = _mm256_permute2x128_si256(P.0[i].into(), Q.0[i].into(), 32).into();
            }

            t0.diff_sum();

            for i in 0..5 {
                t1.0[i] = _mm256_blend_epi32(t0.0[i].into(), P.0[i].into(), 0b11110000).into();
                t0.0[i] = _mm256_permute2x128_si256(t0.0[i].into(), Q.0[i].into(), 49).into();
            }

            let mut t2 = &t0 * &t1;
            
            t2.scale_by_curve_constants();
            
            for i in 0..5 {
                let swapped = _mm256_shuffle_epi32(t2.0[i].into(), 0b10_11_00_01);
                t2.0[i] = _mm256_blend_epi32(t2.0[i].into(), swapped, 0b11110000).into();
            }

            t2.diff_sum();

            let c0 = u32x8::new(0,5,2,7,5,0,7,2); // (ABCD) -> (ADDA)
            let c1 = u32x8::new(4,1,6,3,4,1,6,3); // (ABCD) -> (CBCB)

            for i in 0..5 {
                t0.0[i] = _mm256_permutevar8x32_epi32(t2.0[i], c0);
                t1.0[i] = _mm256_permutevar8x32_epi32(t2.0[i], c1);
            }

            ExtendedPoint(&t0 * &t1)
        }
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a ExtendedPoint {
    type Output = ExtendedPoint;
    /// Scalar multiplication: compute `scalar * self`.
    ///
    /// Uses a window of size 4.
    fn mul(self, scalar: &'b Scalar) -> ExtendedPoint {
        use traits::select_precomputed_point;

        // Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]
        let mut lookup_table: [ExtendedPoint; 8] = [*self; 8];
        for i in 0..7 {
            lookup_table[i+1] = self + &lookup_table[i];
        }

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
            // R = s_i * Q
            let R = select_precomputed_point(scalar_digits[i], &lookup_table);
            // Q = Q + R
            Q = &Q + &R;
        }
        Q
    }
}

#[derive(Clone)]
pub struct EdwardsBasepointTable(pub [[ExtendedPoint; 8]; 32]);

impl<'a, 'b> Mul<&'b Scalar> for &'a EdwardsBasepointTable {
    type Output = ExtendedPoint;

    /// Construct an `ExtendedPoint` from a `Scalar`, `scalar`, by
    /// computing the multiple `aB` of the basepoint `B`.
    ///
    /// Precondition: the scalar must be reduced.
    ///
    /// The computation proceeds as follows, as described on page 13
    /// of the Ed25519 paper.  Write the scalar `a` in radix 16 with
    /// coefficients in [-8,8), i.e.,
    ///
    ///    a = a_0 + a_1*16^1 + ... + a_63*16^63,
    ///
    /// with -8 ≤ a_i < 8.  Then
    ///
    ///    a*B = a_0*B + a_1*16^1*B + ... + a_63*16^63*B.
    ///
    /// Grouping even and odd coefficients gives
    ///
    ///    a*B =       a_0*16^0*B + a_2*16^2*B + ... + a_62*16^62*B
    ///              + a_1*16^1*B + a_3*16^3*B + ... + a_63*16^63*B
    ///        =      (a_0*16^0*B + a_2*16^2*B + ... + a_62*16^62*B)
    ///          + 16*(a_1*16^0*B + a_3*16^2*B + ... + a_63*16^62*B).
    ///
    /// We then use the `select_precomputed_point` function, which
    /// takes `-8 ≤ x < 8` and `[16^2i * B, ..., 8 * 16^2i * B]`,
    /// and returns `x * 16^2i * B` in constant time.
    fn mul(self, scalar: &'b Scalar) -> ExtendedPoint {
        use traits::select_precomputed_point;
        let e = scalar.to_radix_16();
        let mut h = ExtendedPoint::identity();

        for i in (0..64).filter(|x| x % 2 == 1) {
            h = &h + &select_precomputed_point(e[i], &self.0[i/2]);
        }

        h = h.mult_by_pow_2(4);

        for i in (0..64).filter(|x| x % 2 == 0) {
            h = &h + &select_precomputed_point(e[i], &self.0[i/2]);
        }

        h
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
        // Create the table storage
        // XXX can we skip the initialization without too much unsafety?
        // stick 30K on the stack and call it a day.
        let mut table = EdwardsBasepointTable([[ExtendedPoint::identity(); 8]; 32]);
        let mut P = *basepoint;
        for i in 0..32 {
            // P = (16^2)^i * B
            let mut jP = P;
            for j in 1..9 {
                // table[i][j-1] is supposed to be j*(16^2)^i*B
                table.0[i][j-1] = jP;
                jP = &P + &jP;
            }
            P = P.mult_by_pow_2(8);
        }
        table
    }

    /// Get the basepoint for this table as an `ExtendedPoint`.
    pub fn basepoint(&self) -> ExtendedPoint {
        // self.0[0][0] has 1*(16^2)^0*B
        self.0[0][0]
    }
}

/// Given a vector of (possibly secret) scalars and a vector of
/// (possibly secret) points, compute `c_1 P_1 + ... + c_n P_n`.
///
/// This function has the same behaviour as
/// `vartime::multiscalar_mult` but is constant-time.
///
/// # Input
///
/// A vector of `Scalar`s and a vector of `ExtendedPoints`.  It is an
/// error to call this function with two vectors of different lengths.
///
/// XXX need to clear memory
#[cfg(any(feature = "alloc", feature = "std"))]
pub fn multiscalar_mult<'a, 'b, I, J>(scalars: I, points: J) -> ExtendedPoint
    where I: IntoIterator<Item = &'a Scalar>,
          J: IntoIterator<Item = &'b ExtendedPoint>
{
    use traits::select_precomputed_point;
    //assert_eq!(scalars.len(), points.len());

    let lookup_tables: Vec<_> = points.into_iter()
        .map(|P_i| {
            // Construct a lookup table of [P_i,2*P_i,3*P_i,4*P_i,5*P_i,6*P_i,7*P_i]
            let mut lookup_table: [ExtendedPoint; 8] = [*P_i; 8];
            for i in 0..7 {
                lookup_table[i+1] = P_i + &lookup_table[i];
            }
            lookup_table
        }).collect();

    // Setting s_i = i-th scalar, compute
    //
    //    s_i = s_{i,0} + s_{i,1}*16^1 + ... + s_{i,63}*16^63,
    //
    // with `-8 ≤ s_{i,j} < 8` for `0 ≤ j < 63` and `-8 ≤ s_{i,63} ≤ 8`.
    let scalar_digits_list: Vec<_> = scalars.into_iter()
        .map(|c| c.to_radix_16()).collect();

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
        let it = scalar_digits_list.iter().zip(lookup_tables.iter());
        for (s_i, lookup_table_i) in it {
            // R_i = s_{i,j} * P_i
            let R_i = select_precomputed_point(s_i[j], lookup_table_i);
            // Q = Q + R_i
            Q = &Q + &R_i;
        }
    }
    Q
}

pub mod vartime {
    //! Variable-time operations on curve points, useful for non-secret data.
    use super::*;

    /// Given a vector of public scalars and a vector of (possibly secret)
    /// points, compute `c_1 P_1 + ... + c_n P_n`.
    ///
    /// # Input
    ///
    /// A vector of `Scalar`s and a vector of `ExtendedPoints`.  It is an
    /// error to call this function with two vectors of different lengths.
    ///
    /// XXX need to clear memory
    #[cfg(any(feature = "alloc", feature = "std"))]
    pub fn multiscalar_mult<'a, 'b, I, J>(scalars: I, points: J) -> ExtendedPoint
        where I: IntoIterator<Item = &'a Scalar>,
              J: IntoIterator<Item = &'b ExtendedPoint>
    {
        //assert_eq!(scalars.len(), points.len());

        let nafs: Vec<_> = scalars.into_iter()
            .map(|c| c.non_adjacent_form()).collect();
        let odd_multiples: Vec<_> = points.into_iter()
            .map(|P| {
                // Construct a lookup table of [P_i,2*P_i,3*P_i,4*P_i,5*P_i,6*P_i,7*P_i]
                let P2 = P.double();
                let mut lookup_table: [ExtendedPoint; 8] = [*P; 8];
                for i in 0..7 {
                    lookup_table[i+1] = &P2 + &lookup_table[i];
                }
                lookup_table
            }).collect();

        let mut Q = ExtendedPoint::identity();

        for i in (0..255).rev() {
            Q = Q.double();

            for (naf, odd_multiple) in nafs.iter().zip(odd_multiples.iter()) {
                if naf[i] > 0 {
                    Q = &Q + &odd_multiple[( naf[i]/2) as usize];
                } else if naf[i] < 0 {
                    // XXX impl Sub
                    Q = &Q + &(-&odd_multiple[(-naf[i]/2) as usize]);
                }
            }
        }
        Q
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use constants;

    fn serial_add(P: edwards::ExtendedPoint, Q: edwards::ExtendedPoint) -> edwards::ExtendedPoint {
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
    fn vector_addition_vs_serial_addition_vs_edwards_extendedpoint() {
        use constants;
        use scalar::Scalar;

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

    fn serial_double(P: edwards::ExtendedPoint) -> edwards::ExtendedPoint {
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

        edwards::ExtendedPoint{X: X3, Y: Y3, Z: Z3, T: T3}
    }

    fn doubling_test_helper(P: edwards::ExtendedPoint) {
        let R1: edwards::ExtendedPoint = serial_double(P.into()).into();
        let R2: edwards::ExtendedPoint = ExtendedPoint::from(P).double().into();
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
        let P = edwards::ExtendedPoint::identity();
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
        let id1: edwards::ExtendedPoint = ExtendedPoint::identity().into();
        let id2: edwards::ExtendedPoint = edwards::ExtendedPoint::identity();
        assert_eq!(id1.compress(), id2.compress());
    }

    #[test]
    fn neg_vs_edwards_neg() {
        let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
        let Bneg = -&B;
        assert_eq!(edwards::ExtendedPoint::from(Bneg).compress(),
                   (-&constants::ED25519_BASEPOINT_POINT).compress());
    }

    #[test]
    fn scalar_mult_vs_edwards_scalar_mult() {
        let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
        // some random bytes
        let s = Scalar([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);

        let R1 = edwards::ExtendedPoint::from(&B * &s);
        let R2 = &constants::ED25519_BASEPOINT_TABLE * &s;

        assert_eq!(R1.compress(), R2.compress());
    }

    #[test]
    fn scalar_mult_vs_basepoint_table_scalar_mult() {
        let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
        let B_table = EdwardsBasepointTable::create(&B);
        // some random bytes
        let s = Scalar([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);

        let P1 = &B * &s;
        let P2 = &B_table * &s;

        assert_eq!(edwards::ExtendedPoint::from(P1).compress(),
                   edwards::ExtendedPoint::from(P2).compress());
    }

    #[test]
    fn multiscalar_mult_vs_adding_scalar_mults() {
        let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
        let s1 = Scalar([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);
        let s2 = Scalar([165, 30, 79, 89, 58, 24, 195, 245, 248, 146, 203, 236, 119, 43, 64, 119, 196, 111, 188, 251, 248, 53, 234, 59, 215, 28, 218, 13, 59, 120, 14, 4]);

        let P1 = &B * &s2;
        let P2 = &B * &s1;

        let R = &(&P1 * &s1) + &(&P2 * &s2);
        
        let R_multiscalar = multiscalar_mult(&[s1, s2], &[P1, P2]);

        assert_eq!(edwards::ExtendedPoint::from(R).compress(),
                   edwards::ExtendedPoint::from(R_multiscalar).compress());
    }

    mod vartime {
        use super::*;

        #[test]
        fn multiscalar_mult_vs_adding_scalar_mults() {
            let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
            let s1 = Scalar([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);
            let s2 = Scalar([165, 30, 79, 89, 58, 24, 195, 245, 248, 146, 203, 236, 119, 43, 64, 119, 196, 111, 188, 251, 248, 53, 234, 59, 215, 28, 218, 13, 59, 120, 14, 4]);

            let P1 = &B * &s2;
            let P2 = &B * &s1;

            let R = &(&P1 * &s1) + &(&P2 * &s2);
            
            let R_multiscalar = vartime::multiscalar_mult(&[s1, s2], &[P1, P2]);

            assert_eq!(edwards::ExtendedPoint::from(R).compress(),
                       edwards::ExtendedPoint::from(R_multiscalar).compress());
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
        let s = Scalar([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);

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
        let s = Scalar([233, 1, 233, 147, 113, 78, 244, 120, 40, 45, 103, 51, 224, 199, 189, 218, 96, 140, 211, 112, 39, 194, 73, 216, 173, 33, 102, 93, 76, 200, 84, 12]);

        b.iter(|| &table * &s );
    }

    #[bench]
    fn ten_fold_scalar_mult(b: &mut Bencher) {
        let mut csprng: OsRng = OsRng::new().unwrap();
        // Create 10 random scalars
        let scalars: Vec<_> = (0..10).map(|_| Scalar::random(&mut csprng)).collect();
        // Create 10 points (by doing scalar mults)
        let B = &constants::ED25519_BASEPOINT_POINT;
        let points: Vec<_> = scalars.iter().map(|s| ExtendedPoint::from(B * &s)).collect();

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
            let B: ExtendedPoint = constants::ED25519_BASEPOINT_POINT.into();
            let P = &B * &s1;

            b.iter(|| vartime::multiscalar_mult(&[s1, s2], &[B, P]));
        }

        #[bench]
        fn ten_fold_scalar_mult(b: &mut Bencher) {
            let mut csprng: OsRng = OsRng::new().unwrap();
            // Create 10 random scalars
            let scalars: Vec<_> = (0..10).map(|_| Scalar::random(&mut csprng)).collect();
            // Create 10 points (by doing scalar mults)
            let B = &constants::ED25519_BASEPOINT_POINT;
            let points: Vec<_> = scalars.iter().map(|s| ExtendedPoint::from(B * &s)).collect();

            b.iter(|| vartime::multiscalar_mult(&scalars, &points));
        }
    }
}

