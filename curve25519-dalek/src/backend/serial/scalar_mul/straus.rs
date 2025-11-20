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

//! Implementation of the interleaved window method, also known as Straus' method.

#![allow(non_snake_case)]

use alloc::vec::Vec;

use core::borrow::Borrow;
use core::cmp::Ordering;

use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::MultiscalarMul;
use crate::traits::VartimeMultiscalarMul;

/// Perform multiscalar multiplication by the interleaved window
/// method, also known as Straus' method (since it was apparently
/// [first published][solution] by Straus in 1964, as a solution to [a
/// problem][problem] posted in the American Mathematical Monthly in
/// 1963).
///
/// It is easy enough to reinvent, and has been repeatedly.  The basic
/// idea is that when computing
/// \\[
/// Q = s_1 P_1 + \cdots + s_n P_n
/// \\]
/// by means of additions and doublings, the doublings can be shared
/// across the \\( P_i \\\).
///
/// We implement two versions, a constant-time algorithm using fixed
/// windows and a variable-time algorithm using sliding windows.  They
/// are slight variations on the same idea, and are described in more
/// detail in the respective implementations.
///
/// [solution]: https://www.jstor.org/stable/2310929
/// [problem]: https://www.jstor.org/stable/2312273
pub struct Straus {}

impl MultiscalarMul for Straus {
    type Point = EdwardsPoint;

    /// Constant-time Straus using a fixed window of size \\(4\\).
    ///
    /// Our goal is to compute
    /// \\[
    /// Q = s_1 P_1 + \cdots + s_n P_n.
    /// \\]
    ///
    /// For each point \\( P_i \\), precompute a lookup table of
    /// \\[
    /// P_i, 2P_i, 3P_i, 4P_i, 5P_i, 6P_i, 7P_i, 8P_i.
    /// \\]
    ///
    /// For each scalar \\( s_i \\), compute its radix-\\(2^4\\)
    /// signed digits \\( s_{i,j} \\), i.e.,
    /// \\[
    ///    s_i = s_{i,0} + s_{i,1} 16^1 + ... + s_{i,63} 16^{63},
    /// \\]
    /// with \\( -8 \leq s_{i,j} < 8 \\).  Since \\( 0 \leq |s_{i,j}|
    /// \leq 8 \\), we can retrieve \\( s_{i,j} P_i \\) from the
    /// lookup table with a conditional negation: using signed
    /// digits halves the required table size.
    ///
    /// Then as in the single-base fixed window case, we have
    /// \\[
    /// \begin{aligned}
    /// s_i P_i &= P_i (s_{i,0} +     s_{i,1} 16^1 + \cdots +     s_{i,63} 16^{63})   \\\\
    /// s_i P_i &= P_i s_{i,0} + P_i s_{i,1} 16^1 + \cdots + P_i s_{i,63} 16^{63}     \\\\
    /// s_i P_i &= P_i s_{i,0} + 16(P_i s_{i,1} + 16( \cdots +16P_i s_{i,63})\cdots )
    /// \end{aligned}
    /// \\]
    /// so each \\( s_i P_i \\) can be computed by alternately adding
    /// a precomputed multiple \\( P_i s_{i,j} \\) of \\( P_i \\) and
    /// repeatedly doubling.
    ///
    /// Now consider the two-dimensional sum
    /// \\[
    /// \begin{aligned}
    /// s\_1 P\_1 &=& P\_1 s\_{1,0} &+& 16 (P\_1 s\_{1,1} &+& 16 ( \cdots &+& 16 P\_1 s\_{1,63}&) \cdots ) \\\\
    ///     +     & &      +        & &      +            & &             & &     +            &           \\\\
    /// s\_2 P\_2 &=& P\_2 s\_{2,0} &+& 16 (P\_2 s\_{2,1} &+& 16 ( \cdots &+& 16 P\_2 s\_{2,63}&) \cdots ) \\\\
    ///     +     & &      +        & &      +            & &             & &     +            &           \\\\
    /// \vdots    & &  \vdots       & &   \vdots          & &             & &  \vdots          &           \\\\
    ///     +     & &      +        & &      +            & &             & &     +            &           \\\\
    /// s\_n P\_n &=& P\_n s\_{n,0} &+& 16 (P\_n s\_{n,1} &+& 16 ( \cdots &+& 16 P\_n s\_{n,63}&) \cdots )
    /// \end{aligned}
    /// \\]
    /// The sum of the left-hand column is the result \\( Q \\); by
    /// computing the two-dimensional sum on the right column-wise,
    /// top-to-bottom, then right-to-left, we need to multiply by \\(
    /// 16\\) only once per column, sharing the doublings across all
    /// of the input points.
    fn multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<EdwardsPoint>,
    {
        use crate::backend::serial::curve_models::ProjectiveNielsPoint;
        use crate::traits::Identity;
        use crate::window::LookupTable;

        let lookup_tables: Vec<_> = points
            .into_iter()
            .map(|point| LookupTable::<ProjectiveNielsPoint>::from(point.borrow()))
            .collect();

        // This puts the scalar digits into a heap-allocated Vec.
        // To ensure that these are erased, pass ownership of the Vec into a
        // Zeroizing wrapper.
        #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
        let mut scalar_digits: Vec<_> = scalars
            .into_iter()
            .map(|s| s.borrow().as_radix_16())
            .collect();

        let mut Q = EdwardsPoint::identity();
        for j in (0..64).rev() {
            Q = Q.mul_by_pow_2(4);
            let it = scalar_digits.iter().zip(lookup_tables.iter());
            for (s_i, lookup_table_i) in it {
                // R_i = s_{i,j} * P_i
                let R_i = lookup_table_i.select(s_i[j]);
                // Q = Q + R_i
                Q = (&Q + &R_i).as_extended();
            }
        }

        #[cfg(feature = "zeroize")]
        zeroize::Zeroize::zeroize(&mut scalar_digits);

        Q
    }
}

impl VartimeMultiscalarMul for Straus {
    type Point = EdwardsPoint;

    /// Variable-time Straus using a non-adjacent form of width \\(5\\).
    ///
    /// This is completely similar to the constant-time code, but we
    /// use a non-adjacent form for the scalar, and do not do table
    /// lookups in constant time.
    ///
    /// The non-adjacent form has signed, odd digits.  Using only odd
    /// digits halves the table size (since we only need odd
    /// multiples), or gives fewer additions for the same table size.
    fn optional_multiscalar_mul<I, J>(
        scalars: I,
        points: J,
        scalar_bits: Option<usize>,
    ) -> Option<EdwardsPoint>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,
    {
        use crate::backend::serial::curve_models::{
            CompletedPoint, ProjectiveNielsPoint, ProjectivePoint,
        };
        use crate::traits::Identity;
        use crate::window::NafLookupTable5;

        let nafs: Vec<_> = scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect();

        let lookup_tables = points
            .into_iter()
            .map(|P_opt| P_opt.map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(&P)))
            .collect::<Option<Vec<_>>>()?;

        let mut r = ProjectivePoint::identity();

        let scalar_bits = scalar_bits.unwrap_or(256);
        for i in (0..scalar_bits).rev() {
            let mut t: CompletedPoint = r.double();

            for (naf, lookup_table) in nafs.iter().zip(lookup_tables.iter()) {
                match naf[i].cmp(&0) {
                    Ordering::Greater => {
                        t = &t.as_extended() + &lookup_table.select(naf[i] as usize)
                    }
                    Ordering::Less => t = &t.as_extended() - &lookup_table.select(-naf[i] as usize),
                    Ordering::Equal => {}
                }
            }

            r = t.as_projective();
        }

        Some(r.as_extended())
    }
}

#[cfg(test)]
mod tests {
    // Tests for Straus multiscalar multiplication behavior
    // Ensures scalars < 128 bits behave the same when passing
    // `scalar_bits = Some(128)` and `None` to the Straus implementation.

    use std::vec::Vec;

    use crate::{edwards::EdwardsPoint, scalar::Scalar, traits::VartimeMultiscalarMul};

    fn scalar_from_u128(x: u128) -> Scalar {
        let mut bytes = [0u8; 32];
        bytes[..16].copy_from_slice(&x.to_le_bytes());
        Scalar::from_bytes_mod_order(bytes)
    }

    #[test]
    fn straus_multiscalar_mul_128bit_same_as_default() {
        // Construct a small set of scalars all less than 2^128.
        let scalar_values: [u128; 8] = [
            1,
            2,
            3,
            0xFFFF_FFFF_FFFF_FFFFu128,
            (1u128 << 127) - 1,
            0x1234_5678_9ABC_DEF0u128,
            0x0F0F_F0F0_F0F0_0F0Fu128,
            0xDEAD_BEEF_DEAD_BEEFu128,
        ];

        let scalars: Vec<Scalar> = scalar_values.iter().map(|&v| scalar_from_u128(v)).collect();

        // Create a corresponding list of points (multiples of basepoint).
        let mut points: Vec<EdwardsPoint> = Vec::with_capacity(scalars.len());
        for (i, _s) in scalars.iter().enumerate() {
            // Use different base multipliers (i+10) to diversify points.
            let bp = EdwardsPoint::mul_base(&scalar_from_u128((i as u128) + 10));
            points.push(bp);
        }

        // Prepare iterators for the backend function: scalars and Option<EdwardsPoint>
        let scalar_iter = scalars.iter().cloned();
        let point_opts_some = points.iter().cloned().map(Some);

        // Compute with explicit 128 bits
        let res_with_128 = EdwardsPoint::optional_multiscalar_mul(
            scalar_iter.clone(),
            point_opts_some.clone(),
            Some(128),
        )
        .expect("optional_multiscalar_mul returned None with Some(128) flag");

        // Compute with default (None)
        let res_default = EdwardsPoint::optional_multiscalar_mul(
            scalar_iter.clone(),
            point_opts_some.clone(),
            None,
        )
        .expect("optional_multiscalar_mul returned None with None flag");

        assert_eq!(res_with_128.compress(), res_default.compress());
    }
}
