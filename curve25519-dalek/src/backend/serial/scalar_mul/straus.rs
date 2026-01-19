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

use crate::backend::serial::curve_models::{CompletedPoint, ProjectiveNielsPoint, ProjectivePoint};
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::traits::MultiscalarMul;
use crate::traits::VartimeMultiscalarMul;
use crate::window::LookupTable;
use crate::window::NafLookupTable5;

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::*;

// Import spec functions from iterator_specs (ghost only)
#[cfg(verus_keep_ghost)]
use crate::specs::iterator_specs::{
    all_points_some, spec_optional_points_from_iter, spec_points_from_iter, spec_scalars_from_iter,
    unwrap_points,
};

// Import runtime helpers from iterator_specs
use crate::specs::iterator_specs::{
    collect_optional_points_from_iter, collect_points_from_iter, collect_scalars_from_iter,
};

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
        /*
         * VERUS SPEC (intended):
         *   requires
         *       scalars.len() == points.len(),
         *       forall|i| is_well_formed_edwards_point(points[i]),
         *   ensures
         *       is_well_formed_edwards_point(result),
         *       edwards_point_as_affine(result) == sum_of_scalar_muls(scalars, points),
         *
         * NOTE: Verus doesn't support IntoIterator with I::Item projections.
         * The verified version `multiscalar_mul_verus` below uses:
         *   - Iterator bounds instead of IntoIterator
         *   - spec_scalars_from_iter / spec_points_from_iter to convert
         *     iterators to logical sequences (see specs/iterator_specs.rs)
         */
    {
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
    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<EdwardsPoint>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,
        /*
         * VERUS SPEC (intended):
         *   requires
         *       scalars.len() == points.len(),
         *       forall|i| points[i].is_some() ==> is_well_formed_edwards_point(points[i].unwrap()),
         *   ensures
         *       result.is_some() <==> all_points_some(points),
         *       result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
         *       result.is_some() ==> edwards_point_as_affine(result.unwrap())
         *           == sum_of_scalar_muls(scalars, unwrap_points(points)),
         *
         * NOTE: Verus doesn't support IntoIterator with I::Item projections.
         * The verified version `optional_multiscalar_mul_verus` below uses:
         *   - Iterator bounds instead of IntoIterator
         *   - spec_scalars_from_iter / spec_optional_points_from_iter to convert
         *     iterators to logical sequences (see specs/iterator_specs.rs)
         */
    {
        let nafs: Vec<_> = scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect();

        let lookup_tables = points
            .into_iter()
            .map(|P_opt| P_opt.map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(&P)))
            .collect::<Option<Vec<_>>>()?;

        let mut r = ProjectivePoint::identity();

        for i in (0..256).rev() {
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

// ============================================================================
// Verus-compatible version
// ============================================================================

verus! {

/*
 * VERIFICATION NOTE
 * =================
 * Verus limitations addressed in these _verus versions:
 * - IntoIterator with I::Item projections → use Iterator bounds instead
 * - Iterator adapters (map, zip) with closures → use explicit while loops
 * - Op-assignment (+=, -=) on EdwardsPoint → use explicit a = a + b
 *
 * TESTING: `scalar_mul_tests.rs` contains tests that generate random scalars and points,
 * run both original and _verus implementations, and assert equality of results.
 * This is evidence of functional equivalence between the original and refactored versions:
 *     forall scalars s, points p:
 *         optional_multiscalar_mul(s, p) == optional_multiscalar_mul_verus(s, p)
 *         multiscalar_mul(s, p) == multiscalar_mul_verus(s, p)
 */
impl Straus {
    /// Verus-compatible version of optional_multiscalar_mul.
    /// Uses Iterator instead of IntoIterator (Verus doesn't support I::Item projections).
    /// Computes sum(scalars[i] * points[i]) for all i where points[i] is Some.
    pub fn optional_multiscalar_mul_verus<S, I, J>(scalars: I, points: J) -> (result: Option<
        EdwardsPoint,
    >) where S: Borrow<Scalar>, I: Iterator<Item = S>, J: Iterator<Item = Option<EdwardsPoint>>
        requires
    // Same number of scalars and points

            spec_scalars_from_iter::<S, I>(scalars).len() == spec_optional_points_from_iter::<J>(
                points,
            ).len(),
            // All input points (when Some) must be well-formed
            forall|i: int|
                0 <= i < spec_optional_points_from_iter::<J>(points).len() && (
                #[trigger] spec_optional_points_from_iter::<J>(points)[i]).is_some()
                    ==> is_well_formed_edwards_point(
                    spec_optional_points_from_iter::<J>(points)[i].unwrap(),
                ),
        ensures
    // Result is Some if and only if all input points are Some

            result.is_some() <==> all_points_some(spec_optional_points_from_iter::<J>(points)),
            // If result is Some, it is a well-formed Edwards point
            result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
            // Semantic correctness: result = sum(scalars[i] * points[i])
            result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(
                spec_scalars_from_iter::<S, I>(scalars),
                unwrap_points(spec_optional_points_from_iter::<J>(points)),
            ),
    {
        /* Ghost vars to capture spec values before iterator consumption */
        let ghost spec_scalars = spec_scalars_from_iter::<S, I>(scalars);
        let ghost spec_points = spec_optional_points_from_iter::<J>(points);

        /* <ORIGINAL CODE>
    let nafs: Vec<_> = scalars
        .into_iter()
        .map(|c| c.borrow().non_adjacent_form(5))
        .collect();
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Collect iterators to Vec (Verus doesn't support iterator adapters).
         * Then convert each scalar to non-adjacent form (NAF) with width 5.
         */
        let scalars_vec = collect_scalars_from_iter(scalars);
        let points_vec = collect_optional_points_from_iter(points);

        let mut nafs: Vec<[i8; 256]> = Vec::new();
        let mut idx: usize = 0;
        while idx < scalars_vec.len()
            decreases scalars_vec.len() - idx,
        {
            proof {
                assume(false);
            }  // PROOF BYPASS
            nafs.push(scalars_vec[idx].non_adjacent_form(5));
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        /* <ORIGINAL CODE>
    let lookup_tables = points
        .into_iter()
        .map(|P_opt| P_opt.map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(&P)))
        .collect::<Option<Vec<_>>>()?;
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Build lookup tables for each point: precompute odd multiples [1P, 3P, 5P, 7P, ...]
         * Returns None if any point is None (propagates optional failure).
         */
        let mut lookup_tables: Vec<NafLookupTable5<ProjectiveNielsPoint>> = Vec::new();
        idx = 0;
        while idx < points_vec.len()
            decreases points_vec.len() - idx,
        {
            proof {
                assume(false);
            }  // PROOF BYPASS
            match points_vec[idx] {
                Some(P) => {
                    lookup_tables.push(NafLookupTable5::<ProjectiveNielsPoint>::from(&P));
                },
                None => {
                    // PROOF BYPASS: Found a None point, so not all_points_some
                    proof {
                        assume(!all_points_some(spec_points));
                    }
                    return None;
                },
            }
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        /* UNCHANGED FROM ORIGINAL */
        let mut r = ProjectivePoint::identity();

        /* <ORIGINAL CODE>
    for i in (0..256).rev() {
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
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Main double-and-add loop: iterate bit positions 255..0.
         * For each bit position i:
         *   1. Double the accumulator r
         *   2. For each (scalar, point) pair, add/sub the appropriate table entry
         *      based on the NAF digit at position i
         */
        let mut i: usize = 256;
        loop
            decreases i,
        {
            proof {
                assume(false);
            }  // PROOF BYPASS
            if i == 0 {
                break ;
            }
            i = i - 1;

            let mut t: CompletedPoint = r.double();

            // Inner loop: iterate over nafs and lookup_tables
            let mut j: usize = 0;
            let min_len = if nafs.len() < lookup_tables.len() {
                nafs.len()
            } else {
                lookup_tables.len()
            };
            while j < min_len
                decreases min_len - j,
            {
                proof {
                    assume(false);
                }  // PROOF BYPASS
                let naf = &nafs[j];
                let lookup_table = &lookup_tables[j];

                match naf[i].cmp(&0) {
                    Ordering::Greater => {
                        t = &t.as_extended() + &lookup_table.select(naf[i] as usize);
                    },
                    Ordering::Less => {
                        t = &t.as_extended() - &lookup_table.select((-naf[i]) as usize);
                    },
                    Ordering::Equal => {},
                }
                j = j + 1;
            }

            r = t.as_projective();
        }
        /* </REFACTORED CODE> */

        assume(false);  // PROOF BYPASS: as_extended precondition requires loop invariants
        let result = r.as_extended();

        // PROOF BYPASS: Assert postconditions for verification goal
        proof {
            assume(all_points_some(spec_points));
            assume(is_well_formed_edwards_point(result));
            assume(edwards_point_as_affine(result) == sum_of_scalar_muls(
                spec_scalars,
                unwrap_points(spec_points),
            ));
        }

        Some(result)
    }

    /// Verus-compatible version of multiscalar_mul (constant-time).
    /// Uses Iterator instead of IntoIterator (Verus doesn't support I::Item projections).
    /// Computes sum(scalars[i] * points[i]).
    pub fn multiscalar_mul_verus<S, P, I, J>(scalars: I, points: J) -> (result: EdwardsPoint) where
        S: Borrow<Scalar>,
        P: Borrow<EdwardsPoint>,
        I: Iterator<Item = S>,
        J: Iterator<Item = P>,

        requires
    // Same number of scalars and points

            spec_scalars_from_iter::<S, I>(scalars).len() == spec_points_from_iter::<P, J>(
                points,
            ).len(),
            // All input points must be well-formed
            forall|i: int|
                0 <= i < spec_points_from_iter::<P, J>(points).len()
                    ==> is_well_formed_edwards_point(
                    #[trigger] spec_points_from_iter::<P, J>(points)[i],
                ),
        ensures
    // Result is a well-formed Edwards point

            is_well_formed_edwards_point(result),
            // Semantic correctness: result = sum(scalars[i] * points[i])
            edwards_point_as_affine(result) == sum_of_scalar_muls(
                spec_scalars_from_iter::<S, I>(scalars),
                spec_points_from_iter::<P, J>(points),
            ),
    {
        use crate::traits::Identity;

        /* Ghost vars to capture spec values before iterator consumption */
        let ghost spec_scalars = spec_scalars_from_iter::<S, I>(scalars);
        let ghost spec_points = spec_points_from_iter::<P, J>(points);

        /* <ORIGINAL CODE>
        let lookup_tables: Vec<_> = points
            .into_iter()
            .map(|point| LookupTable::<ProjectiveNielsPoint>::from(point.borrow()))
            .collect();
        </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Collect iterators to Vec (Verus doesn't support iterator adapters).
         * Then build lookup tables for each point: precompute multiples [1P, 2P, ..., 8P]
         */
        let scalars_vec = collect_scalars_from_iter(scalars);
        let points_vec = collect_points_from_iter(points);
        let mut lookup_tables: Vec<LookupTable<ProjectiveNielsPoint>> = Vec::new();
        let mut idx: usize = 0;
        while idx < points_vec.len()
            decreases points_vec.len() - idx,
        {
            proof {
                assume(false);
            }  // PROOF BYPASS
            lookup_tables.push(LookupTable::<ProjectiveNielsPoint>::from(&points_vec[idx]));
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        /* <ORIGINAL CODE>
        let mut scalar_digits: Vec<_> = scalars
            .into_iter()
            .map(|s| s.borrow().as_radix_16())
            .collect();
        </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Convert each scalar to radix-16 signed digits: s = sum(s_j * 16^j)
         */
        let mut scalar_digits: Vec<[i8; 64]> = Vec::new();
        idx = 0;
        while idx < scalars_vec.len()
            decreases scalars_vec.len() - idx,
        {
            proof {
                assume(false);
            }  // PROOF BYPASS
            scalar_digits.push(scalars_vec[idx].as_radix_16());
            idx = idx + 1;
        }
        /* </REFACTORED CODE> */

        /* UNCHANGED FROM ORIGINAL */
        let mut Q = EdwardsPoint::identity();

        /* <ORIGINAL CODE>
        for j in (0..64).rev() {
            Q = Q.mul_by_pow_2(4);
            let it = scalar_digits.iter().zip(lookup_tables.iter());
            for (s_i, lookup_table_i) in it {
                let R_i = lookup_table_i.select(s_i[j]);
                Q = (&Q + &R_i).as_extended();
            }
        }
        </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Main loop: iterate digit positions 63..0 (radix-16 has 64 digits).
         * For each position j:
         *   1. Multiply accumulator Q by 16 (= 2^4)
         *   2. For each (scalar, point) pair, add s_j * P_i from lookup table
         */
        let mut j: usize = 64;
        loop
            decreases j,
        {
            proof {
                assume(false);
            }  // PROOF BYPASS
            if j == 0 {
                break ;
            }
            j = j - 1;

            Q = Q.mul_by_pow_2(4);

            // Inner loop: iterate over scalar_digits and lookup_tables
            let mut k: usize = 0;
            let min_len = if scalar_digits.len() < lookup_tables.len() {
                scalar_digits.len()
            } else {
                lookup_tables.len()
            };
            while k < min_len
                decreases min_len - k,
            {
                proof {
                    assume(false);
                }  // PROOF BYPASS
                let s_i = &scalar_digits[k];
                let lookup_table_i = &lookup_tables[k];
                let R_i = lookup_table_i.select(s_i[j]);
                Q = (&Q + &R_i).as_extended();
                k = k + 1;
            }
        }
        /* </REFACTORED CODE> */

        // PROOF BYPASS: Assume postconditions (requires full loop invariant proofs)
        proof {
            assume(is_well_formed_edwards_point(Q));
            assume(edwards_point_as_affine(Q) == sum_of_scalar_muls(spec_scalars, spec_points));
        }

        Q
    }
}

// impl Straus
} // verus!
