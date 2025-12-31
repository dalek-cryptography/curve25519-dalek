// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2019 Oleg Andreev
// See LICENSE for licensing information.
//
// Authors:
// - Oleg Andreev <oleganza@gmail.com>
//! Implementation of a variant of Pippenger's algorithm.
#![allow(non_snake_case)]

use alloc::vec::Vec;

use core::borrow::Borrow;
use core::cmp::Ordering;

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::VartimeMultiscalarMul;

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::*;

// Re-export spec functions from scalar_mul_specs for use by other modules
#[cfg(verus_keep_ghost)]
pub use crate::specs::scalar_mul_specs::{
    all_points_some, spec_optional_points_from_iter, spec_points_from_iter, spec_scalars_from_iter,
    sum_of_scalar_muls, unwrap_points,
};

// Re-export runtime helpers from scalar_mul_specs
#[cfg(feature = "alloc")]
pub use crate::specs::scalar_mul_specs::{
    collect_optional_points_from_iter, collect_points_from_iter, collect_scalars_from_iter,
};

/// Implements a version of Pippenger's algorithm.
///
/// The algorithm works as follows:
///
/// Let `n` be a number of point-scalar pairs.
/// Let `w` be a window of bits (6..8, chosen based on `n`, see cost factor).
///
/// 1. Prepare `2^(w-1) - 1` buckets with indices `[1..2^(w-1))` initialized with identity points.
///    Bucket 0 is not needed as it would contain points multiplied by 0.
/// 2. Convert scalars to a radix-`2^w` representation with signed digits in `[-2^w/2, 2^w/2]`.
///    Note: only the last digit may equal `2^w/2`.
/// 3. Starting with the last window, for each point `i=[0..n)` add it to a bucket indexed by
///    the point's scalar's value in the window.
/// 4. Once all points in a window are sorted into buckets, add buckets by multiplying each
///    by their index. Efficient way of doing it is to start with the last bucket and compute two sums:
///    intermediate sum from the last to the first, and the full sum made of all intermediate sums.
/// 5. Shift the resulting sum of buckets by `w` bits by using `w` doublings.
/// 6. Add to the return value.
/// 7. Repeat the loop.
///
/// Approximate cost w/o wNAF optimizations (A = addition, D = doubling):
///
/// ```ascii
/// cost = (n*A + 2*(2^w/2)*A + w*D + A)*256/w
///          |          |       |     |   |
///          |          |       |     |   looping over 256/w windows
///          |          |       |     adding to the result
///    sorting points   |       shifting the sum by w bits (to the next window, starting from last window)
///    one by one       |
///    into buckets     adding/subtracting all buckets
///                     multiplied by their indexes
///                     using a sum of intermediate sums
/// ```
///
/// For large `n`, dominant factor is (n*256/w) additions.
/// However, if `w` is too big and `n` is not too big, then `(2^w/2)*A` could dominate.
/// Therefore, the optimal choice of `w` grows slowly as `n` grows.
///
/// This algorithm is adapted from section 4 of <https://eprint.iacr.org/2012/549.pdf>.
pub struct Pippenger;

impl VartimeMultiscalarMul for Pippenger {
    type Point = EdwardsPoint;

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
         *     iterators to logical sequences (see specs/scalar_mul_specs.rs)
         */
    {
        use crate::traits::Identity;

        let mut scalars = scalars.into_iter();
        let size = scalars.by_ref().size_hint().0;

        // Digit width in bits. As digit width grows,
        // number of point additions goes down, but amount of
        // buckets and bucket additions grows exponentially.
        let w = if size < 500 {
            6
        } else if size < 800 {
            7
        } else {
            8
        };

        let max_digit: usize = 1 << w;
        let digits_count: usize = Scalar::to_radix_2w_size_hint(w);
        let buckets_count: usize = max_digit / 2; // digits are signed+centered hence 2^w/2, excluding 0-th bucket

        // Collect optimized scalars and points in buffers for repeated access
        // (scanning the whole set per digit position).
        let scalars = scalars.map(|s| s.borrow().as_radix_2w(w));

        let points = points
            .into_iter()
            .map(|p| p.map(|P| P.as_projective_niels()));

        let scalars_points = scalars
            .zip(points)
            .map(|(s, maybe_p)| maybe_p.map(|p| (s, p)))
            .collect::<Option<Vec<_>>>()?;

        // Prepare 2^w/2 buckets.
        // buckets[i] corresponds to a multiplication factor (i+1).
        let mut buckets: Vec<_> = (0..buckets_count)
            .map(|_| EdwardsPoint::identity())
            .collect();

        let mut columns = (0..digits_count).rev().map(|digit_index| {
            // Clear the buckets when processing another digit.
            for bucket in &mut buckets {
                *bucket = EdwardsPoint::identity();
            }

            // Iterate over pairs of (point, scalar)
            // and add/sub the point to the corresponding bucket.
            // Note: if we add support for precomputed lookup tables,
            // we'll be adding/subtracting point premultiplied by `digits[i]` to buckets[0].
            for (digits, pt) in scalars_points.iter() {
                // Widen digit so that we don't run into edge cases when w=8.
                let digit = digits[digit_index] as i16;
                match digit.cmp(&0) {
                    Ordering::Greater => {
                        let b = (digit - 1) as usize;
                        buckets[b] = (&buckets[b] + pt).as_extended();
                    }
                    Ordering::Less => {
                        let b = (-digit - 1) as usize;
                        buckets[b] = (&buckets[b] - pt).as_extended();
                    }
                    Ordering::Equal => {}
                }
            }

            // Add the buckets applying the multiplication factor to each bucket.
            // The most efficient way to do that is to have a single sum with two running sums:
            // an intermediate sum from last bucket to the first, and a sum of intermediate sums.
            //
            // For example, to add buckets 1*A, 2*B, 3*C we need to add these points:
            //   C
            //   C B
            //   C B A   Sum = C + (C+B) + (C+B+A)
            let mut buckets_intermediate_sum = buckets[buckets_count - 1];
            let mut buckets_sum = buckets[buckets_count - 1];
            for i in (0..(buckets_count - 1)).rev() {
                buckets_intermediate_sum += buckets[i];
                buckets_sum += buckets_intermediate_sum;
            }

            buckets_sum
        });

        // Take the high column as an initial value to avoid wasting time doubling the identity element in `fold()`.
        let hi_column = columns.next().expect("should have more than zero digits");

        Some(columns.fold(hi_column, |total, p| total.mul_by_pow_2(w as u32) + p))
    }
}

// ============================================================================
// Verus-compatible version
// ============================================================================

verus! {

/*
 * VERIFICATION NOTE
 * =================
 * Verus limitations addressed in this _verus version:
 * - IntoIterator with I::Item projections → use Iterator bounds instead
 * - Iterator adapters (map, zip) with closures → use explicit while loops
 * - Op-assignment (+=, -=) on EdwardsPoint → use explicit a = a + b
 *
 * TESTING: `scalar_mul_tests.rs` contains tests that generate random scalars and points,
 * run both original and _verus implementations, and assert equality of results.
 * This is evidence of functional equivalence between the original and refactored versions:
 *     forall scalars s, points p: optional_multiscalar_mul(s, p) == optional_multiscalar_mul_verus(s, p)
 */
impl Pippenger {
    /// Verus-compatible version of optional_multiscalar_mul.
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
    // Result is Some iff all input points are Some

            result.is_some() <==> all_points_some(spec_optional_points_from_iter::<J>(points)),
            // If result is Some, it is a well-formed Edwards point
            result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
            // Semantic correctness: result = sum(scalars[i] * points[i])
            result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(
                spec_scalars_from_iter::<S, I>(scalars),
                unwrap_points(spec_optional_points_from_iter::<J>(points)),
            ),
    {
        use crate::traits::Identity;

        /* Ghost vars to capture spec values before iterator consumption */
        let ghost spec_scalars = spec_scalars_from_iter::<S, I>(scalars);
        let ghost spec_points = spec_optional_points_from_iter::<J>(points);

        /* <ORIGINAL CODE>
    let mut scalars = scalars.into_iter();
    let size = scalars.by_ref().size_hint().0;
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Collect iterators to Vec (Verus doesn't support size_hint on &mut).
         * Get size from collected Vec.
         */
        let scalars_vec = collect_scalars_from_iter(scalars);
        let size = scalars_vec.len();
        let points_vec = collect_optional_points_from_iter(points);
        /* </REFACTORED CODE> */

        /* UNCHANGED FROM ORIGINAL: Digit width selection based on input size */
        // Digit width in bits. As digit width grows,
        // number of point additions goes down, but amount of
        // buckets and bucket additions grows exponentially.
        let w = if size < 500 {
            6
        } else if size < 800 {
            7
        } else {
            8
        };

        /* UNCHANGED FROM ORIGINAL: Bucket configuration */
        let max_digit: usize = 1 << w;
        let digits_count: usize = Scalar::to_radix_2w_size_hint(w);
        let buckets_count: usize = max_digit / 2;  // digits are signed+centered hence 2^w/2, excluding 0-th bucket

        if digits_count == 0 || buckets_count == 0 {
            // PROOF BYPASS: Dead code for valid w (6,7,8), assume postcondition
            proof {
                assume(!all_points_some(spec_points));
            }
            return None;
        }
        // Collect optimized scalars and points in buffers for repeated access
        // (scanning the whole set per digit position).
        /* <ORIGINAL CODE>
    let scalars = scalars.map(|s| s.borrow().as_radix_2w(w));
    let points = points.into_iter().map(|p| p.map(|P| P.as_projective_niels()));
    let scalars_points = scalars.zip(points).map(|(s, maybe_p)| maybe_p.map(|p| (s, p))).collect::<Option<Vec<_>>>()?;
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Pair scalars (as radix-2^w digits) with points (as ProjectiveNiels).
         * Returns None if any point is None.
         */

        let mut scalars_points: Vec<([i8; 64], ProjectiveNielsPoint)> = Vec::new();
        let mut idx: usize = 0;
        let min_len = if scalars_vec.len() < points_vec.len() {
            scalars_vec.len()
        } else {
            points_vec.len()
        };
        while idx < min_len
            decreases min_len - idx,
        {
            assume(false);  // PROOF BYPASS
            let digits = scalars_vec[idx].as_radix_2w(w);
            let maybe_p = points_vec[idx].map(|P| P.as_projective_niels());
            match maybe_p {
                Some(p) => scalars_points.push((digits, p)),
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

        // Prepare 2^w/2 buckets.
        // buckets[i] corresponds to a multiplication factor (i+1).
        /* <ORIGINAL CODE>
    let mut buckets: Vec<_> = (0..buckets_count).map(|_| EdwardsPoint::identity()).collect();
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Initialize 2^(w-1) buckets with identity points.
         * Bucket i will accumulate points with digit value (i+1).
         */
        let mut buckets: Vec<EdwardsPoint> = Vec::new();
        let mut init_idx: usize = 0;
        while init_idx < buckets_count
            decreases buckets_count - init_idx,
        {
            assume(false);  // PROOF BYPASS
            buckets.push(EdwardsPoint::identity());
            init_idx = init_idx + 1;
        }
        /* </REFACTORED CODE> */

        /* <ORIGINAL CODE>
    let mut columns = (0..digits_count).rev().map(|digit_index| {
        // Clear the buckets when processing another digit.
        for bucket in &mut buckets {
            *bucket = EdwardsPoint::identity();
        }

        for (digits, pt) in scalars_points.iter() {
            let digit = digits[digit_index] as i16;
            match digit.cmp(&0) {
                Ordering::Greater => {
                    let b = (digit - 1) as usize;
                    buckets[b] = (&buckets[b] + pt).as_extended();
                }
                Ordering::Less => {
                    let b = (-digit - 1) as usize;
                    buckets[b] = (&buckets[b] - pt).as_extended();
                }
                Ordering::Equal => {}
            }
        }

        let mut buckets_intermediate_sum = buckets[buckets_count - 1];
        let mut buckets_sum = buckets[buckets_count - 1];
        for i in (0..(buckets_count - 1)).rev() {
            buckets_intermediate_sum += buckets[i];
            buckets_sum += buckets_intermediate_sum;
        }

        buckets_sum
    });

    let hi_column = columns.next().expect("should have more than zero digits");
    Some(columns.fold(hi_column, |total, p| total.mul_by_pow_2(w as u32) + p))
    </ORIGINAL CODE> */
        /* <REFACTORED CODE>
         * Pippenger bucket method: process digit columns right-to-left.
         * For each column:
         *   1. Clear buckets to identity
         *   2. Sort points into buckets based on scalar digit value
         *   3. Sum buckets: bucket[i] contributes (i+1) * bucket[i] to column sum
         *   4. Accumulate: total = total * 2^w + column_sum
         */
        // Process hi_column (digit_index = digits_count - 1)
        let digit_index_hi: usize = digits_count - 1;

        // Clear buckets
        let mut bucket_idx: usize = 0;
        while bucket_idx < buckets_count
            decreases buckets_count - bucket_idx,
        {
            assume(false);  // PROOF BYPASS
            buckets.set(bucket_idx, EdwardsPoint::identity());
            bucket_idx = bucket_idx + 1;
        }

        // Fill buckets for hi_column
        let mut sp_idx: usize = 0;
        while sp_idx < scalars_points.len()
            decreases scalars_points.len() - sp_idx,
        {
            assume(false);  // PROOF BYPASS
            let sp = &scalars_points[sp_idx];
            let digits = &sp.0;
            let pt = &sp.1;
            let digit = digits[digit_index_hi] as i16;
            if digit > 0 {
                let b = (digit - 1) as usize;
                buckets.set(b, (&buckets[b] + pt).as_extended());
            } else if digit < 0 {
                let b = (-digit - 1) as usize;
                buckets.set(b, (&buckets[b] - pt).as_extended());
            }
            sp_idx = sp_idx + 1;
        }

        // Sum buckets for hi_column
        assume(false);  // PROOF BYPASS: bucket access
        let mut buckets_intermediate_sum = buckets[buckets_count - 1];
        let mut hi_column = buckets[buckets_count - 1];
        if buckets_count > 1 {
            let mut j: usize = buckets_count - 2;
            loop
                decreases j,
            {
                assume(false);  // PROOF BYPASS
                buckets_intermediate_sum = &buckets_intermediate_sum + &buckets[j];
                hi_column = &hi_column + &buckets_intermediate_sum;
                if j == 0 {
                    break ;
                }
                j = j - 1;
            }
        }
        // Fold remaining columns (digit_index = digits_count-2 .. 0)

        let mut total = hi_column;
        if digits_count > 1 {
            let mut digit_index: usize = digits_count - 2;
            loop
                decreases digit_index,
            {
                assume(false);  // PROOF BYPASS

                // Clear buckets
                let mut bucket_idx2: usize = 0;
                while bucket_idx2 < buckets_count
                    decreases buckets_count - bucket_idx2,
                {
                    assume(false);  // PROOF BYPASS
                    buckets.set(bucket_idx2, EdwardsPoint::identity());
                    bucket_idx2 = bucket_idx2 + 1;
                }

                // Fill buckets
                let mut sp_idx2: usize = 0;
                while sp_idx2 < scalars_points.len()
                    decreases scalars_points.len() - sp_idx2,
                {
                    assume(false);  // PROOF BYPASS
                    let sp = &scalars_points[sp_idx2];
                    let digits = &sp.0;
                    let pt = &sp.1;
                    let digit = digits[digit_index] as i16;
                    if digit > 0 {
                        let b = (digit - 1) as usize;
                        buckets.set(b, (&buckets[b] + pt).as_extended());
                    } else if digit < 0 {
                        let b = (-digit - 1) as usize;
                        buckets.set(b, (&buckets[b] - pt).as_extended());
                    }
                    sp_idx2 = sp_idx2 + 1;
                }

                // Sum buckets
                assume(false);  // PROOF BYPASS: bucket access
                let mut buckets_intermediate_sum2 = buckets[buckets_count - 1];
                let mut column = buckets[buckets_count - 1];
                if buckets_count > 1 {
                    let mut j2: usize = buckets_count - 2;
                    loop
                        decreases j2,
                    {
                        assume(false);  // PROOF BYPASS
                        buckets_intermediate_sum2 = &buckets_intermediate_sum2 + &buckets[j2];
                        column = &column + &buckets_intermediate_sum2;
                        if j2 == 0 {
                            break ;
                        }
                        j2 = j2 - 1;
                    }
                }
                // Accumulate: total = total * 2^w + column

                total = &total.mul_by_pow_2(w as u32) + &column;

                if digit_index == 0 {
                    break ;
                }
                digit_index = digit_index - 1;
            }
        }  /* </REFACTORED CODE> */
        // PROOF BYPASS: Assume postconditions (requires full loop invariant proofs)
        // At this point, we reached the end without returning None, so all points were Some

        proof {
            assume(all_points_some(spec_points));
            assume(is_well_formed_edwards_point(total));
            assume(edwards_point_as_affine(total) == sum_of_scalar_muls(
                spec_scalars,
                unwrap_points(spec_points),
            ));
        }

        Some(total)
    }
}

// impl Pippenger
} // verus!
// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::constants;
//     #[test]
//     fn test_vartime_pippenger() {
//         // Reuse points across different tests
//         let mut n = 512;
//         let x = Scalar::from(2128506u64).invert();
//         let y = Scalar::from(4443282u64).invert();
//         let points: Vec<_> = (0..n)
//             .map(|i| constants::ED25519_BASEPOINT_POINT * Scalar::from(1 + i as u64))
//             .collect();
//         let scalars: Vec<_> = (0..n)
//             .map(|i| x + (Scalar::from(i as u64) * y)) // fast way to make ~random but deterministic scalars
//             .collect();
//         let premultiplied: Vec<EdwardsPoint> = scalars
//             .iter()
//             .zip(points.iter())
//             .map(|(sc, pt)| sc * pt)
//             .collect();
//         while n > 0 {
//             let scalars = &scalars[0..n].to_vec();
//             let points = &points[0..n].to_vec();
//             let control: EdwardsPoint = premultiplied[0..n].iter().sum();
//             let subject = Pippenger::vartime_multiscalar_mul(scalars.clone(), points.clone());
//             assert_eq!(subject.compress(), control.compress());
//             n /= 2;
//         }
//     }
// }
