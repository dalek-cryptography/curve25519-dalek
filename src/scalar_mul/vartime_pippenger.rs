// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
// - Oleg Andreev <oleganza@gmail.com>
#![allow(non_snake_case)]

//! Implements a version of Pippenger's algorithm.

use core::borrow::Borrow;

use curve_models::ProjectiveNielsPoint;
use edwards::EdwardsPoint;
use scalar::Scalar;

use traits::{Identity, VartimeMultiscalarMul};

/// Implements a version of Pippenger's algorithm.
/// See the trait implementation documentation for more details.
pub struct Pippenger;

#[cfg(any(feature = "alloc", feature = "std"))]
impl VartimeMultiscalarMul for Pippenger {
    type Point = EdwardsPoint;

    /// Perform variable-time, variable-base scalar multiplication using the Pippenger algorithm.
    ///
    /// The algorithm works as follows:
    ///
    /// Let `n` be a number of point-scalar pairs.
    /// Let `w` be a window of bits (5..15, chosen based on `n`, see cost factor).
    ///
    /// 1. Prepare `2^(w-1) - 1` buckets with indices `[1..2^(w-1))` initialized with identity point.
    ///    Bucket 0 is not needed as it will contain points multiplied by 0.
    /// 2. Convert scalars to a radix-`2^w` representation with signed digits in `[-2^w/2, 2^w/2]`.
    ///    Note: all but last digit will never be equal `2^w/2`, but that's irrelevant to us here.
    /// 3. Starting with the last window, for each point `i=[0..n)` add it to a a bucket indexed by
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
    fn vartime_multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<EdwardsPoint>,
    {
        let mut scalars = scalars.into_iter();
        let size = scalars.by_ref().size_hint().0;
        let w = if size < 3 {
            1
        } else if size < 13 {
            2
        } else if size < 27 {
            3
        } else if size < 66 {
            4
        } else if size < 190 {
            5
        } else if size < 500 {
            6
        } else if size < 800 {
            7
        } else if size < 3_000 {
            8
        } else if size < 6_000 {
            9
        } else if size < 13_000 {
            10
        } else if size < 23_000 {
            11
        } else if size < 45_000 {
            12
        } else if size < 160_000 {
            13
        } else if size < 260_000 {
            14
        } else {
            15
        };

        let window_size = 1 << w;
        let windows_count = (256 + w - 1) / w; // == ceil(256/w)
        let buckets_count = window_size / 2; // digits are signed+centered hence 2^w/2, excluding 0-th bucket

        // Step 1. Prepare scalar representation using signed digits radix 2^w.
        // Each digit will be in [-2^w/2, 2^w/2].
        let all_digits: Vec<_> = scalars
            .into_iter()
            .map(|c| c.borrow().to_arbitrary_radix(w))
            .collect();
        let ps: Vec<ProjectiveNielsPoint> = points
            .into_iter()
            .map(|p| p.borrow().to_projective_niels())
            .collect();

        // Iterate the digits from last to first so we can shift the result by w bits
        // at the end of each iteration (e.g. w doublings).
        let mut result = EdwardsPoint::identity();
        for i in (0..windows_count).rev() {
            // Step 2. Shift the current result by w bits to leave room for a new window.
            if i < (windows_count - 1) {
                result = result.mul_by_pow_2(w as u32);
            }

            // Step 3. Prepare 2^w/2 buckets.
            // buckets[i] corresponds to a multiplication factor (i+1).
            let mut buckets: Vec<_> = (0..buckets_count)
                .map(|_| EdwardsPoint::identity())
                .collect();

            // Step 4. Iterate over pairs of (point, scalar)
            // and add/sub the point to the corresponding bucket.
            // Note: when we add support for precomputed lookup tables,
            // we'll be adding/subtractiong point premultiplied by `digits[i]` to buckets[0].
            for (digits, pt) in all_digits.iter().zip(ps.iter()) {
                if digits[i] > 0 {
                    let b = (digits[i] - 1) as usize;
                    buckets[b] = (&buckets[b] + pt).to_extended();
                } else if digits[i] < 0 {
                    let b = (-digits[i] - 1) as usize;
                    buckets[b] = (&buckets[b] - pt).to_extended();;
                }
            }

            // Step 5. Add the buckets applying the multiplication factor to each bucket.
            // The most efficient way to do that is to have a single sum with two running sums:
            // an intermediate sum from last bucket to the first, and a sum of intermediate sums.
            //
            // For example, to add buckets 1*A, 2*B, 3*C we need to add these points:
            //   C
            //   C B
            //   C B A   Sum = C + (C+B) + (C+B+A)
            let mut buckets_intermediate_sum = buckets[buckets_count - 1].clone();
            let mut buckets_sum = buckets[buckets_count - 1].clone();
            for i in (0..(buckets_count - 1)).rev() {
                buckets_intermediate_sum += buckets[i];
                buckets_sum += buckets_intermediate_sum;
            }

            // Step 5. Add to result
            result += buckets_sum;
        }

        result
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use constants;
    use scalar::Scalar;

    #[test]
    fn test_vartime_pippenger() {
        // Reuse points across different tests
        let mut n = 256;
        let points: Vec<_> = (0..n)
            .map(|i| constants::ED25519_BASEPOINT_POINT * Scalar::from_u64(1 + i as u64))
            .collect();
        let scalars: Vec<_> = (0..n)
            .map(|i| Scalar::from_u64((i + 1) as u64).invert())
            .collect();

        while n > 0 {
            let scalars = &scalars[0..n].to_vec();
            let points = &points[0..n].to_vec();

            let subject = Pippenger::vartime_multiscalar_mul(scalars.clone(), points.clone());

            let control: EdwardsPoint = scalars
                .iter()
                .zip(points.iter())
                .map(|(sc, pt)| sc * pt)
                .sum();

            assert_eq!(subject.compress(), control.compress());

            n = n / 2;
        }
    }
}
