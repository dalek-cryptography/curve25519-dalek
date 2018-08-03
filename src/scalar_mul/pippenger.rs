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

//! Implements a version of Pippenger's algorithm.

#![allow(non_snake_case)]

#[cfg(any(feature = "alloc", feature = "std"))]
use core::borrow::Borrow;

#[cfg(any(feature = "alloc", feature = "std"))]
use edwards::EdwardsPoint;
#[cfg(any(feature = "alloc", feature = "std"))]
use scalar::Scalar;
#[cfg(any(feature = "alloc", feature = "std"))]
use scalar::DigitsBatch;

// TODO: add const-time version of pippenger
// #[cfg(any(feature = "alloc", feature = "std"))]
// use traits::MultiscalarMul;

#[cfg(any(feature = "alloc", feature = "std"))]
use traits::VartimeMultiscalarMul;

#[allow(unused_imports)]
use prelude::*;

use curve_models::ProjectiveNielsPoint;

use traits::{Identity};

/// Implements a version of Pippenger's algorithm.
///
/// The algorithm works as follows:
///
/// Let `n` be a number of point-scalar pairs.
/// Let `w` be a window of bits (5..15, chosen based on `n`, see cost factor).
///
/// 1. Prepare `2^(w-1) - 1` buckets with indices `[1..2^(w-1))` initialized with identity points.
///    Bucket 0 is not needed as it would contain points multiplied by 0.
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
pub struct Pippenger;

#[cfg(any(feature = "alloc", feature = "std"))]
impl VartimeMultiscalarMul for Pippenger {
    type Point = EdwardsPoint;

    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<EdwardsPoint>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,
    {
        let mut scalars = scalars.into_iter();
        let size = scalars.by_ref().size_hint().0;

        // Digit width in bits. As digit width grows,
        // number of point additions goes down, but amount of
        // buckets and bucket additions grows exponentially.
        let w = if size < 13 {
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

        let max_digit: usize = 1 << w;
        let digits_count: usize = (256 + w - 1) / w; // == ceil(256/w)
        let buckets_count: usize = max_digit / 2; // digits are signed+centered hence 2^w/2, excluding 0-th bucket

        // Prepare scalar representation using signed digits radix 2^w.
        // Each digit will be in [-2^w/2, 2^w/2].
        let mut digits_batch = DigitsBatch::new(scalars, w);
        let ps: Vec<ProjectiveNielsPoint> = match points
            .into_iter()
            .map(|p| p.map(|P| P.to_projective_niels()))
            .collect::<Option<Vec<_>>>() {
                Some(x) => x,
                None => return None
            };

        // Prepare 2^w/2 buckets.
        // buckets[i] corresponds to a multiplication factor (i+1).
        let mut buckets: Vec<_> = (0..buckets_count)
            .map(|_| EdwardsPoint::identity())
            .collect();

        let columns: Vec<_> = (0..digits_count).map(|_| {

            // Clear the buckets when processing another digit.
            for i in 0..buckets_count {
                buckets[i] = EdwardsPoint::identity();
            }
            
            // Iterate over pairs of (point, scalar)
            // and add/sub the point to the corresponding bucket.
            // Note: if we add support for precomputed lookup tables,
            // we'll be adding/subtractiong point premultiplied by `digits[i]` to buckets[0].
            for (digit, pt) in digits_batch.next_batch().zip(ps.iter()) {
                if digit > 0 {
                    let b = (digit - 1) as usize;
                    buckets[b] = (&buckets[b] + pt).to_extended();
                } else if digit < 0 {
                    let b = (-digit - 1) as usize;
                    buckets[b] = (&buckets[b] - pt).to_extended();
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
        })
        .collect();
        // ^ Note: we collect points because if we chain .rev().fold()
        // then the .map() will run in reversed order, producing incorrect digit values
        // (they can only be produced in lo->hi order).

        // Add the intermediate per-digit results in hi->lo order
        // so that we can minimize doublings.
        Some(columns[0..(digits_count-1)]
            .iter()
            .rev()
            .fold(
                columns[digits_count-1],
                |total, &p| {
                    total.mul_by_pow_2(w as u32) + p
                })
        )
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
        let mut n = 512;
        let x = Scalar::from(2128506u64).invert();
        let y = Scalar::from(4443282u64).invert();
        let points: Vec<_> = (0..n)
            .map(|i| constants::ED25519_BASEPOINT_POINT * Scalar::from(1 + i as u64))
            .collect();
        let scalars: Vec<_> = (0..n)
            .map(|i| x + (Scalar::from(i as u64)*y)) // fast way to make ~random but deterministic scalars
            .collect();

        let premultiplied: Vec<EdwardsPoint> = scalars
            .iter()
            .zip(points.iter())
            .map(|(sc, pt)| sc * pt)
            .collect();

        while n > 0 {
            let scalars = &scalars[0..n].to_vec();
            let points = &points[0..n].to_vec();
            let control: EdwardsPoint = premultiplied[0..n].iter().sum();

            let subject = Pippenger::vartime_multiscalar_mul(scalars.clone(), points.clone());

            assert_eq!(subject.compress(), control.compress());

            n = n / 2;
        }
    }
}
