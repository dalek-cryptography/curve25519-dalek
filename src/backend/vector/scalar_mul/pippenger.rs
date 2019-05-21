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

use core::borrow::Borrow;

use backend::vector::{CachedPoint, ExtendedPoint};
use edwards::EdwardsPoint;
use scalar::Scalar;
use traits::{Identity, VartimeMultiscalarMul};

#[allow(unused_imports)]
use prelude::*;

/// Implements a version of Pippenger's algorithm.
///
/// See the documentation in the serial `scalar_mul::pippenger` module for details.
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
        let w = if size < 500 {
            6
        } else if size < 800 {
            7
        } else {
            8
        };

        let max_digit: usize = 1 << w;
        let digits_count: usize = (256 + w - 1) / w; // == ceil(256/w)
        let buckets_count: usize = max_digit / 2; // digits are signed+centered hence 2^w/2, excluding 0-th bucket

        // Collect optimized scalars and points in buffers for repeated access
        // (scanning the whole set per digit position).
        let scalars = scalars.into_iter()
        	.map(|s| s.borrow().to_pippenger_radix(w).0 )
        	.collect::<Vec<_>>();
        let points: Vec<CachedPoint> = match points
            .into_iter()
            .map(|p| p.map(|P| CachedPoint::from(ExtendedPoint::from(P))))
            .collect::<Option<Vec<_>>>() {
            Some(x) => x,
            None => return None,
        };

        // Prepare 2^w/2 buckets.
        // buckets[i] corresponds to a multiplication factor (i+1).
        let mut buckets: Vec<ExtendedPoint> = (0..buckets_count)
            .map(|_| ExtendedPoint::identity())
            .collect();

        let columns: Vec<ExtendedPoint> = (0..digits_count).map(|digit_index| {

            // Clear the buckets when processing another digit.
            for i in 0..buckets_count {
                buckets[i] = ExtendedPoint::identity();
            }
            
            // Iterate over pairs of (point, scalar)
            // and add/sub the point to the corresponding bucket.
            // Note: if we add support for precomputed lookup tables,
            // we'll be adding/subtractiong point premultiplied by `digits[i]` to buckets[0].
            for (digits, pt) in scalars.iter().zip(points.iter()) {
            	let digit = digits[digit_index];
                if digit > 0 {
                    let b = (digit - 1) as usize;
                    buckets[b] = &buckets[b] + pt;
                } else if digit < 0 {
                    let b = (-digit - 1) as usize;
                    buckets[b] = &buckets[b] - pt;
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
                buckets_intermediate_sum = &buckets_intermediate_sum + &CachedPoint::from(buckets[i]);
                buckets_sum = &buckets_sum + &CachedPoint::from(buckets_intermediate_sum);
            }

            buckets_sum
        })
        .collect();
        // ^ Note: we collect points because if we chain .rev().fold()
        // then the .map() will run in reversed order, producing incorrect digit values
        // (they can only be produced in lo->hi order).

        // Add the intermediate per-digit results in hi->lo order
        // so that we can minimize doublings.
        Some(
            columns[0..(digits_count - 1)]
                .iter()
                .rev()
                .fold(columns[digits_count - 1], |total, &p| {
                    &total.mul_by_pow_2(w as u32) + &CachedPoint::from(p)
                })
                .into(),
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
            .map(|i| {
                constants::ED25519_BASEPOINT_POINT * Scalar::from(1 + i as u64)
            })
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