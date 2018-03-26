// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
#![allow(non_snake_case)]

use core::borrow::Borrow;

use clear_on_drop::ClearOnDrop;

use traits::Identity;
use scalar::Scalar;
use edwards::EdwardsPoint;
use scalar_mul::window::LookupTable;
use backend::avx2::edwards::{CachedPoint, ExtendedPoint};

/// Perform constant-time, variable-base scalar multiplication.
pub(crate) fn multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint
where
    I: IntoIterator,
    I::Item: Borrow<Scalar>,
    J: IntoIterator,
    J::Item: Borrow<EdwardsPoint>,
{
    // Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]
    // for each input point P
    let lookup_tables: Vec<_> = points
        .into_iter()
        .map(|point| {
            let avx2_point = ExtendedPoint::from(*point.borrow());
            LookupTable::<CachedPoint>::from(avx2_point)
        })
        .collect();

    let scalar_digits_vec: Vec<_> = scalars
        .into_iter()
        .map(|s| s.borrow().to_radix_16())
        .collect();
    // Pass ownership to a ClearOnDrop wrapper
    let scalar_digits = ClearOnDrop::new(scalar_digits_vec);

    let mut Q = ExtendedPoint::identity();
    for j in (0..64).rev() {
        Q = Q.mul_by_pow_2(4);
        let it = scalar_digits.iter().zip(lookup_tables.iter());
        for (s_i, lookup_table_i) in it {
            // Q = Q + s_{i,j} * P_i
            Q = &Q + &lookup_table_i.select(s_i[j]);
        }
    }
    Q.into()
}
