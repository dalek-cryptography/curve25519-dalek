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

use traits::Identity;
use scalar::Scalar;
use edwards::EdwardsPoint;
use scalar_mul::window::OddLookupTable;
use backend::avx2::edwards::{CachedPoint, ExtendedPoint};

/// Perform variable-time, variable-base scalar multiplication.
pub(crate) fn multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint
where
    I: IntoIterator,
    I::Item: Borrow<Scalar>,
    J: IntoIterator,
    J::Item: Borrow<EdwardsPoint>,
{
    let nafs: Vec<_> = scalars
        .into_iter()
        .map(|c| c.borrow().non_adjacent_form())
        .collect();
    let lookup_tables: Vec<_> = points
        .into_iter()
        .map(|point| OddLookupTable::<CachedPoint>::from(point.borrow()))
        .collect();

    let mut Q = ExtendedPoint::identity();

    for i in (0..255).rev() {
        Q = Q.double();

        for (naf, lookup_table) in nafs.iter().zip(lookup_tables.iter()) {
            if naf[i] > 0 {
                Q = &Q + &lookup_table.select(naf[i] as usize);
            } else if naf[i] < 0 {
                Q = &Q - &lookup_table.select(-naf[i] as usize);
            }
        }
    }
    Q.into()
}
