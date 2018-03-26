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

use core::ops::{Add, Sub};
use core::borrow::Borrow;

use scalar::Scalar;

//use super::window::OddLookupTable;
use scalar_mul::window::OddLookupTable;
use traits::{Doubleable, Identity};

/// Perform variable-time, variable-base scalar multiplication.
pub(crate) fn multiscalar_mul<I, J, ExtendedPoint, CompletedPoint, ProjectivePoint, CachedPoint>(
    scalars: I,
    points: J,
) -> ExtendedPoint
where
    I: IntoIterator,
    I::Item: Borrow<Scalar>,
    J: IntoIterator,
    J::Item: Borrow<ExtendedPoint>,
    for<'a> OddLookupTable<CachedPoint>: From<&'a ExtendedPoint>,
    for<'a, 'b> &'a ExtendedPoint: Add<&'b CachedPoint, Output = CompletedPoint>,
    for<'a, 'b> &'a ExtendedPoint: Sub<&'b CachedPoint, Output = CompletedPoint>,
    ExtendedPoint: Identity + From<CompletedPoint> + From<ProjectivePoint>,
    ProjectivePoint: Identity + Doubleable<Output = CompletedPoint> + From<CompletedPoint>,
    CachedPoint: Copy,
{
    let nafs: Vec<_> = scalars
        .into_iter()
        .map(|c| c.borrow().non_adjacent_form())
        .collect();
    let lookup_tables: Vec<_> = points
        .into_iter()
        .map(|P| OddLookupTable::from(P.borrow()))
        .collect();

    let mut r = ProjectivePoint::identity();

    for i in (0..255).rev() {
        let mut t: CompletedPoint = r.double();

        for (naf, lookup_table) in nafs.iter().zip(lookup_tables.iter()) {
            if naf[i] > 0 {
                t = &ExtendedPoint::from(t) + &lookup_table.select(naf[i] as usize);
            } else if naf[i] < 0 {
                t = &ExtendedPoint::from(t) - &lookup_table.select(-naf[i] as usize);
            }
        }

        r = ProjectivePoint::from(t);
    }

    ExtendedPoint::from(r)
}
