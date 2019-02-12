// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2019 Henry de Valence.
// See LICENSE for licensing information.
//
// Authors:
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Precomputation for Straus's method.

#![allow(non_snake_case)]

use core::borrow::Borrow;

use clear_on_drop::ClearOnDrop;

use backend::serial::curve_models::{
    AffineNielsPoint, CompletedPoint, ProjectiveNielsPoint, ProjectivePoint,
};
use edwards::EdwardsPoint;
use scalar::Scalar;
use traits::Identity;
use traits::{PrecomputedMultiscalarMul, VartimePrecomputedMultiscalarMul};
use window::{LookupTable, NafLookupTable5, NafLookupTable8};

#[allow(unused_imports)]
use prelude::*;

pub struct PrecomputedStraus {
    static_lookup_tables: Vec<LookupTable<AffineNielsPoint>>,
}

impl PrecomputedMultiscalarMul for PrecomputedStraus {
    type Point = EdwardsPoint;

    fn new<I>(static_points: I) -> Self
    where
        I: IntoIterator,
        I::Item: Borrow<Self::Point>,
    {
        PrecomputedStraus {
            static_lookup_tables: static_points
                .into_iter()
                .map(|point| LookupTable::<AffineNielsPoint>::from(point.borrow()))
                .collect(),
        }
    }

    fn mixed_multiscalar_mul<I, J, K>(
        &self,
        static_scalars: I,
        dynamic_scalars: J,
        dynamic_points: K,
    ) -> Self::Point
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<Scalar>,
        K: IntoIterator,
        K::Item: Borrow<Self::Point>,
    {
        let mut static_scalars = static_scalars.into_iter();
        let mut dynamic_scalars = dynamic_scalars.into_iter();
        let mut dynamic_points = dynamic_points.into_iter();

        // Check that the input lengths are consistent with each other:
        let (ss_lo, ss_hi) = static_scalars.by_ref().size_hint();
        let (ds_lo, ds_hi) = dynamic_scalars.by_ref().size_hint();
        let (dp_lo, dp_hi) = dynamic_points.by_ref().size_hint();

        // Static points match static scalars
        let sp = self.static_lookup_tables.len();
        assert_eq!(ss_lo, sp);
        assert_eq!(ss_hi, Some(sp));

        // Dynamic points match dynamic scalars
        assert_eq!(ds_lo, dp_lo);
        assert_eq!(ds_hi, Some(ds_lo));
        assert_eq!(ds_hi, dp_hi);
        let dp = dp_lo;

        // This does two allocs for the scalar digits instead of
        // putting them in a contiguous array, which makes handling
        // the two kinds of lookup tables slightly easier.
        // Use a ClearOnDrop wrapper.

        let static_scalar_digits_vec: Vec<_> =
            static_scalars.map(|s| s.borrow().to_radix_16()).collect();
        let static_scalar_digits = ClearOnDrop::new(static_scalar_digits_vec);

        let dynamic_scalar_digits_vec: Vec<_> =
            dynamic_scalars.map(|s| s.borrow().to_radix_16()).collect();
        let dynamic_scalar_digits = ClearOnDrop::new(dynamic_scalar_digits_vec);

        // Build lookup tables for dynamic points
        let dynamic_lookup_tables: Vec<_> = dynamic_points
            .map(|point| LookupTable::<ProjectiveNielsPoint>::from(point.borrow()))
            .collect();

        let mut R = EdwardsPoint::identity();
        for j in (0..64).rev() {
            R = R.mul_by_pow_2(4);
            for i in 0..dp {
                let t_ij = dynamic_scalar_digits[i][j];
                R = (&R + &dynamic_lookup_tables[i].select(t_ij)).to_extended();
            }
            for i in 0..sp {
                let s_ij = static_scalar_digits[i][j];
                R = (&R + &self.static_lookup_tables[i].select(s_ij)).to_extended();
            }
        }

        R
    }
}

pub struct VartimePrecomputedStraus {
    static_lookup_tables: Vec<NafLookupTable8<AffineNielsPoint>>,
}

impl VartimePrecomputedMultiscalarMul for VartimePrecomputedStraus {
    type Point = EdwardsPoint;

    fn new<I>(static_points: I) -> Self
    where
        I: IntoIterator,
        I::Item: Borrow<Self::Point>,
    {
        Self {
            static_lookup_tables: static_points
                .into_iter()
                .map(|P| NafLookupTable8::<AffineNielsPoint>::from(P.borrow()))
                .collect(),
        }
    }

    fn vartime_mixed_multiscalar_mul<I, J, K>(
        &self,
        static_scalars: I,
        dynamic_scalars: J,
        dynamic_points: K,
    ) -> Self::Point
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<Scalar>,
        K: IntoIterator,
        K::Item: Borrow<Self::Point>,
    {
        let static_nafs = static_scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect::<Vec<_>>();
        let dynamic_nafs: Vec<_> = dynamic_scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect::<Vec<_>>();

        let dynamic_lookup_tables = dynamic_points
            .into_iter()
            .map(|P| NafLookupTable5::<ProjectiveNielsPoint>::from(P.borrow()))
            .collect::<Vec<_>>();

        let sp = self.static_lookup_tables.len();
        let dp = dynamic_lookup_tables.len();
        assert_eq!(sp, static_nafs.len());
        assert_eq!(dp, dynamic_nafs.len());

        // We could save some doublings by looking for the highest
        // nonzero NAF coefficient, but since we might have a lot of
        // them to search, it's not clear it's worthwhile to check.
        let mut S = ProjectivePoint::identity();
        for j in (0..255).rev() {
            let mut R: CompletedPoint = S.double();

            for i in 0..dp {
                let t_ij = dynamic_nafs[i][j];
                if t_ij > 0 {
                    R = &R.to_extended() + &dynamic_lookup_tables[i].select(t_ij as usize);
                } else if t_ij < 0 {
                    R = &R.to_extended() - &dynamic_lookup_tables[i].select(-t_ij as usize);
                }
            }

            for i in 0..sp {
                let t_ij = static_nafs[i][j];
                if t_ij > 0 {
                    R = &R.to_extended() + &self.static_lookup_tables[i].select(t_ij as usize);
                } else if t_ij < 0 {
                    R = &R.to_extended() - &self.static_lookup_tables[i].select(-t_ij as usize);
                }
            }

            S = R.to_projective();
        }

        S.to_extended()
    }
}
