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

use backend::vector::{CachedPoint, ExtendedPoint};
use edwards::EdwardsPoint;
use scalar::Scalar;
use traits::Identity;
use traits::{PrecomputedMultiscalarMul, VartimePrecomputedMultiscalarMul};
use window::{LookupTable, NafLookupTable5, NafLookupTable8};

#[allow(unused_imports)]
use prelude::*;

pub struct PrecomputedStraus {
    static_lookup_tables: Vec<LookupTable<CachedPoint>>,
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
                .map(|point| LookupTable::<CachedPoint>::from(point.borrow()))
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
        // This does two allocs for the scalar digits instead of
        // putting them in a contiguous array, which makes handling
        // the two kinds of lookup tables slightly easier.
        // Use a ClearOnDrop wrapper.

        let static_scalar_digits_vec: Vec<_> = static_scalars
            .into_iter()
            .map(|s| s.borrow().to_radix_16())
            .collect();
        let static_scalar_digits = ClearOnDrop::new(static_scalar_digits_vec);

        let dynamic_scalar_digits_vec: Vec<_> = dynamic_scalars
            .into_iter()
            .map(|s| s.borrow().to_radix_16())
            .collect();
        let dynamic_scalar_digits = ClearOnDrop::new(dynamic_scalar_digits_vec);

        // Build lookup tables for dynamic points
        let dynamic_lookup_tables: Vec<_> = dynamic_points
            .into_iter()
            .map(|point| LookupTable::<CachedPoint>::from(point.borrow()))
            .collect();

        let sp = self.static_lookup_tables.len();
        let dp = dynamic_lookup_tables.len();
        assert_eq!(sp, static_scalar_digits.len());
        assert_eq!(dp, dynamic_scalar_digits.len());

        let mut R = ExtendedPoint::identity();
        for j in (0..64).rev() {
            R = R.mul_by_pow_2(4);
            for i in 0..dp {
                let t_ij = dynamic_scalar_digits[i][j];
                R = &R + &dynamic_lookup_tables[i].select(t_ij);
            }
            for i in 0..sp {
                let s_ij = static_scalar_digits[i][j];
                R = &R + &self.static_lookup_tables[i].select(s_ij);
            }
        }

        R.into()
    }
}

pub struct VartimePrecomputedStraus {
    static_lookup_tables: Vec<NafLookupTable8<CachedPoint>>,
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
                .map(|P| NafLookupTable8::<CachedPoint>::from(P.borrow()))
                .collect(),
        }
    }

    fn optional_mixed_multiscalar_mul<I, J, K>(
        &self,
        static_scalars: I,
        dynamic_scalars: J,
        dynamic_points: K,
    ) -> Option<Self::Point>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<Scalar>,
        K: IntoIterator<Item = Option<Self::Point>>,
    {
        let static_nafs = static_scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect::<Vec<_>>();
        let dynamic_nafs: Vec<_> = dynamic_scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect::<Vec<_>>();

        let dynamic_lookup_tables = match dynamic_points
            .into_iter()
            .map(|P_opt| P_opt.map(|P| NafLookupTable5::<CachedPoint>::from(&P)))
            .collect::<Option<Vec<_>>>()
        {
            Some(x) => x,
            None => return None,
        };

        let sp = self.static_lookup_tables.len();
        let dp = dynamic_lookup_tables.len();
        assert_eq!(sp, static_nafs.len());
        assert_eq!(dp, dynamic_nafs.len());

        // We could save some doublings by looking for the highest
        // nonzero NAF coefficient, but since we might have a lot of
        // them to search, it's not clear it's worthwhile to check.
        let mut R = ExtendedPoint::identity();
        for j in (0..255).rev() {
            R = R.double();

            for i in 0..dp {
                let t_ij = dynamic_nafs[i][j];
                if t_ij > 0 {
                    R = &R + &dynamic_lookup_tables[i].select(t_ij as usize);
                } else if t_ij < 0 {
                    R = &R - &dynamic_lookup_tables[i].select(-t_ij as usize);
                }
            }

            for i in 0..sp {
                let t_ij = static_nafs[i][j];
                if t_ij > 0 {
                    R = &R + &self.static_lookup_tables[i].select(t_ij as usize);
                } else if t_ij < 0 {
                    R = &R - &self.static_lookup_tables[i].select(-t_ij as usize);
                }
            }
        }

        Some(R.into())
    }
}
