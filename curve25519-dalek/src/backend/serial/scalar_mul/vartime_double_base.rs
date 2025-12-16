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
#![allow(non_snake_case)]

use core::cmp::Ordering;

use crate::backend::serial::curve_models::{ProjectiveNielsPoint, ProjectivePoint};
use crate::constants;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::window::NafLookupTable5;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::window_specs::*;

use vstd::prelude::*;

verus! {

/// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
// VERIFICATION NOTE: PROOF BYPASS - complex loop invariants not yet verified.
// Uses `assume(false)` at loop entry points to skip internal verification.
pub fn mul(a: &Scalar, A: &EdwardsPoint, b: &Scalar) -> (out: EdwardsPoint)
    requires
// Input point must be well-formed

        is_well_formed_edwards_point(*A),
    ensures
// Result is a well-formed Edwards point

        is_well_formed_edwards_point(out),
        // Functional correctness: out = a*A + b*B where B is the Ed25519 basepoint
        edwards_point_as_affine(out) == {
            let aA = edwards_scalar_mul(edwards_point_as_affine(*A), spec_scalar(a));
            let bB = edwards_scalar_mul(spec_ed25519_basepoint(), spec_scalar(b));
            edwards_add(aA.0, aA.1, bB.0, bB.1)
        },
{
    let a_naf = a.non_adjacent_form(5);

    #[cfg(feature = "precomputed-tables")]
    let b_naf = b.non_adjacent_form(8);
    #[cfg(not(feature = "precomputed-tables"))]
    let b_naf = b.non_adjacent_form(5);

    // Find starting index
    let mut i: usize = 255;
    /* <ORIGINAL CODE>
    for j in (0..256).rev() {
        i = j;
        if a_naf[i] != 0 || b_naf[i] != 0 {
            break;
        }
    }
    </ORIGINAL CODE> */
    // VERIFICATION NOTE: Verus doesn't support for-loops over Rev<Range<_>>
    // This loop checks indices 255, 254, ..., 1, 0 (inclusive) to match original behavior.
    loop
        invariant
            i <= 255,
        decreases i + 1,  // +1 accounts for the final iteration at i == 0

    {
        if a_naf[i] != 0 || b_naf[i] != 0 {
            break ;
        }
        if i == 0 {
            break ;  // Checked index 0, now exit
        }
        i -= 1;
    }

    let table_A = NafLookupTable5::<ProjectiveNielsPoint>::from(A);
    #[cfg(feature = "precomputed-tables")]
    let table_B = &constants::AFFINE_ODD_MULTIPLES_OF_BASEPOINT;
    #[cfg(not(feature = "precomputed-tables"))]
    let table_B = &NafLookupTable5::<ProjectiveNielsPoint>::from(
        &constants::ED25519_BASEPOINT_POINT,
    );

    let mut r = ProjectivePoint::identity();

    loop
        invariant
            i <= 255,
        decreases i,
    {
        assume(false);  // PROOF BYPASS
        let mut t = r.double();

        match a_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_A.select(a_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_A.select(-a_naf[i] as usize),
            Ordering::Equal => {},
        }

        match b_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_B.select(b_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_B.select(-b_naf[i] as usize),
            Ordering::Equal => {},
        }

        r = t.as_projective();

        if i == 0 {
            break ;
        }
        i -= 1;
    }

    assume(false);  // PROOF BYPASS: precondition for as_extended
    let result = r.as_extended();
    proof {
        // PROOF BYPASS: postconditions
        assume(is_well_formed_edwards_point(result));
        assume(edwards_point_as_affine(result) == {
            let aA = edwards_scalar_mul(edwards_point_as_affine(*A), spec_scalar(a));
            let bB = edwards_scalar_mul(spec_ed25519_basepoint(), spec_scalar(b));
            edwards_add(aA.0, aA.1, bB.0, bB.1)
        });
    }
    result
}

} // verus!
