// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2020 Jack Grigg
// See LICENSE for licensing information.
//
// Author:
// Jack Grigg <thestr4d@gmail.com>
#![allow(non_snake_case)]

use backend::serial::curve_models::{ProjectiveNielsPoint, ProjectivePoint};
use constants::{AFFINE_ODD_MULTIPLES_OF_BASEPOINT, AFFINE_ODD_MULTIPLES_OF_B_SHL_128};
use edwards::EdwardsPoint;
use scalar::{lattice_reduction::find_short_vector, Scalar};
use traits::Identity;
use window::NafLookupTable5;

/// Computes \\([δa]A + [δb]B - [δ]C\\) in variable time.
///
/// - \\(B\\) is the Ed25519 basepoint.
/// - \\(δ\\) is a value invertible \\( \mod \ell \\), which is selected internally to
///   this function.
///
/// This corresponds to the signature verification optimisation presented in
/// [Antipa et al 2005](http://cacr.uwaterloo.ca/techreports/2005/cacr2005-28.pdf).
pub fn mul(a: &Scalar, A: &EdwardsPoint, b: &Scalar, C: &EdwardsPoint) -> EdwardsPoint {
    // Starting with the target equation:
    //
    //     [(δa mod l)]A + [(δb mod l)]B - [δ]C
    //
    // We can split δb mod l into two halves e_0 (128 bits) and e_1 (125 bits), and
    // rewrite the equation as:
    //
    //     [(δa mod l)]A + [e_0]B + [e_1 2^128]B - [δ]C
    //
    // B and [2^128]B are precomputed, and their resulting scalar multiplications each
    // have half as many doublings. We therefore want to find a pair of signed integers
    //
    //     (d_0, d_1) = (δa mod l, δ)
    //
    // that both have as few bits as possible, similarly reducing the number of doublings
    // in the scalar multiplications [d_0]A and [d_1]C. This is equivalent to finding a
    // short vector in a lattice of dimension 2.

    // Find a short vector.
    let (d_0, d_1) = find_short_vector(a);

    // Move the signs of d_0 and d_1 into their corresponding bases and scalars.
    let A = if d_0.is_negative() { -A } else { *A };
    let (b, negC) = if d_1.is_negative() {
        (-b, *C)
    } else {
        (*b, -C)
    };
    let d_0 = Scalar::from(d_0.abs() as u128);
    let d_1 = Scalar::from(d_1.abs() as u128);

    // Calculate the remaining scalars.
    let (e_0, e_1) = {
        let db = b * d_1;
        let mut e_0 = [0; 32];
        let mut e_1 = [0; 32];
        e_0[..16].copy_from_slice(&db.as_bytes()[..16]);
        e_1[..16].copy_from_slice(&db.as_bytes()[16..]);
        (Scalar { bytes: e_0 }, Scalar { bytes: e_1 })
    };

    // Now we can compute the following using Straus's method:
    //     [d_0]A + [e_0]B + [e_1][2^128]B + [d_1][-C]
    //
    // We inline it here so we can use precomputed multiples of [2^128]B.

    let d_0_naf = d_0.non_adjacent_form(5);
    let e_0_naf = e_0.non_adjacent_form(8);
    let e_1_naf = e_1.non_adjacent_form(8);
    let d_1_naf = d_1.non_adjacent_form(5);

    // Find starting index
    let mut i: usize = 255;
    for j in (0..256).rev() {
        i = j;
        if d_0_naf[i] != 0 || e_0_naf[i] != 0 || e_1_naf[i] != 0 || d_1_naf[i] != 0 {
            break;
        }
    }

    let table_A = NafLookupTable5::<ProjectiveNielsPoint>::from(&A);
    let table_B = AFFINE_ODD_MULTIPLES_OF_BASEPOINT;
    let table_B_SHL_128 = AFFINE_ODD_MULTIPLES_OF_B_SHL_128;
    let table_negC = NafLookupTable5::<ProjectiveNielsPoint>::from(&negC);

    let mut r = ProjectivePoint::identity();
    loop {
        let mut t = r.double();

        if d_0_naf[i] > 0 {
            t = &t.to_extended() + &table_A.select(d_0_naf[i] as usize);
        } else if d_0_naf[i] < 0 {
            t = &t.to_extended() - &table_A.select(-d_0_naf[i] as usize);
        }

        if e_0_naf[i] > 0 {
            t = &t.to_extended() + &table_B.select(e_0_naf[i] as usize);
        } else if e_0_naf[i] < 0 {
            t = &t.to_extended() - &table_B.select(-e_0_naf[i] as usize);
        }

        if e_1_naf[i] > 0 {
            t = &t.to_extended() + &table_B_SHL_128.select(e_1_naf[i] as usize);
        } else if e_1_naf[i] < 0 {
            t = &t.to_extended() - &table_B_SHL_128.select(-e_1_naf[i] as usize);
        }

        if d_1_naf[i] > 0 {
            t = &t.to_extended() + &table_negC.select(d_1_naf[i] as usize);
        } else if d_1_naf[i] < 0 {
            t = &t.to_extended() - &table_negC.select(-d_1_naf[i] as usize);
        }

        r = t.to_projective();

        if i == 0 {
            break;
        }
        i -= 1;
    }

    r.to_extended()
}

#[cfg(test)]
mod tests {
    use super::mul;
    use constants::{ED25519_BASEPOINT_POINT, ED25519_BASEPOINT_TABLE};
    use scalar::Scalar;
    use traits::IsIdentity;

    #[test]
    fn test_mul() {
        let a = Scalar::from(2u8);
        let A = ED25519_BASEPOINT_POINT.double(); // [2]B
        let b = Scalar::from(4u8);
        let C = A.double().double(); // [8]B

        // The equation evaluates to the identity, so will be unaffected by δ.
        assert_eq!(
            mul(&a, &A, &b, &C),
            (a * A) + (b * ED25519_BASEPOINT_POINT) - C
        );

        // Now test some random values.
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let a = Scalar::random(&mut rng);
            let A = &Scalar::random(&mut rng) * &ED25519_BASEPOINT_TABLE;
            let b = Scalar::random(&mut rng);

            // With a correctly-constructed C, we get the identity.
            let C = (a * A) + (b * ED25519_BASEPOINT_POINT);
            assert!(mul(&a, &A, &b, &C).is_identity());

            // With a random C, with high probability we do not get the identity.
            let C = &Scalar::random(&mut rng) * &ED25519_BASEPOINT_TABLE;
            assert!(!mul(&a, &A, &b, &C).is_identity());
        }
    }
}
