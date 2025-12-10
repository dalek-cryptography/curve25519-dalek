// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.

#![allow(non_snake_case)]

use core::cmp::Ordering;

use crate::backend::serial::curve_models::{ProjectiveNielsPoint, ProjectivePoint};
use crate::constants;
use crate::edwards::EdwardsPoint;
use crate::scalar::{HEEA_MAX_INDEX, Scalar};
use crate::traits::Identity;
use crate::window::NafLookupTable5;

/// Compute \\(a_1 A_1 + a_2 A_2 + b B\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
///
/// This function is optimized for the case where \\(a_1\\) and \\(a_2\\) are known to be less than
/// \\(2^{128}\\), while \\(b\\) is a full 256-bit scalar.
///
/// # Optimization Strategy
///
/// The function decomposes the 256-bit scalar \\(b\\) as \\(b = b_{lo} + b_{hi} \cdot 2^{128}\\),
/// where both \\(b_{lo}\\) and \\(b_{hi}\\) are 128-bit values. This allows computing:
///
/// \\[
/// a_1 A_1 + a_2 A_2 + b_{lo} B + b_{hi} B'
/// \\]
///
/// where \\(B' = B \cdot 2^{128}\\) is a precomputed constant. Now all four scalars
/// (\\(a_1, a_2, b_{lo}, b_{hi}\\)) are 128 bits, and two of the bases (\\(B\\) and \\(B'\\))
/// use precomputed tables.
///
/// # Implementation
///
/// - For \\(A_1\\) and \\(A_2\\): NAF with window width 5 (8 precomputed points each)
/// - For \\(B\\): NAF with window width 8 when precomputed tables available (64 points)
/// - For \\(B'\\): NAF with window width 5 (could be optimized with precomputed table)
///
/// The algorithm shares doublings across all four scalar multiplications, processing
/// only 128 bits instead of 256, providing approximately 2x speedup over the naive approach.
pub fn mul_128_128_256(
    a1: &Scalar,
    A1: &EdwardsPoint,
    a2: &Scalar,
    A2: &EdwardsPoint,
    b: &Scalar,
) -> EdwardsPoint {
    // assert that a1 and a2 are less than 2^128
    debug_assert!(a1.as_bytes()[16..32].iter().all(|&b| b == 0));
    debug_assert!(a2.as_bytes()[16..32].iter().all(|&b| b == 0));

    // Decompose b into b_lo (lower 128 bits) and b_hi (upper 128 bits)
    // b = b_lo + b_hi * 2^128
    let b_bytes = b.as_bytes();

    let mut b_lo_bytes = [0u8; 32];
    let mut b_hi_bytes = [0u8; 32];

    // Copy lower 16 bytes to b_lo, upper 16 bytes to b_hi
    b_lo_bytes[..16].copy_from_slice(&b_bytes[..16]);
    b_hi_bytes[..16].copy_from_slice(&b_bytes[16..]);

    let b_lo = Scalar::from_canonical_bytes(b_lo_bytes).unwrap();
    let b_hi = Scalar::from_canonical_bytes(b_hi_bytes).unwrap();

    // Compute NAF representations (all scalars are now ~128 bits)
    let a1_naf = a1.non_adjacent_form(5);
    let a2_naf = a2.non_adjacent_form(5);
    let b_lo_naf = b_lo.non_adjacent_form(5);
    let b_hi_naf = b_hi.non_adjacent_form(5);

    // Find starting index - check all NAFs up to bit 127
    // (with potential carry to bit 128 or 129)
    let mut i = HEEA_MAX_INDEX;
    for j in (0..HEEA_MAX_INDEX).rev() {
        i = j;
        if a1_naf[i] != 0 || a2_naf[i] != 0 || b_lo_naf[i] != 0 || b_hi_naf[i] != 0 {
            break;
        }
    }

    // Create lookup tables
    let table_A1 = NafLookupTable5::<ProjectiveNielsPoint>::from(A1);
    let table_A2 = NafLookupTable5::<ProjectiveNielsPoint>::from(A2);

    #[cfg(feature = "precomputed-tables")]
    let table_B = &constants::AFFINE_ODD_MULTIPLES_OF_BASEPOINT;
    #[cfg(not(feature = "precomputed-tables"))]
    let table_B =
        &NafLookupTable5::<ProjectiveNielsPoint>::from(&constants::ED25519_BASEPOINT_POINT);

    // B' = B * 2^128 (precomputed constant point)
    #[cfg(feature = "precomputed-tables")]
    let table_B_128 = &constants::AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128;
    #[cfg(not(feature = "precomputed-tables"))]
    let table_B_128 =
        &NafLookupTable5::<ProjectiveNielsPoint>::from(&constants::ED25519_BASEPOINT_128_POINT);

    let mut r = ProjectivePoint::identity();

    loop {
        let mut t = r.double();

        // Add contributions from a1*A1
        match a1_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_A1.select(a1_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_A1.select(-a1_naf[i] as usize),
            Ordering::Equal => {}
        }

        // Add contributions from a2*A2
        match a2_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_A2.select(a2_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_A2.select(-a2_naf[i] as usize),
            Ordering::Equal => {}
        }

        // Add contributions from b_lo*B
        match b_lo_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_B.select(b_lo_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_B.select(-b_lo_naf[i] as usize),
            Ordering::Equal => {}
        }

        // Add contributions from b_hi*B' where B' = B * 2^128
        match b_hi_naf[i].cmp(&0) {
            Ordering::Greater => t = &t.as_extended() + &table_B_128.select(b_hi_naf[i] as usize),
            Ordering::Less => t = &t.as_extended() - &table_B_128.select(-b_hi_naf[i] as usize),
            Ordering::Equal => {}
        }

        r = t.as_projective();

        if i == 0 {
            break;
        }
        i -= 1;
    }

    r.as_extended()
}
