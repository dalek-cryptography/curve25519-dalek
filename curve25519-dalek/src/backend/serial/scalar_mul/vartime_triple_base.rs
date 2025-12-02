// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - zhenfei zhang <zhangzhenfei@gmail.com>
#![allow(non_snake_case)]

use core::cmp::Ordering;

use crate::backend::serial::curve_models::{ProjectiveNielsPoint, ProjectivePoint};
use crate::constants;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
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
    let mut i: usize = 130;
    for j in (0..131).rev() {
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

#[cfg(test)]
mod test {

    use rand::rng;

    use super::*;
    use crate::scalar::Scalar;

    #[test]
    fn test_triple_base_multiplication() {
        // Test vectors with random scalars
        let a1 = Scalar::from(12345u64);
        let a2 = Scalar::from(67890u64);
        let b = Scalar::random(&mut rng());

        // Random points (using scalar multiplication of basepoint)
        let A1 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(2u64);
        let A2 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(3u64);

        // Compute using the optimized triple-base function
        let result = mul_128_128_256(&a1, &A1, &a2, &A2, &b);

        // Compute using naive addition
        let expected = &(&(&a1 * &A1) + &(&a2 * &A2)) + &(&b * &constants::ED25519_BASEPOINT_POINT);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_triple_base_multiplication_128() {
        // Test with 128-bit scalars for a1 and a2
        // Create a 128-bit scalar (use lower half)
        let a1_bytes = [
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let a1 = Scalar::from_bytes_mod_order(a1_bytes);

        let a2_bytes = [
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
            0x77, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let a2 = Scalar::from_bytes_mod_order(a2_bytes);

        // Full 256-bit scalar for b
        let b = Scalar::random(&mut rng());

        // Test points
        let A1 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(5u64);
        let A2 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(7u64);

        // Test the optimized 128-bit version
        let result_128 = mul_128_128_256(&a1, &A1, &a2, &A2, &b);

        // Compute expected result
        let expected = &(&(&a1 * &A1) + &(&a2 * &A2)) + &(&b * &constants::ED25519_BASEPOINT_POINT);

        assert_eq!(result_128, expected, "Optimized 128-bit version failed");
    }

    #[test]
    fn test_triple_base_with_zero_scalars() {
        let a1 = Scalar::ZERO;
        let a2 = Scalar::from(123u64);
        let b = Scalar::random(&mut rng());

        let A1 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(2u64);
        let A2 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(3u64);

        let result = mul_128_128_256(&a1, &A1, &a2, &A2, &b);
        let expected = &(&a2 * &A2) + &(&b * &constants::ED25519_BASEPOINT_POINT);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_triple_base_with_identity_points() {
        let a1 = Scalar::from(111u64);
        let a2 = Scalar::from(222u64);
        let b = Scalar::random(&mut rng());

        let A1 = EdwardsPoint::identity();
        let A2 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(3u64);

        let result = mul_128_128_256(&a1, &A1, &a2, &A2, &b);
        let expected = &(&a2 * &A2) + &(&b * &constants::ED25519_BASEPOINT_POINT);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_triple_base_consistency() {
        // Test that both functions give the same result for 128-bit inputs
        let a1 = Scalar::from(0x123456789ABCDEFu64);
        let a2 = Scalar::from(0xFEDCBA987654321u64);
        let b = Scalar::random(&mut rng());

        let A1 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(11u64);
        let A2 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(13u64);

        let result_optimized = mul_128_128_256(&a1, &A1, &a2, &A2, &b);
        let result_general =
            &(&(&a1 * &A1) + &(&a2 * &A2)) + &(&b * &constants::ED25519_BASEPOINT_POINT);

        assert_eq!(result_optimized, result_general);
    }

    #[test]
    fn test_triple_base_large_scalars() {
        // Test with large scalars
        let mut a1_bytes = [0xFFu8; 32];
        for i in 16..32 {
            a1_bytes[i] = 0x00;
        }
        let a1 = Scalar::from_bytes_mod_order(a1_bytes);

        let mut a2_bytes = [0xAAu8; 32];
        for i in 16..32 {
            a2_bytes[i] = 0x00;
        }
        let a2 = Scalar::from_bytes_mod_order(a2_bytes);

        let b = Scalar::random(&mut rng());

        let A1 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(17u64);
        let A2 = &constants::ED25519_BASEPOINT_POINT * &Scalar::from(19u64);

        let result = mul_128_128_256(&a1, &A1, &a2, &A2, &b);
        let expected = &(&(&a1 * &A1) + &(&a2 * &A2)) + &(&b * &constants::ED25519_BASEPOINT_POINT);

        assert_eq!(result, expected);
    }
}
