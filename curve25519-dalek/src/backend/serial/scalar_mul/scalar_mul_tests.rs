//! Tests for verifying Verus-compatible implementations match original implementations.
//!
//! These tests compare the _verus versions of multiscalar multiplication functions
//! against their original implementations to ensure functional equivalence.
#![cfg(test)]

use crate::constants;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::{MultiscalarMul, VartimeMultiscalarMul};
use alloc::vec::Vec;

use super::pippenger::Pippenger;
use super::straus::Straus;

#[test]
fn test_pippenger_original_vs_verus() {
    // Test sizes covering all window width cases:
    // w=6 for size < 500, w=7 for 500 <= size < 800, w=8 for size >= 800
    let test_sizes = [
        1, 2, 3, 4, 8, 16, 32, 64, 128, 256, 499, 500, 501, 799, 800, 801, 1000,
    ];

    let num_rounds = 20; // Random rounds per size
    let mut total_comparisons = 0;

    for size in test_sizes {
        for round in 0..num_rounds {
            // Generate pseudo-random scalars and points using deterministic seeds
            // Different seed for each (size, round) combination
            let seed_base = (size as u64) * 1000 + (round as u64);

            let points: Vec<_> = (0..size)
                .map(|i| {
                    let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                    constants::ED25519_BASEPOINT_POINT * seed
                })
                .collect();

            let scalars: Vec<_> = (0..size)
                .map(|i| {
                    let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                    let b = Scalar::from((i as u64) + 1);
                    a * b // Mix to get varied scalars
                })
                .collect();

            // Original implementation
            let original = Pippenger::optional_multiscalar_mul(
                scalars.iter(),
                points.iter().map(|p| Some(*p)),
            );

            // Verus implementation
            let verus = Pippenger::optional_multiscalar_mul_verus(
                scalars.iter(),
                points.iter().map(|p| Some(*p)),
            );

            assert!(
                original.is_some(),
                "Original returned None at size={}, round={}",
                size,
                round
            );
            assert!(
                verus.is_some(),
                "Verus returned None at size={}, round={}",
                size,
                round
            );

            assert_eq!(
                original.unwrap().compress(),
                verus.unwrap().compress(),
                "Mismatch at size={}, round={}",
                size,
                round
            );

            total_comparisons += 1;
        }
    }

    println!(
        "Pippenger original vs verus: {} comparisons passed!",
        total_comparisons
    );
}

#[test]
fn test_straus_optional_original_vs_verus() {
    // Test various sizes
    let test_sizes = [1, 2, 3, 4, 8, 16, 32, 64, 100, 150];

    let num_rounds = 20; // Random rounds per size
    let mut total_comparisons = 0;

    for size in test_sizes {
        for round in 0..num_rounds {
            // Generate pseudo-random scalars and points using deterministic seeds
            let seed_base = (size as u64) * 1000 + (round as u64);

            let points: Vec<_> = (0..size)
                .map(|i| {
                    let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                    constants::ED25519_BASEPOINT_POINT * seed
                })
                .collect();

            let scalars: Vec<_> = (0..size)
                .map(|i| {
                    let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                    let b = Scalar::from((i as u64) + 1);
                    a * b
                })
                .collect();

            // Original implementation
            let original =
                Straus::optional_multiscalar_mul(scalars.iter(), points.iter().map(|p| Some(*p)));

            // Verus implementation
            let verus = Straus::optional_multiscalar_mul_verus(
                scalars.iter(),
                points.iter().map(|p| Some(*p)),
            );

            assert!(
                original.is_some(),
                "Original returned None at size={}, round={}",
                size,
                round
            );
            assert!(
                verus.is_some(),
                "Verus returned None at size={}, round={}",
                size,
                round
            );

            assert_eq!(
                original.unwrap().compress(),
                verus.unwrap().compress(),
                "Mismatch at size={}, round={}",
                size,
                round
            );

            total_comparisons += 1;
        }
    }

    println!(
        "Straus optional original vs verus: {} comparisons passed!",
        total_comparisons
    );
}

#[test]
fn test_straus_multiscalar_original_vs_verus() {
    // Test various sizes (constant-time multiscalar_mul)
    let test_sizes = [1, 2, 3, 4, 8, 16, 32, 64, 100, 150];

    let num_rounds = 20; // Random rounds per size
    let mut total_comparisons = 0;

    for size in test_sizes {
        for round in 0..num_rounds {
            // Generate pseudo-random scalars and points using deterministic seeds
            let seed_base = (size as u64) * 1000 + (round as u64);

            let points: Vec<_> = (0..size)
                .map(|i| {
                    let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                    constants::ED25519_BASEPOINT_POINT * seed
                })
                .collect();

            let scalars: Vec<_> = (0..size)
                .map(|i| {
                    let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                    let b = Scalar::from((i as u64) + 1);
                    a * b
                })
                .collect();

            // Original implementation (via trait)
            let original = Straus::multiscalar_mul(scalars.iter(), points.iter());

            // Verus implementation
            let verus = Straus::multiscalar_mul_verus(scalars.iter(), points.iter());

            assert_eq!(
                original.compress(),
                verus.compress(),
                "Mismatch at size={}, round={}",
                size,
                round
            );

            total_comparisons += 1;
        }
    }

    println!(
        "Straus multiscalar_mul original vs verus: {} comparisons passed!",
        total_comparisons
    );
}

#[test]
fn test_edwards_optional_dispatcher_original_vs_verus() {
    // Test sizes on both sides of the dispatch threshold (190)
    // size < 190: uses Straus
    // size >= 190: uses Pippenger
    let test_sizes = [1, 10, 50, 100, 150, 189, 190, 191, 200, 300];

    let num_rounds = 10;
    let mut total_comparisons = 0;

    for size in test_sizes {
        for round in 0..num_rounds {
            let seed_base = (size as u64) * 1000 + (round as u64);

            let points: Vec<_> = (0..size)
                .map(|i| {
                    let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                    constants::ED25519_BASEPOINT_POINT * seed
                })
                .collect();

            let scalars: Vec<_> = (0..size)
                .map(|i| {
                    let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                    let b = Scalar::from((i as u64) + 1);
                    a * b
                })
                .collect();

            // Original EdwardsPoint dispatcher
            let original = EdwardsPoint::optional_multiscalar_mul(
                scalars.iter(),
                points.iter().map(|p| Some(*p)),
            );

            // Verus EdwardsPoint dispatcher
            let verus = EdwardsPoint::optional_multiscalar_mul_verus(
                scalars.iter().cloned(),
                points.iter().map(|p| Some(*p)),
            );

            assert!(
                original.is_some(),
                "Original returned None at size={}, round={}",
                size,
                round
            );
            assert!(
                verus.is_some(),
                "Verus returned None at size={}, round={}",
                size,
                round
            );

            assert_eq!(
                original.unwrap().compress(),
                verus.unwrap().compress(),
                "Mismatch at size={}, round={}",
                size,
                round
            );

            total_comparisons += 1;
        }
    }

    println!(
        "Edwards optional dispatcher original vs verus: {} comparisons passed!",
        total_comparisons
    );
}

#[test]
fn test_edwards_multiscalar_dispatcher_original_vs_verus() {
    // Test sizes (constant-time version only dispatches to Straus)
    let test_sizes = [1, 10, 50, 100, 150, 189];

    let num_rounds = 10;
    let mut total_comparisons = 0;

    for size in test_sizes {
        for round in 0..num_rounds {
            let seed_base = (size as u64) * 1000 + (round as u64);

            let points: Vec<_> = (0..size)
                .map(|i| {
                    let seed = Scalar::from(seed_base + (i as u64) * 7 + 1);
                    constants::ED25519_BASEPOINT_POINT * seed
                })
                .collect();

            let scalars: Vec<_> = (0..size)
                .map(|i| {
                    let a = Scalar::from(seed_base * 3 + (i as u64) * 13 + 5);
                    let b = Scalar::from((i as u64) + 1);
                    a * b
                })
                .collect();

            // Original EdwardsPoint dispatcher (via trait)
            let original = EdwardsPoint::multiscalar_mul(scalars.iter(), points.iter());

            // Verus EdwardsPoint dispatcher
            let verus = EdwardsPoint::multiscalar_mul_verus(scalars.iter(), points.iter());

            assert_eq!(
                original.compress(),
                verus.compress(),
                "Mismatch at size={}, round={}",
                size,
                round
            );

            total_comparisons += 1;
        }
    }

    println!(
        "Edwards multiscalar_mul dispatcher original vs verus: {} comparisons passed!",
        total_comparisons
    );
}
