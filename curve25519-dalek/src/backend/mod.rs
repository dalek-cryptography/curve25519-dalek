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
//! **INTERNALS:** Pluggable implementations for different architectures.
//!
//! The backend code is split into two parts: a serial backend,
//! and a vector backend.
//!
//! The [`serial`] backend contains 32- and 64-bit implementations of
//! field arithmetic and scalar arithmetic, as well as implementations
//! of point operations using the mixed-model strategy (passing
//! between different curve models depending on the operation).
//!
//! The [`vector`] backend contains implementations of vectorized
//! field arithmetic, used to implement point operations using a novel
//! implementation strategy derived from parallel formulas of Hisil,
//! Wong, Carter, and Dawson.
//!
//! Because the two strategies give rise to different curve models,
//! it's not possible to reuse exactly the same scalar multiplication
//! code (or to write it generically), so both serial and vector
//! backends contain matching implementations of scalar multiplication
//! algorithms.  These are intended to be selected by a `#[cfg]`-based
//! type alias.
//!
//! The [`vector`] backend is selected by the `simd_backend` cargo
//! feature; it uses the [`serial`] backend for non-vectorized operations.
use crate::EdwardsPoint;
use crate::Scalar;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[cfg(all(feature = "alloc", verus_keep_ghost))]
#[allow(unused_imports)]
use crate::specs::scalar_mul_specs::{
    all_points_some, spec_optional_points_from_iter, spec_points_from_iter, spec_scalars_from_iter,
    sum_of_scalar_muls, unwrap_points,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;

pub mod serial;

use vstd::prelude::*;

// #[cfg(curve25519_dalek_backend = "simd")]
// pub mod vector;

verus! {

#[derive(Copy, Clone)]
enum BackendKind {
    // #[cfg(curve25519_dalek_backend = "simd")]
    // Avx2,
    // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
    // Avx512,
    Serial,
}

#[inline]
fn get_selected_backend() -> (result: BackendKind)
    ensures
        matches!(result, BackendKind::Serial),
{
    // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
    // {
    //     cpufeatures::new!(cpuid_avx512, "avx512ifma", "avx512vl");
    //     let token_avx512: cpuid_avx512::InitToken = cpuid_avx512::init();
    //     if token_avx512.get() {
    //         return BackendKind::Avx512;
    //     }
    // }
    // #[cfg(curve25519_dalek_backend = "simd")]
    // {
    //     cpufeatures::new!(cpuid_avx2, "avx2");
    //     let token_avx2: cpuid_avx2::InitToken = cpuid_avx2::init();
    //     if token_avx2.get() {
    //         return BackendKind::Avx2;
    //     }
    // }
    BackendKind::Serial
}

} // verus!
#[allow(missing_docs)]
#[cfg(feature = "alloc")]
pub fn pippenger_optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<EdwardsPoint>
where
    I: IntoIterator,
    I::Item: core::borrow::Borrow<Scalar>,
    J: IntoIterator<Item = Option<EdwardsPoint>>,
{
    use crate::traits::VartimeMultiscalarMul;

    match get_selected_backend() {
        // #[cfg(curve25519_dalek_backend = "simd")]
        // BackendKind::Avx2 =>
        //     vector::scalar_mul::pippenger::spec_avx2::Pippenger::optional_multiscalar_mul::<I, J>(scalars, points),
        // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
        // BackendKind::Avx512 =>
        //     vector::scalar_mul::pippenger::spec_avx512ifma_avx512vl::Pippenger::optional_multiscalar_mul::<I, J>(scalars, points),
        BackendKind::Serial => {
            serial::scalar_mul::pippenger::Pippenger::optional_multiscalar_mul::<I, J>(
                scalars, points,
            )
        }
    }
}

#[cfg(feature = "alloc")]
pub(crate) enum VartimePrecomputedStraus {
    // #[cfg(curve25519_dalek_backend = "simd")]
    // Avx2(vector::scalar_mul::precomputed_straus::spec_avx2::VartimePrecomputedStraus),
    // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
    // Avx512ifma(
    //     vector::scalar_mul::precomputed_straus::spec_avx512ifma_avx512vl::VartimePrecomputedStraus,
    // ),
    Scalar(serial::scalar_mul::precomputed_straus::VartimePrecomputedStraus),
}

#[cfg(feature = "alloc")]
impl VartimePrecomputedStraus {
    pub fn new<I>(static_points: I) -> Self
    where
        I: IntoIterator,
        I::Item: core::borrow::Borrow<EdwardsPoint>,
    {
        use crate::traits::VartimePrecomputedMultiscalarMul;

        match get_selected_backend() {
            // #[cfg(curve25519_dalek_backend = "simd")]
            // BackendKind::Avx2 =>
            //     VartimePrecomputedStraus::Avx2(vector::scalar_mul::precomputed_straus::spec_avx2::VartimePrecomputedStraus::new(static_points)),
            // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
            // BackendKind::Avx512 =>
            //     VartimePrecomputedStraus::Avx512ifma(vector::scalar_mul::precomputed_straus::spec_avx512ifma_avx512vl::VartimePrecomputedStraus::new(static_points)),
            BackendKind::Serial => VartimePrecomputedStraus::Scalar(
                serial::scalar_mul::precomputed_straus::VartimePrecomputedStraus::new(
                    static_points,
                ),
            ),
        }
    }

    pub fn optional_mixed_multiscalar_mul<I, J, K>(
        &self,
        static_scalars: I,
        dynamic_scalars: J,
        dynamic_points: K,
    ) -> Option<EdwardsPoint>
    where
        I: IntoIterator,
        I::Item: core::borrow::Borrow<Scalar>,
        J: IntoIterator,
        J::Item: core::borrow::Borrow<Scalar>,
        K: IntoIterator<Item = Option<EdwardsPoint>>,
    {
        use crate::traits::VartimePrecomputedMultiscalarMul;

        match self {
            // #[cfg(curve25519_dalek_backend = "simd")]
            // VartimePrecomputedStraus::Avx2(inner) => inner.optional_mixed_multiscalar_mul(
            //     static_scalars,
            //     dynamic_scalars,
            //     dynamic_points,
            // ),
            // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
            // VartimePrecomputedStraus::Avx512ifma(inner) => inner.optional_mixed_multiscalar_mul(
            //     static_scalars,
            //     dynamic_scalars,
            //     dynamic_points,
            // ),
            VartimePrecomputedStraus::Scalar(inner) => inner.optional_mixed_multiscalar_mul(
                static_scalars,
                dynamic_scalars,
                dynamic_points,
            ),
        }
    }
}

#[allow(missing_docs)]
#[cfg(feature = "alloc")]
pub fn straus_multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint
where
    I: IntoIterator,
    I::Item: core::borrow::Borrow<Scalar>,
    J: IntoIterator,
    J::Item: core::borrow::Borrow<EdwardsPoint>,
{
    use crate::traits::MultiscalarMul;

    match get_selected_backend() {
        // #[cfg(curve25519_dalek_backend = "simd")]
        // BackendKind::Avx2 => {
        //     vector::scalar_mul::straus::spec_avx2::Straus::multiscalar_mul::<I, J>(scalars, points)
        // }
        // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
        // BackendKind::Avx512 => {
        //     vector::scalar_mul::straus::spec_avx512ifma_avx512vl::Straus::multiscalar_mul::<I, J>(
        //         scalars, points,
        //     )
        // }
        BackendKind::Serial => {
            serial::scalar_mul::straus::Straus::multiscalar_mul::<I, J>(scalars, points)
        }
    }
}

#[allow(missing_docs)]
#[cfg(feature = "alloc")]
pub fn straus_optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<EdwardsPoint>
where
    I: IntoIterator,
    I::Item: core::borrow::Borrow<Scalar>,
    J: IntoIterator<Item = Option<EdwardsPoint>>,
{
    use crate::traits::VartimeMultiscalarMul;

    match get_selected_backend() {
        // #[cfg(curve25519_dalek_backend = "simd")]
        // BackendKind::Avx2 => {
        //     vector::scalar_mul::straus::spec_avx2::Straus::optional_multiscalar_mul::<I, J>(
        //         scalars, points,
        //     )
        // }
        // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
        // BackendKind::Avx512 => {
        //     vector::scalar_mul::straus::spec_avx512ifma_avx512vl::Straus::optional_multiscalar_mul::<
        //         I,
        //         J,
        //     >(scalars, points)
        // }
        BackendKind::Serial => {
            serial::scalar_mul::straus::Straus::optional_multiscalar_mul::<I, J>(scalars, points)
        }
    }
}

verus! {

/// Perform constant-time, variable-base scalar multiplication.
/// Computes scalar * point on the Ed25519 curve.
pub fn variable_base_mul(point: &EdwardsPoint, scalar: &Scalar) -> (result: EdwardsPoint)
    requires
// as_radix_16 requires scalar.bytes[31] <= 127 (MSB clear, i.e. scalar < 2^255)

        scalar.bytes[31] <= 127,
        // Input point must be well-formed (valid coordinates with proper limb bounds)
        is_well_formed_edwards_point(*point),
    ensures
// Result is a well-formed Edwards point

        is_well_formed_edwards_point(result),
        // Functional correctness: result represents scalar * point
        edwards_point_as_affine(result) == edwards_scalar_mul(
            edwards_point_as_affine(*point),
            spec_scalar(scalar),
        ),
{
    match get_selected_backend() {
        // #[cfg(curve25519_dalek_backend = "simd")]
        // BackendKind::Avx2 => vector::scalar_mul::variable_base::spec_avx2::mul(point, scalar),
        // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
        // BackendKind::Avx512 => {
        //     vector::scalar_mul::variable_base::spec_avx512ifma_avx512vl::mul(point, scalar)
        // }
        BackendKind::Serial => serial::scalar_mul::variable_base::mul(point, scalar),
    }
}

/// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
#[allow(non_snake_case)]
pub fn vartime_double_base_mul(a: &Scalar, A: &EdwardsPoint, b: &Scalar) -> (result: EdwardsPoint)
    requires
        is_well_formed_edwards_point(*A),
    ensures
        is_well_formed_edwards_point(result),
        // Functional correctness: result = a*A + b*B where B is the Ed25519 basepoint
        edwards_point_as_affine(result) == {
            let aA = edwards_scalar_mul(edwards_point_as_affine(*A), spec_scalar(a));
            let bB = edwards_scalar_mul(spec_ed25519_basepoint(), spec_scalar(b));
            edwards_add(aA.0, aA.1, bB.0, bB.1)
        },
{
    match get_selected_backend() {
        // #[cfg(curve25519_dalek_backend = "simd")]
        // BackendKind::Avx2 => vector::scalar_mul::vartime_double_base::spec_avx2::mul(a, A, b),
        // #[cfg(all(curve25519_dalek_backend = "simd", nightly))]
        // BackendKind::Avx512 => {
        //     vector::scalar_mul::vartime_double_base::spec_avx512ifma_avx512vl::mul(a, A, b)
        // }
        BackendKind::Serial => serial::scalar_mul::vartime_double_base::mul(a, A, b),
    }
}

/// Verus-compatible Straus multiscalar multiplication dispatcher.
/// Uses Iterator instead of IntoIterator (Verus doesn't support I::Item projections).
#[allow(missing_docs)]
#[cfg(feature = "alloc")]
pub fn straus_multiscalar_mul_verus<S, P, I, J>(scalars: I, points: J) -> (result:
    EdwardsPoint) where
    S: core::borrow::Borrow<Scalar>,
    P: core::borrow::Borrow<EdwardsPoint>,
    I: Iterator<Item = S> + Clone,
    J: Iterator<Item = P> + Clone,

    requires
        spec_scalars_from_iter::<S, I>(scalars).len() == spec_points_from_iter::<P, J>(
            points,
        ).len(),
        forall|i: int|
            0 <= i < spec_points_from_iter::<P, J>(points).len() ==> is_well_formed_edwards_point(
                #[trigger] spec_points_from_iter::<P, J>(points)[i],
            ),
    ensures
        is_well_formed_edwards_point(result),
        edwards_point_as_affine(result) == sum_of_scalar_muls(
            spec_scalars_from_iter::<S, I>(scalars),
            spec_points_from_iter::<P, J>(points),
        ),
{
    match get_selected_backend() {
        BackendKind::Serial => {
            serial::scalar_mul::straus::Straus::multiscalar_mul_verus(scalars, points)
        },
    }
}

/// Verus-compatible Straus optional multiscalar multiplication dispatcher.
/// Uses Iterator instead of IntoIterator (Verus doesn't support I::Item projections).
#[allow(missing_docs)]
#[cfg(feature = "alloc")]
pub fn straus_optional_multiscalar_mul_verus<S, I, J>(scalars: I, points: J) -> (result: Option<
    EdwardsPoint,
>) where
    S: core::borrow::Borrow<Scalar>,
    I: Iterator<Item = S> + Clone,
    J: Iterator<Item = Option<EdwardsPoint>> + Clone,

    requires
        spec_scalars_from_iter::<S, I>(scalars).len() == spec_optional_points_from_iter::<J>(
            points,
        ).len(),
        forall|i: int|
            0 <= i < spec_optional_points_from_iter::<J>(points).len() && (
            #[trigger] spec_optional_points_from_iter::<J>(points)[i]).is_some()
                ==> is_well_formed_edwards_point(
                spec_optional_points_from_iter::<J>(points)[i].unwrap(),
            ),
    ensures
        result.is_some() <==> all_points_some(spec_optional_points_from_iter::<J>(points)),
        result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
        result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(
            spec_scalars_from_iter::<S, I>(scalars),
            unwrap_points(spec_optional_points_from_iter::<J>(points)),
        ),
{
    match get_selected_backend() {
        BackendKind::Serial => {
            serial::scalar_mul::straus::Straus::optional_multiscalar_mul_verus(scalars, points)
        },
    }
}

/// Verus-compatible Pippenger optional multiscalar multiplication dispatcher.
/// Uses Iterator instead of IntoIterator (Verus doesn't support I::Item projections).
#[allow(missing_docs)]
#[cfg(feature = "alloc")]
pub fn pippenger_optional_multiscalar_mul_verus<S, I, J>(scalars: I, points: J) -> (result: Option<
    EdwardsPoint,
>) where
    S: core::borrow::Borrow<Scalar>,
    I: Iterator<Item = S> + Clone,
    J: Iterator<Item = Option<EdwardsPoint>> + Clone,

    requires
        spec_scalars_from_iter::<S, I>(scalars).len() == spec_optional_points_from_iter::<J>(
            points,
        ).len(),
        forall|i: int|
            0 <= i < spec_optional_points_from_iter::<J>(points).len() && (
            #[trigger] spec_optional_points_from_iter::<J>(points)[i]).is_some()
                ==> is_well_formed_edwards_point(
                spec_optional_points_from_iter::<J>(points)[i].unwrap(),
            ),
    ensures
        result.is_some() <==> all_points_some(spec_optional_points_from_iter::<J>(points)),
        result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
        result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(
            spec_scalars_from_iter::<S, I>(scalars),
            unwrap_points(spec_optional_points_from_iter::<J>(points)),
        ),
{
    match get_selected_backend() {
        BackendKind::Serial => {
            serial::scalar_mul::pippenger::Pippenger::optional_multiscalar_mul_verus(
                scalars,
                points,
            )
        },
    }
}

} // verus!
