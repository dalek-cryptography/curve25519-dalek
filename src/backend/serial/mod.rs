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

//! Serial implementations of field, scalar, point arithmetic.
//!
//! When the vector backend is disabled, the crate uses the mixed-model strategy
//! for implementing point operations and scalar multiplication; see the
//! [`curve_models`] and [`scalar_mul`] documentation for more information.
//!
//! When the vector backend is enabled, the field and scalar
//! implementations are still used for non-vectorized operations.

use cfg_if::cfg_if;

cfg_if! {
    if #[cfg(feature = "fiat_backend")] {
        #[cfg(not(target_pointer_width = "64"))]
        #[cfg_attr(
            docsrs,
            doc(cfg(all(feature = "fiat_backend", not(target_pointer_width = "64"))))
        )]
        pub mod fiat_u32;

        #[cfg(target_pointer_width = "64")]
        #[cfg_attr(
            docsrs,
            doc(cfg(all(feature = "fiat_backend", target_pointer_width = "64")))
        )]
        pub mod fiat_u64;
    } else {
        #[cfg(not(target_pointer_width = "64"))]
        #[cfg_attr(docsrs, doc(cfg(not(target_pointer_width = "64"))))]
        pub mod u32;

        #[cfg(target_pointer_width = "64")]
        #[cfg_attr(docsrs, doc(cfg(target_pointer_width = "64")))]
        pub mod u64;
    }
}

pub mod curve_models;

#[cfg(not(all(
    feature = "simd_backend",
    any(target_feature = "avx2", target_feature = "avx512ifma")
)))]
#[cfg_attr(
    docsrs,
    doc(cfg(not(all(
        feature = "simd_backend",
        any(target_feature = "avx2", target_feature = "avx512ifma")
    ))))
)]
pub mod scalar_mul;
