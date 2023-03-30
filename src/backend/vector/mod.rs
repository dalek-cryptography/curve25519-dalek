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

#![doc = include_str!("../../../docs/parallel-formulas.md")]

#[cfg(not(any(
    target_feature = "avx2",
    all(target_feature = "avx512ifma", nightly),
    docsrs
)))]
compile_error!("'simd' backend selected without target_feature=+avx2 or +avx512ifma");

#[allow(missing_docs)]
pub mod packed_simd;

#[cfg(any(
    all(
        target_feature = "avx2",
        not(all(target_feature = "avx512ifma", nightly))
    ),
    all(docsrs, target_arch = "x86_64")
))]
pub mod avx2;
#[cfg(any(
    all(
        target_feature = "avx2",
        not(all(target_feature = "avx512ifma", nightly))
    ),
    all(docsrs, target_arch = "x86_64")
))]
pub(crate) use self::avx2::{edwards::CachedPoint, edwards::ExtendedPoint};

#[cfg(any(
    all(target_feature = "avx512ifma", nightly),
    all(docsrs, target_arch = "x86_64")
))]
pub mod ifma;
#[cfg(all(target_feature = "avx512ifma", nightly))]
pub(crate) use self::ifma::{edwards::CachedPoint, edwards::ExtendedPoint};

#[cfg(any(
    target_feature = "avx2",
    all(target_feature = "avx512ifma", nightly),
    all(docsrs, target_arch = "x86_64")
))]
#[allow(missing_docs)]
pub mod scalar_mul;

// Precomputed table re-exports

#[cfg(any(
    all(
        target_feature = "avx2",
        not(all(target_feature = "avx512ifma", nightly)),
        feature = "precomputed-tables"
    ),
    all(docsrs, target_arch = "x86_64")
))]
pub(crate) use self::avx2::constants::BASEPOINT_ODD_LOOKUP_TABLE;

#[cfg(all(target_feature = "avx512ifma", nightly, feature = "precomputed-tables"))]
pub(crate) use self::ifma::constants::BASEPOINT_ODD_LOOKUP_TABLE;
