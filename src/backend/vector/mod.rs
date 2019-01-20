// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

// Conditionally include the notes if:
// - we're on nightly (so we can include docs at all)
// - we're in stage 2 of the build.
// The latter point prevents a really silly and annoying problem,
// where the location of ".." is different depending on whether we're
// building the crate for real, or whether we're in build.rs
// generating the lookup tables (in which case we're relative to the
// location of build.rs, not lib.rs, so the markdown file appears
// missing).
#![cfg_attr(
    all(feature = "nightly", feature = "stage2_build"),
    doc(include = "../docs/parallel-formulas.md")
)]

#[cfg(not(any(target_feature = "avx2", target_feature = "avx512ifma",)))]
compile_error!("simd_backend selected without target_feature=+avx2 or +avx512ifma");

#[cfg(any(all(target_feature = "avx2", not(target_feature = "avx512ifma")), rustdoc))]
#[doc(cfg(all(target_feature = "avx2", not(target_feature = "avx512ifma"))))]
pub mod avx2;
#[cfg(all(target_feature = "avx2", not(target_feature = "avx512ifma")))]
pub(crate) use self::avx2::{
    constants::BASEPOINT_ODD_LOOKUP_TABLE, edwards::CachedPoint, edwards::ExtendedPoint,
};

#[cfg(any(target_feature = "avx512ifma", rustdoc))]
#[doc(cfg(target_feature = "avx512ifma"))]
pub mod ifma;
#[cfg(target_feature = "avx512ifma")]
pub(crate) use self::ifma::{
    constants::BASEPOINT_ODD_LOOKUP_TABLE, edwards::CachedPoint, edwards::ExtendedPoint,
};

pub mod scalar_mul;
