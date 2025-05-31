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

#[allow(missing_docs)]
pub mod packed_simd;

pub mod avx2;

#[cfg(all(curve25519_dalek_backend = "unstable_avx512", nightly))]
pub mod ifma;

pub mod scalar_mul;
