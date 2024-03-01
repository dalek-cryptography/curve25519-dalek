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
#[cfg(all(target_arch="x86_64"))]
pub mod packed_simd;


#[cfg(all(target_arch="x86_64"))]
pub mod avx2;

#[cfg(all(nightly, target_arch="x86_64"))]
pub mod ifma;

#[cfg(all(nightly, target_arch="aarch64"))]
pub mod neon;

pub mod scalar_mul;
