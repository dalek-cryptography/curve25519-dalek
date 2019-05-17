// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

pub mod variable_base;

pub mod vartime_double_base;

#[cfg(any(feature = "alloc", feature = "std"))]
pub mod straus;

#[cfg(any(feature = "alloc", feature = "std"))]
pub mod precomputed_straus;
