// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2019 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Implementations of various scalar multiplication algorithms.
//!
//! Note that all of these implementations use serial code for field
//! arithmetic with the multi-model strategy described in the
//! `curve_models` module.  The vectorized AVX2 backend has its own
//! scalar multiplication implementations, since it only uses one
//! curve model.

pub mod variable_base;

pub mod vartime_double_base;

#[cfg(feature = "alloc")]
pub mod straus;

#[cfg(feature = "alloc")]
pub mod precomputed_straus;

#[cfg(feature = "alloc")]
pub mod pippenger;
