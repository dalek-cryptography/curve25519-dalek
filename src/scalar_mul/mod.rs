// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
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

pub mod window;

pub mod variable_base;

#[cfg(feature = "stage2_build")]
pub mod vartime_double_base;

pub mod straus;

pub mod pippenger;
