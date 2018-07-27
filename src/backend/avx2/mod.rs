// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

// Conditionally include the AVX2 notes if:
// - we're on nightly (so we can include docs at all)
// - we're in stage 2 of the build.
// The latter point prevents a really silly and annoying problem,
// where the location of ".." is different depending on whether we're
// building the crate for real, or whether we're in build.rs
// generating the lookup tables (in which case we're relative to the
// location of build.rs, not lib.rs, so the markdown file appears
// missing).
#![cfg_attr(
    all(feature = "nightly", feature = "stage2_build"), doc(include = "../docs/avx2-notes.md")
)]

pub(crate) mod field;

pub(crate) mod edwards;

pub(crate) mod constants;

pub(crate) mod scalar_mul;
