// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

// See the comment above the ristretto::notes module.
#![cfg_attr(
    all(feature = "nightly", feature = "stage2_build"), doc(include = "../docs/avx2-notes.md")
)]

pub(crate) mod field;

pub(crate) mod edwards;

pub(crate) mod constants;

pub(crate) mod scalar_mul;
