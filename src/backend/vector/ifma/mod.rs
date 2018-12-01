// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2018 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Henry de Valence <hdevalence@hdevalence.ca>

#![cfg_attr(
    all(feature = "nightly", feature = "stage2_build"),
    doc(include = "../docs/ifma-notes.md")
)]

pub mod field;

pub mod edwards;

pub mod constants;
