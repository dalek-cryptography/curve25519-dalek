// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "alloc", feature(alloc))]
#![cfg_attr(feature = "nightly", feature(i128_type))]
#![cfg_attr(feature = "nightly", feature(cfg_target_feature))]
#![cfg_attr(feature = "bench", feature(test))]
#![cfg_attr(all(feature = "nightly", feature = "std"), feature(zero_one))]

#![allow(unused_features)]
#![deny(missing_docs)] // refuse to compile if documentation is missing

//! # curve25519-dalek
//!
//! **A high-performance, pure-Rust implementation of group operations for Ristretto and Curve25519.**
//!
//! **[SPOILER ALERT]** The Twelfth Doctor's first encounter with the Daleks is
//! in his second full episode, "Into the Dalek".  A beleaguered ship of the
//! "Combined Galactic Resistance" has discovered a broken Dalek that has
//! turned "good", desiring to kill all other Daleks.  The Doctor, Clara and a
//! team of soldiers are miniaturized and enter the Dalek, which the Doctor
//! names Rusty.  They repair the damage, but accidentally restore it to its
//! original nature, causing it to go on the rampage and alert the Dalek fleet
//! to the whereabouts of the rebel ship.  However, the Doctor manages to
//! return Rusty to its previous state by linking his mind with the Dalek's:
//! Rusty shares the Doctor's view of the universe's beauty, but also his deep
//! hatred of the Daleks.  Rusty destroys the other Daleks and departs the
//! ship, determined to track down and bring an end to the Dalek race.

//------------------------------------------------------------------------
// External dependencies:
//------------------------------------------------------------------------

#[cfg(feature = "std")]
extern crate core;

#[cfg(feature = "std")]
extern crate rand;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(all(test, feature = "bench"))]
extern crate test;

#[cfg(feature = "yolocrypto")]
extern crate stdsimd;

// The `Digest` trait is implemented using `generic_array`, so we need it
// too. Hopefully we can eliminate `generic_array` from `Digest` once const
// generics land.
extern crate digest;
extern crate generic_array;

// Used for traits related to constant-time code.
extern crate subtle;

#[cfg(feature = "serde")]
extern crate serde;
#[cfg(all(test, feature = "serde"))]
extern crate serde_cbor;

//------------------------------------------------------------------------
// curve25519-dalek public modules
//------------------------------------------------------------------------

// Scalar arithmetic mod l = 2^252 + ..., the order of the Ristretto group
pub mod scalar;
// Point operations on the Montgomery form of Curve25519
pub mod montgomery;
// Point operations on the Edwards form of Curve25519
pub mod edwards;
// Group operations on the Ristretto group
pub mod ristretto;
// Useful constants, like the Ed25519 basepoint
pub mod constants;
// External (and internal) traits.
pub mod traits;

//------------------------------------------------------------------------
// curve25519-dalek internal modules
//------------------------------------------------------------------------

// Finite field arithmetic mod p = 2^255 - 19
pub(crate) mod field;

// Arithmetic backends (using u32, u64, etc) live here
pub(crate) mod backend;

// Internal curve models which are not part of the public API.
pub(crate) mod curve_models;
