// -*- mode: rust; coding: utf-8; -*-
//
// To the extent possible under law, the authors have waived all copyright and
// related or neighboring rights to curve25519-dalek, using the Creative
// Commons "CC0" public domain dedication.
// See <http://creativecommons.org/publicdomain/zero/.0/> for full details.
//
// Authors:
//  - Isis Agora Lovecruft <isis@patternsinthevoid.net>
//  - Henry de Valence <hdevalence@hdevalence.ca>

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "alloc", feature(alloc))]
#![cfg_attr(feature = "nightly", feature(i128_type))]
#![cfg_attr(feature = "bench", feature(test))]
#![cfg_attr(all(feature = "nightly", feature = "std"), feature(zero_one))]

#![allow(unused_features)]
#![deny(missing_docs)] // refuse to compile if documentation is missing

//! # curve25519-dalek
//!
//! **A Rust implementation of field and group operations on an Edwards curve
//! over GF(2^255 - 19).**
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

#[cfg(all(test, feature = "bench"))]
extern crate test;

#[cfg(test)]
extern crate sha2;

#[macro_use]
extern crate arrayref;

extern crate generic_array;
extern crate digest;
extern crate subtle;

#[cfg(feature = "serde")]
extern crate serde;
#[cfg(all(test, feature = "serde"))]
extern crate serde_cbor;

#[cfg(feature = "std")]
extern crate core;

#[cfg(feature = "std")]
extern crate rand;

#[cfg(feature = "alloc")]
extern crate alloc;

// Modules for low-level operations directly on field elements and curve points.

pub mod field;
pub mod scalar;
pub mod curve;

// Feature gate decaf while our implementation is unfinished and probably incorrect.
#[cfg(feature = "yolocrypto")]
pub mod decaf;

// Other miscelaneous utilities.

pub mod utils;

// Low-level curve and point constants, as well as pre-computed curve group elements.

pub mod constants;
