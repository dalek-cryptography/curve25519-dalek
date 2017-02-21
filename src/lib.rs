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

#![no_std]
#![allow(unused_features)]
#![feature(test)]
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

#[cfg(test)]
extern crate test;

#[macro_use]
extern crate arrayref;

#[cfg(feature = "std")]
extern crate rand;

// Modules for low-level operations directly on field elements and curve points.

pub mod field;
pub mod curve;
pub mod scalar;

// Constant-time functions and other miscelaneous utilities.

pub mod subtle;
pub mod utils;

// Low-level curve and point constants, as well as pre-computed curve group elements.

pub mod constants;
