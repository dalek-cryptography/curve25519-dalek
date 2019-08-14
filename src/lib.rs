// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

#![no_std]
#![cfg_attr(feature = "nightly", feature(test))]
#![cfg_attr(all(feature = "alloc", not(feature = "std")), feature(alloc))]
#![cfg_attr(feature = "nightly", feature(external_doc))]
#![cfg_attr(feature = "nightly", feature(doc_cfg))]
#![cfg_attr(feature = "simd_backend", feature(stdsimd))]
// Refuse to compile if documentation is missing, but only on nightly.
//
// This means that missing docs will still fail CI, but means we can use
// README.md as the crate documentation.
#![cfg_attr(feature = "nightly", deny(missing_docs))]

#![cfg_attr(feature = "nightly", doc(include = "../README.md"))]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]

//! Note that docs will only build on nightly Rust until
//! [RFC 1990 stabilizes](https://github.com/rust-lang/rust/issues/44732).

//------------------------------------------------------------------------
// External dependencies:
//------------------------------------------------------------------------

#[cfg(all(feature = "alloc", not(feature = "std")))]
#[macro_use]
extern crate alloc;

#[cfg(feature = "std")]
#[macro_use]
extern crate std;

#[cfg(all(feature = "nightly", feature = "packed_simd"))]
extern crate packed_simd;

extern crate byteorder;
extern crate clear_on_drop;
pub extern crate digest;
extern crate rand_core;
#[cfg(all(test, feature = "stage2_build"))]
extern crate rand_os;

// Used for traits related to constant-time code.
extern crate subtle;

#[cfg(all(test, feature = "serde"))]
extern crate bincode;
#[cfg(feature = "serde")]
extern crate serde;
#[cfg(all(test, feature = "serde"))]
extern crate serde_json;
#[cfg(all(feature = "serde", feature = "hex"))]
extern crate hex;

// Internal macros. Must come first!
#[macro_use]
pub(crate) mod macros;

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

// Crate-local prelude (for alloc-dependent features like `Vec`)
pub(crate) mod prelude;

// Generic code for window lookups
pub(crate) mod window;
