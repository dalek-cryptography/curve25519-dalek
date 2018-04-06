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

#![cfg_attr(feature = "nightly", feature(cfg_target_feature))]
#![cfg_attr(feature = "nightly", feature(external_doc))]
#![cfg_attr(all(feature = "nightly", feature = "yolocrypto"), feature(stdsimd))]

// Refuse to compile if documentation is missing, but only on nightly.
//
// This means that missing docs will still fail CI, but means we can use
// README.md as the crate documentation.
#![cfg_attr(all(feature = "nightly"), deny(missing_docs))]

#![cfg_attr(feature = "nightly", doc(include = "../README.md"))]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]

//! Note that docs will only build on nightly Rust until
//! [RFC 1990 stabilizes](https://github.com/rust-lang/rust/issues/44732).

//------------------------------------------------------------------------
// External dependencies:
//------------------------------------------------------------------------

#[cfg(feature = "std")]
extern crate core;
#[cfg(feature = "alloc")]
extern crate alloc;

extern crate rand;
extern crate clear_on_drop;
extern crate byteorder;

extern crate byteorder;

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

// Internal curve models which are not part of the public API.
pub(crate) mod curve_models;

// Implementations of scalar mul algorithms live here
pub(crate) mod scalar_mul;
