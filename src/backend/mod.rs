// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! This module contains "backends" that contain different
//! implementations of common code for different architectures.
//!
//! The naming of the `u32` and `u64` modules is somewhat unfortunate,
//! since these are also the names of primitive types.  Since types have
//! a different namespace than modules, this isn't a problem to the
//! compiler, but it could cause confusion.
//!
//! However, it's unlikely that the names of those modules would be
//! brought into scope directly, instead of used as
//! `backend::u32::field` or similar.  Unfortunately we can't use
//! `32bit` since identifiers can't start with letters, and the backends
//! do use `u32`/`u64`, so this seems like a least-bad option.

#[cfg(not(feature="radix_51"))]
pub mod u32;

#[cfg(feature="radix_51")]
pub mod u64;

/// Code using AVX2.
#[cfg(all(feature="yolocrypto", not(feature="radix_51")))]
pub mod avx2;

