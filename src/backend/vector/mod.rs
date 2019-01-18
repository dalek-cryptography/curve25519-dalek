// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Pluggable implementations for different architectures.
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

#[cfg(not(any(target_feature = "avx2", target_feature = "avx512ifma",)))]
compile_error!("simd_backend selected without target_feature=+avx2 or +avx512ifma");

#[cfg(all(target_feature = "avx2", not(target_feature = "avx512ifma")))]
pub mod avx2;
#[cfg(all(target_feature = "avx2", not(target_feature = "avx512ifma")))]
pub(crate) use self::avx2::{
    constants::BASEPOINT_ODD_LOOKUP_TABLE, edwards::CachedPoint, edwards::ExtendedPoint,
};

#[cfg(all(target_feature = "avx512ifma"))]
pub mod ifma;
#[cfg(all(target_feature = "avx512ifma"))]
pub(crate) use self::ifma::{
    constants::BASEPOINT_ODD_LOOKUP_TABLE, edwards::CachedPoint, edwards::ExtendedPoint,
};

pub mod scalar_mul;
