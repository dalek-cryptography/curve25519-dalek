// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2019 Isis Lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>

//! Errors which may occur.
//!
//! Currently, these are only used in the implementations of `TryFrom`.
//!
//! This module optionally implements support for the types in the `failure`
//! crate.  This can be enabled by building with `--features failure`.

use core::fmt;
use core::fmt::Display;

/// Internal errors.  Most application-level developers will likely not
/// need to pay any attention to these.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) enum InternalError {
    /// An error in the length of bytes handed to a constructor.
    ///
    /// To use this, pass a string specifying the `name` of the type which is
    /// returning the error, and the `length` in bytes which its constructor
    /// expects.
    BytesLengthError {
        name: &'static str,
        length: usize,
    },
}

impl Display for InternalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            InternalError::BytesLengthError{ name: n, length: l}
                => write!(f, "{} must be {} bytes in length", n, l),
        }
    }
}

#[cfg(feature = "failure")]
impl ::failure::Fail for InternalError {}

/// Errors which may occur.
///
/// This error may arise due to:
///
/// * Being given bytes with a length different to what was expected.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub struct CurveError(pub(crate) InternalError);

impl Display for CurveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(feature = "failure")]
impl ::failure::Fail for CurveError {
    fn cause(&self) -> Option<&dyn (::failure::Fail)> {
        Some(&self.0)
    }
}
