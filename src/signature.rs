// -*- mode: rust; -*-
//
// This file is part of ed25519-dalek.
// Copyright (c) 2017-2019 isis lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>

//! An ed25519 signature.

use core::fmt::Debug;

use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::scalar::Scalar;

#[cfg(feature = "serde")]
use serde::de::Error as SerdeError;
#[cfg(feature = "serde")]
use serde::de::Visitor;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "serde")]
use serde::{Deserializer, Serializer};

use crate::constants::*;
use crate::errors::*;

/// An ed25519 signature.
///
/// # Note
///
/// These signatures, unlike the ed25519 signature reference implementation, are
/// "detached"—that is, they do **not** include a copy of the message which has
/// been signed.
#[allow(non_snake_case)]
#[derive(Copy, Eq, PartialEq)]
pub struct Signature {
    /// `R` is an `EdwardsPoint`, formed by using an hash function with
    /// 512-bits output to produce the digest of:
    ///
    /// - the nonce half of the `ExpandedSecretKey`, and
    /// - the message to be signed.
    ///
    /// This digest is then interpreted as a `Scalar` and reduced into an
    /// element in ℤ/lℤ.  The scalar is then multiplied by the distinguished
    /// basepoint to produce `R`, and `EdwardsPoint`.
    pub(crate) R: CompressedEdwardsY,

    /// `s` is a `Scalar`, formed by using an hash function with 512-bits output
    /// to produce the digest of:
    ///
    /// - the `r` portion of this `Signature`,
    /// - the `PublicKey` which should be used to verify this `Signature`, and
    /// - the message to be signed.
    ///
    /// This digest is then interpreted as a `Scalar` and reduced into an
    /// element in ℤ/lℤ.
    pub(crate) s: Scalar,
}

impl Clone for Signature {
    fn clone(&self) -> Self {
        *self
    }
}

impl Debug for Signature {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        write!(f, "Signature( R: {:?}, s: {:?} )", &self.R, &self.s)
    }
}

impl Signature {
    /// Convert this `Signature` to a byte array.
    #[inline]
    pub fn to_bytes(&self) -> [u8; SIGNATURE_LENGTH] {
        let mut signature_bytes: [u8; SIGNATURE_LENGTH] = [0u8; SIGNATURE_LENGTH];

        signature_bytes[..32].copy_from_slice(&self.R.as_bytes()[..]);
        signature_bytes[32..].copy_from_slice(&self.s.as_bytes()[..]);
        signature_bytes
    }

    /// Construct a `Signature` from a slice of bytes.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<Signature, SignatureError> {
        if bytes.len() != SIGNATURE_LENGTH {
            return Err(SignatureError(InternalError::BytesLengthError {
                name: "Signature",
                length: SIGNATURE_LENGTH,
            }));
        }
        let mut lower: [u8; 32] = [0u8; 32];
        let mut upper: [u8; 32] = [0u8; 32];

        lower.copy_from_slice(&bytes[..32]);
        upper.copy_from_slice(&bytes[32..]);

        if upper[31] & 224 != 0 {
            return Err(SignatureError(InternalError::ScalarFormatError));
        }

        Ok(Signature {
            R: CompressedEdwardsY(lower),
            s: Scalar::from_bits(upper),
        })
    }
}

#[cfg(feature = "serde")]
impl Serialize for Signature {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

#[cfg(feature = "serde")]
impl<'d> Deserialize<'d> for Signature {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'d>,
    {
        struct SignatureVisitor;

        impl<'d> Visitor<'d> for SignatureVisitor {
            type Value = Signature;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                formatter.write_str("An ed25519 signature as 64 bytes, as specified in RFC8032.")
            }

            fn visit_bytes<E>(self, bytes: &[u8]) -> Result<Signature, E>
            where
                E: SerdeError,
            {
                Signature::from_bytes(bytes).or(Err(SerdeError::invalid_length(bytes.len(), &self)))
            }
        }
        deserializer.deserialize_bytes(SignatureVisitor)
    }
}
