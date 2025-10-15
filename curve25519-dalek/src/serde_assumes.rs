//! Verus assumptions for serde integration.
//!
//! This module exists to make verification builds with the `serde` feature
//! succeed. The actual `Serialize`/`Deserialize` impls are marked
//! `#[verifier::external]` in the codebase, so we don't need additional
//! specifications here yet.

use vstd::prelude::*;

verus! {
    // Intentionally empty for now
}

#[cfg(feature = "serde")]
use serde::de::Visitor;
#[cfg(feature = "serde")]
use serde::{Deserializer, Serializer};

#[cfg(feature = "serde")]
use crate::Scalar;

// (removed modular helpers to avoid trait associated-type projections during verification)

#[cfg(feature = "serde")]
#[verifier::external_body]
pub fn de_invalid_length<E: serde::de::Error>(len: usize, expected: &'static str) -> E {
    E::invalid_length(len, &expected)
}

#[cfg(feature = "serde")]
#[verifier::external_body]
pub fn de_custom<E: serde::de::Error>(msg: &'static str) -> E {
    E::custom(msg)
}

#[cfg(feature = "serde")]
#[verifier::external_body]
pub fn serialize_scalar_as_tuple<S>(serializer: S, bytes: &[u8; 32]) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    serializer.serialize_bytes(&bytes[..])
}

#[cfg(feature = "serde")]
#[verifier::external_body]
pub fn deserialize_scalar_from_tuple<'de, D>(deserializer: D) -> Result<Scalar, D::Error>
where
    D: Deserializer<'de>,
{
    struct BytesVisitor;

    impl<'de> Visitor<'de> for BytesVisitor {
        type Value = Scalar;

        fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            formatter
                .write_str("a byte slice of length 32 whose little-endian interpretation is < ℓ")
        }

        fn visit_bytes<E>(self, v: &[u8]) -> Result<Scalar, E>
        where
            E: serde::de::Error,
        {
            if v.len() != 32 {
                return Err(E::invalid_length(v.len(), &"expected 32 bytes"));
            }
            let mut bytes = [0u8; 32];
            bytes.copy_from_slice(&v[0..32]);
            match Scalar::from_canonical_bytes(bytes).into() {
                Some(s) => Ok(s),
                None => Err(E::custom("scalar was not canonically encoded")),
            }
        }
    }

    deserializer.deserialize_bytes(BytesVisitor)
}
