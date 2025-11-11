//! External type specifications for core Rust types
//! This module provides Verus-compatible wrappers for core types that are used
//! in the codebase but not directly supported by Verus.
use core::array::TryFromSliceError;
use core::convert::TryInto;

#[allow(unused_imports)]
use crate::specs::scalar_specs_u64::*;
#[allow(unused_imports)]
use crate::Scalar;
use vstd::prelude::*;

#[cfg(feature = "rand_core")]
use rand_core::RngCore;

verus! {

/// External type specification for TryFromSliceError
/// This error type is returned when trying to convert a slice to an array fails
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExTryFromSliceError(TryFromSliceError);

/// Wrapper for slice to array conversion (try_into)
/// Converts a slice &[u8] to a fixed-size array [u8; 32]
/// Succeeds if and only if the slice has exactly 32 bytes.
#[verifier::external_body]
pub fn try_into_32_bytes_array(bytes: &[u8]) -> (result: Result<[u8; 32], TryFromSliceError>)
    ensures
// Success when length matches the target array size (32)

        bytes@.len() == 32 ==> matches!(result, Ok(_)),
        // Failure when length doesn't match
        bytes@.len() != 32 ==> matches!(result, Err(_)),
        // When successful, the array contains the same bytes as the input slice
        match result {
            Ok(arr) => arr@ == bytes@,
            Err(_) => true,
        },
{
    bytes.try_into()
}

// External type specifications for formatters
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFormatter<'a>(core::fmt::Formatter<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFmtError(core::fmt::Error);

// Assume specification for core::fmt::Formatter::write_str used e.g. by serde Visitors
pub assume_specification<'a>[ core::fmt::Formatter::<'a>::write_str ](
    _0: &mut core::fmt::Formatter<'a>,
    _1: &str,
) -> core::result::Result<(), core::fmt::Error>
;

// Build a Seq<u8> from fixed arrays (for specs)
pub open spec fn seq_from2(b: &[u8; 2]) -> Seq<u8> {
    Seq::new(2, |i: int| b[i])
}

pub open spec fn seq_from4(b: &[u8; 4]) -> Seq<u8> {
    Seq::new(4, |i: int| b[i])
}

pub open spec fn seq_from8(b: &[u8; 8]) -> Seq<u8> {
    Seq::new(8, |i: int| b[i])
}

pub open spec fn seq_from16(b: &[u8; 16]) -> Seq<u8> {
    Seq::new(16, |i: int| b[i])
}

#[verifier::external_body]
pub fn u16_to_le_bytes(x: u16) -> (bytes: [u8; 2])
    ensures
        bytes_seq_to_nat(seq_from2(&bytes)) == x as nat,
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u32_to_le_bytes(x: u32) -> (bytes: [u8; 4])
    ensures
        bytes_seq_to_nat(seq_from4(&bytes)) == x as nat,
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u64_to_le_bytes(x: u64) -> (bytes: [u8; 8])
    ensures
        bytes_seq_to_nat(seq_from8(&bytes)) == x as nat,
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u128_to_le_bytes(x: u128) -> (bytes: [u8; 16])
    ensures
        bytes_seq_to_nat(seq_from16(&bytes)) == x as nat,
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u16_from_le_bytes(bytes: [u8; 2]) -> (x: u16)
    ensures
        x as nat == bytes_seq_to_nat(seq_from2(&bytes)),
{
    u16::from_le_bytes(bytes)
}

#[verifier::external_body]
pub fn u32_from_le_bytes(bytes: [u8; 4]) -> (x: u32)
    ensures
        x as nat == bytes_seq_to_nat(seq_from4(&bytes)),
{
    u32::from_le_bytes(bytes)
}

#[verifier::external_body]
pub fn u64_from_le_bytes(bytes: [u8; 8]) -> (x: u64)
    ensures
        x as nat == bytes_seq_to_nat(seq_from8(&bytes)),
{
    u64::from_le_bytes(bytes)
}

#[verifier::external_body]
pub fn u128_from_le_bytes(bytes: [u8; 16]) -> (x: u128)
    ensures
        x as nat == bytes_seq_to_nat(seq_from16(&bytes)),
{
    u128::from_le_bytes(bytes)
}

/// Wrapper for FieldElement negation to avoid Verus internal error
#[verifier::external_body]
pub fn negate_field<T>(a: &T) -> (result: T) where for <'a>&'a T: core::ops::Neg<Output = T> {
    -a
}

// annotations for random values
pub uninterp spec fn is_random(x: u8) -> bool;

pub uninterp spec fn is_random_bytes(bytes: &[u8]) -> bool;

pub uninterp spec fn is_random_scalar(scalar: &Scalar) -> bool;

#[cfg(feature = "rand_core")]
#[verifier::external_body]
pub fn fill_bytes<R: RngCore>(rng: &mut R, bytes: &mut [u8; 64])
    ensures
        is_random_bytes(bytes),
{
    rng.fill_bytes(bytes)
}

#[cfg(feature = "digest")]
#[verifier::external_body]
pub fn sha512_hash_bytes(input: &[u8]) -> (result: [u8; 64])
    ensures
        is_random_bytes(input) ==> is_random_bytes(&result),
{
    use digest::Digest;
    let mut hasher = sha2::Sha512::new();
    hasher.update(input);
    hasher.finalize().into()
}

// Assume specification for array hash implementation
// This is used when hashing fixed-size arrays like [u8; 32] in Hash implementations
pub assume_specification<T, const N: usize, H>[ <[T; N] as core::hash::Hash>::hash ](
    _0: &[T; N],
    _1: &mut H,
) where H: core::hash::Hasher, T: core::hash::Hash
;

} // verus!
