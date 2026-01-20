//! External type specifications for core Rust types
//! This module provides Verus-compatible wrappers for core types that are used
//! in the codebase but not directly supported by Verus.
use core::array::TryFromSliceError;
use core::convert::TryInto;

#[allow(unused_imports)]
use crate::field::FieldElement;
#[allow(unused_imports)]
use crate::montgomery::MontgomeryPoint;
#[allow(unused_imports)]
use crate::ristretto::RistrettoPoint;
#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar52_specs::*;
#[allow(unused_imports)]
use crate::Scalar;
use vstd::prelude::*;

#[cfg(feature = "rand_core")]
use rand_core::RngCore;

#[cfg(feature = "digest")]
use digest::Digest;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::proba_specs::is_uniform_bytes;

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

/// Construct a CompressedEdwardsY from an array result.
///
/// CompressedEdwardsY is a wrapper around [u8; 32]. This function maps
/// a Result<[u8; 32], TryFromSliceError> to Result<CompressedEdwardsY, TryFromSliceError>,
/// wrapping successful arrays in the CompressedEdwardsY struct.
///
/// The postcondition specifies properties expected to hold for Result::map:
/// - Success/failure status is preserved (Ok maps to Ok, Err maps to Err)
/// - On success, the wrapped value is transformed (CompressedEdwardsY(arr).0 == arr)
///
/// Verus cannot automatically verify these properties through Result::map,
/// so we provide this wrapper with explicit postconditions.
#[verifier::external_body]
pub fn compressed_edwards_y_from_array_result(
    arr_result: Result<[u8; 32], TryFromSliceError>,
) -> (result: Result<crate::edwards::CompressedEdwardsY, TryFromSliceError>)
    ensures
        arr_result.is_ok() <==> result.is_ok(),
        arr_result.is_ok() ==> result.unwrap().0@ == arr_result.unwrap()@,
{
    arr_result.map(|arr| crate::edwards::CompressedEdwardsY(arr))
}

/// Extract the first 32 bytes from a 64-byte array.
#[verifier::external_body]
pub fn first_32_bytes(bytes: &[u8; 64]) -> (result: [u8; 32])
    ensures
        forall|i: int| 0 <= i < 32 ==> result[i] == bytes[i],
        result@ == bytes@.subrange(0, 32),
{
    let mut result = [0u8;32];
    result.copy_from_slice(&bytes[0..32]);
    result
}

/// Extract the last 32 bytes from a 64-byte array.
#[verifier::external_body]
pub fn last_32_bytes(bytes: &[u8; 64]) -> (result: [u8; 32])
    ensures
        forall|i: int| 0 <= i < 32 ==> result[i] == bytes[(32 + i) as int],
        result@ == bytes@.subrange(32, 64),
{
    let mut result = [0u8;32];
    result.copy_from_slice(&bytes[32..64]);
    result
}

// NOTE: Probabilistic specs (is_uniform_*, axiom_uniform_*) are in proba_specs.rs.
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

pub open spec fn seq_from32(b: &[u8; 32]) -> Seq<u8> {
    b@
}

#[verifier::external_body]
pub fn u16_to_le_bytes(x: u16) -> (bytes: [u8; 2])
    ensures
        bytes_to_nat_prefix(bytes@, 2) == x as nat,
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u32_to_le_bytes(x: u32) -> (bytes: [u8; 4])
    ensures
        bytes_to_nat_prefix(bytes@, 4) == x as nat,
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u64_to_le_bytes(x: u64) -> (bytes: [u8; 8])
    ensures
        bytes_to_nat_prefix(bytes@, 8) == x as nat,
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u128_to_le_bytes(x: u128) -> (bytes: [u8; 16])
    ensures
        bytes_to_nat_prefix(bytes@, 16) == x as nat,
{
    x.to_le_bytes()
}

#[verifier::external_body]
pub fn u16_from_le_bytes(bytes: [u8; 2]) -> (x: u16)
    ensures
        x as nat == bytes_to_nat_prefix(bytes@, 2),
{
    u16::from_le_bytes(bytes)
}

#[verifier::external_body]
pub fn u32_from_le_bytes(bytes: [u8; 4]) -> (x: u32)
    ensures
        x as nat == bytes_to_nat_prefix(bytes@, 4),
{
    u32::from_le_bytes(bytes)
}

#[verifier::external_body]
pub fn u64_from_le_bytes(bytes: [u8; 8]) -> (x: u64)
    ensures
        x as nat == bytes_to_nat_prefix(bytes@, 8),
{
    u64::from_le_bytes(bytes)
}

#[verifier::external_body]
pub fn u128_from_le_bytes(bytes: [u8; 16]) -> (x: u128)
    ensures
        x as nat == bytes_to_nat_prefix(bytes@, 16),
{
    u128::from_le_bytes(bytes)
}

/// Wrapper for FieldElement negation to avoid Verus internal error
#[verifier::external_body]
pub fn negate_field<T>(a: &T) -> (result: T) where for <'a>&'a T: core::ops::Neg<Output = T> {
    -a
}

// Assume specification for array hash implementation
// This is used when hashing fixed-size arrays like [u8; 32] in Hash implementations
pub assume_specification<T, const N: usize, H>[ <[T; N] as core::hash::Hash>::hash ](
    _0: &[T; N],
    _1: &mut H,
) where H: core::hash::Hasher, T: core::hash::Hash
;

// Spec function: models the state of a hasher after hashing bytes
pub spec fn spec_state_after_hash<H, T, const N: usize>(initial_state: H, bytes: &[T; N]) -> H;

/// Spec function: the hash state after hashing a MontgomeryPoint
/// This is defined as the hash state of its canonical byte representation
pub open spec fn spec_state_after_hash_montgomery<H>(
    initial_state: H,
    point: &MontgomeryPoint,
) -> H {
    // The hash state of a MontgomeryPoint is determined by its canonical bytes
    // Canonical bytes are: spec_fe51_to_bytes(spec_fe51_from_bytes(point.0))
    let canonical_seq = spec_fe51_to_bytes(&spec_fe51_from_bytes(&point.0));
    let canonical_bytes = seq_to_array_32(canonical_seq);
    spec_state_after_hash(initial_state, &canonical_bytes)
}

pub proof fn axiom_hash_is_canonical<H>(
    point1: &MontgomeryPoint,
    point2: &MontgomeryPoint,
    state: H,
)
    requires
// The two points represent the same field element (same canonical value)

        spec_field_element_from_bytes(&point1.0) == spec_field_element_from_bytes(&point2.0),
    ensures
// Points with equal field element values hash to the same state

        spec_state_after_hash_montgomery(state, point1) == spec_state_after_hash_montgomery(
            state,
            point2,
        ),
{
    // Axiom: hashing depends only on the canonical field-element value.
    admit();
}

// Convert a Seq<u8> to a [u8; 32] array (requires seq.len() >= 32)
pub open spec fn seq_to_array_32(s: Seq<u8>) -> [u8; 32] {
    [
        s[0],
        s[1],
        s[2],
        s[3],
        s[4],
        s[5],
        s[6],
        s[7],
        s[8],
        s[9],
        s[10],
        s[11],
        s[12],
        s[13],
        s[14],
        s[15],
        s[16],
        s[17],
        s[18],
        s[19],
        s[20],
        s[21],
        s[22],
        s[23],
        s[24],
        s[25],
        s[26],
        s[27],
        s[28],
        s[29],
        s[30],
        s[31],
    ]
}

/*** Zeroize specifications ***/

#[cfg(feature = "zeroize")]
// Wrapper for zeroize on [u8; 32] arrays
// After zeroizing, all bytes should be zero
#[verifier::external_body]
pub fn zeroize_bytes32(bytes: &mut [u8; 32])
    ensures
        forall|i: int| 0 <= i < 32 ==> #[trigger] bytes[i] == 0u8,
{
    use zeroize::Zeroize;
    bytes.zeroize();
}

#[cfg(feature = "zeroize")]
// Wrapper for zeroize on [u64; 5] arrays (used by FieldElement51)
// After zeroizing, all limbs should be zero
#[verifier::external_body]
pub fn zeroize_limbs5(limbs: &mut [u64; 5])
    ensures
        forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] == 0u64,
{
    use zeroize::Zeroize;
    limbs.zeroize();
}

#[cfg(feature = "zeroize")]
// Wrapper for zeroize on bool values
// After zeroizing, the bool should be false
#[verifier::external_body]
pub fn zeroize_bool(b: &mut bool)
    ensures
        *b == false,
{
    use zeroize::Zeroize;
    b.zeroize();
}

// =============================================================================
// RNG and Hash Function Wrappers
// =============================================================================
// In normal Rust builds we provide exec wrappers without probabilistic specs.
// In `cargo verus verify`, we use `verus_keep_ghost` variants with `ensures`.
#[cfg(all(feature = "rand_core", not(verus_keep_ghost)))]
#[verifier::external_body]
pub fn fill_bytes<R: RngCore>(rng: &mut R, bytes: &mut [u8; 64]) {
    rng.fill_bytes(bytes)
}

#[cfg(all(feature = "rand_core", verus_keep_ghost))]
#[verifier::external_body]
/// Fill bytes from a cryptographic RNG, producing uniform random bytes.
pub fn fill_bytes<R: RngCore>(rng: &mut R, bytes: &mut [u8; 64])
    ensures
        is_uniform_bytes(bytes),
{
    rng.fill_bytes(bytes)
}

#[cfg(all(feature = "digest", not(verus_keep_ghost)))]
#[verifier::external_body]
pub fn sha512_hash_bytes(input: &[u8]) -> (result: [u8; 64]) {
    let mut hasher = sha2::Sha512::new();
    hasher.update(input);
    hasher.finalize().into()
}

#[cfg(all(feature = "digest", verus_keep_ghost))]
/// Uninterpreted spec function for SHA-512 hash.
/// Models the SHA-512 hash as a function from input bytes to 64 output bytes.
pub uninterp spec fn spec_sha512(input: Seq<u8>) -> Seq<u8>;

#[cfg(all(feature = "digest", verus_keep_ghost))]
/// Axiom: SHA-512 always produces exactly 64 bytes of output.
pub proof fn axiom_sha512_output_length(input: Seq<u8>)
    ensures
        spec_sha512(input).len() == 64,
{
    admit();
}

#[cfg(all(feature = "digest", verus_keep_ghost))]
#[verifier::external_body]
/// Compute SHA-512 hash of input bytes.
/// If input is uniform, output is computationally indistinguishable from uniform.
pub fn sha512_hash_bytes(input: &[u8]) -> (result: [u8; 64])
    ensures
        result@ == spec_sha512(input@),
        is_uniform_bytes(input) ==> is_uniform_bytes(&result),
{
    let mut hasher = sha2::Sha512::new();
    hasher.update(input);
    hasher.finalize().into()
}

} // verus!
