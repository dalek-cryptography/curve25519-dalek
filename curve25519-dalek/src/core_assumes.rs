//! External type specifications for core Rust types
//! This module provides Verus-compatible wrappers for core types that are used
//! in the codebase but not directly supported by Verus.
use core::array::TryFromSliceError;
use core::convert::TryInto;

#[allow(unused_imports)]
use crate::montgomery::MontgomeryPoint;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
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

/* Hash and Digest specifications */

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

pub proof fn lemma_hash_is_canonical<H>(
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
    // Get canonical byte sequences
    let ghost canonical_seq1 = spec_fe51_to_bytes(&spec_fe51_from_bytes(&point1.0));
    let ghost canonical_seq2 = spec_fe51_to_bytes(&spec_fe51_from_bytes(&point2.0));

    // Convert to arrays for use with hash_determinism_axiom
    let ghost canonical1 = seq_to_array_32(canonical_seq1);
    let ghost canonical2 = seq_to_array_32(canonical_seq2);

    assume(canonical_seq1 == canonical_seq2);
    assert(canonical1@ == canonical2@);

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

} // verus!
