//! Core shared specifications for 64-bit backend
//!
//! This module contains byte/nat conversion functions that are shared between
//! field and scalar implementations. These are domain-neutral utilities that
//! interpret byte arrays as natural numbers in little-endian format.
#![allow(unused)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Convert a 32-byte array to its natural number representation (little-endian).
///
/// This function interprets a byte array as a 256-bit little-endian integer:
/// bytes[0] + bytes[1] * 2^8 + bytes[2] * 2^16 + ... + bytes[31] * 2^248
///
/// Note: We use byte-first order (bytes[i] * pow2(i*8)) to match
/// the natural structure of byte contribution functions used in proofs.
///
/// Used by both field and scalar implementations for byte serialization.
#[verusfmt::skip]
pub open spec fn as_nat_32_u8(bytes: &[u8; 32]) -> nat {
    // Verus error: `core::iter::range::impl&%15::fold` is not supported
    // we write them out manually
    (bytes[ 0] as nat) * pow2( 0 * 8) +
    (bytes[ 1] as nat) * pow2( 1 * 8) +
    (bytes[ 2] as nat) * pow2( 2 * 8) +
    (bytes[ 3] as nat) * pow2( 3 * 8) +
    (bytes[ 4] as nat) * pow2( 4 * 8) +
    (bytes[ 5] as nat) * pow2( 5 * 8) +
    (bytes[ 6] as nat) * pow2( 6 * 8) +
    (bytes[ 7] as nat) * pow2( 7 * 8) +
    (bytes[ 8] as nat) * pow2( 8 * 8) +
    (bytes[ 9] as nat) * pow2( 9 * 8) +
    (bytes[10] as nat) * pow2(10 * 8) +
    (bytes[11] as nat) * pow2(11 * 8) +
    (bytes[12] as nat) * pow2(12 * 8) +
    (bytes[13] as nat) * pow2(13 * 8) +
    (bytes[14] as nat) * pow2(14 * 8) +
    (bytes[15] as nat) * pow2(15 * 8) +
    (bytes[16] as nat) * pow2(16 * 8) +
    (bytes[17] as nat) * pow2(17 * 8) +
    (bytes[18] as nat) * pow2(18 * 8) +
    (bytes[19] as nat) * pow2(19 * 8) +
    (bytes[20] as nat) * pow2(20 * 8) +
    (bytes[21] as nat) * pow2(21 * 8) +
    (bytes[22] as nat) * pow2(22 * 8) +
    (bytes[23] as nat) * pow2(23 * 8) +
    (bytes[24] as nat) * pow2(24 * 8) +
    (bytes[25] as nat) * pow2(25 * 8) +
    (bytes[26] as nat) * pow2(26 * 8) +
    (bytes[27] as nat) * pow2(27 * 8) +
    (bytes[28] as nat) * pow2(28 * 8) +
    (bytes[29] as nat) * pow2(29 * 8) +
    (bytes[30] as nat) * pow2(30 * 8) +
    (bytes[31] as nat) * pow2(31 * 8)
}

/// Recursive helper for converting a 32-byte array to nat.
///
/// This version is useful for proofs that need structural induction.
/// It produces the same result as `as_nat_32_u8` but in recursive form.
pub open spec fn as_nat_32_u8_rec(bytes: &[u8; 32], index: nat) -> nat
    decreases 32 - index,
{
    if index >= 32 {
        0
    } else {
        (bytes[index as int] as nat) * pow2(index * 8) + as_nat_32_u8_rec(bytes, index + 1)
    }
}

/// Load 8 consecutive bytes from a byte array and interpret as a little-endian u64.
///
/// Returns: bytes[i] + bytes[i+1] * 2^8 + ... + bytes[i+7] * 2^56
///
/// This is commonly used when unpacking byte arrays into larger word-sized limbs.
#[verusfmt::skip]
pub open spec fn load8_at_spec(input: &[u8], i: usize) -> nat {
    (pow2(0 * 8) * input[i + 0] +
     pow2(1 * 8) * input[i + 1] +
     pow2(2 * 8) * input[i + 2] +
     pow2(3 * 8) * input[i + 3] +
     pow2(4 * 8) * input[i + 4] +
     pow2(5 * 8) * input[i + 5] +
     pow2(6 * 8) * input[i + 6] +
     pow2(7 * 8) * input[i + 7]) as nat
}

} // verus!
