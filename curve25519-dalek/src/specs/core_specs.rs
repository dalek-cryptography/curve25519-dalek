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
/// IMPORTANT: This explicit 32-term form is kept for SMT solver efficiency.
/// For generic arrays, use `bytes_seq_as_nat(bytes@)` directly.
#[verusfmt::skip]
pub open spec fn u8_32_as_nat(bytes: &[u8; 32]) -> nat {
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

/// Generic suffix sum: sum of bytes[start..N] with original positional weights.
///
/// Computes: sum_{i=start}^{N-1} bytes[i] * 2^(i*8)
///
/// This preserves original positions (unlike bytes_seq_as_nat on a suffix slice).
/// Useful for loop invariants: prefix(start) + suffix(start) == total.
pub open spec fn bytes_as_nat_suffix<const N: usize>(bytes: &[u8; N], start: int) -> nat
    decreases (N as int) - start,
{
    if start >= N as int {
        0
    } else {
        (bytes[start] as nat) * pow2((start * 8) as nat) + bytes_as_nat_suffix(bytes, start + 1)
    }
}

/// 32-byte recursive helper (backward compatible).
/// Equivalent to `bytes_as_nat_suffix::<32>` with nat index.
pub open spec fn u8_32_as_nat_rec(bytes: &[u8; 32], index: nat) -> nat
    decreases 32 - index,
{
    if index >= 32 {
        0
    } else {
        (bytes[index as int] as nat) * pow2(index * 8) + u8_32_as_nat_rec(bytes, index + 1)
    }
}

// NOTE: Bridge lemmas (lemma_u8_32_as_nat_equals_rec, lemma_u8_32_as_nat_equals_suffix_32,
// lemma_u8_32_as_nat_equals_suffix_64) have been moved to to_nat_lemmas.rs
/// Load 8 consecutive bytes from a byte array and interpret as a little-endian u64.
///
/// Returns: bytes[i] + bytes[i+1] * 2^8 + ... + bytes[i+7] * 2^56
///
/// This is commonly used when unpacking byte arrays into larger word-sized limbs.
#[verusfmt::skip]
pub open spec fn spec_load8_at(input: &[u8], i: usize) -> nat {
    (pow2(0 * 8) * input[i + 0] +
     pow2(1 * 8) * input[i + 1] +
     pow2(2 * 8) * input[i + 2] +
     pow2(3 * 8) * input[i + 3] +
     pow2(4 * 8) * input[i + 4] +
     pow2(5 * 8) * input[i + 5] +
     pow2(6 * 8) * input[i + 6] +
     pow2(7 * 8) * input[i + 7]) as nat
}

#[verusfmt::skip]
pub open spec fn u64_5_as_nat_generic_radix(arr: [u64;5], radix: nat) -> nat {
    (
                          arr[0] +
        pow2(1 * radix) * arr[1] +
        pow2(2 * radix) * arr[2] +
        pow2(3 * radix) * arr[3] +
        pow2(4 * radix) * arr[4]
    ) as nat
}

// ============================================================================
// Byte sequence to nat conversion
// ============================================================================
/// Little-endian natural value of an arbitrary-length byte sequence.
/// Computes: bytes[0] + bytes[1] * 2^8 + bytes[2] * 2^16 + ...
pub open spec fn bytes_seq_as_nat(bytes: Seq<u8>) -> nat
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        0
    } else {
        (bytes[0] as nat) + pow2(8) * bytes_seq_as_nat(bytes.skip(1))
    }
}

/// Little-endian natural value of first j bytes of a sequence.
/// Computes: bytes[0] + bytes[1]*2^8 + ... + bytes[j-1]*2^((j-1)*8)
///
/// This is the canonical "prefix sum" for byte-to-nat conversion proofs.
/// Used for incremental byte-to-word conversion and injectivity proofs.
pub open spec fn bytes_as_nat_prefix(bytes: Seq<u8>, j: nat) -> nat
    recommends
        j <= bytes.len(),
    decreases j,
{
    if j == 0 {
        0
    } else {
        let j1: nat = (j - 1) as nat;
        bytes_as_nat_prefix(bytes, j1) + pow2(((j1) * 8) as nat) * bytes[j1 as int] as nat
    }
}

// ============================================================================
// Word-to-nat conversion (generic over word type)
// ============================================================================
/// THE fully generic primitive for word-to-nat conversion.
/// Works with any word type via Seq<nat> - use arr@.map(|i, x| x as nat) to convert.
///
/// Computes: sum_{i=0}^{num_words-1} words[i] * 2^(i * bits_per_word)
pub open spec fn words_as_nat_gen(words: Seq<nat>, num_words: int, bits_per_word: int) -> nat
    decreases num_words,
{
    if num_words <= 0 {
        0
    } else {
        let word_value = words[num_words - 1] * pow2(((num_words - 1) * bits_per_word) as nat);
        word_value + words_as_nat_gen(words, num_words - 1, bits_per_word)
    }
}

/// Convenience wrapper for u64 arrays.
/// Use this for the common case of &[u64] inputs.
/// For proofs requiring reveal_with_fuel, use reveal_with_fuel(words_as_nat_gen, n).
pub open spec fn words_as_nat_u64(words: &[u64], num_words: int, bits_per_word: int) -> nat {
    words_as_nat_gen(words@.map(|i: int, x: u64| x as nat), num_words, bits_per_word)
}

// ============================================================================
// Word extraction from byte sequences (generic over any length)
// ============================================================================
//
// NOTE: These functions are specialized for u8 (bytes) because they implement
// the common "extract 64-bit words from byte arrays" pattern.
//
// For other element types (u16, u32, etc.), use words_as_nat_gen directly:
//   - u16 array: words_as_nat_gen(arr@.map(|i, x| x as nat), len, 16)
//   - u32 array: words_as_nat_gen(arr@.map(|i, x| x as nat), len, 32)
/// Extract a 64-bit word (8 bytes) from any byte sequence.
/// Returns bytes[base..base+8] as little-endian u64 value.
#[verusfmt::skip]
pub open spec fn word64_from_bytes(bytes: Seq<u8>, word_idx: int) -> nat {
    let num_words = bytes.len() as int / 8;
    if !(0 <= word_idx && word_idx < num_words) {
        0
    } else {
        let base = word_idx * 8;
        (bytes[(base + 0) as int] as nat) * pow2( 0) +
        (bytes[(base + 1) as int] as nat) * pow2( 8) +
        (bytes[(base + 2) as int] as nat) * pow2(16) +
        (bytes[(base + 3) as int] as nat) * pow2(24) +
        (bytes[(base + 4) as int] as nat) * pow2(32) +
        (bytes[(base + 5) as int] as nat) * pow2(40) +
        (bytes[(base + 6) as int] as nat) * pow2(48) +
        (bytes[(base + 7) as int] as nat) * pow2(56)
    }
}

/// Extract partial word (first `upto` bytes of a word).
/// Used for proofs involving partial word construction.
pub open spec fn word64_from_bytes_partial(bytes: Seq<u8>, word_idx: int, upto: int) -> nat
    decreases
            if upto <= 0 {
                0
            } else if upto >= 8 {
                0
            } else {
                upto as nat
            },
{
    let num_words = bytes.len() as int / 8;
    if !(0 <= word_idx && word_idx < num_words) {
        0
    } else if upto <= 0 {
        0
    } else if upto >= 8 {
        word64_from_bytes(bytes, word_idx)
    } else {
        let j = upto - 1;
        word64_from_bytes_partial(bytes, word_idx, j) + (bytes[(word_idx * 8 + j) as int] as nat)
            * pow2((j * 8) as nat)
    }
}

/// Sum of extracted words to nat (first `count` 64-bit words).
/// Computes: sum_{i=0}^{count-1} word64_from_bytes(bytes, i) * 2^(i*64)
pub open spec fn words64_from_bytes_to_nat(bytes: Seq<u8>, count: int) -> nat
    decreases
            if count <= 0 {
                0
            } else {
                count as nat
            },
{
    let num_words = bytes.len() as int / 8;
    if count <= 0 {
        0
    } else if count > num_words {
        words64_from_bytes_to_nat(bytes, num_words)
    } else {
        let idx = count - 1;
        words64_from_bytes_to_nat(bytes, idx) + word64_from_bytes(bytes, idx) * pow2(
            (idx * 64) as nat,
        )
    }
}

// ============================================================================
// Wide (64-byte) array to nat conversion
// ============================================================================
// NOTE: bytes_wide_to_nat has been inlined to bytes_seq_as_nat(bytes@)
// Use bytes_seq_as_nat(bytes@) directly for 64-byte arrays.
// bytes64_to_nat_suffix has been replaced by the generic bytes_as_nat_suffix<const N>.
// ============================================================================
// Bit array to nat conversion
// ============================================================================
/// Convert a boolean array (bits in little-endian order) to a natural number.
/// bits[0] is the least significant bit.
/// Computes: sum_{i=0}^{255} bits[i] * 2^i
pub open spec fn bits_as_nat(bits: &[bool; 256]) -> nat {
    bits_as_nat_rec(bits, 0)
}

/// Recursive helper for bits_as_nat.
pub open spec fn bits_as_nat_rec(bits: &[bool; 256], index: int) -> nat
    decreases 256 - index,
{
    if index >= 256 {
        0
    } else {
        let bit_value = if bits[index] {
            1nat
        } else {
            0nat
        };
        bit_value * pow2(index as nat) + bits_as_nat_rec(bits, index + 1)
    }
}

/// Convert a boolean slice (bits in big-endian order) to a natural number.
/// bits[0] is the most significant bit.
/// Used for scalar multiplication where bits are processed MSB first.
pub open spec fn bits_be_as_nat(bits: &[bool], len: int) -> nat
    recommends
        0 <= len <= bits.len(),
    decreases len,
{
    if len <= 0 {
        0
    } else {
        let bit_value = if bits[len - 1] {
            1nat
        } else {
            0nat
        };
        bit_value + 2 * bits_be_as_nat(bits, len - 1)
    }
}

} // verus!
