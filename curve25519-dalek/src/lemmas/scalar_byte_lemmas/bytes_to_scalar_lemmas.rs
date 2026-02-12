//! Proofs for converting bytes to Scalar52 representation
//!
//! This module contains lemmas that prove the correctness of the `from_bytes` function,
//! which converts a 32-byte array into a Scalar52 (5 limbs of 52 bits each).
//!
//! The conversion happens in three stages:
//! 1. Pack 32 bytes into 4 u64 words (8 bytes per word)
//! 2. Extract 5 limbs of 52 bits from those 4 words
//! 3. Prove the final representation matches the original byte array's natural value
//!
//! The main lemmas are:
//! - `lemma_byte_to_word_step`: Proves one byte OR operation in the word-building loop
//! - `lemma_bytes_to_word_equivalence`: Proves 4 words correctly represent 32 bytes
//! - `lemma_words_to_scalar`: Proves 5 limbs correctly represent 4 words
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::calc;
use vstd::prelude::*;

use super::super::common_lemmas::bit_lemmas::*;
use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

// Import helper lemmas from field_lemmas
use super::super::field_lemmas::limbs_to_bytes_lemmas::*;

use crate::backend::serial::u64::scalar::Scalar52;
use crate::specs::core_specs::*;
use crate::specs::scalar52_specs::*;

verus! {

/// Proves the correctness of one iteration of the byte-to-word conversion loop
///
/// This lemma verifies that OR-ing a single byte (shifted by j*8 bits) into a word
/// maintains the invariant that the word represents the first j+1 bytes as a little-endian
/// natural number.
///
/// # Arguments
/// * `bytes` - The 32-byte input array
/// * `words` - The partially-built word array (4 words)
/// * `i` - Current word index (0..4)
/// * `j` - Current byte index within the word (0..8)
///
/// # Loop context
/// This is used in: `words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);`
pub proof fn lemma_byte_to_word_step(bytes: [u8; 32], words: [u64; 4], i: usize, j: usize)
    requires
        0 <= j < 8 && 0 <= i < 4,
        words[i as int] < pow2(j as nat * 8),
        forall|i2: int| i + 1 <= i2 < 4 ==> words[i2] == 0u64,
        words[i as int] == bytes_as_nat_prefix(
            Seq::new(8, |j2: int| bytes[i as int * 8 + j2]),
            j as nat,
        ),
        forall|i2: int|
            0 <= i2 < i ==> ((words[i2] as nat) == bytes_as_nat_prefix(
                Seq::new(8, |j: int| bytes[i2 * 8 + j]),
                8,
            )),
    ensures
        (words[i as int] | (bytes[(i * 8) + j] as u64) << (j * 8)) < pow2((j as nat + 1) * 8),
        (words[i as int] | (bytes[(i * 8) + j] as u64) << (j * 8)) == bytes_as_nat_prefix(
            Seq::new(8, |j2: int| bytes[(i as nat) * 8 + j2]),
            (j + 1) as nat,
        ),
{
    assert(i < 4 && j < 8);
    assert((i as u64) * 8u64 < 32u64);
    let idx = (i as u64) * 8 + (j as u64);
    assert(idx < 32);

    let old_word = words[i as int];
    let new_byte = bytes[idx] as u64;

    assert(j < 8);
    lemma_mul_strict_inequality(j as int, 8, 8);
    assert((j as int * 8) < 64);
    lemma_pow2_strictly_increases(j as nat * 8, 64);

    assert(1 * pow2(j as nat * 8) == pow2(j as nat * 8));
    assert(1 * pow2(j as nat * 8) < pow2(64));
    lemma_u64_pow2_no_overflow(j as nat * 8);

    let j8 = (j * 8) as u64;

    assert(old_word < (1u64 << j8)) by {
        assert(old_word < pow2(j8 as nat));
        assert(j8 < u64::BITS);
        assert(1 * pow2(j8 as nat) <= u64::MAX);
        lemma_u64_shl_is_mul(1, j8);
        assert((1u64 << j8) == 1 * pow2(j8 as nat));
    };

    assert(new_byte <= (u64::MAX >> j8)) by {
        assert(new_byte <= 255);
        assert((u64::MAX >> (j * 8)) == (u64::MAX / (pow2(j8 as nat) as u64))) by {
            lemma_u64_shr_is_div(u64::MAX, j8);
        }
        assert(u64::MAX / (pow2(56) as u64) <= u64::MAX / (pow2(j8 as nat) as u64)) by {
            assert(j8 <= 56);
            assert(pow2(j8 as nat) <= pow2(56)) by {
                lemma_pow_increases(2, j8 as nat, 56);
                lemma_pow2(j8 as nat);
                lemma_pow2(56);
            }
            lemma_div_is_ordered_by_denominator(
                u64::MAX as int,
                pow2(j8 as nat) as int,
                pow2(56) as int,
            );
            assert(((u64::MAX as int) / (pow2(56) as int)) <= ((u64::MAX as int) / (pow2(
                j8 as nat,
            ) as int)));
            lemma_u64_pow2_no_overflow(56);
        }
        assert(255 <= u64::MAX / (pow2(56) as u64)) by {
            lemma_pow2(56);
            lemma_u64_pow2_no_overflow(56);
            reveal(pow);
            assert(255 <= u64::MAX / (pow(2, 56) as u64)) by (compute);
        }
    }

    assert((old_word | (new_byte << (j8))) == (old_word + (new_byte << (j8)))) by {
        lemma_u64_bit_or_is_plus(old_word, new_byte, j8 as u64);
    }

    let j8next = (j as u64 + 1) * 8 as u64;

    assert(old_word + (new_byte << j8) == old_word + new_byte * pow2(j8 as nat)) by {
        assert(new_byte <= 255);
        assert(pow2(j8 as nat) <= pow2(56)) by {
            lemma_pow_increases(2, j8 as nat, 56);
            lemma_pow2(j8 as nat);
            lemma_pow2(56);
        }
        assert(new_byte * pow2(j8 as nat) <= new_byte * pow2(56)) by {
            lemma_mul_le(new_byte as nat, new_byte as nat, pow2(j8 as nat), pow2(56));
        };
        assert(new_byte * pow2(j8 as nat) <= u64::MAX) by {
            lemma_mul_inequality(new_byte as int, 255, pow2(56) as int);
            assert(255 * pow(2, 56) <= u64::MAX) by (compute);
            assert(255 * pow2(56) <= u64::MAX) by {
                lemma_pow2(56);
            };
        }
        lemma_u64_shl_is_mul(new_byte, j8);
    };

    assert(old_word + (new_byte << j8) < pow2(j8next as nat)) by {
        assert((new_byte as int) * pow2(j8 as nat) <= 255 * pow2(j8 as nat)) by {
            lemma_mul_inequality(new_byte as int, 255, pow2(j8 as nat) as int);
        }
        assert(old_word + new_byte * pow2(j8 as nat) <= 256 * pow2(j8 as nat));
        assert(256 * pow2(j8 as nat) == pow2(8) * pow2(j8 as nat)) by {
            lemma_pow2(8);
            assert(256 == pow(2, 8)) by (compute);
            assert(256 == pow2(8));
        }
        assert(256 * pow2(j8 as nat) == pow2(8 + (j8 as nat))) by {
            lemma_pow2_adds(8, j8 as nat);
        }
    }

    assert(old_word == bytes_as_nat_prefix(
        Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]),
        j as nat,
    ));

    assert(bytes_as_nat_prefix(Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]), j as nat) + pow2(
        (j as nat) * 8,
    ) * bytes[(i as int) * 8 + j] == bytes_as_nat_prefix(
        Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]),
        (j + 1) as nat,
    )) by {
        reveal(bytes_as_nat_prefix);
    }

    assert(bytes_as_nat_prefix(Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]), j as nat)
        + bytes[(i as int) * 8 + j] * pow2((j as nat) * 8) == bytes_as_nat_prefix(
        Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]),
        (j + 1) as nat,
    )) by {
        lemma_mul_is_commutative(bytes[(i as int) * 8 + j] as int, pow2((j as nat) * 8) as int);
    }

    assert(old_word + new_byte * pow2(j8 as nat) == bytes_as_nat_prefix(
        Seq::new(8, |j2: int| bytes[(i as int) * 8 + j2]),
        (j + 1) as nat,
    ));

    assert(old_word + new_byte * pow2(j8 as nat) == old_word + (new_byte << j8)) by {}

    assert((words[i as int] | (bytes[(i * 8) + j] as u64) << (j * 8)) < pow2((j as nat + 1) * 8));
    assert((words[i as int] | (bytes[(i * 8) + j] as u64) << (j * 8)) == bytes_as_nat_prefix(
        Seq::new(8, |j2: int| bytes[(i as nat) * 8 + j2]),
        (j + 1) as nat,
    ));
}

/// Proves that 4 u64 words correctly represent a 32-byte array as a natural number
///
/// This lemma connects the byte-level and word-level representations, proving that
/// the natural number value of 32 bytes equals the natural number value of 4 words
/// (when each word contains 8 bytes in little-endian order).
///
/// # Mathematical relationship
/// If `words[i]` contains `bytes[i*8..i*8+8]` in little-endian order, then:
/// ```text
/// u8_32_as_nat(bytes) = words_as_nat_u64(&words, 4, 64)
/// = words[0] + words[1]*2^64 + words[2]*2^128 + words[3]*2^192
/// ```
///
/// # Arguments
/// * `bytes` - The 32-byte input array
/// * `words` - The 4 u64 words built from the bytes
pub proof fn lemma_bytes_to_word_equivalence(bytes: &[u8; 32], words: [u64; 4])
    requires
        forall|i2: int|
            0 <= i2 < 4 ==> ((words[i2] as nat) == bytes_as_nat_prefix(
                Seq::new(8, |j: int| bytes[i2 * 8 + j]),
                8,
            )),
    ensures
        u8_32_as_nat(bytes) == words_as_nat_u64(&words, 4, 64),
{
    // For each of the 4 words, prove it equals the sum of its 8 bytes with appropriate powers of 2
    assert(words[0] == bytes[0] * pow2(0) + bytes[1] * pow2(8) + bytes[2] * pow2(16) + bytes[3]
        * pow2(24) + bytes[4] * pow2(32) + bytes[5] * pow2(40) + bytes[6] * pow2(48) + bytes[7]
        * pow2(56)) by {
        reveal_with_fuel(bytes_as_nat_prefix, 9);
        lemma_mul_commutative_8_terms(
            bytes[0] as int,
            pow2(0) as int,
            bytes[1] as int,
            pow2(8) as int,
            bytes[2] as int,
            pow2(16) as int,
            bytes[3] as int,
            pow2(24) as int,
            bytes[4] as int,
            pow2(32) as int,
            bytes[5] as int,
            pow2(40) as int,
            bytes[6] as int,
            pow2(48) as int,
            bytes[7] as int,
            pow2(56) as int,
        );
    }

    lemma_pow2_distributivity_over_word(
        words[0] as nat,
        bytes[0] as nat,
        bytes[1] as nat,
        bytes[2] as nat,
        bytes[3] as nat,
        bytes[4] as nat,
        bytes[5] as nat,
        bytes[6] as nat,
        bytes[7] as nat,
        0,
    );

    assert(words[1] == bytes[8] * pow2(0) + bytes[9] * pow2(8) + bytes[10] * pow2(16) + bytes[11]
        * pow2(24) + bytes[12] * pow2(32) + bytes[13] * pow2(40) + bytes[14] * pow2(48) + bytes[15]
        * pow2(56)) by {
        reveal_with_fuel(bytes_as_nat_prefix, 9);
        lemma_mul_commutative_8_terms(
            bytes[8] as int,
            pow2(0) as int,
            bytes[9] as int,
            pow2(8) as int,
            bytes[10] as int,
            pow2(16) as int,
            bytes[11] as int,
            pow2(24) as int,
            bytes[12] as int,
            pow2(32) as int,
            bytes[13] as int,
            pow2(40) as int,
            bytes[14] as int,
            pow2(48) as int,
            bytes[15] as int,
            pow2(56) as int,
        );
    }

    lemma_pow2_distributivity_over_word(
        words[1] as nat,
        bytes[8] as nat,
        bytes[9] as nat,
        bytes[10] as nat,
        bytes[11] as nat,
        bytes[12] as nat,
        bytes[13] as nat,
        bytes[14] as nat,
        bytes[15] as nat,
        64,
    );

    assert(words[2] == bytes[16] * pow2(0) + bytes[17] * pow2(8) + bytes[18] * pow2(16) + bytes[19]
        * pow2(24) + bytes[20] * pow2(32) + bytes[21] * pow2(40) + bytes[22] * pow2(48) + bytes[23]
        * pow2(56)) by {
        reveal_with_fuel(bytes_as_nat_prefix, 9);
        lemma_mul_commutative_8_terms(
            bytes[16] as int,
            pow2(0) as int,
            bytes[17] as int,
            pow2(8) as int,
            bytes[18] as int,
            pow2(16) as int,
            bytes[19] as int,
            pow2(24) as int,
            bytes[20] as int,
            pow2(32) as int,
            bytes[21] as int,
            pow2(40) as int,
            bytes[22] as int,
            pow2(48) as int,
            bytes[23] as int,
            pow2(56) as int,
        );
    }

    lemma_pow2_distributivity_over_word(
        words[2] as nat,
        bytes[16] as nat,
        bytes[17] as nat,
        bytes[18] as nat,
        bytes[19] as nat,
        bytes[20] as nat,
        bytes[21] as nat,
        bytes[22] as nat,
        bytes[23] as nat,
        128,
    );

    assert(words[3] == bytes[24] * pow2(0) + bytes[25] * pow2(8) + bytes[26] * pow2(16) + bytes[27]
        * pow2(24) + bytes[28] * pow2(32) + bytes[29] * pow2(40) + bytes[30] * pow2(48) + bytes[31]
        * pow2(56)) by {
        reveal_with_fuel(bytes_as_nat_prefix, 10);
        lemma_mul_commutative_8_terms(
            bytes[24] as int,
            pow2(0) as int,
            bytes[25] as int,
            pow2(8) as int,
            bytes[26] as int,
            pow2(16) as int,
            bytes[27] as int,
            pow2(24) as int,
            bytes[28] as int,
            pow2(32) as int,
            bytes[29] as int,
            pow2(40) as int,
            bytes[30] as int,
            pow2(48) as int,
            bytes[31] as int,
            pow2(56) as int,
        );
    }

    lemma_pow2_distributivity_over_word(
        words[3] as nat,
        bytes[24] as nat,
        bytes[25] as nat,
        bytes[26] as nat,
        bytes[27] as nat,
        bytes[28] as nat,
        bytes[29] as nat,
        bytes[30] as nat,
        bytes[31] as nat,
        192,
    );

    reveal(u8_32_as_nat);
    reveal_with_fuel(words_as_nat_gen, 5);
}

/// Proves that 5 Scalar52 limbs correctly represent 4 u64 words
///
/// This lemma verifies the bit-slicing operation that extracts 5 limbs of 52 bits each
/// from 4 words of 64 bits each. The limbs overlap across word boundaries.
///
/// # Limb extraction pattern
/// ```text
/// Word layout (4 × 64 bits = 256 bits total):
/// [----word[0]----][----word[1]----][----word[2]----][----word[3]----]
///
/// Limb extraction (5 × 52 bits = 260 bits, last limb only 48 bits):
/// [--limb[0]--][--limb[1]--][--limb[2]--][--limb[3]--][limb[4]]
///        \___12 bits from word[1]
///                    \___12 bits from word[2]
///                                \___8 bits from word[3]
/// ```
///
/// # Arguments
/// * `words` - The 4 u64 words containing the packed bytes
/// * `s` - The Scalar52 with 5 limbs extracted from the words
/// * `mask` - The 52-bit mask (2^52 - 1)
/// * `top_mask` - The 48-bit mask (2^48 - 1) for the final limb
pub proof fn lemma_words_to_scalar(words: [u64; 4], s: Scalar52, mask: u64, top_mask: u64)
    requires
        mask == (1u64 << 52) - 1,
        top_mask == (1u64 << 48) - 1,
        s.limbs[0] == words[0] & mask,
        s.limbs[1] == ((words[0] >> 52) | (words[1] << 12)) & mask,
        s.limbs[2] == ((words[1] >> 40) | (words[2] << 24)) & mask,
        s.limbs[3] == ((words[2] >> 28) | (words[3] << 36)) & mask,
        s.limbs[4] == (words[3] >> 16) & top_mask,
    ensures
        words_as_nat_u64(&words, 4, 64) == scalar52_to_nat(&s),
        limbs_bounded(&s),
{
    // Bit-vector proofs that masks work correctly
    assert(1u64 << 52 > 0) by (bit_vector);
    assert(1u64 << 48 > 0) by (bit_vector);

    lemma_u64_pow2_no_overflow(52);
    lemma_u64_pow2_no_overflow(40);
    lemma_u64_pow2_no_overflow(28);
    lemma_u64_pow2_no_overflow(16);

    // Split each word into two parts at strategic bit positions
    // This corresponds to how limbs are extracted from overlapping word boundaries
    let word_0_first = words[0] % pow2(52) as u64;  // Lower 52 bits of word[0] → limb[0]
    let word_0_second = words[0] / pow2(52) as u64;  // Upper 12 bits of word[0] → part of limb[1]
    let word_1_first = words[1] % pow2(40) as u64;  // Lower 40 bits of word[1] → part of limb[1]
    let word_1_second = words[1] / pow2(40) as u64;  // Upper 24 bits of word[1] → part of limb[2]
    let word_2_first = words[2] % pow2(28) as u64;  // Lower 28 bits of word[2] → part of limb[2]
    let word_2_second = words[2] / pow2(28) as u64;  // Upper 36 bits of word[2] → part of limb[3]
    let word_3_first = words[3] % pow2(16) as u64;  // Lower 16 bits of word[3] → part of limb[3]
    let word_3_second = words[3] / pow2(16) as u64;  // Upper 48 bits of word[3] → limb[4]

    assert(words[0] == word_0_first + word_0_second * pow2(52)) by {
        lemma_fundamental_div_mod(words[0] as int, pow2(52) as int);
    }
    assert(words[1] == word_1_first + word_1_second * pow2(40)) by {
        lemma_fundamental_div_mod(words[1] as int, pow2(40) as int);
    }
    assert(words[2] == word_2_first + word_2_second * pow2(28)) by {
        lemma_fundamental_div_mod(words[2] as int, pow2(28) as int);
    }
    assert(words[3] == word_3_first + word_3_second * pow2(16)) by {
        lemma_fundamental_div_mod(words[3] as int, pow2(16) as int);
    }

    assert(mask + 1 == pow2(52)) by {
        lemma_pow2(52);
        assert((pow(2, 52) as u64) == (1u64 << 52)) by (compute);
        assert(pow(2, 52) as u64 == mask + 1);
    }
    assert(low_bits_mask(52) == mask);

    let words0 = words[0] as u64;
    let words1 = words[1] as u64;
    let words2 = words[2] as u64;
    let words3 = words[3] as u64;

    assert(words0 & mask < (1u64 << 52)) by (bit_vector)
        requires
            mask == ((1u64 << 52) - 1),
    ;
    assert(((words0 >> 52) | (words1 << 12)) & mask < (1u64 << 52)) by (bit_vector)
        requires
            mask == ((1u64 << 52) - 1),
    ;
    assert(((words1 >> 40) | (words2 << 24)) & mask < (1u64 << 52)) by (bit_vector)
        requires
            mask == ((1u64 << 52) - 1),
    ;
    assert(((words2 >> 28) | (words3 << 36)) & mask < (1u64 << 52)) by (bit_vector)
        requires
            mask == ((1u64 << 52) - 1),
    ;
    assert((words3 >> 16) & top_mask < (1u64 << 52)) by (bit_vector)
        requires
            top_mask == ((1u64 << 48) - 1),
    ;

    // Prove each limb equals the correct combination of word parts

    // Limb 0: Just the lower 52 bits of word[0]
    assert(s.limbs[0] == word_0_first) by {
        assert(words[0] & mask == words[0] % pow2(52) as u64) by {
            lemma_u64_low_bits_mask_is_mod(words[0], 52);
        };
    };

    // Limb 1: Upper 12 bits of word[0] combined with lower 40 bits of word[1] (shifted left by 12)
    assert(s.limbs[1] == word_0_second + word_1_first * pow2(12)) by {
        assert((((words0 >> 52) | (words1 << 12)) & mask) == (words0 >> 52) + ((words1 & (((1u64
            << 40) - 1u64) as u64)) << 12)) by (bit_vector)
            requires
                mask == ((1u64 << 52) - 1),
        ;

        assert(low_bits_mask(40) == ((1u64 << 40) - 1u64)) by {
            lemma_pow2(40);
            assert(pow(2, 40) == (1u64 << 40)) by (compute);
            assert(pow2(40) - 1 == low_bits_mask(40));
        };

        assert(((words0 >> 52) + ((words1 & (((1u64 << 40) - 1u64) as u64)) << 12)) == ((words0
            / pow2(52) as u64) + ((words1 % pow2(40) as u64) * pow2(12)))) by {
            lemma_u64_low_bits_mask_is_mod(words1, 40);

            assert((words1 % pow2(40) as u64) * pow2(12) < pow2(52)) by {
                lemma_pow2_pos(40);
                lemma_mod_division_less_than_divisor(words1 as int, pow2(40) as int);
                lemma_pow2_pos(12);
                lemma_mul_strict_inequality(
                    (words1 % pow2(40) as u64) as int,
                    pow2(40) as int,
                    pow2(12) as int,
                );
                assert((words1 % pow2(40) as u64) * pow2(12) < pow2(40) * pow2(12));
                lemma_pow2_adds(40, 12);
            }
            lemma_u64_shl_is_mul(words1 % pow2(40) as u64, 12);
            lemma_u64_shr_is_div(words0, 52);
        };

        assert(s.limbs[1] == (words0 / pow2(52) as u64) + ((words1 % pow2(40) as u64) * pow2(12)));
    }

    // Limb 2: Upper 24 bits of word[1] combined with lower 28 bits of word[2] (shifted left by 24)
    assert(s.limbs[2] == word_1_second + word_2_first * pow2(24)) by {
        assert((((words1 >> 40) | (words2 << 24)) & mask) == (words1 >> 40) + ((words2 & (((1u64
            << 28) - 1u64) as u64)) << 24)) by (bit_vector)
            requires
                mask == ((1u64 << 52) - 1),
        ;

        assert(low_bits_mask(28) == ((1u64 << 28) - 1u64)) by {
            lemma_pow2(28);
            assert(pow(2, 28) == (1u64 << 28)) by (compute);
            assert(pow2(28) - 1 == low_bits_mask(28));
        };

        assert(((words1 >> 40) + ((words2 & (((1u64 << 28) - 1u64) as u64)) << 24)) == ((words1
            / pow2(40) as u64) + ((words2 % pow2(28) as u64) * pow2(24)))) by {
            lemma_u64_low_bits_mask_is_mod(words2, 28);

            assert((words2 % pow2(28) as u64) * pow2(24) < pow2(52)) by {
                lemma_pow2_pos(28);
                lemma_mod_division_less_than_divisor(words2 as int, pow2(28) as int);
                lemma_pow2_pos(24);
                lemma_mul_strict_inequality(
                    (words2 % pow2(28) as u64) as int,
                    pow2(28) as int,
                    pow2(24) as int,
                );
                assert((words2 % pow2(28) as u64) * pow2(24) < pow2(28) * pow2(24));
                lemma_pow2_adds(28, 24);
            }
            lemma_u64_shl_is_mul(words2 % pow2(28) as u64, 24);
            lemma_u64_shr_is_div(words1, 40);
        };
        assert(s.limbs[2] == (words1 / pow2(40) as u64) + ((words2 % pow2(28) as u64) * pow2(24)));
    }

    // Limb 3: Upper 36 bits of word[2] combined with lower 16 bits of word[3] (shifted left by 36)
    assert(s.limbs[3] == word_2_second + word_3_first * pow2(36)) by {
        assert((((words2 >> 28) | (words3 << 36)) & mask) == (words2 >> 28) + ((words3 & (((1u64
            << 16) - 1u64) as u64)) << 36)) by (bit_vector)
            requires
                mask == ((1u64 << 52) - 1),
        ;

        assert(low_bits_mask(16) == ((1u64 << 16) - 1u64)) by {
            lemma_pow2(16);
            assert(pow(2, 16) == (1u64 << 16)) by (compute);
            assert(pow2(16) - 1 == low_bits_mask(16));
        };

        assert(((words2 >> 28) + ((words3 & (((1u64 << 16) - 1u64) as u64)) << 36)) == ((words2
            / pow2(28) as u64) + ((words3 % pow2(16) as u64) * pow2(36)))) by {
            lemma_u64_low_bits_mask_is_mod(words3, 16);

            assert((words3 % pow2(16) as u64) * pow2(36) < pow2(52)) by {
                lemma_pow2_pos(16);
                lemma_mod_division_less_than_divisor(words3 as int, pow2(16) as int);
                lemma_pow2_pos(36);
                lemma_mul_strict_inequality(
                    (words3 % pow2(16) as u64) as int,
                    pow2(16) as int,
                    pow2(36) as int,
                );
                assert((words3 % pow2(16) as u64) * pow2(36) < pow2(16) * pow2(36));
                lemma_pow2_adds(16, 36);
            }
            lemma_u64_shl_is_mul(words3 % pow2(16) as u64, 36);
            lemma_u64_shr_is_div(words2, 28);
        };

        assert(s.limbs[3] == (words2 / pow2(28) as u64) + ((words3 % pow2(16) as u64) * pow2(36)));
    }

    // Limb 4: Just the upper 48 bits of word[3]
    assert(s.limbs[4] == word_3_second) by {
        assert(words3 >> 16 & (top_mask) == words3 >> 16) by (bit_vector)
            requires
                top_mask == ((1u64 << 48) - 1u64),
        ;
        lemma_u64_shr_is_div(words3, 16);
    }

    reveal(scalar52_to_nat);
    reveal_with_fuel(seq_to_nat_52, 10);
    reveal_with_fuel(words_as_nat_gen, 5);

    assert(words_as_nat_u64(&words, 4, 64) == words[0] + words[1] * pow2(64) + words[2] * pow2(128)
        + words[3] * pow2(192)) by {
        assert(pow2(0) == 1) by {
            lemma_pow2(0);
            assert(pow(2, 0) == 1) by (compute);
        }
        assert(words[0] == words[0] * 1);
    };

    calc! {
        (==)
        words_as_nat_u64(&words, 4, 64); (==) {}
        (words[0] + words[1] * pow2(64) + words[2] * pow2(128) + words[3] * pow2(
            192,
        )) as nat; (==) {}
        ((word_0_first + word_0_second * pow2(52)) + (word_1_first + word_1_second * pow2(40))
            * pow2(64) + (word_2_first + word_2_second * pow2(28)) * pow2(128) + (word_3_first
            + word_3_second * pow2(16)) * pow2(192)) as nat; (==) {
            lemma_mul_is_distributive_add_other_way(
                pow2(64) as int,
                word_1_first as int,
                word_1_second * pow2(40) as int,
            );
            lemma_mul_is_associative(word_1_second as int, pow2(40) as int, pow2(64) as int);
            lemma_pow2_adds(40, 64);

            lemma_mul_is_distributive_add_other_way(
                pow2(128) as int,
                word_2_first as int,
                word_2_second * pow2(28) as int,
            );
            lemma_mul_is_associative(word_2_second as int, pow2(28) as int, pow2(128) as int);
            lemma_pow2_adds(28, 128);

            lemma_mul_is_distributive_add_other_way(
                pow2(192) as int,
                word_3_first as int,
                word_3_second * pow2(16) as int,
            );
            lemma_mul_is_associative(word_3_second as int, pow2(16) as int, pow2(192) as int);
            lemma_pow2_adds(16, 192);
        }
        ((word_0_first + word_0_second * pow2(52)) + (word_1_first * pow2(64) + word_1_second
            * pow2(104)) + (word_2_first * pow2(128) + word_2_second * pow2(156)) + (word_3_first
            * pow2(192) + word_3_second * pow2(208))) as nat;
    }
    let a = s.limbs[0] as int;
    let b = s.limbs[1] as int;
    let c = s.limbs[2] as int;
    let d = s.limbs[3] as int;
    let e = s.limbs[4] as int;

    calc! {
        (==)
        scalar52_to_nat(&s) as int; (==) {}
        // Start expression
        a + (b + (c + (d + e * (pow2(52) as int)) * (pow2(52) as int)) * (pow2(52) as int)) * (pow2(
            52,
        ) as int);
        // 1) Expand innermost: (d + e*2^52)*2^52
        (==) {
            lemma_mul_is_distributive_add_other_way(pow2(52) as int, d, e * (pow2(52) as int));
            lemma_mul_is_associative(e, pow2(52) as int, pow2(52) as int);
            lemma_pow2_adds(52, 52);
        }
        a + (b + (c + (d * (pow2(52) as int) + e * (pow2(104) as int))) * (pow2(52) as int)) * (
        pow2(
            52,
        ) as int);
        // 2) Expand next level: (c + (d*2^52 + e*2^104)) * 2^52
        (==) {
            let T1 = d * (pow2(52) as int) + e * (pow2(104) as int);
            lemma_mul_is_distributive_add_other_way(pow2(52) as int, c, T1);
            lemma_mul_is_distributive_add_other_way(
                pow2(52) as int,
                d * (pow2(52) as int),
                e * (pow2(104) as int),
            );
            lemma_mul_is_associative(d, pow2(52) as int, pow2(52) as int);
            lemma_pow2_adds(52, 52);
            lemma_mul_is_associative(e, pow2(104) as int, pow2(52) as int);
            lemma_pow2_adds(104, 52);
        }
        a + (b + (c * (pow2(52) as int) + d * (pow2(104) as int) + e * (pow2(156) as int))) * (pow2(
            52,
        ) as int);
        // 3) Expand outer level: (b + (c*2^52 + d*2^104 + e*2^156)) * 2^52
        (==) {
            let U = c * (pow2(52) as int) + d * (pow2(104) as int) + e * (pow2(156) as int);
            lemma_mul_is_distributive_add_other_way(pow2(52) as int, b, U);
            let U1 = c * (pow2(52) as int) + d * (pow2(104) as int);
            lemma_mul_is_distributive_add_other_way(pow2(52) as int, U1, e * (pow2(156) as int));
            lemma_mul_is_distributive_add_other_way(
                pow2(52) as int,
                c * (pow2(52) as int),
                d * (pow2(104) as int),
            );
            lemma_mul_is_associative(c, pow2(52) as int, pow2(52) as int);
            lemma_pow2_adds(52, 52);
            lemma_mul_is_associative(d, pow2(104) as int, pow2(52) as int);
            lemma_pow2_adds(104, 52);
            lemma_mul_is_associative(e, pow2(156) as int, pow2(52) as int);
            lemma_pow2_adds(156, 52);
        }
        a + b * (pow2(52) as int) + c * (pow2(104) as int) + d * (pow2(156) as int) + e * (pow2(
            208,
        ) as int); (==) {}
        word_0_first + (word_0_second + word_1_first * pow2(12)) * pow2(52) + (word_1_second
            + word_2_first * pow2(24)) * pow2(104) + (word_2_second + word_3_first * pow2(36))
            * pow2(156) + word_3_second * pow2(208); (==) {
            lemma_mul_is_distributive_add_other_way(
                pow2(52) as int,
                word_0_second as int,
                word_1_first * (pow2(12) as int),
            );
            lemma_mul_is_associative(word_1_first as int, pow2(12) as int, pow2(52) as int);
            lemma_pow2_adds(12, 52);
            assert(pow2(12) * pow2(52) == pow2(64));
            lemma_mul_is_distributive_add_other_way(
                pow2(104) as int,
                word_1_second as int,
                word_2_first * (pow2(24) as int),
            );
            lemma_mul_is_associative(word_2_first as int, pow2(24) as int, pow2(104) as int);
            lemma_pow2_adds(24, 104);
            assert(pow2(12) * pow2(52) == pow2(64));
            lemma_mul_is_distributive_add_other_way(
                pow2(156) as int,
                word_2_second as int,
                word_3_first * (pow2(36) as int),
            );
            lemma_mul_is_associative(word_3_first as int, pow2(36) as int, pow2(156) as int);
            lemma_pow2_adds(36, 156);
        }
        (word_0_first + word_0_second * pow2(52) + word_1_first * pow2(64) + word_1_second * pow2(
            104,
        ) + word_2_first * pow2(128) + word_2_second * pow2(156) + word_3_first * pow2(192)
            + word_3_second * pow2(208));
    };
}

} // verus!
