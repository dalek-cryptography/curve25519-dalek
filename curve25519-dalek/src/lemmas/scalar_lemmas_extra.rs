#[allow(unused_imports)]
use super::super::specs::core_specs::*;
#[allow(unused_imports)]
use super::common_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants;
#[allow(unused_imports)]
use crate::backend::serial::u64::scalar::Scalar52;
#[allow(unused_imports)]
use crate::specs::scalar52_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::bits::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;

#[allow(unused_imports)]
use super::common_lemmas::bit_lemmas::*;
#[allow(unused_imports)]
use super::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use super::common_lemmas::shift_lemmas::*;
#[allow(unused_imports)]
use super::field_lemmas::load8_lemmas::*;

#[allow(unused_imports)]
use super::scalar_lemmas::*;

verus! {

/// Helper lemma for decomposing a word's contribution at a given scale.
/// Given a word that is split at bit position `split_pos`, this lemma proves:
///   pow2(scale) * word == pow2(scale) * low_part + pow2(scale + split_pos) * high_part
/// where low_part = word & (u64::MAX >> mask_shift) and high_part = word >> split_pos
/// Note: mask_shift = 64 - split_pos
pub proof fn lemma_word_contribution_decomposition(
    word: u64,
    scale: nat,
    split_pos: u64,
    mask_shift: u64,
    low_part: nat,
    high_part: nat,
)
    requires
        split_pos > 0 && split_pos < 64,
        mask_shift + split_pos == 64,
        low_part == (word & (u64::MAX >> mask_shift)) as nat,
        high_part == (word >> split_pos) as nat,
    ensures
        pow2(scale) * (word as nat) == pow2(scale) * low_part + pow2(scale + split_pos as nat)
            * high_part,
{
    let low_mask = u64::MAX >> mask_shift;
    let low = word & low_mask;
    let high = word >> split_pos;

    // Low part is bounded
    assert((word & low_mask) < (1u64 << split_pos)) by (bit_vector)
        requires
            split_pos > 0 && split_pos < 64 && mask_shift + split_pos == 64 && low_mask == u64::MAX
                >> mask_shift,
    ;

    // High part is bounded
    assert((word >> split_pos) <= u64::MAX >> split_pos) by (bit_vector)
        requires
            split_pos > 0 && split_pos < 64,
    ;

    // Word decomposes into low | (high << split_pos)
    assert(word == (word & low_mask) | ((word >> split_pos) << split_pos)) by (bit_vector)
        requires
            split_pos > 0 && split_pos < 64 && mask_shift + split_pos == 64 && low_mask == u64::MAX
                >> mask_shift,
    ;

    lemma_u64_bit_or_is_plus(low, high, split_pos);
    vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high, split_pos, u64::MAX);
    vstd::bits::lemma_u64_shl_is_mul(high, split_pos);

    // pow2(scale) * (pow2(split_pos) * high_part) == pow2(scale + split_pos) * high_part
    assert(pow2(scale) * (pow2(split_pos as nat) * high_part) == pow2(scale + split_pos as nat)
        * high_part) by {
        assert(pow2(scale) * (pow2(split_pos as nat) * high_part) == (pow2(scale) * pow2(
            split_pos as nat,
        )) * high_part) by (nonlinear_arith);
        lemma_pow2_adds(scale, split_pos as nat);
    }
    // Final ensures: pow2(scale) * word == pow2(scale) * low_part + pow2(scale + split_pos) * high_part
    assert(pow2(scale) * (word as nat) == pow2(scale) * low_part + pow2(scale + split_pos as nat)
        * high_part) by {
        broadcast use group_mul_is_distributive;

    };

}

/// Helper lemma for proving a limb (from adjacent words) equals the sum of high bits
/// from the previous word and low bits from the next word.
/// The limb is formed as: ((prev_word >> prev_shift) | (next_word << high_bits)) & mask
/// and equals: high_part + pow2(high_bits) * low_part
///
/// Parameters:
/// - `prev_word`, `next_word`: The two adjacent words
/// - `prev_shift`: How many bits to shift prev_word right (64 - high_bits)
/// - `high_bits`: Number of bits from prev_word contributing to the limb
/// - `low_mask_shift`: How many bits to shift for the low mask (64 - low_bits, where low_bits = 52 - high_bits)
/// - `limb`: The computed limb value
/// - `high_part`: (prev_word >> prev_shift) as nat
/// - `low_part`: (next_word & low_mask) as nat
pub proof fn lemma_limb_from_adjacent_words(
    prev_word: u64,
    next_word: u64,
    prev_shift: u64,
    high_bits: u64,
    low_mask_shift: u64,
    limb: nat,
    high_part: nat,
    low_part: nat,
)
    requires
        high_bits > 0 && high_bits < 52,
        prev_shift + high_bits == 64,
        low_mask_shift + (52 - high_bits) == 64,
        limb == (((prev_word >> prev_shift) | (next_word << high_bits)) & (u64::MAX >> 12)) as nat,
        high_part == (prev_word >> prev_shift) as nat,
        low_part == (next_word & (u64::MAX >> low_mask_shift)) as nat,
    ensures
        limb == high_part + pow2(high_bits as nat) * low_part,
{
    let mask = u64::MAX >> 12;
    let low_mask = u64::MAX >> low_mask_shift;
    let high_val = prev_word >> prev_shift;
    let low_val = next_word & low_mask;

    // High part is bounded by 2^high_bits
    assert((prev_word >> prev_shift) < (1u64 << high_bits)) by (bit_vector)
        requires
            high_bits > 0 && high_bits < 52 && prev_shift + high_bits == 64,
    ;

    // Low part fits when shifted by high_bits
    assert((next_word & low_mask) <= u64::MAX >> high_bits) by (bit_vector)
        requires
            high_bits > 0 && high_bits < 52 && low_mask_shift + (52 - high_bits) == 64 && low_mask
                == u64::MAX >> low_mask_shift,
    ;

    // OR with mask simplifies
    assert(((prev_word >> prev_shift) | (next_word << high_bits)) & mask == (prev_word
        >> prev_shift) | ((next_word & low_mask) << high_bits)) by (bit_vector)
        requires
            high_bits > 0 && high_bits < 52 && prev_shift + high_bits == 64 && low_mask_shift + (52
                - high_bits) == 64 && low_mask == u64::MAX >> low_mask_shift && mask == u64::MAX
                >> 12,
    ;

    // Combined value fits in 52 bits
    assert(((prev_word >> prev_shift) | ((next_word & low_mask) << high_bits)) < (1u64 << 52))
        by (bit_vector)
        requires
            high_bits > 0 && high_bits < 52 && prev_shift + high_bits == 64 && low_mask_shift + (52
                - high_bits) == 64 && low_mask == u64::MAX >> low_mask_shift,
    ;

    lemma_u64_bit_or_is_plus(high_val, low_val, high_bits);
    vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low_val, high_bits, u64::MAX);
    vstd::bits::lemma_u64_shl_is_mul(low_val, high_bits);
}

/// Lemma: suffix sum at word boundary equals word contribution + remaining suffix.
/// Shows how bytes_as_nat_suffix decomposes at word (8-byte) boundaries.
pub proof fn lemma_bytes_suffix_matches_word_partial(bytes: &[u8; 64], word_idx: int, upto: int)
    requires
        0 <= word_idx < 8,
        0 <= upto <= 8,
    ensures
        bytes_as_nat_suffix(bytes, word_idx * 8) == pow2(((word_idx * 8) * 8) as nat)
            * word64_from_bytes_partial(bytes@, word_idx, upto) + bytes_as_nat_suffix(
            bytes,
            word_idx * 8 + upto,
        ),
    decreases upto,
{
    let base = word_idx * 8;
    let pow_base = pow2((base * 8) as nat);
    if upto == 0 {
        assert(pow_base * 0 + bytes_as_nat_suffix(bytes, base + 0) == pow_base
            * word64_from_bytes_partial(bytes@, word_idx, 0) + bytes_as_nat_suffix(
            bytes,
            base + 0,
        ));
    } else {
        let prev = upto - 1;
        lemma_bytes_suffix_matches_word_partial(bytes, word_idx, prev);
        if upto >= 8 {
            // Inline lemma_word64_from_bytes_partial_step_last
            reveal_with_fuel(word64_from_bytes_partial, 9);
        }
        let partial_prev = word64_from_bytes_partial(bytes@, word_idx, prev);
        let byte_val = bytes[(base + prev) as int] as nat;
        lemma_pow2_adds(((base * 8) as nat), ((prev * 8) as nat));

        // Rewriting byte_val * pow2((base + prev) * 8) = pow_base * byte_val * pow2(prev * 8)
        assert(byte_val * (pow_base * pow2((prev * 8) as nat)) == pow_base * byte_val * pow2(
            (prev * 8) as nat,
        )) by (nonlinear_arith);
        // Factor out pow_base
        assert(pow_base * partial_prev + pow_base * byte_val * pow2((prev * 8) as nat) == pow_base
            * (partial_prev + byte_val * pow2((prev * 8) as nat))) by (nonlinear_arith);
    }
}

pub proof fn lemma_low_limbs_encode_low_expr(lo: &[u64; 5], words: &[u64; 8], mask: u64)
    requires
        mask == (1u64 << 52) - 1u64,
        lo[0] == words[0] & mask,
        lo[1] == ((words[0] >> 52) | (words[1] << 12)) & mask,
        lo[2] == ((words[1] >> 40) | (words[2] << 24)) & mask,
        lo[3] == ((words[2] >> 28) | (words[3] << 36)) & mask,
        lo[4] == ((words[3] >> 16) | (words[4] << 48)) & mask,
    ensures
        five_limbs_to_nat_aux(*lo) == (words[0] as nat) + pow2(64) * (words[1] as nat) + pow2(128)
            * (words[2] as nat) + pow2(192) * (words[3] as nat) + pow2(256) * ((words[4]
            & 0xf) as nat),
{
    // Common mask equality used throughout
    assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);

    let masked_words_sum = ((words[0] & mask) as nat) + pow2(52) * ((((words[0] >> 52) | (words[1]
        << 12)) & mask) as nat) + pow2(104) * ((((words[1] >> 40) | (words[2] << 24))
        & mask) as nat) + pow2(156) * ((((words[2] >> 28) | (words[3] << 36)) & mask) as nat)
        + pow2(208) * ((((words[3] >> 16) | (words[4] << 48)) & mask) as nat);

    let unmasked_words_sum = (words[0] as nat) + pow2(64) * (words[1] as nat) + pow2(128) * (
    words[2] as nat) + pow2(192) * (words[3] as nat) + pow2(256) * ((words[4] & 0xf) as nat);

    let limb1 = (((words[0] >> 52) | (words[1] << 12)) & mask) as nat;
    let limb2 = (((words[1] >> 40) | (words[2] << 24)) & mask) as nat;
    let limb3 = (((words[2] >> 28) | (words[3] << 36)) & mask) as nat;
    let limb4 = (((words[3] >> 16) | (words[4] << 48)) & mask) as nat;

    let w0_low = ((words[0] & mask) as nat);
    let w0_high = (words[0] >> 52) as nat;

    let w1_low = ((words[1] & (u64::MAX >> 24)) as nat);
    let w1_high = (words[1] >> 40) as nat;
    let w2_low = ((words[2] & (u64::MAX >> 36)) as nat);
    let w2_high = (words[2] >> 28) as nat;
    let w3_low = ((words[3] & (u64::MAX >> 48)) as nat);
    let w3_high = (words[3] >> 16) as nat;
    let w4_low = (words[4] & 0xf) as nat;

    // Limb 1 consists of word 0's top 12 bits and word 1's low 40 bits.
    lemma_limb_from_adjacent_words(words[0], words[1], 52, 12, 24, limb1, w0_high, w1_low);
    // Limb 2 consists of word 1's top 24 bits and word 2's low 28 bits.
    lemma_limb_from_adjacent_words(words[1], words[2], 40, 24, 36, limb2, w1_high, w2_low);
    // Limb 3 consists of word 2's top 36 bits and word 3's low 16 bits.
    lemma_limb_from_adjacent_words(words[2], words[3], 28, 36, 48, limb3, w2_high, w3_low);
    // Limb 4 consists of word 3's top 48 bits and word 4's low 4 bits.
    assert(limb4 == w3_high + pow2(48) * w4_low) by {
        let w3 = words[3];
        let w4 = words[4];
        let high48 = w3 >> 16;
        let low4 = w4 & 0xf;

        assert(((w3 >> 16) | (w4 << 48)) & (u64::MAX >> 12) == (w3 >> 16) | ((w4 & 0xf) << 48))
            by (bit_vector);
        assert((w3 >> 16) < (1u64 << 48)) by (bit_vector);
        assert((w4 & 0xf) <= u64::MAX >> 48) by (bit_vector);
        assert(((w3 >> 16) | ((w4 & 0xf) << 48)) < (1u64 << 52)) by (bit_vector);
        lemma_u64_bit_or_is_plus(high48, low4, 48);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(low4, 48, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(low4, 48);
    };
    // Word 0 equals its low 52 bits plus its top 12 bits shifted by 52.
    assert(words[0] as nat == w0_low + pow2(52) * w0_high) by {
        let w0 = words[0];
        let high = w0 >> 52;
        let low = w0 & mask;

        assert((w0 & (u64::MAX >> 12)) < (1u64 << 52)) by (bit_vector);
        assert((w0 >> 52) <= u64::MAX >> 52) by (bit_vector);
        lemma_decompose(w0, mask);
        lemma_u64_bit_or_is_plus(low, high, 52);
    };
    // Word 1's contribution at scale 2^64 equals its low 40 bits plus its high 24 bits.
    assert(pow2(64) * (words[1] as nat) == pow2(64) * w1_low + pow2(104) * w1_high) by {
        lemma_word_contribution_decomposition(words[1], 64, 40, 24, w1_low, w1_high);
    };
    // Word 2's contribution at scale 2^128 equals its low 28 bits plus its high 36 bits.
    assert(pow2(128) * (words[2] as nat) == pow2(128) * w2_low + pow2(156) * w2_high) by {
        lemma_word_contribution_decomposition(words[2], 128, 28, 36, w2_low, w2_high);
    };
    // Word 3's contribution at scale 2^192 equals its low 16 bits plus its high 48 bits.
    assert(pow2(192) * (words[3] as nat) == pow2(192) * w3_low + pow2(208) * w3_high) by {
        lemma_word_contribution_decomposition(words[3], 192, 16, 48, w3_low, w3_high);
    };

    assert(w0_low + pow2(52) * (w0_high + pow2(12) * w1_low) + pow2(104) * (w1_high + pow2(24)
        * w2_low) + pow2(156) * (w2_high + pow2(36) * w3_low) + pow2(208) * (w3_high + pow2(48)
        * w4_low) == unmasked_words_sum) by {
        broadcast use group_mul_is_distributive;
        broadcast use lemma_mul_is_associative;

        lemma_pow2_adds(52, 12);
        lemma_pow2_adds(104, 24);
        lemma_pow2_adds(156, 36);
        lemma_pow2_adds(208, 48);
    };
    assert(masked_words_sum == unmasked_words_sum);
}

pub proof fn lemma_high_limbs_encode_high_expr(hi: &[u64; 5], words: &[u64; 8], mask: u64)
    requires
        mask == (1u64 << 52) - 1u64,
        hi[0] == (words[4] >> 4) & mask,
        hi[1] == ((words[4] >> 56) | (words[5] << 8)) & mask,
        hi[2] == ((words[5] >> 44) | (words[6] << 20)) & mask,
        hi[3] == ((words[6] >> 32) | (words[7] << 32)) & mask,
        hi[4] == words[7] >> 20,
    ensures
        five_limbs_to_nat_aux(*hi) == (words[4] >> 4) as nat + pow2(60) * (words[5] as nat) + pow2(
            124,
        ) * (words[6] as nat) + pow2(188) * (words[7] as nat),
{
    // Common mask equality used throughout
    assert((1u64 << 52) - 1u64 == u64::MAX >> 12) by (bit_vector);

    let limb0 = ((words[4] >> 4) & mask) as nat;
    let limb1 = (((words[4] >> 56) | (words[5] << 8)) & mask) as nat;
    let limb2 = (((words[5] >> 44) | (words[6] << 20)) & mask) as nat;
    let limb3 = (((words[6] >> 32) | (words[7] << 32)) & mask) as nat;
    let limb4 = (words[7] >> 20) as nat;

    let masked_words_sum = limb0 + pow2(52) * limb1 + pow2(104) * limb2 + pow2(156) * limb3 + pow2(
        208,
    ) * limb4;

    let unmasked_words_sum = (words[4] >> 4) as nat + pow2(60) * (words[5] as nat) + pow2(124) * (
    words[6] as nat) + pow2(188) * (words[7] as nat);

    let w4_high = (words[4] >> 56) as nat;
    let w5_low = (words[5] & (u64::MAX >> 20)) as nat;
    let w5_high = (words[5] >> 44) as nat;
    let w6_low = (words[6] & (u64::MAX >> 32)) as nat;
    let w6_high = (words[6] >> 32) as nat;
    let w7_low = (words[7] & (u64::MAX >> 44)) as nat;
    let w7_high = (words[7] >> 20) as nat;

    // Limb 0 consists of word 4's bits 4 through 55.

    // Limb 1 consists of word 4's top 8 bits and word 5's low 44 bits.
    lemma_limb_from_adjacent_words(words[4], words[5], 56, 8, 20, limb1, w4_high, w5_low);

    // Limb 2 consists of word 5's top 20 bits and word 6's low 32 bits.
    lemma_limb_from_adjacent_words(words[5], words[6], 44, 20, 32, limb2, w5_high, w6_low);

    // Limb 3 consists of word 6's top 32 bits and word 7's low 20 bits.
    lemma_limb_from_adjacent_words(words[6], words[7], 32, 32, 44, limb3, w6_high, w7_low);

    // Limb 4 consists of word 7's top 44 bits.

    // Word 4 shifted by 4 equals limb 0 plus limb 1's contribution from word 4's high bits.
    assert((words[4] >> 4) as nat == limb0 + pow2(52) * w4_high) by {
        let w4 = words[4];
        let low52 = (w4 >> 4) & mask;
        let high8 = w4 >> 56;

        assert(((w4 >> 4) & (u64::MAX >> 12)) < (1u64 << 52)) by (bit_vector);
        assert(high8 <= u64::MAX >> 52) by {
            assert((w4 >> 56) <= u64::MAX >> 56) by (bit_vector);
            assert(u64::MAX >> 56 <= u64::MAX >> 52) by (bit_vector);
        }
        assert((w4 >> 4) == ((w4 >> 4) & (u64::MAX >> 12)) | ((w4 >> 56) << 52)) by (bit_vector);
        lemma_u64_bit_or_is_plus(low52, high8, 52);
        vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(high8, 52, u64::MAX);
        vstd::bits::lemma_u64_shl_is_mul(high8, 52);
    };

    // Word 5's contribution at scale 2^60 equals its low 44 bits plus its high 20 bits.
    assert(pow2(60) * (words[5] as nat) == pow2(60) * w5_low + pow2(104) * w5_high) by {
        lemma_word_contribution_decomposition(words[5], 60, 44, 20, w5_low, w5_high);
    };

    // Word 6's contribution at scale 2^124 equals its low 32 bits plus its high 32 bits.
    assert(pow2(124) * (words[6] as nat) == pow2(124) * w6_low + pow2(156) * w6_high) by {
        lemma_word_contribution_decomposition(words[6], 124, 32, 32, w6_low, w6_high);
    };

    // Word 7's contribution at scale 2^188 equals its low 20 bits plus its high 44 bits.
    assert(pow2(188) * (words[7] as nat) == pow2(188) * w7_low + pow2(208) * w7_high) by {
        lemma_word_contribution_decomposition(words[7], 188, 20, 44, w7_low, w7_high);
    };

    assert(limb0 + pow2(52) * (w4_high + pow2(8) * w5_low) + pow2(104) * (w5_high + pow2(20)
        * w6_low) + pow2(156) * (w6_high + pow2(32) * w7_low) + pow2(208) * w7_high
        == unmasked_words_sum) by {
        broadcast use group_mul_is_distributive;
        broadcast use lemma_mul_is_associative;

        lemma_pow2_adds(52, 8);
        lemma_pow2_adds(104, 20);
        lemma_pow2_adds(156, 32);
    };
    assert(masked_words_sum == unmasked_words_sum);
}

/// Proves that the lo limbs constructed from 8 words with the given mask are bounded by 2^52.
/// This is part of Stage 3 in from_bytes_wide.
pub proof fn lemma_lo_limbs_bounded(lo: &Scalar52, words: &[u64; 8], mask: u64)
    requires
        mask == (1u64 << 52) - 1u64,
        lo.limbs[0] == words[0] & mask,
        lo.limbs[1] == ((words[0] >> 52) | (words[1] << 12)) & mask,
        lo.limbs[2] == ((words[1] >> 40) | (words[2] << 24)) & mask,
        lo.limbs[3] == ((words[2] >> 28) | (words[3] << 36)) & mask,
        lo.limbs[4] == ((words[3] >> 16) | (words[4] << 48)) & mask,
    ensures
        forall|i: int| #![auto] 0 <= i < 5 ==> lo.limbs[i] < (1u64 << 52),
{
    lemma_borrow_and_mask_bounded(words[0], mask);
    lemma_borrow_and_mask_bounded((words[0] >> 52) | (words[1] << 12), mask);
    lemma_borrow_and_mask_bounded((words[1] >> 40) | (words[2] << 24), mask);
    lemma_borrow_and_mask_bounded((words[2] >> 28) | (words[3] << 36), mask);
    lemma_borrow_and_mask_bounded((words[3] >> 16) | (words[4] << 48), mask);
}

/// Proves that the hi limbs constructed from 8 words with the given mask are bounded by 2^52.
/// This is part of Stage 3 in from_bytes_wide.
pub proof fn lemma_hi_limbs_bounded(hi: &Scalar52, words: &[u64; 8], mask: u64)
    requires
        mask == (1u64 << 52) - 1u64,
        hi.limbs[0] == (words[4] >> 4) & mask,
        hi.limbs[1] == ((words[4] >> 56) | (words[5] << 8)) & mask,
        hi.limbs[2] == ((words[5] >> 44) | (words[6] << 20)) & mask,
        hi.limbs[3] == ((words[6] >> 32) | (words[7] << 32)) & mask,
        hi.limbs[4] == words[7] >> 20,
    ensures
        forall|i: int| #![auto] 0 <= i < 5 ==> hi.limbs[i] < (1u64 << 52),
{
    lemma_borrow_and_mask_bounded(words[4] >> 4, mask);
    lemma_borrow_and_mask_bounded((words[4] >> 56) | (words[5] << 8), mask);
    lemma_borrow_and_mask_bounded((words[5] >> 44) | (words[6] << 20), mask);
    lemma_borrow_and_mask_bounded((words[6] >> 32) | (words[7] << 32), mask);
    let word7 = words[7];
    assert(word7 >> 20 <= u64::MAX >> 20) by (bit_vector);
    assert(u64::MAX >> 20 < (1u64 << 52)) by (bit_vector);
}

/// Proves that Montgomery reduction cancels the R factor from a product.
///
/// Given a product (before * const_nat) reduced via Montgomery reduction, this lemma
/// proves that after cancelling R, we get: after ≡ before * extra_factor (mod L)
///
/// Usage in from_bytes_wide:
/// - For lo: const_nat = R, extra_factor = 1 → after ≡ before (mod L)
/// - For hi: const_nat = R², extra_factor = R → after ≡ before * R (mod L)
pub proof fn lemma_montgomery_reduce_cancels_r(
    after_nat: nat,
    before_nat: nat,
    const_nat: nat,
    extra_factor: nat,
)
    requires
// const_nat is congruent to extra_factor * R mod L

        const_nat % group_order() == (extra_factor * montgomery_radix()) % group_order(),
        // From montgomery_reduce: (after * R) % L == (before * const_nat) % L
        (after_nat * montgomery_radix()) % group_order() == (before_nat * const_nat)
            % group_order(),
    ensures
        after_nat % group_order() == (before_nat * extra_factor) % group_order(),
        // Also establish the intermediate form needed by Stage 5
        (after_nat * montgomery_radix()) % group_order() == (before_nat * extra_factor
            * montgomery_radix()) % group_order(),
{
    // Establish: (before * const_nat) % L == (before * extra_factor * R) % L
    lemma_mul_factors_congruent_implies_products_congruent(
        before_nat as int,
        (extra_factor * montgomery_radix()) as int,
        const_nat as int,
        group_order() as int,
    );
    // Associativity: before * extra_factor * R
    lemma_mul_is_associative(before_nat as int, extra_factor as int, montgomery_radix() as int);
    // Cancel the R multiplication
    lemma_cancel_mul_pow2_mod(after_nat, before_nat * extra_factor, montgomery_radix());
}

/// Proves that combining the high and low chunks at the 2^260 boundary reproduces the
/// weighted word sum. This is the "HighLow-Recombine" step in from_bytes_wide.
///
/// Given:
/// - low_expr = w0 + 2^64*w1 + 2^128*w2 + 2^192*w3 + 2^256*(w4 % 16)
/// - high_expr = (w4 / 16) + 2^60*w5 + 2^124*w6 + 2^188*w7
/// - wide_sum = w0 + 2^64*w1 + 2^128*w2 + 2^192*w3 + 2^256*w4 + 2^320*w5 + 2^384*w6 + 2^448*w7
///
/// Proves: 2^260 * high_expr + low_expr == wide_sum
pub proof fn lemma_high_low_recombine(
    w0: nat,
    w1: nat,
    w2: nat,
    w3: nat,
    w4: nat,
    w5: nat,
    w6: nat,
    w7: nat,
    w4_low: nat,
    w4_high: nat,
)
    requires
        w4_low == w4 % 16,
        w4_high == w4 / 16,
    ensures
        ({
            let low_expr = w0 + pow2(64) * w1 + pow2(128) * w2 + pow2(192) * w3 + pow2(256)
                * w4_low;
            let high_expr = w4_high + pow2(60) * w5 + pow2(124) * w6 + pow2(188) * w7;
            let wide_sum = w0 + pow2(64) * w1 + pow2(128) * w2 + pow2(192) * w3 + pow2(256) * w4
                + pow2(320) * w5 + pow2(384) * w6 + pow2(448) * w7;
            pow2(260) * high_expr + low_expr == wide_sum
        }),
{
    // Key insight: 2^260 * (w4/16) + 2^256 * (w4%16) == 2^256 * w4
    lemma_pow2_adds(256, 4);
    lemma2_to64();
    assert(pow2(2) == pow2(1) * pow2(1)) by {
        lemma_pow2_adds(1, 1);
    };
    assert(pow2(4) == pow2(2) * pow2(2)) by {
        lemma_pow2_adds(2, 2);
    };
    lemma_fundamental_div_mod(w4 as int, 16);

    // Word position scaling: 2^260 * 2^k == 2^(260+k)
    lemma_pow2_adds(260, 60);
    lemma_pow2_adds(260, 124);
    lemma_pow2_adds(260, 188);

    // Distribute 2^260 across high_expr terms and combine with low_expr
    broadcast use group_mul_is_distributive, lemma_mul_is_associative;

}

/// Proves that combining Montgomery-reduced hi and lo pieces preserves congruence
/// with the original wide input modulo the group order L.
///
/// Given:
/// - hi_raw = wide_input / R and lo_raw = wide_input % R (where R = 2^260)
/// - hi and lo are Montgomery reductions satisfying:
///   - hi * R ≡ hi_raw * R^2 (mod L)
///   - lo * R ≡ lo_raw * R (mod L)
/// - result = (hi + lo) mod L
///
/// Proves: result * R ≡ wide_input * R (mod L)
pub proof fn lemma_montgomery_reduced_sum_congruent(
    result_nat: nat,
    hi_nat: nat,
    lo_nat: nat,
    hi_raw_nat: nat,
    lo_raw_nat: nat,
    wide_input: nat,
)
    requires
// result comes from Scalar52::add

        result_nat == (hi_nat + lo_nat) % group_order(),
        // From Stage 4 Montgomery reductions
        (hi_nat * montgomery_radix()) % group_order() == (hi_raw_nat * montgomery_radix()
            * montgomery_radix()) % group_order(),
        (lo_nat * montgomery_radix()) % group_order() == (lo_raw_nat * montgomery_radix())
            % group_order(),
        // hi_raw and lo_raw come from dividing wide_input at the Montgomery radix boundary
        hi_raw_nat == wide_input / montgomery_radix(),
        lo_raw_nat == wide_input % montgomery_radix(),
    ensures
        (result_nat * montgomery_radix()) % group_order() == (wide_input * montgomery_radix())
            % group_order(),
{
    let r_nat = montgomery_radix();
    let group_int = group_order() as int;

    // Prove the key relationship from div/mod properties
    lemma_pow2_pos(260);
    lemma_fundamental_div_mod(wide_input as int, r_nat as int);

    // hi_raw_nat * r^2 + lo_raw_nat * r == r * (hi_raw_nat * r + lo_raw_nat) == r * wide_input
    assert(hi_raw_nat * r_nat * r_nat + lo_raw_nat * r_nat == wide_input * r_nat) by {
        lemma_mul_is_commutative(hi_raw_nat as int, r_nat as int);
        lemma_mul_is_distributive_add_other_way(
            r_nat as int,
            (hi_raw_nat * r_nat) as int,
            lo_raw_nat as int,
        );
    };

    lemma_small_mod(((hi_nat + lo_nat) % group_order()) as nat, group_order());
    lemma_mul_factors_congruent_implies_products_congruent(
        r_nat as int,
        ((hi_nat + lo_nat) % group_order()) as int,
        (hi_nat + lo_nat) as int,
        group_int,
    );
    lemma_mul_is_distributive_add(r_nat as int, hi_nat as int, lo_nat as int);
    lemma_add_mod_noop((r_nat * hi_nat) as int, (r_nat * lo_nat) as int, group_int);
    lemma_add_mod_noop((hi_raw_nat * r_nat * r_nat) as int, (lo_raw_nat * r_nat) as int, group_int);
}

} // verus!
