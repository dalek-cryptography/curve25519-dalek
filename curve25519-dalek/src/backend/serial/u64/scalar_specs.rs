#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {
pub open spec fn seq_to_nat(limbs: Seq<nat>) -> nat
decreases limbs.len()
{
    if limbs.len() == 0 {
        0
    } else {
        limbs[0] + seq_to_nat(limbs.subrange(1, limbs.len() as int)) * pow2(52)
    }
}

pub open spec fn slice128_to_nat(limbs: &[u128]) -> nat
{
    seq_to_nat(limbs@.map(|i, x| x as nat))
}

pub open spec fn to_nat(limbs: &[u64]) -> nat
{
    seq_to_nat(limbs@.map(|i, x| x as nat))
}

pub open spec fn nine_limbs_to_nat_aux(limbs: &[u128; 9]) -> nat {
    (limbs[0] as nat) +
    (limbs[1] as nat) * pow2(52) +
    (limbs[2] as nat) * pow2(104) +
    (limbs[3] as nat) * pow2(156) +
    (limbs[4] as nat) * pow2(208) +
    (limbs[5] as nat) * pow2(260) +
    (limbs[6] as nat) * pow2(312) +
    (limbs[7] as nat) * pow2(364) +
    (limbs[8] as nat) * pow2(416)
}

pub open spec fn five_limbs_to_nat_aux(limbs: [u64; 5]) -> nat {
    (limbs[0] as nat) +
    pow2(52) * (limbs[1] as nat) +
    pow2(104) * (limbs[2] as nat) +
    pow2(156) * (limbs[3] as nat) +
    pow2(208) * (limbs[4] as nat)
}

// Modular reduction of to_nat mod L
spec fn to_scalar(limbs: &[u64; 5]) -> nat {
    to_nat(limbs) % group_order()
}

/// natural value of a 256 bit bitstring represented as array of 32 bytes
pub open spec fn bytes_to_nat(bytes: &[u8; 32]) -> nat {
    // Convert bytes to nat in little-endian order using recursive helper
    bytes_to_nat_rec(bytes, 0)
}

pub open spec fn bytes_to_nat_rec(bytes: &[u8; 32], index: int) -> nat
decreases 32 - index
{
    if index >= 32 {
        0
    } else {
        (bytes[index] as nat) * pow2((index * 8) as nat) + bytes_to_nat_rec(bytes, index + 1)
    }
}

/// natural value of a 512 bit bitstring represented as array of 64 bytes
pub open spec fn bytes_wide_to_nat(bytes: &[u8; 64]) -> nat {
    // Convert bytes to nat in little-endian order using recursive helper
    bytes_wide_to_nat_rec(bytes, 0)
}

pub open spec fn bytes_wide_to_nat_rec(bytes: &[u8; 64], index: int) -> nat
decreases 64 - index
{
    if index >= 64 {
        0
    } else {
        (bytes[index] as nat) * pow2((index * 8) as nat) + bytes_wide_to_nat_rec(bytes, index + 1)
    }
}

// Generic function to convert array of words to natural number
// Takes: array of words, number of words, bits per word
// Note: This is a specification function that works with concrete types
pub open spec fn words_to_nat_gen_u64(words: &[u64], num_words: int, bits_per_word: int) -> nat
decreases num_words
{
    if num_words <= 0 {
        0
    } else {
        let word_value = (words[num_words - 1] as nat) * pow2(((num_words - 1) * bits_per_word) as nat);
        word_value + words_to_nat_gen_u64(words, num_words - 1, bits_per_word)
    }
}

pub open spec fn words_to_nat_gen_u32(words: &[u32], num_words: int, bits_per_word: int) -> nat
decreases num_words
{
    if num_words <= 0 {
        0
    } else {
        let word_value = (words[num_words - 1] as nat) * pow2(((num_words - 1) * bits_per_word) as nat);
        word_value + words_to_nat_gen_u32(words, num_words - 1, bits_per_word)
    }
}

// natural value of a 256 bit bitstring represented as an array of 4 words of 64 bits
// Now implemented using the generic function
pub open spec fn words_to_nat(words: &[u64; 4]) -> nat {
    words_to_nat_gen_u64(words, 4, 64)
}

// Group order: the value of L as a natural number
pub open spec fn group_order() -> nat {
    pow2(252) + 27742317777372353535851937790883648493nat
}

// Montgomery radix R = 2^260
pub open spec fn montgomery_radix() -> nat {
    pow2(260)
}

} // verus!
