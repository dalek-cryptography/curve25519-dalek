#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mask_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

// Specialization for b = 51
pub proof fn lemma_two_factoring_51(k: nat, ai: u64)
    ensures
        pow2(k + 51) * ai == pow2(k) * (pow2(51) * ai),
{
    lemma_two_factoring(k, 51, ai);
}

pub proof fn lemma_add_then_shift(a: u64, b: u64)
    requires
        a < (1u64 << 52),
        b < (1u64 << 52),
    ensures
        (a + b) < (1u64 << 53),
        ((a + b) as u64 >> 51) < 4,
{
    lemma2_to64_rest();
    assert((a + b) < 1u64 << 53) by {
        assert((1u64 << 52) + (1u64 << 52) == 1u64 << 53) by (compute);
    }
    assert(1u64 << 53 == (1u64 << 51) * 4) by (bit_vector);
    // 0 < b  /\ a < b * c => a/b < c
    lemma_multiply_divide_lt((a + b) as int, (1u64 << 51) as int, 4int);
    lemma_shift_is_pow2(51);
    lemma_shift_is_pow2(53);
    assert((a + b) as u64 >> 51 == (a + b) as u64 / (pow2(51) as u64)) by {
        lemma_u64_shr_is_div((a + b) as u64, 51);
    }
    assert(pow2(53) / pow2(51) == 4) by {
        lemma_pow2_subtracts(51, 53);
    }
}

// >> preserves [<=]. Unfortunately, these operations are u128 and
// we need lemma_u128_shr_is_div.
pub proof fn lemma_shr_51_le(a: u128, b: u128)
    requires
        a <= b,
    ensures
        (a >> 51) <= (b >> 51),
{
    lemma_pow2_pos(51);
    lemma2_to64_rest();  // pow2(51) value
    lemma_u128_shr_is_div(a, 51);
    lemma_u128_shr_is_div(b, 51);
    lemma_div_is_ordered(a as int, b as int, 51);
}

// Corollary of above, using the identity (a << x) >> x == a for u64::MAX
pub proof fn lemma_shr_51_fits_u64(a: u128)
    requires
        a <= (u64::MAX as u128) << 51,
    ensures
        (a >> 51) <= (u64::MAX as u128),
{
    assert(((u64::MAX as u128) << 51) >> 51 == (u64::MAX as u128)) by (compute);
    lemma_shr_51_le(a, (u64::MAX as u128) << 51);
}

// Auxiliary datatype lemma
// Should work for any k <= 64, but the proofs are convoluted and we can't use BV
// (x as u64) = x % 2^64, so x = 2^64 * (x / 2^64) + (x as u64). Thus
// (x as u64) % 2^k = (x as u64) % 2^k, because 2^k | 2^64 * (...) for k <= 64
pub proof fn lemma_cast_then_mod_51(x: u128)
    ensures
        (x as u64) % (pow2(51) as u64) == x % (pow2(51) as u128),
{
    lemma2_to64_rest();  // pow2(51 | 64)
    assert((x as u64) % 0x8000000000000 == x % 0x8000000000000) by (bit_vector);
}

pub proof fn lemma_mul_sub(ci: int, cj: int, cj_0: int, k: nat)
    ensures
        pow2(k) * (ci - pow2(51) * (cj - cj_0)) == pow2(k) * ci - pow2(k + 51) * cj + pow2(k + 51)
            * cj_0,
{
    // 2^k (ci - X) = 2^k ci - 2^k X
    lemma_mul_is_distributive_sub(pow2(k) as int, ci, pow2(51) * (cj - cj_0));
    // 2^k (2^51 * Y) = (2^k * 2^51) * Y
    lemma_mul_is_associative(pow2(k) as int, pow2(51) as int, cj - cj_0);
    // 2^k * 2^51 = 2^(k + 51)
    lemma_pow2_adds(k, 51);
    // 2^(k + 51) * (cj - cj_0) = 2^(k + 51) * cj - 2^(k + 51) * cj_0
    lemma_mul_is_distributive_sub(pow2(k + 51) as int, cj, cj_0);
}

// Masking with low_bits_mask(51) gives a value bounded by 2^51
pub proof fn lemma_masked_lt_51(v: u64)
    ensures
        v & mask51 < (1u64 << 51),
{
    l51_bit_mask_lt();  // mask51 == low_bits_mask(51)
    lemma_masked_lt(v, 51);
}

// lemma_div_and_mod specialization for k = 51, using mask51 == low_bits_mask(51)
pub proof fn lemma_div_and_mod_51(ai: u64, bi: u64, v: u64)
    requires
        ai == v >> 51,
        bi == v & mask51,
    ensures
        ai == v / (pow2(51) as u64),
        bi == v % (pow2(51) as u64),
        v == ai * pow2(51) + bi,
{
    l51_bit_mask_lt();  // mask51 == low_bits_mask(51)
    lemma_div_and_mod(ai, bi, v, 51);
}

pub broadcast proof fn lemma_cast_then_mask_51(x: u128)
    ensures
        #![trigger (x as u64) & mask51]
        (x as u64) & mask51 == x & (mask51 as u128),
{
    assert((x as u64) & 2251799813685247u64 == x & (2251799813685247u64 as u128)) by (bit_vector);
}

} // verus!
