#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::mask_lemmas::*;
use super::pow_lemmas::*;
use super::shift_lemmas::*;

// Proofs that bitwise or with zero returns the other value
macro_rules! lemma_bitwise_or_zero_is_id {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for any `x` of type "]
        #[doc = stringify!($uN)]
        #[doc = ", both `x | 0` and `0 | x` equal x."]
        pub broadcast proof fn $name(x: $uN)
            ensures
                #![trigger x | 0, 0 | x]
                x | 0 == x,
                0 | x == x,
        {
            assert(x | 0 == x) by (bit_vector);
            assert(0 | x == x) by (bit_vector);
        }
    }
    };
}

lemma_bitwise_or_zero_is_id!(lemma_u8_bitwise_or_zero_is_id, u8);
lemma_bitwise_or_zero_is_id!(lemma_u16_bitwise_or_zero_is_id, u16);
lemma_bitwise_or_zero_is_id!(lemma_u32_bitwise_or_zero_is_id, u32);
lemma_bitwise_or_zero_is_id!(lemma_u64_bitwise_or_zero_is_id, u64);
lemma_bitwise_or_zero_is_id!(lemma_u128_bitwise_or_zero_is_id, u128);

// Proofs that bitwise disjunction for N-bit integers equals addition if for some `n` one factor
// only uses the top `N-n` bits, and the other the low `n` bits.
macro_rules! lemma_bit_or_is_plus {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for any `a`, `b` and `k` of type "]
        #[doc = stringify!($uN)]
        #[doc = ", `a | (b << k)` equals `a + (b << k)` if `a` is smaller than `2^k` and `b << k` does not overflow."]
        pub proof fn $name(a: $uN, b: $uN, k: $uN)
            by (bit_vector)
            requires
                k < <$uN>::BITS,
                a < (1 as $uN) << k,
                b <= (<$uN>::MAX >> k),
            ensures
                a | (b << k) == a + (b << k)
            {}
    }
    };
}

lemma_bit_or_is_plus!(lemma_u8_bit_or_is_plus, u8);
lemma_bit_or_is_plus!(lemma_u16_bit_or_is_plus, u16);
lemma_bit_or_is_plus!(lemma_u32_bit_or_is_plus, u32);
lemma_bit_or_is_plus!(lemma_u64_bit_or_is_plus, u64);
lemma_bit_or_is_plus!(lemma_u128_bit_or_is_plus, u128);

// Proofs that right-shifting and masking distribute over bitwise disjunction
macro_rules! lemma_distribute_over_bit_or {
    ($name:ident, $no_overflow:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for any `a`, `b` and `k` of type "]
        #[doc = stringify!($uN)]
        #[doc = ", `(a | b) >> c` equals `(a >> c) | (b >> c)` and `(a | b) & M` equals `(a & M) | (b & M)` for `M = low_bits_mask(c)`."]
        pub proof fn $name(a: $uN, b: $uN, c: $uN)
            requires
                c < <$uN>::BITS,
            ensures
                (a | b) >> c == (a >> c) | (b >> c),
                (a | b) & (low_bits_mask(c as nat) as $uN) ==
                (a & (low_bits_mask(c as nat) as $uN)) |
                (b & (low_bits_mask(c as nat) as $uN)),
            {
                assert(low_bits_mask(c as nat) <= $uN::MAX) by {
                    $no_overflow(c as nat);
                }
                assert((a | b) >> c == (a >> c) | (b >> c)) by (bit_vector);
                let lbm = (low_bits_mask(c as nat) as $uN);
                assert((a | b) & lbm == (a & lbm) | (b & lbm)) by (bit_vector);
            }
    }
    };
}

lemma_distribute_over_bit_or!(
    lemma_u8_distribute_over_bit_or,
    lemma_u8_low_bits_masks_fit,
    u8
);
lemma_distribute_over_bit_or!(
    lemma_u16_distribute_over_bit_or,
    lemma_u16_low_bits_masks_fit,
    u16
);
lemma_distribute_over_bit_or!(
    lemma_u32_distribute_over_bit_or,
    lemma_u32_low_bits_masks_fit,
    u32
);
lemma_distribute_over_bit_or!(
    lemma_u64_distribute_over_bit_or,
    lemma_u64_low_bits_masks_fit,
    u64
);
