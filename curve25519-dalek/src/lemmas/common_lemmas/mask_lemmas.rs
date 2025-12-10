#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::pow_lemmas::*;
use super::shift_lemmas::*;

// Proofs of when masking a value fits into the number of bits used by the mask.
macro_rules! lemma_masked_lt {
    ($name:ident, $mask_is_mod: ident, $no_overflow: ident, $shl_is_mul: ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(v: $uN, k: nat)
            requires
                k < <$uN>::BITS,
            ensures
                v & (low_bits_mask(k) as $uN) < (1 as $uN << k)
        {
            assert(pow2(k) <= <$uN>::MAX) by {
                $no_overflow(k);
            }
            assert(v & (low_bits_mask(k) as $uN) == v % (pow2(k) as $uN)) by {
                $mask_is_mod(v, k);
            }
            // pow2(k) > 0
            lemma_pow2_pos(k);
            // v % pow2(k) < pow2(k)
            lemma_mod_bound(v as int, pow2(k) as int);
            assert((1 as $uN << k) == pow2(k)) by {
                $shl_is_mul(1 as $uN, k as $uN);
            }
        }
    }
    };
}

lemma_masked_lt!(
    lemma_u8_masked_lt,
    lemma_u8_low_bits_mask_is_mod,
    lemma_u8_pow2_le_max,
    lemma_u8_shl_is_mul,
    u8
);
lemma_masked_lt!(
    lemma_u16_masked_lt,
    lemma_u16_low_bits_mask_is_mod,
    lemma_u16_pow2_le_max,
    lemma_u16_shl_is_mul,
    u16
);
lemma_masked_lt!(
    lemma_u32_masked_lt,
    lemma_u32_low_bits_mask_is_mod,
    lemma_u32_pow2_le_max,
    lemma_u32_shl_is_mul,
    u32
);
lemma_masked_lt!(
    lemma_u64_masked_lt,
    lemma_u64_low_bits_mask_is_mod,
    lemma_u64_pow2_le_max,
    lemma_u64_shl_is_mul,
    u64
);
// TODO: missing VSTD lemmas for u128
// lemma_masked_lt!(lemma_u128_masked_lt, lemma_u128_low_bits_mask_is_mod, lemma_u128_pow2_le_max, lemma_u128_shl_is_mul, u128);

// Proofs of when k <= N => 2^k - 1 <= uN::MAX = 2^N - 1
macro_rules! lemma_low_bits_masks_fit {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(k: nat)
            requires
                k <= <$uN>::BITS,
            ensures
                low_bits_mask(k) <= <$uN>::MAX,
        {
            lemma_low_bits_mask_values();  // lbm(0) = 0 ... lbm(64) = 2^64
            assert(low_bits_mask(<$uN>::BITS as nat) <= <$uN>::MAX) by (compute);
            if (k < <$uN>::BITS) {
                lemma_low_bits_mask_increases(k, <$uN>::BITS as nat);
            }
        }
    }
    };
}

lemma_low_bits_masks_fit!(lemma_u8_low_bits_masks_fit, u8);
lemma_low_bits_masks_fit!(lemma_u16_low_bits_masks_fit, u16);
lemma_low_bits_masks_fit!(lemma_u32_low_bits_masks_fit, u32);
lemma_low_bits_masks_fit!(lemma_u64_low_bits_masks_fit, u64);
// TODO
// lemma_low_bits_masks_fit!(lemma_u128_low_bits_masks_fit, u128);

verus! {

// a < b => (2^a - 1) < (2^b - 1)
pub proof fn lemma_low_bits_mask_increases(a: nat, b: nat)
    requires
        a < b,
    ensures
        low_bits_mask(a) < low_bits_mask(b),
    decreases a + b,
{
    if (a == 0) {
        // lbm(0) = 0
        lemma_low_bits_mask_values();
        // lbm(b) = 2 * lbm(b - 1) + 1, in particular, > 0
        lemma_low_bits_mask_unfold(b);
    } else {
        // lbm(b) / 2 = lbm(b - 1)
        lemma_low_bits_mask_div2(b);
        // lbm(a) / 2 = lbm(a - 1)
        lemma_low_bits_mask_div2(a);
        // lbm(a - 1) < lbm(b - 1)
        lemma_low_bits_mask_increases((a - 1) as nat, (b - 1) as nat);
    }

}

} // verus!
