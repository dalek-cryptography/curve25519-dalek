#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::shift_lemmas::*;

verus! {

// Because &-ing low_bits_mask(k) is a mod operation, it follows that
// v & (low_bits_mask(k) as u64) = v % pow2(k) < pow2(k)
pub proof fn lemma_masked_lt(v: u64, k: nat)
    requires
        0 <= k < 64,
    ensures
        v & (low_bits_mask(k) as u64) < (1u64 << k),
{
    // v & (low_bits_mask(k) as u64) = v % pow2(k)
    lemma_u64_low_bits_mask_is_mod(v, k);
    // pow2(k) > 0
    lemma_pow2_pos(k);
    // v % pow2(k) < pow2(k)
    lemma_mod_bound(v as int, pow2(k) as int);
    // 1 << k = pow2(k)
    lemma_shift_is_pow2(k);
}

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

// k <= 64 => 2^k - 1 <= u64::MAX = 2^64 - 1
pub proof fn lemma_low_bits_masks_fit_u64(k: nat)
    requires
        k <= 64,
    ensures
        low_bits_mask(k) <= u64::MAX,
{
    lemma_low_bits_mask_values();  // lbm(0) = 0, lbm(64) = 2^64
    assert(low_bits_mask(64) <= u64::MAX) by (compute);
    if (k < 64) {
        lemma_low_bits_mask_increases(k, 64);
    }
}

fn main() {
}

} // verus!
