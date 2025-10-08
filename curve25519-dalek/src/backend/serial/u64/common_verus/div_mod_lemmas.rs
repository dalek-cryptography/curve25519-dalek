#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

pub proof fn lemma_div_and_mod(ai:u64, bi: u64, v: u64, k: nat)
    requires
        k < 64,
        ai == v >> k,
        bi == v & (low_bits_mask(k) as u64)
    ensures
        ai == v / (pow2(k) as u64),
        bi == v % (pow2(k) as u64),
        v == ai * pow2(k) + bi
{
    lemma2_to64();
    lemma2_to64_rest(); // pow2(63) = 0x8000000000000000

    // v >> k = v / pow2(k);
    lemma_u64_shr_is_div(v, k as u64);

    // v & low_bits_mask(k) = v % pow2(k);
    lemma_u64_low_bits_mask_is_mod(v, k);

    // 0 < pow2(k) <= u64::MAX
    lemma_pow2_pos(k);
    assert(pow2(k) <= u64::MAX) by {
        assert(0x8000000000000000 <= u64::MAX) by (compute);
        if (k < 63) {
            lemma_pow2_strictly_increases(k, 63);
        }
    }

    // v = (pow2(k) * (v / pow2(k)) + (v % pow2(k)))
    lemma_fundamental_div_mod(v as int, pow2(k) as int);
}

// Combination of mod lemmas, (b +- a * m) % m = b % m
pub proof fn lemma_mod_sum_factor(a: int, b: int, m: int)
    requires
        m > 0
    ensures
        (a * m + b) % m == b % m
{
    // (a * m + b) % m == ((a * m) % m + b % m) % m
    lemma_add_mod_noop(a * m, b, m);
    // (a * m) % m == 0
    lemma_mod_multiples_basic(a, m);
    // b % m % m = b % m
    lemma_mod_twice(b, m);
}

pub proof fn lemma_mod_diff_factor(a: int, b: int, m: int)
    requires
        m > 0,
    ensures
        (b - a * m) % m == b % m
{
    // (b - a * m) % m == (b % m - (a * m) % m) % m
    lemma_sub_mod_noop(b, a * m, m);
    // (a * m) % m == 0
    lemma_mod_multiples_basic(a, m);
    // b % m % m = b % m
    lemma_mod_twice(b, m);
}

pub proof fn lemma_div_of_sum(a: nat, b: nat, k: nat)
    requires
        (a % k) + (b % k) < k // also implies k != 0
    ensures
        (a + b) / k == a / k + b / k
{
    let a0 = a / k;
    let b0 = b / k;

    assert(a == k * a0 + (a % k)) by {
        lemma_fundamental_div_mod(a as int, k as int);
    }

    assert(b == k * b0 + (b % k)) by {
        lemma_fundamental_div_mod(b as int, k as int);
    }

    assert(a + b == k * (a0 + b0) + (a % k) + (b % k)) by {
        lemma_mul_is_distributive_add(k as int, a0 as int, b0 as int);
    }

    lemma_div_multiples_vanish_fancy((a0 + b0) as int, ((a % k) + (b % k)) as int, k as int);
}

fn main() {}

}
