#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::mul_lemmas::*;

verus! {

// Auxiliary lemma for exponentiation
pub proof fn pow2_le_max64(k: nat)
    requires
        k < 64,
    ensures
        pow2(k) <= u64::MAX
    {
        lemma2_to64();
        lemma2_to64_rest();
    }

// Rewriting lemma; 2^(a + b) * x = 2^a * (2^b * x)
// Parenthesis placement matters here
pub proof fn lemma_two_factoring(a : nat, b: nat, v: u64)
    ensures
        pow2(a + b) * v == pow2(a) * (pow2(b) * v)
{
    lemma_pow2_adds(a, b);
    lemma_mul_is_associative(pow2(a) as int, pow2(b) as int, v as int);
}

// (v^(2^k))^2 = v^(2^(k + 1))
pub proof fn lemma_pow2_square(v: int, i: nat)
    ensures
        pow(v, pow2(i)) * pow(v, pow2(i)) == pow(v, pow2(i + 1))
{
    // pow(v, pow2(i)) * pow(v, pow2(i)) = pow(v, pow2(i) + pow2(i));
    lemma_pow_adds(v as int, pow2(i), pow2(i));
    // 2 * pow2(i) = pow2(i + 1)
    lemma_pow2_unfold(i + 1);
}

// v^(2^i) >= 0
pub proof fn lemma_pow_nat_is_nat(v: nat, i: nat)
    ensures
        pow(v as int, pow2(i)) >= 0
{
    lemma_pow2_pos(i); // pow2(i) > 0
    if (v == 0) {
        lemma0_pow(pow2(i));
    }
    else {
        lemma_pow_positive(v as int, pow2(i));
    }
}

pub proof fn pow2_mul_u8(a: u8, k: nat)
    ensures
        pow2(k) * a <= pow2(k + 8) - pow2(k)
{
    assert(a <= pow2(8) - 1) by {
        lemma2_to64();
    }

    mul_le(a as nat, (pow2(8) - 1) as nat, pow2(k), pow2(k));
    assert((pow2(8) - 1) * pow2(k) == pow2(k + 8) - pow2(k)) by {
        lemma_mul_is_distributive_sub(pow2(k) as int, pow2(8) as int, 1);
        lemma_pow2_adds(k, 8);
    }

}

pub proof fn u8_times_pow2_fits_u64(a: u8, k: nat)
    requires
        k <= 56
    ensures
        (a as u64) * pow2(k) <= u64::MAX
{
    assert((a as u64) * pow2(k) <= (a as u64) * pow2(56)) by {
        assert(pow2(k) <= pow2(56)) by {
            if(k < 56) {
                lemma_pow2_strictly_increases(k, 56);
            }
        }
        mul_le(a as nat, a as nat, pow2(k), pow2(56));
    }

    pow2_mul_u8(a, 56);
    assert(pow2(64) - pow2(56) <= u64::MAX) by {
        lemma2_to64_rest();
    }

}

pub proof fn mask_pow2(x: nat, k: nat, s: nat)
    requires
        k < s < 64
    ensures
        (x * pow2(k)) % pow2(s) == (x % pow2((s - k) as nat)) * pow2(k)
{
    let d = (s - k) as nat;

    assert(pow2(s) == pow2(k) * pow2(d)) by {
        lemma_pow2_adds(k, d);
    }

    assert(pow2(k) * pow2(d) > 0) by {
        lemma_pow2_pos(s);
    }

    assert((pow2(k) * x) % (pow2(k) * pow2(d)) == pow2(k) * (x % pow2(d))) by {
        lemma_truncate_middle(x as int, pow2(k) as int, pow2(d) as int);
    }

}

fn main() {}

}
