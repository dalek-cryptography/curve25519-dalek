#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::seq::*;

use super::mul_lemmas::*;
use super::sum_lemmas::*;

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

pub proof fn pow2_mul_general(a: nat, s: nat, k: nat)
    requires
        a < pow2(s)
    ensures
        pow2(k) * a <= pow2(k + s) - pow2(k),
        a * pow2(k) <= pow2(k + s) - pow2(k)
{
    assert(a <= pow2(s) - 1); // x < y <=> x <= y - 1

    mul_le(a as nat, (pow2(s) - 1) as nat, pow2(k), pow2(k));
    assert((pow2(s) - 1) * pow2(k) == pow2(k + s) - pow2(k)) by {
        lemma_mul_is_distributive_sub(pow2(k) as int, pow2(s) as int, 1);
        lemma_pow2_adds(k, s);
    }

    lemma_mul_is_commutative(a as int, pow2(k) as int);
}

pub proof fn pow2_mul_u8(a: u8, k: nat)
    ensures
        pow2(k) * a <= pow2(k + 8) - pow2(k)
{
    assert(a < pow2(8)) by {
        lemma2_to64();
    }

    pow2_mul_general(a as nat, 8, k);
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

pub proof fn div_pow2_preserves_decomposition(a: u64, b: u64, s: nat, k: nat)
    requires
        a < pow2(s),
        a + b * pow2(s) <= u64::MAX,
        k <= s < 64
    ensures
        (a as nat) / pow2(k) < pow2((s - k) as nat),
        (b * pow2(s)) as nat / pow2(k) == b * pow2((s - k) as nat),
        (a as nat) / pow2(k) + b * pow2((s - k) as nat) <= u64::MAX
{
    let d = (s - k) as nat;

    assert(pow2(k) > 0) by {
        lemma_pow2_pos(k);
    }

    assert(pow2(s) == pow2(d) * pow2(k)) by {
        lemma_pow2_adds(d, k);
    }

    assert( a as nat / pow2(k) < pow2(d) ) by {
        assert( a as nat / pow2(k) < pow2(s) / pow2(k) ) by {
            lemma_div_by_multiple_is_strongly_ordered( a as int, pow2(s) as int, pow2(d) as int, pow2(k) as int);
        }
        assert( pow2(s) / pow2(k) == pow2(d) ) by {
            lemma_div_by_multiple(pow2(d) as int, pow2(k) as int);
        }
    }

    assert((b * pow2(s)) as nat / pow2(k) == b * pow2(d)) by {
        assert(b * pow2(s) == (b * pow2(d)) * pow2(k)) by {
            lemma_mul_is_associative(b as int, pow2(d) as int, pow2(k) as int);
        }
        assert( ((b * pow2(d)) * pow2(k)) as nat / pow2(k) == b * pow2(d) ) by {
            lemma_div_by_multiple(b * pow2(d), pow2(k) as int);
        }
    }
}

pub open spec fn pow2_sum(coefs: Seq<nat>, offset: nat, step: nat, k: nat) -> nat
    decreases k
{
    if (k == 0) {
        coefs[offset as int] * pow2(0)
    }
    else {
        // k > 0
        pow2_sum(coefs, offset, step, (k - 1) as nat) + coefs[(offset + k) as int] * pow2(k * step)
    }
}

pub proof fn pow2_sum_bounds(coefs: Seq<nat>, offset: nat, step: nat, k: nat)
    requires
        offset + k <= coefs.len(),
        forall |i: nat| 0 <= i <= k ==> #[trigger] coefs[(offset + i) as int] < pow2(step)
    ensures
        pow2_sum(coefs, offset, step, k) < pow2((k + 1) * step)
    decreases k
{
    if (k == 0){
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(coefs[offset as int] * pow2(0) == coefs[offset as int]) by {
            lemma_mul_basics_3(coefs[offset as int] as int);
        }
    }
    else {
        assert(
            pow2_sum(coefs, offset, step, k)
            ==
            pow2_sum(coefs, offset, step, (k - 1) as nat) + coefs[(offset + k) as int] * pow2(k * step)
        ) by {
            reveal_with_fuel(pow2_sum, 1);
        }

        assert(pow2_sum(coefs, offset, step, (k - 1) as nat) < pow2(k * step)) by {
            pow2_sum_bounds(coefs, offset, step, (k-1) as nat);
        }

        assert(coefs[(offset + k) as int] * pow2(k * step) <= pow2((k + 1) * step) - pow2(k * step)) by {
            assert((k + 1) * step == k * step + step) by {
                lemma_mul_is_distributive_add_other_way(step as int, k as int, 1);
            }
            assert(coefs[(offset + k) as int] * pow2(k * step) <= pow2(k * step + step) - pow2(k * step)) by {
                pow2_mul_general(coefs[(offset + k) as int], step, k * step);
            }
        }
    }
}


fn main() {}

}
