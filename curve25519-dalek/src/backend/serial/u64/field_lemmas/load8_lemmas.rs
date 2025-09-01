#![allow(unused)]
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::calc;
use vstd::prelude::*;

use super::super::common_verus::bit_lemmas::*;
use super::super::common_verus::mul_lemmas::*;
use super::super::common_verus::pow_lemmas::*;
use super::super::common_verus::shift_lemmas::*;

use super::field_core::*;

verus! {


pub proof fn bit_or_is_plus(a: u64, b: u8, k: u64)
    requires
        k + 8 <= 64,
        a < 1u64 << k
    ensures
        a | ((b as u64) << (k as u64)) == a + ((b as u64) << (k as u64)),
        a + ((b as u64) << (k as u64)) <= u64::MAX
{
    assert(a | ((b as u64) << (k as u64)) == a + ((b as u64) << (k as u64))) by (bit_vector)
        requires
            k + 8 <= 64,
            a < 1u64 << k;
}

pub open spec fn load8_at_or_version_rec(input: &[u8], i: usize, k: nat) -> u64
    decreases k
{
    if (k == 0) {
        (input[i as int] as u64)
    }
    else {
        // k > 0
        load8_at_or_version_rec(input, i, (k - 1) as nat) | ((input[i + k] as u64) << k * 8)
    }
}

pub proof fn rec_version_is_exec(input: &[u8], i: usize)
    ensures
        load8_at_or_version_rec(input, i, 7)
        ==
        (input[i as int] as u64)
        | ((input[i + 1] as u64) << 8)
        | ((input[i + 2] as u64) << 16)
        | ((input[i + 3] as u64) << 24)
        | ((input[i + 4] as u64) << 32)
        | ((input[i + 5] as u64) << 40)
        | ((input[i + 6] as u64) << 48)
        | ((input[i + 7] as u64) << 56)
{
    assert(load8_at_or_version_rec(input, i, 0) == (input[i as int] as u64));

    assert forall |j: nat| 1 <= j <= 7 implies
        #[trigger] load8_at_or_version_rec(input, i, j) ==
        load8_at_or_version_rec(input, i, (j - 1) as nat)
        | ((input[i + j] as u64) << 8 * j)
    by {
        reveal_with_fuel(load8_at_or_version_rec, 1);
    }
}

pub open spec fn load8_at_plus_version_rec(input: &[u8], i: usize, k: nat) -> u64
    decreases k
{
    if (k == 0) {
        (input[i as int] as u64)
    }
    else {
        // k > 0
        (load8_at_plus_version_rec(input, i, (k - 1) as nat) + ((input[i + k] as u64) << k * 8)) as u64
    }
}

pub proof fn load8_at_plus_version_rec_is_bounded(input: &[u8], i: usize, k: nat)
    requires
        k <= 7
    ensures
        load8_at_plus_version_rec(input, i, k) < pow2(8 * (k + 1))
    decreases k
{

    assert(u8::MAX < pow2(8)) by {
        lemma2_to64();
    }

    if (k == 0) {
        // just needs the the pre-if assert
    }
    else {
        // k > 0
        // Let f(k) := load8_at_plus_version_rec(input, i, k)
        // IH: f(k - 1) < pow2(8 * k)
        assert(load8_at_plus_version_rec(input, i, (k - 1) as nat) < pow2(8 * k)) by {
            load8_at_plus_version_rec_is_bounded(input, i, (k - 1) as nat);
        }

        let c = (input[i + k] as u64);
        assert(c < pow2(8));

        // f(k) = f(k - 1) + c * pow2(8 * k)
        assert(c << (8 * k) == c * pow2(8 * k)) by {
            assert((input[i + k] as u64) * pow2(8 * k) <= u64::MAX) by {
                assert(u64::MAX == pow2(64) - 1) by {
                    lemma2_to64_rest();
                }
                assert(c * pow2(8 * k) < pow2(64)) by {
                    assert(c * pow2(8 * k) < pow2(8) * pow2(8 * k)) by {
                        lemma_mul_strict_inequality(
                            c as int,
                            pow2(8) as int,
                            pow2(8 * k) as int
                        );
                    }
                    assert(pow2(8) * pow2(8 * k) <= pow2(64)) by {
                        assert(pow2(8 * k) <= pow2(56)) by {
                            if (k < 7) {
                                lemma_pow2_strictly_increases(8 * k, 56);
                            }
                        }
                        lemma_pow2_pos(8);
                        lemma_mul_inequality(
                            pow2(8 * k) as int,
                            pow2(56) as int,
                            pow2(8) as int
                        );
                        lemma_pow2_adds(8, 56);
                    }
                }
            }
            lemma_u64_shl_is_mul(c, (8 * k) as u64);
        }

        // f(k - 1) < 1 * 2^(8k)
        // c <= 2^8 - 1
        // f(k -1) + c * 2^8k < 2^8 * 2^8k = 2^(8 * (k + 1))

        assert(load8_at_plus_version_rec(input, i, k) < pow2(8 * k) + c * pow2(8 * k));

        assert(pow2(8 * k) + c * pow2(8 * k) <= pow2(8 * (k +1))) by {
            // x + c * x == c ( x + 1 )
            assert( pow2(8 * k) + c * pow2(8 * k) == pow2(8 *k) * (c + 1) ) by {
                lemma_mul_is_distributive_add( pow2(8 * k) as int, c as int, 1 );
            }
            assert(c + 1 <= pow2(8));

            assert(pow2(8 * k) * (c + 1) <= pow2(8 * (k + 1))) by {
                lemma_mul_inequality(
                    (c + 1) as int,
                    pow2(8) as int,
                    pow2(8 * k) as int
                );
                lemma_pow2_adds(8, 8 * k);
                lemma_mul_is_distributive_add(8, 1, k as int);
            }
        }
    }
}


pub proof fn plus_version_is_spec_lemma(input: &[u8], i: usize, j: nat)
    requires
        1 <= j <= 7
    ensures
        (input[i + j] as u64) << 8 * j == pow2(j * 8) * input[i + j],
        input[i + j] * pow2(j * 8) <= u64::MAX,
        pow2(8 * (j + 1)) - 1 <= pow2(64) - 1,
        pow2(8) * pow2(8 * j) == pow2(8 * (j + 1))
{
    assert(pow2(64) - 1 == u64::MAX) by {
        lemma2_to64_rest();
    }

    assert(u8::MAX + 1 == pow2(8)) by {
        lemma2_to64();
    }

    assert(pow2(8 * (j + 1)) - 1 <= pow2(64) - 1) by {
        if (j < 7){
            lemma_pow2_strictly_increases(8 * (j + 1), 64);
        }
    }

    lemma_pow2_adds(8, j * 8);

    lemma_mul_inequality(input[i + j] as int, u8::MAX as int, pow2(j * 8) as int);

    assert((input[i + j] as u64) * pow2(j * 8) <= u64::MAX) by {
        assert(u8::MAX * pow2(j * 8) <= pow2(64) - 1) by {
            assert(
                u8::MAX * pow2(j * 8)
                ==
                (pow2(8) - 1) * pow2(j * 8)
                ==
                pow2(8 * (j + 1)) - pow2(j * 8)
            ) by {
                assert(pow2(8) >= 1) by {
                    lemma2_to64();
                }
                lemma_mul_is_distributive_sub(pow2(8) as int, 1, pow2(j * 8) as int);
            }
            assert(pow2(j * 8) > 1) by {
                lemma2_to64(); // pow2(0)
                lemma_pow2_strictly_increases(0, j * 8)
            }
        }
    }
    lemma_u64_shl_is_mul((input[i + j] as u64), (j * 8) as u64);
}

pub proof fn plus_version_is_spec(input: &[u8], i: usize)
    ensures
        load8_at_plus_version_rec(input, i, 7)
        ==
        load8_at_spec(input, i)
{
    assert(load8_at_plus_version_rec(input, i, 0) == input[i as int] as u64);

    assert(pow2(64) - 1 == u64::MAX) by {
        lemma2_to64_rest();
    }

    assert(u8::MAX + 1 == pow2(8)) by {
        lemma2_to64();
    }

    assert((input[i as int] as u64) == pow2(0 * 8) * input[i + 0]) by {
            lemma2_to64();
        }
    plus_version_is_spec_lemma(input, i, 1);
    plus_version_is_spec_lemma(input, i, 2);
    plus_version_is_spec_lemma(input, i, 3);
    plus_version_is_spec_lemma(input, i, 4);
    plus_version_is_spec_lemma(input, i, 5);
    plus_version_is_spec_lemma(input, i, 6);
    plus_version_is_spec_lemma(input, i, 7);

    // suffices to prove this, the _lemma results then give the spec formulation for free
    assert(
        load8_at_plus_version_rec(input, i, 7)
        ==
         (input[i as int] as u64)
        + ((input[i + 1] as u64) << 8)
        + ((input[i + 2] as u64) << 16)
        + ((input[i + 3] as u64) << 24)
        + ((input[i + 4] as u64) << 32)
        + ((input[i + 5] as u64) << 40)
        + ((input[i + 6] as u64) << 48)
        + ((input[i + 7] as u64) << 56)
    ) by {
        assert forall |j: nat| 1 <= j <= 7 implies
        #[trigger] load8_at_plus_version_rec(input, i, j)
        ==
        load8_at_plus_version_rec(input, i, (j - 1) as nat) + ((input[i + j] as u64) << j * 8)
        by {
            reveal_with_fuel(load8_at_plus_version_rec, 1);

            assert(load8_at_plus_version_rec(input, i, (j - 1) as nat) + ((input[i + j] as u64) << j * 8) <= u64::MAX) by {
                assert(load8_at_plus_version_rec(input, i, (j - 1) as nat) <= pow2(8 * j) - 1 ) by {
                    load8_at_plus_version_rec_is_bounded(input, i, (j - 1) as nat);
                }

                assert((input[i + j] as u64) << j * 8 <= u8::MAX * pow2(j * 8) ) by {
                    // input[k] < MAX8 => input[k] * 2^(8j) < MAX8 * 2^(8j)
                    lemma_mul_inequality(input[i + j] as int, u8::MAX as int, pow2(j * 8) as int);
                }

                assert(
                    load8_at_plus_version_rec(input, i, (j - 1) as nat) + ((input[i + j] as u64) << j * 8)
                    <=
                    pow2(8 * (j + 1)) - 1
                ) by {
                    lemma_mul_is_distributive_add(1, u8::MAX as int, pow2(j * 8) as int);
                }
            }

        }
    }
}

pub proof fn load8_at_versions_equivalent(input: &[u8], i: usize, k: nat)
    requires
        k <= 7
    ensures
        load8_at_or_version_rec(input, i, k) == load8_at_plus_version_rec(input, i, k)
    decreases k
{
    if (k == 0){
        // trivial
    }
    else {
        load8_at_versions_equivalent(input, i, (k - 1) as nat);
        let prev = load8_at_plus_version_rec(input, i, (k - 1) as nat);
        assert(prev < (1u64 << 8 * k)) by {
            load8_at_plus_version_rec_is_bounded(input, i, (k - 1) as nat);
            shift_is_pow2(8 * k);
        }
        bit_or_is_plus(prev, input[i + k], (8 * k) as u64);
    }
}

pub proof fn load8_at_spec_fits_u64(input: &[u8], i: usize)
    requires
        i + 7 < input.len()
    ensures
        load8_at_spec(input, i) <= u64::MAX
{
    lemma2_to64();
    lemma2_to64_rest();

    assert forall |j: nat| 0 <= j < 8 implies #[trigger] pow2(j * 8) * input[i + j] <= pow2((j + 1) * 8) - pow2(j * 8) by {
        // sanity check, holds for all u8
        assert(input[i + j] <= pow2(8) - 1);
        mul_le(pow2(j * 8), pow2(j * 8), input[i + j] as nat, (pow2(8) - 1) as nat);
        assert(pow2(j * 8) * (pow2(8) - 1) == pow2((j + 1) * 8) - pow2(j * 8)) by {
            lemma_mul_is_distributive_sub(pow2(j * 8) as int, pow2(8) as int, 1);
            lemma_pow2_adds(j * 8, 8);
        }

    }
}


pub proof fn load8_rshift3(input: &[u8], i: usize)
    requires
        i + 7 < input.len()
    ensures
        true
{
  assert(true);
}

fn main() {}

}
