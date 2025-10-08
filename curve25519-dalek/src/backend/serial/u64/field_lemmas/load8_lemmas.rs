#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::calc;
use vstd::prelude::*;

use super::super::common_verus::bit_lemmas::*;
use super::super::common_verus::div_mod_lemmas::*;
use super::super::common_verus::mul_lemmas::*;
use super::super::common_verus::pow_lemmas::*;
use super::super::common_verus::shift_lemmas::*;

use super::field_core::*;

verus! {


pub proof fn bit_or_is_plus(a: u64, b: u64, k: u64)
    by (bit_vector)
    requires
        b <= (u64::MAX >> k),
        a < 1u64 << k,

    ensures
        a | (b << k) == a + (b << k)
{
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
        let v = input[i + k];
        assert(v <= (u64::MAX >> ((k * 8) as u64))) by {
            assert(v <= u8::MAX);
            assert(u64::MAX >> ((k * 8) as u64) >= u64::MAX >> 56) by {
                shr_nonincreasing(u64::MAX, k * 8, 56);
            }
            assert(u8::MAX <= u64::MAX >> 56) by (compute);
        }
        bit_or_is_plus(prev, input[i + k] as u64, (8 * k) as u64);
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

pub proof fn load8_lemma_base(a: nat, b: u8, j: nat, k: nat)
    requires
        a < pow2(j),
        j + 8 <= 64
    ensures
        a + (b * pow2(j)) == pow2(k) * (a / pow2(k) + (b * pow2(j)) as nat / pow2(k)) + (a % pow2(k) + (b * pow2(j)) as nat % pow2(k)),
        pow2(k) > 0,
{
    let cb = (b * pow2(j)) as nat;

    // No div by 0
    assert(pow2(k) > 0) by {
        lemma_pow2_pos(k);
    }

    assert( a == pow2(k) * (a / pow2(k)) + a % pow2(k)) by {
        lemma_fundamental_div_mod(a as int, pow2(k) as int);
    }

    assert( cb == pow2(k) * (cb / pow2(k)) + cb % pow2(k)) by {
        lemma_fundamental_div_mod(cb as int, pow2(k) as int);
    }

    assert(a + cb == pow2(k) * (a / pow2(k) + cb / pow2(k)) + (a % pow2(k) + cb % pow2(k))) by {
        lemma_mul_is_distributive_add( pow2(k) as int, (a / pow2(k)) as int, (cb / pow2(k)) as int);
        lemma_mul_is_associative(
            (pow2(k) * (a / pow2(k) + cb / pow2(k))) as int,
            (a % pow2(k)) as int,
            (cb % pow2(k)) as int
        );
    }

}

pub proof fn load8_lemma1(a: nat, b: u8, j: nat, k: nat)
    requires
        a < pow2(j),
        j + 8 <= 64,
        k <= j
    ensures
        (a + b * pow2(j)) as nat / pow2(k)
        ==
        a / pow2(k) + (b * pow2(j)) as nat / pow2(k)

{
    let cb = (b * pow2(j)) as nat;

    load8_lemma_base(a, b, j, k);

    assert(cb % pow2(k) == 0) by {
            lemma_pow2_adds((j - k) as nat, k);
            lemma_mul_is_associative(b as int, pow2((j - k) as nat) as int, pow2(k) as int);
            lemma_mod_multiples_basic(b * pow2((j - k) as nat), pow2(k) as int);
        }

    assert((a % pow2(k) + cb % pow2(k)) < pow2(k)) by {
        lemma_mod_division_less_than_divisor(a as int, pow2(k) as int);
    }

    lemma_div_multiples_vanish_fancy(
        (a / pow2(k) + cb / pow2(k)) as int,
        (a % pow2(k) + cb % pow2(k)) as int,
        pow2(k) as int
    );
}

pub proof fn load8_lemma2(a: nat, b: u8, j: nat, k: nat)
    requires
        a < pow2(j),
        j + 8 <= 64,
        j < k < 64
    ensures
        (a + b * pow2(j)) as nat / pow2(k)
        ==
        (b * pow2(j)) as nat / pow2(k)
        ==
        b as nat / pow2((k - j) as nat)

{
    let cb = (b * pow2(j)) as nat;

    // a + cb == pow2(k) * (a / pow2(k) + cb / pow2(k)) + (a % pow2(k) + cb % pow2(k)),
    load8_lemma_base(a, b, j, k);

    let d = (k - j) as nat;

    // 2^k = 2^j * 2^(k - j)
    lemma_pow2_adds(j, d);
    // 2^x > 0
    lemma_pow2_pos(j);
    lemma_pow2_pos(d);

    assert(
        (a + b * pow2(j)) as nat / pow2(k)
        ==
        ((a + b * pow2(j)) as nat / pow2(j)) / pow2(d)
    ) by {
        lemma_div_denominator((a + cb) as int, pow2(j) as int, pow2(d) as int );
    }

    assert((b * pow2(j)) as nat / pow2(j) == b) by {
        lemma_div_multiples_vanish(b as int, pow2(j) as int);
    }

    assert((a + b * pow2(j)) as nat / pow2(j) == b) by {
        // == a / pow2(j) + (b * pow2(j)) as nat / pow2(j)
        load8_lemma1(a, b, j, j);
        assert( a / pow2(j) == 0 ) by {
            lemma_basic_div(a as int, pow2(j) as int);
        }
    }

    assert(cb / pow2(k) == b as nat / pow2(d)) by {
        lemma_div_denominator(cb as int, pow2(j) as int, pow2(d) as int )
    }
}

pub proof fn load8_lemma(a: nat, b: u8, j: nat, k: nat)
    requires
        a < pow2(j),
        j + 8 <= 64,
        k < 64
    ensures
        (a + b * pow2(j)) as nat / pow2(k)
        ==
        a / pow2(k) + (b * pow2(j)) as nat / pow2(k)
{
    if ( k <= j) {
        load8_lemma1(a, b, j, k);
    }
    else {
        // j < k
        load8_lemma2(a, b, j, k);

        assert(a / pow2(k) == 0) by {
            lemma_pow2_strictly_increases(j, k);
            lemma_basic_div(a as int, pow2(k) as int);
        }
    }
}

pub proof fn load8_plus_ver_shifted(input: &[u8], i: usize, k: nat, s64: u64)
    requires
        i + 7 < input.len(),
        0 < k <= 7,
        s64 < 64
    ensures
        load8_at_plus_version_rec(input, i, k) >> s64
        ==
        load8_at_plus_version_rec(input, i, (k - 1) as nat) / (pow2(s64 as nat) as u64) +
        (pow2(k * 8) * input[i + k]) as u64 / (pow2(s64 as nat) as u64)
    decreases k
{

    let s = s64 as nat;

    assert(pow2(s) <= u64::MAX) by {
        pow2_le_max64(s);
    }

    assert(pow2(s) > 0) by {
        lemma_pow2_pos(s);
    }

    assert(pow2(k * 8) <= u64::MAX) by {
        assert(pow2(k * 8) <= pow2(56)) by {
            if (k < 7){
                lemma_pow2_strictly_increases(k * 8, 56);
            }
        }
        assert(pow2(56) <= u64::MAX) by {
            lemma2_to64_rest();
        }
    }

    let p64 = pow2(s) as u64;

    let xk = load8_at_plus_version_rec(input, i, k);
    let xk_1 = load8_at_plus_version_rec(input, i, (k-1) as nat);
    let v = input[i + k];
    let v_n = v as nat;

    assert(
        xk
        ==
        (xk_1 + ((v as u64) << k * 8)) as u64
    ) by {
        reveal_with_fuel(load8_at_plus_version_rec, 1);
    }

    assert(xk >> s64 == xk / p64) by {
        assert( xk >> s64 == xk as nat / pow2(s) ) by {
            lemma_u64_shr_is_div(xk, s64);
        }
        // the conversion follows from pow2(s) > 0
    }

    assert(v * pow2(k * 8) <= u64::MAX) by {
            assert(v <= 0xFF);
            assert(pow2(k * 8) <= 0x100000000000000) by {
                lemma2_to64_rest(); // pow2(56)
                if (k < 7){
                    lemma_pow2_strictly_increases(8 * k, 56);
                }
            }
            mul_le(v as nat, 0xFF, pow2(k * 8), 0x100000000000000);
            assert(0xFF * 0x100000000000000 <= u64::MAX) by (compute);
        }

    assert(((v as u64) << k * 8) == pow2(k * 8) * v) by {
        lemma_u64_shl_is_mul(v as u64, (k * 8) as u64);
    }

    assert(
        xk >> s64
        ==
        (xk_1 + pow2(k * 8) * v) as u64 / p64
    );

    assert(xk_1 < pow2(8 * k)) by {
        load8_at_plus_version_rec_is_bounded(input, i, (k-1) as nat);
    }

    assert(xk_1 % p64 + (((pow2(k * 8) * v) as u64) % p64) < p64) by {
        if (s <= k * 8) {
            if (s < k * 8){
                assert(p64 < pow2(8 * k)) by {
                    lemma_pow2_strictly_increases(s, k *8);
                }
            }
            assert(((pow2(k * 8) * v_n)) % pow2(s) == 0) by {
                let s0 = (k * 8 - s) as nat;
                assert(pow2(k * 8) == pow2(s) * pow2(s0)) by {
                    lemma_pow2_adds(s, s0);
                }
                assert((pow2(k * 8) * v_n) == (pow2(s0) * v_n) * pow2(s)) by {
                    assert(pow2(k * 8) * v_n == pow2(s) * (pow2(s0) * v_n)) by {
                        lemma_mul_is_associative(pow2(s) as int, pow2(s0) as int, v_n as int);
                    }
                    assert(pow2(s) * (pow2(s0) * v_n) == (pow2(s0) * v_n) * pow2(s)) by {
                        // solver seems to need commutativity here explicitly for some reason
                        lemma_mul_is_commutative(pow2(s) as int, (pow2(s0) * v_n) as int);
                    }
                }
                assert(((pow2(s0) * v_n) * pow2(s)) % pow2(s) == 0) by {
                    lemma_mod_multiples_basic((pow2(s0) * v_n) as int, pow2(s) as int);
                }

            }
            lemma_mod_bound(xk_1 as int, p64 as int);
        }
        else {
            // s > k * 8
            // a + b = a | b
            // (a | b) & c == (a & c) | (b & c)
            // (a & c) | (b & c) = (a & c) + (b & c)
            let d = (s - k * 8) as nat;
            lemma_pow2_pos(d);
            let a = xk_1;
            let b = ((pow2(k * 8) * v) as u64);
            assert(b == (v as u64) << k * 8) by {
                    assert(pow2(k * 8) * v == v * pow2(k * 8)) by {
                        lemma_mul_is_commutative(v as int, pow2(k * 8) as int)
                    }
                    assert((v as u64) * pow2(k * 8) == (v as u64) << k * 8) by {
                        lemma_u64_shl_is_mul(v as u64, (k * 8) as u64);
                    }
                }

            // a + b = a | b
            assert(a + b == a | b) by {
                assert(a < 1u64 << ((k * 8) as u64)) by {
                    shift_is_pow2(k * 8);
                }
                assert(v <= (u64::MAX >> ((k * 8) as u64))) by {
                    assert(v <= u8::MAX);
                    assert(u64::MAX >> ((k * 8) as u64) >= u64::MAX >> 56) by {
                        shr_nonincreasing(u64::MAX, k * 8, 56);
                    }
                    assert(u8::MAX <= u64::MAX >> 56) by (compute);
                }
                bit_or_is_plus(a, v as u64, (k * 8) as u64);
            }

            let lbm = low_bits_mask(s) as u64;

            // (a | b) & c == (a & c) | (b & c)
            assert((a | b) & lbm == (a & lbm) | (b & lbm)) by (bit_vector);

            assert(b & lbm == (v_n % pow2(d)) * pow2(k * 8)) by {
                assert(b & lbm == b % p64) by {
                    lemma_u64_low_bits_mask_is_mod(b, s);
                }
                // Redundant, but useful to follow along
                // ----
                assert(b % p64 == (b as nat) % pow2(s));
                assert(b as nat == v_n * pow2(k * 8));
                // ----
                assert((b as nat) % pow2(s) == (v_n % pow2(d)) * pow2(k * 8)) by {
                    assert((v_n * pow2(k * 8)) % pow2(s) == (v_n % pow2(d)) * pow2(k * 8)) by {
                        mask_pow2(v_n, k * 8, s);
                    }
                }
            }

            let w = v_n % pow2(d);

            assert(w <= u64::MAX) by {
                assert(v_n % pow2(d) < pow2(d)) by {
                    lemma_mod_bound(v_n as int, pow2(d) as int);
                }
                assert(pow2(d) < pow2(63)) by {
                    lemma_pow2_strictly_increases(d, 63);
                }
                assert(pow2(63) < u64::MAX) by {
                    lemma2_to64_rest();
                }
            }
            assert( b & lbm == ((w as u64) << (k * 8 as u64))) by {
                lemma_u64_shl_is_mul(w as u64, (k * 8) as u64);
            }

            // (a & c) | (b & c) = (a & c) + (b & c)
            assert( (a & lbm) | (b & lbm) == (a & lbm) + (b & lbm)) by {
                assert( (a & lbm) < 1u64 << ((k * 8) as u64)) by {
                    assert(1u64 << ((k * 8) as u64) == pow2(k * 8)) by {
                        shift_is_pow2(k * 8);
                    }
                    assert(a & lbm <= a) by (bit_vector);
                }
                assert(
                    (a & lbm) | ((w as u64) << (k * 8 as u64))
                    ==
                    (a & lbm) + ((w as u64) << (k * 8 as u64))
                ) by {
                    assert(w <= (u64::MAX >> ((k * 8) as nat))) by {
                        assert(w < pow2(d)) by {
                            lemma_mod_bound(w as int, pow2(d) as int);
                        }
                        // d = s - 8k
                        assert(pow2(d) == pow2(s) / pow2(k * 8)) by {
                            lemma_pow2_subtracts(k * 8, s);
                        }
                        assert((u64::MAX >> ((k * 8) as nat)) == u64::MAX / (pow2(k * 8) as u64)) by {
                            lemma_u64_shr_is_div(u64::MAX, (k * 8) as u64);
                        }
                        assert(pow2(s) < u64::MAX) by {
                            assert(pow2(s) <= pow2(63)) by {
                                if (s < 63){
                                    lemma_pow2_strictly_increases(s, 63);
                                }
                            }
                            assert(pow2(63) < u64::MAX) by {
                                lemma2_to64_rest();
                            }
                        }
                        assert(pow2(s) / pow2(k * 8) <= u64::MAX / (pow2(k * 8) as u64)) by {
                            lemma_div_is_ordered(pow2(s) as int, u64::MAX as int, pow2(k * 8) as int);
                        }
                    }
                    bit_or_is_plus((a & lbm) as u64, w as u64, (k * 8) as u64);
                }
            }
            assert( a & lbm == xk_1 % p64 ) by {
                lemma_u64_low_bits_mask_is_mod(xk_1, s);
            }

            assert( b & lbm == ((pow2(k * 8) * v) as u64) % p64) by {
                lemma_u64_low_bits_mask_is_mod(b, s);
            }

            assert((a | b) & lbm < p64) by {
                lemma_u64_low_bits_mask_is_mod(a | b, s);
            }
        }
    }


    assert((xk_1 + pow2(k * 8) * v) as u64 / p64 == xk_1 / p64 + ((pow2(k * 8) * v) as u64) / p64) by {
        assert(xk_1 + pow2(k * 8) * v <= u64::MAX) by {
            assert(v <= u8::MAX); // known
            assert(pow2(8 * k) <= 0x100000000000000) by {
                if (k < 7){
                    lemma_pow2_strictly_increases(k * 8 , 56);
                }
                lemma2_to64_rest();
            }
            assert(xk_1 < pow2(8 * k)); // known
            assert(xk_1 <= 0x100000000000000 - 1);
            assert(pow2(k *8) * v <= 0x100000000000000 * u8::MAX) by {
                mul_le(pow2(k * 8), 0x100000000000000, v_n, u8::MAX as nat);
            }
            assert((0x100000000000000 - 1) + (0x100000000000000) * u8::MAX <= u64::MAX) by (compute);
        }
        lemma_div_of_sum(
            xk_1 as nat,
            (pow2(k * 8) * v) as nat,
            p64 as nat
        );
    }



}




fn main() {}

}
