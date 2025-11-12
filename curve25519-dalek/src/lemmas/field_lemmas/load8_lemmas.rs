#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::calc;
use vstd::prelude::*;

use super::super::common_lemmas::bit_lemmas::*;
use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mask_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::core_specs::*;
use crate::specs::field_specs_u64::*;

verus! {

pub open spec fn load8_at_or_version_rec(input: &[u8], i: usize, k: nat) -> u64
    decreases k,
{
    if (k == 0) {
        (input[i as int] as u64)
    } else {
        // k > 0
        load8_at_or_version_rec(input, i, (k - 1) as nat) | ((input[i + k] as u64) << k * 8)
    }
}

pub proof fn rec_version_is_exec(input: &[u8], i: usize)
    ensures
        load8_at_or_version_rec(input, i, 7) == (input[i as int] as u64) | ((input[i + 1] as u64)
            << 8) | ((input[i + 2] as u64) << 16) | ((input[i + 3] as u64) << 24) | ((input[i
            + 4] as u64) << 32) | ((input[i + 5] as u64) << 40) | ((input[i + 6] as u64) << 48) | ((
        input[i + 7] as u64) << 56),
{
    assert(load8_at_or_version_rec(input, i, 0) == (input[i as int] as u64));

    assert forall|j: nat| 1 <= j <= 7 implies #[trigger] load8_at_or_version_rec(input, i, j)
        == load8_at_or_version_rec(input, i, (j - 1) as nat) | ((input[i + j] as u64) << 8 * j) by {
        reveal_with_fuel(load8_at_or_version_rec, 1);
    }
}

pub open spec fn load8_at_plus_version_rec(input: &[u8], i: usize, k: nat) -> u64
    decreases k,
{
    if (k == 0) {
        (input[i as int] as u64)
    } else {
        // k > 0
        (load8_at_plus_version_rec(input, i, (k - 1) as nat) + ((input[i + k] as u64) << k
            * 8)) as u64
    }
}

pub proof fn load8_at_plus_version_rec_is_bounded(input: &[u8], i: usize, k: nat)
    requires
        k <= 7,
    ensures
        load8_at_plus_version_rec(input, i, k) < pow2(8 * (k + 1)),
    decreases k,
{
    assert(u8::MAX < pow2(8)) by {
        lemma2_to64();
    }

    if (k == 0) {
        // just needs the the pre-if assert
    } else {
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
                        lemma_mul_strict_inequality(c as int, pow2(8) as int, pow2(8 * k) as int);
                    }
                    assert(pow2(8) * pow2(8 * k) <= pow2(64)) by {
                        assert(pow2(8 * k) <= pow2(56)) by {
                            if (k < 7) {
                                lemma_pow2_strictly_increases(8 * k, 56);
                            }
                        }
                        lemma_pow2_pos(8);
                        lemma_mul_inequality(pow2(8 * k) as int, pow2(56) as int, pow2(8) as int);
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

        assert(pow2(8 * k) + c * pow2(8 * k) <= pow2(8 * (k + 1))) by {
            // x + c * x == c ( x + 1 )
            assert(pow2(8 * k) + c * pow2(8 * k) == pow2(8 * k) * (c + 1)) by {
                lemma_mul_is_distributive_add(pow2(8 * k) as int, c as int, 1);
            }
            assert(c + 1 <= pow2(8));

            assert(pow2(8 * k) * (c + 1) <= pow2(8 * (k + 1))) by {
                lemma_mul_inequality((c + 1) as int, pow2(8) as int, pow2(8 * k) as int);
                lemma_pow2_adds(8, 8 * k);
                lemma_mul_is_distributive_add(8, 1, k as int);
            }
        }
    }
}

pub proof fn plus_version_is_spec_lemma(input: &[u8], i: usize, j: nat)
    requires
        1 <= j <= 7,
    ensures
        (input[i + j] as u64) << 8 * j == pow2(j * 8) * input[i + j],
        input[i + j] * pow2(j * 8) <= u64::MAX,
        pow2(8 * (j + 1)) - 1 <= pow2(64) - 1,
        pow2(8) * pow2(8 * j) == pow2(8 * (j + 1)),
{
    assert(pow2(64) - 1 == u64::MAX) by {
        lemma2_to64_rest();
    }

    assert(u8::MAX + 1 == pow2(8)) by {
        lemma2_to64();
    }

    assert(pow2(8 * (j + 1)) - 1 <= pow2(64) - 1) by {
        if (j < 7) {
            lemma_pow2_strictly_increases(8 * (j + 1), 64);
        }
    }

    lemma_pow2_adds(8, j * 8);

    lemma_mul_inequality(input[i + j] as int, u8::MAX as int, pow2(j * 8) as int);

    assert((input[i + j] as u64) * pow2(j * 8) <= u64::MAX) by {
        assert(u8::MAX * pow2(j * 8) <= pow2(64) - 1) by {
            assert(u8::MAX * pow2(j * 8) == (pow2(8) - 1) * pow2(j * 8) == pow2(8 * (j + 1)) - pow2(
                j * 8,
            )) by {
                assert(pow2(8) >= 1) by {
                    lemma2_to64();
                }
                lemma_mul_is_distributive_sub(pow2(8) as int, 1, pow2(j * 8) as int);
            }
            assert(pow2(j * 8) > 1) by {
                lemma2_to64();  // pow2(0)
                lemma_pow2_strictly_increases(0, j * 8)
            }
        }
    }
    lemma_u64_shl_is_mul((input[i + j] as u64), (j * 8) as u64);
}

pub proof fn plus_version_is_spec(input: &[u8], i: usize)
    ensures
        load8_at_plus_version_rec(input, i, 7) == load8_at_spec(input, i),
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
    assert(load8_at_plus_version_rec(input, i, 7) == (input[i as int] as u64) + ((input[i
        + 1] as u64) << 8) + ((input[i + 2] as u64) << 16) + ((input[i + 3] as u64) << 24) + ((
    input[i + 4] as u64) << 32) + ((input[i + 5] as u64) << 40) + ((input[i + 6] as u64) << 48) + ((
    input[i + 7] as u64) << 56)) by {
        assert forall|j: nat| 1 <= j <= 7 implies #[trigger] load8_at_plus_version_rec(input, i, j)
            == load8_at_plus_version_rec(input, i, (j - 1) as nat) + ((input[i + j] as u64) << j
            * 8) by {
            reveal_with_fuel(load8_at_plus_version_rec, 1);

            assert(load8_at_plus_version_rec(input, i, (j - 1) as nat) + ((input[i + j] as u64) << j
                * 8) <= u64::MAX) by {
                assert(load8_at_plus_version_rec(input, i, (j - 1) as nat) <= pow2(8 * j) - 1) by {
                    load8_at_plus_version_rec_is_bounded(input, i, (j - 1) as nat);
                }

                assert((input[i + j] as u64) << j * 8 <= u8::MAX * pow2(j * 8)) by {
                    // input[k] < MAX8 => input[k] * 2^(8j) < MAX8 * 2^(8j)
                    lemma_mul_inequality(input[i + j] as int, u8::MAX as int, pow2(j * 8) as int);
                }

                assert(load8_at_plus_version_rec(input, i, (j - 1) as nat) + ((input[i + j] as u64)
                    << j * 8) <= pow2(8 * (j + 1)) - 1) by {
                    lemma_mul_is_distributive_add(1, u8::MAX as int, pow2(j * 8) as int);
                }
            }

        }
    }
}

pub proof fn load8_at_versions_equivalent(input: &[u8], i: usize, k: nat)
    requires
        k <= 7,
    ensures
        load8_at_or_version_rec(input, i, k) == load8_at_plus_version_rec(input, i, k),
    decreases k,
{
    if (k == 0) {
        // trivial
    } else {
        load8_at_versions_equivalent(input, i, (k - 1) as nat);
        let prev = load8_at_plus_version_rec(input, i, (k - 1) as nat);
        assert(prev < (1u64 << 8 * k)) by {
            load8_at_plus_version_rec_is_bounded(input, i, (k - 1) as nat);
            lemma_shift_is_pow2(8 * k);
        }
        let v = input[i + k];
        assert(v <= (u64::MAX >> ((k * 8) as u64))) by {
            assert(v <= u8::MAX);
            assert(u64::MAX >> ((k * 8) as u64) >= u64::MAX >> 56) by {
                lemma_shr_nonincreasing(u64::MAX, k * 8, 56);
            }
            assert(u8::MAX <= u64::MAX >> 56) by (compute);
        }
        lemma_bit_or_is_plus(prev, input[i + k] as u64, (8 * k) as u64);
    }
}

pub proof fn load8_plus_fits_u64(input: &[u8], i: usize, k: nat)
    requires
        i + k < input.len(),
        0 < k <= 7,
    ensures
        load8_at_plus_version_rec(input, i, (k - 1) as nat) + pow2(k * 8) * input[i + k]
            <= u64::MAX,
{
    let xk_1 = load8_at_plus_version_rec(input, i, (k - 1) as nat);
    let v = input[i + k];

    assert((xk_1 + pow2(k * 8) * v) <= u64::MAX) by {
        assert(v <= u8::MAX);  // known
        assert(pow2(8 * k) <= 0x100000000000000) by {
            if (k < 7) {
                lemma_pow2_strictly_increases(k * 8, 56);
            }
            lemma2_to64_rest();
        }
        assert(xk_1 < pow2(8 * k)) by {
            load8_at_plus_version_rec_is_bounded(input, i, (k - 1) as nat);
        }
        assert(xk_1 <= 0x100000000000000 - 1);
        assert(pow2(k * 8) * v <= 0x100000000000000 * u8::MAX) by {
            lemma_mul_le(pow2(k * 8), 0x100000000000000, v as nat, u8::MAX as nat);
        }
        assert((0x100000000000000 - 1) + (0x100000000000000) * u8::MAX <= u64::MAX) by (compute);
    }
}

pub proof fn load8_at_spec_fits_u64(input: &[u8], i: usize)
    requires
        i + 7 < input.len(),
    ensures
        load8_at_spec(input, i) <= u64::MAX,
{
    plus_version_is_spec(input, i);
    load8_plus_fits_u64(input, i, 7);
}

pub proof fn load8_plus_ver_div_mod(input: &[u8], i: usize, k: nat, s: nat)
    requires
        i + 7 < input.len(),
        0 < k <= 7,
        s < 64,
    ensures
        load8_at_plus_version_rec(input, i, k) / (pow2(s) as u64) == load8_at_plus_version_rec(
            input,
            i,
            (k - 1) as nat,
        ) / (pow2(s) as u64) + (pow2(k * 8) * input[i + k]) as u64 / (pow2(s) as u64),
        load8_at_plus_version_rec(input, i, k) % (pow2(s) as u64) == load8_at_plus_version_rec(
            input,
            i,
            (k - 1) as nat,
        ) % (pow2(s) as u64) + (pow2(k * 8) * input[i + k]) as u64 % (pow2(s) as u64),
{
    assert(pow2(s) <= u64::MAX) by {
        lemma_pow2_le_max64(s);
    }

    assert(pow2(s) > 0) by {
        lemma_pow2_pos(s);
    }

    assert(pow2(k * 8) <= u64::MAX) by {
        lemma_pow2_le_max64(k * 8);
    }

    let p64 = pow2(s) as u64;

    let xk = load8_at_plus_version_rec(input, i, k);
    let xk_1 = load8_at_plus_version_rec(input, i, (k - 1) as nat);
    let v = input[i + k];
    let v_n = v as nat;

    assert(xk == (xk_1 + ((v as u64) << k * 8)) as u64) by {
        reveal_with_fuel(load8_at_plus_version_rec, 1);
    }

    assert(v * pow2(k * 8) <= u64::MAX) by {
        lemma_u8_times_pow2_fits_u64(v, k * 8);
    }

    assert(((v as u64) << k * 8) == pow2(k * 8) * v) by {
        lemma_u64_shl_is_mul(v as u64, (k * 8) as u64);
    }

    assert(xk_1 < pow2(8 * k)) by {
        load8_at_plus_version_rec_is_bounded(input, i, (k - 1) as nat);
    }

    assert((xk_1 + pow2(k * 8) * v) as u64 / p64 == xk_1 / p64 + ((pow2(k * 8) * v) as u64) / p64
        && (xk_1 + pow2(k * 8) * v) as u64 % p64 == xk_1 % p64 + ((pow2(k * 8) * v) as u64) % p64)
        by {
        assert((xk_1 + pow2(k * 8) * v) <= u64::MAX) by {
            load8_plus_fits_u64(input, i, k);
        }
        lemma_bitops_lifted(xk_1, v as u64, (k * 8) as nat, s);
    }
}

// For each 0 <= j <= 7 this lemma helps us show
// ((s_j + a_{j + 1}) / 2^s) % 2^t == (s_j / 2^s) % 2^t + (a_{j + 1} / 2^s) % 2^t
// where s_j = s[j]_0 and a_{j+1} = a[j] in the load8_shift_mod body.
// s_j represents the j-th partial sum (of load8 summands)
// The myriad of `requires` conditions captures the local scope in load8_shift_mod
pub proof fn load8_shift_mod_lemma(
    s_jplus1: u64,
    s_j: u64,
    a_jplus1: u64,
    x: u8,
    j: nat,
    s: nat,
    t: nat,
)
    requires
        s_j < pow2(j * 8),
        s_j + x * pow2(j * 8) <= u64::MAX,
        a_jplus1 == (x * pow2(j * 8)) as u64,
        s_jplus1 == s_j + a_jplus1,
        s_jplus1 / (pow2(s) as u64) == s_j / (pow2(s) as u64) + a_jplus1 / (pow2(s) as u64),
        0 <= j <= 7,
        s < 64,
        t < 64,
        0 < pow2(s) <= u64::MAX,
        0 < pow2(t) <= u64::MAX,
    ensures
        (s_jplus1 / (pow2(s) as u64)) % (pow2(t) as u64) == (s_j / (pow2(s) as u64)) % (pow2(
            t,
        ) as u64) + (a_jplus1 / (pow2(s) as u64)) % (pow2(t) as u64),
{
    let ps64 = (pow2(s) as u64);
    let pt64 = (pow2(t) as u64);

    assert((s_jplus1 / ps64) % pt64 == (s_j / ps64) % pt64 + (a_jplus1 / ps64) % pt64) by {
        if (s <= j * 8) {
            assert(pow2(s) <= pow2(j * 8)) by {
                if (s < j * 8) {
                    lemma_pow2_strictly_increases(s, j * 8);
                }
            }
            assert(x * pow2(s) <= a_jplus1) by {
                lemma_mul_inequality(pow2(s) as int, pow2(j * 8) as int, x as int);
            }
            assert(s_j + x * pow2(s) <= s_j + a_jplus1 <= u64::MAX);

            let d = (8 * j - s) as nat;

            assert(s_j / ps64 < pow2(d) && a_jplus1 / ps64 == x * pow2(d) && s_j / ps64 + x * pow2(
                d,
            ) <= u64::MAX) by {
                lemma_div_pow2_preserves_decomposition(s_j, x as u64, j * 8, s);
            }

            assert((s_j / ps64 + x * pow2(d)) as u64 % pt64 == (s_j / ps64) % pt64 + (x * pow2(
                d,
            )) as u64 % pt64 == (s_j / ps64) % pt64 + (a_jplus1 / ps64) % pt64) by {
                lemma_bitops_lifted(s_j / ps64, x as u64, d, t);
            }
        } else {
            // s > j * 8
            assert(pow2(j * 8) < pow2(s)) by {
                lemma_pow2_strictly_increases(j * 8, s);
            }
            assert(s_j / ps64 == 0) by {
                lemma_basic_div(s_j as int, ps64 as int);
            }

            assert(0u64 % pt64 == 0) by {
                lemma_small_mod(0, pow2(t));
            }
        }
    }
}

pub proof fn load8_shift_mod(input: &[u8], i: usize, s64: u64, t: nat)
    requires
        i + 7 < input.len(),
        s64 < 64,
        t < 64,
    ensures
        (load8_at_spec(input, i) as u64 >> s64) & (low_bits_mask(t) as u64) == ((pow2(0 * 8)
            * input[i + 0]) as u64 / (pow2(s64 as nat) as u64)) % (pow2(t) as u64) + ((pow2(1 * 8)
            * input[i + 1]) as u64 / (pow2(s64 as nat) as u64)) % (pow2(t) as u64) + ((pow2(2 * 8)
            * input[i + 2]) as u64 / (pow2(s64 as nat) as u64)) % (pow2(t) as u64) + ((pow2(3 * 8)
            * input[i + 3]) as u64 / (pow2(s64 as nat) as u64)) % (pow2(t) as u64) + ((pow2(4 * 8)
            * input[i + 4]) as u64 / (pow2(s64 as nat) as u64)) % (pow2(t) as u64) + ((pow2(5 * 8)
            * input[i + 5]) as u64 / (pow2(s64 as nat) as u64)) % (pow2(t) as u64) + ((pow2(6 * 8)
            * input[i + 6]) as u64 / (pow2(s64 as nat) as u64)) % (pow2(t) as u64) + ((pow2(7 * 8)
            * input[i + 7]) as u64 / (pow2(s64 as nat) as u64)) % (pow2(t) as u64),
{
    let x = load8_at_spec(input, i) as u64;
    let y = load8_at_plus_version_rec(input, i, 7);
    let s = s64 as nat;
    let ps64 = pow2(s) as u64;

    assert(0 < pow2(s) <= u64::MAX) by {
        lemma_pow2_pos(s);
        lemma_pow2_le_max64(s);
    }

    assert(x >> s64 == x / ps64) by {
        lemma_u64_shr_is_div(x, s64);
    }

    assert(x == y) by {
        plus_version_is_spec(input, i);
    }

    assert forall|j: nat| j <= 7 implies #[trigger] pow2(j * 8) * input[i + j] <= u64::MAX by {
        assert(pow2(j * 8) * input[i + j] == input[i + j] * pow2(j * 8));
        lemma_u8_times_pow2_fits_u64(input[i + j], j * 8);
    }

    assert(y / ps64 == (pow2(0 * 8) * input[i + 0]) as u64 / ps64 + (pow2(1 * 8) * input[i
        + 1]) as u64 / ps64 + (pow2(2 * 8) * input[i + 2]) as u64 / ps64 + (pow2(3 * 8) * input[i
        + 3]) as u64 / ps64 + (pow2(4 * 8) * input[i + 4]) as u64 / ps64 + (pow2(5 * 8) * input[i
        + 5]) as u64 / ps64 + (pow2(6 * 8) * input[i + 6]) as u64 / ps64 + (pow2(7 * 8) * input[i
        + 7]) as u64 / ps64) by {
        load8_plus_ver_div_mod(input, i, 7, s);
        load8_plus_ver_div_mod(input, i, 6, s);
        load8_plus_ver_div_mod(input, i, 5, s);
        load8_plus_ver_div_mod(input, i, 4, s);
        load8_plus_ver_div_mod(input, i, 3, s);
        load8_plus_ver_div_mod(input, i, 2, s);
        load8_plus_ver_div_mod(input, i, 1, s);

        assert(load8_at_plus_version_rec(input, i, 0) == (pow2(0 * 8) * input[i + 0]) as u64) by {
            assert(load8_at_plus_version_rec(input, i, 0) == (input[i as int] as u64));
            assert(pow2(0 * 8) == 1) by {
                lemma2_to64();
            }
            assert((pow2(0 * 8) * input[i + 0]) as u64 == (input[i as int] as u64)) by {
                lemma_mul_basics_4(input[i as int] as int);  // 1 * x = x
            }
        }
    }

    let pt64 = pow2(t) as u64;
    let z = y / ps64;

    assert(low_bits_mask(t) <= u64::MAX) by {
        lemma_low_bits_masks_fit_u64(t);
    }

    assert(z & (low_bits_mask(t) as u64) == z % pt64) by {
        lemma_u64_low_bits_mask_is_mod(z, t);
    }

    assert forall|j: nat| 0 <= j <= 7 implies #[trigger] pow2(j * 8) > 0 by {
        lemma_pow2_pos(j * 8);
    }

    assert forall|j: nat| 0 <= j <= 7 implies #[trigger] (pow2(j * 8) * input[i + j]) <= pow2(
        (j + 1) * 8,
    ) - pow2(j * 8) by {
        assert(j * 8 + 8 == (j + 1) * 8) by {
            lemma_mul_is_distributive_add_other_way(8, j as int, 1);
        }
        lemma_pow2_mul_bound_u8(input[i + j], j * 8);
    }

    // pow2(_) values;
    lemma2_to64();
    lemma2_to64_rest();
    assert(0 < pow2(t) <= u64::MAX) by {
        lemma_pow2_pos(t);
        lemma_pow2_le_max64(t);
    }

    // ---- lemmas about X * pow2
    assert forall|j: nat| 0 <= j <= 7 implies #[trigger] pow2(j * 8) * input[i + j]
        == #[trigger] input[i + j] * pow2(j * 8) by {
        lemma_mul_is_commutative(pow2(j * 8) as int, input[i + j] as int);
    }

    assert forall|j: nat| 0 <= j <= 7 implies #[trigger] (pow2(j * 8) * input[i + j]) <= pow2(
        (j + 1) * 8,
    ) - pow2(j * 8) && pow2((j + 1) * 8) > pow2(j * 8) by {
        assert(j * 8 + 8 == (j + 1) * 8) by {
            lemma_mul_is_distributive_add_other_way(8, j as int, 1);
        }
        lemma_pow2_mul_bound_u8(input[i + j], j * 8);
        assert(pow2((j + 1) * 8) > pow2(j * 8)) by {
            lemma_pow2_strictly_increases(j * 8, j * 8 + 8);
        }
    }
    // ---- lemmas about X * pow2 <END>

    let a0 = (pow2(0 * 8) * input[i + 0]) as u64;
    let a1 = (pow2(1 * 8) * input[i + 1]) as u64;
    let a2 = (pow2(2 * 8) * input[i + 2]) as u64;
    let a3 = (pow2(3 * 8) * input[i + 3]) as u64;
    let a4 = (pow2(4 * 8) * input[i + 4]) as u64;
    let a5 = (pow2(5 * 8) * input[i + 5]) as u64;
    let a6 = (pow2(6 * 8) * input[i + 6]) as u64;
    let a7 = (pow2(7 * 8) * input[i + 7]) as u64;

    // Trigger the forall-s
    assert(a0 == input[i + 0] * pow2(0));
    assert(a1 == input[i + 1] * pow2(8));
    assert(a2 == input[i + 2] * pow2(16));
    assert(a3 == input[i + 3] * pow2(24));
    assert(a4 == input[i + 4] * pow2(32));
    assert(a5 == input[i + 5] * pow2(40));
    assert(a6 == input[i + 6] * pow2(48));
    assert(a7 == input[i + 7] * pow2(56));

    let s0_0 = a0;
    let s0 = s0_0 / ps64;

    assert(s0_0 < pow2(1 * 8));
    assert(s0_0 + a1 <= u64::MAX);

    let s1_0 = (s0_0 + a1) as u64;
    let s1 = s1_0 / ps64;

    assert(s1_0 < pow2(2 * 8));
    assert(s1 == s0_0 / ps64 + a1 / ps64) by {
        lemma_bitops_lifted(s0_0, input[i + 1] as u64, 1 * 8, s);
    }
    assert(s1_0 + a2 <= u64::MAX);

    let s2_0 = (s1_0 + a2) as u64;
    let s2 = s2_0 / ps64;

    assert(s2_0 < pow2(3 * 8));
    assert(s2 == s1_0 / ps64 + a2 / ps64) by {
        lemma_bitops_lifted(s1_0, input[i + 2] as u64, 2 * 8, s);
    }
    assert(s2_0 + a3 <= u64::MAX);

    let s3_0 = (s2_0 + a3) as u64;
    let s3 = s3_0 / ps64;

    assert(s3_0 < pow2(4 * 8));
    assert(s3 == s2_0 / ps64 + a3 / ps64) by {
        lemma_bitops_lifted(s2_0, input[i + 3] as u64, 3 * 8, s);
    }
    assert(s3_0 + a4 <= u64::MAX);

    let s4_0 = (s3_0 + a4) as u64;
    let s4 = s4_0 / ps64;

    assert(s4_0 < pow2(5 * 8));
    assert(s4 == s3_0 / ps64 + a4 / ps64) by {
        lemma_bitops_lifted(s3_0, input[i + 4] as u64, 4 * 8, s);
    }
    assert(s4_0 + a5 <= u64::MAX);

    let s5_0 = (s4_0 + a5) as u64;
    let s5 = s5_0 / ps64;

    assert(s5_0 < pow2(6 * 8));
    assert(s5 == s4_0 / ps64 + a5 / ps64) by {
        lemma_bitops_lifted(s4_0, input[i + 5] as u64, 5 * 8, s);
    }
    assert(s5_0 + a6 <= u64::MAX);

    let s6_0 = (s5_0 + a6) as u64;
    let s6 = s6_0 / ps64;

    assert(s6_0 < pow2(7 * 8));
    assert(s6 == s5_0 / ps64 + a6 / ps64) by {
        lemma_bitops_lifted(s5_0, input[i + 6] as u64, 6 * 8, s);
    }
    assert(s6_0 + a7 <= u64::MAX);

    let s7_0 = (s6_0 + a7) as u64;
    let s7 = s7_0 / ps64;

    assert(s7 == s6_0 / ps64 + a7 / ps64) by {
        lemma_bitops_lifted(s6_0, input[i + 7] as u64, 7 * 8, s);
    }

    assert(s7 == z);

    assert(s6_0 <= pow2(7 * 8) - 1);
    assert(s5_0 <= pow2(6 * 8) - 1);
    assert(s4_0 <= pow2(5 * 8) - 1);
    assert(s3_0 <= pow2(4 * 8) - 1);
    assert(s2_0 <= pow2(3 * 8) - 1);
    assert(s1_0 <= pow2(2 * 8) - 1);
    assert(s0_0 <= pow2(1 * 8) - 1);

    assert(z % pt64 == ((pow2(0 * 8) * input[i + 0]) as u64 / ps64) % pt64 + ((pow2(1 * 8) * input[i
        + 1]) as u64 / ps64) % pt64 + ((pow2(2 * 8) * input[i + 2]) as u64 / ps64) % pt64 + ((pow2(
        3 * 8,
    ) * input[i + 3]) as u64 / ps64) % pt64 + ((pow2(4 * 8) * input[i + 4]) as u64 / ps64) % pt64
        + ((pow2(5 * 8) * input[i + 5]) as u64 / ps64) % pt64 + ((pow2(6 * 8) * input[i + 6]) as u64
        / ps64) % pt64 + ((pow2(7 * 8) * input[i + 7]) as u64 / ps64) % pt64) by {
        load8_shift_mod_lemma(s7_0, s6_0, a7, input[i + 7], 7, s, t);
        load8_shift_mod_lemma(s6_0, s5_0, a6, input[i + 6], 6, s, t);
        load8_shift_mod_lemma(s5_0, s4_0, a5, input[i + 5], 5, s, t);
        load8_shift_mod_lemma(s4_0, s3_0, a4, input[i + 4], 4, s, t);
        load8_shift_mod_lemma(s3_0, s2_0, a3, input[i + 3], 3, s, t);
        load8_shift_mod_lemma(s2_0, s1_0, a2, input[i + 2], 2, s, t);
        load8_shift_mod_lemma(s1_0, s0_0, a1, input[i + 1], 1, s, t);
    }
}

pub proof fn load8_limb_base(input: &[u8], i: usize, k: u64)
    requires
        i + 7 < input.len(),
        k < 64,
    ensures
        0 < pow2(51) <= u64::MAX,
        load8_at_spec(input, i) <= u64::MAX,
        ((load8_at_spec(input, i) as u64) >> k) & mask51 == (((input[i + 0] * pow2(0 * 8)) as u64)
            / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 1] * pow2(1 * 8)) as u64)
            / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 2] * pow2(2 * 8)) as u64)
            / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 3] * pow2(3 * 8)) as u64)
            / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 4] * pow2(4 * 8)) as u64)
            / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 5] * pow2(5 * 8)) as u64)
            / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 6] * pow2(6 * 8)) as u64)
            / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 7] * pow2(7 * 8)) as u64)
            / (pow2(k as nat) as u64)) % (pow2(51) as u64),
{
    assert(0 < pow2(51) <= u64::MAX) by {
        lemma_pow2_pos(51);
        lemma_pow2_le_max64(51);
    }

    assert(0 < pow2(k as nat) <= u64::MAX) by {
        lemma_pow2_pos(k as nat);
        lemma_pow2_le_max64(k as nat);
    }

    let p51 = pow2(51) as u64;
    let pk = pow2(k as nat) as u64;

    assert(mask51 == low_bits_mask(51)) by {
        l51_bit_mask_lt();
    }

    assert(load8_at_spec(input, i) <= u64::MAX) by {
        load8_at_spec_fits_u64(input, i);
    }

    assert((load8_at_spec(input, i) as u64 >> k) & (low_bits_mask(51) as u64) == (((input[i + 0]
        * pow2(0 * 8)) as u64) / pk) % p51 + (((input[i + 1] * pow2(1 * 8)) as u64) / pk) % p51 + ((
    (input[i + 2] * pow2(2 * 8)) as u64) / pk) % p51 + (((input[i + 3] * pow2(3 * 8)) as u64) / pk)
        % p51 + (((input[i + 4] * pow2(4 * 8)) as u64) / pk) % p51 + (((input[i + 5] * pow2(
        5 * 8,
    )) as u64) / pk) % p51 + (((input[i + 6] * pow2(6 * 8)) as u64) / pk) % p51 + (((input[i + 7]
        * pow2(7 * 8)) as u64) / pk) % p51) by {
        load8_shift_mod(input, i, k, 51);
    }

}

pub open spec fn lemma_pow2_mul_div_mod_small_mul_u8_t51_cond(k: nat, j: nat) -> bool {
    (j * 8 <= k) && (8 <= 51 + k - 8 * j)
}

pub open spec fn lemma_pow2_mul_div_mod_small_div_u8_t51_cond(k: nat, j: nat) -> bool {
    (k <= j * 8) && (8 + j * 8 - k <= 51)
}

pub open spec fn lemma_pow2_mul_div_mod_close_mod_u8_t51_cond(k: nat, j: nat) -> bool {
    (k <= j * 8) && (j * 8 - k <= 51)
}

pub open spec fn lemma_pow2_mul_div_mod_small_mod_u8_t51_cond(k: nat, j: nat) -> bool {
    (k <= j * 8) && (51 <= j * 8 - k)
}

// Generalized load8_limb theorem. Asserts that
// - the first few summands are shifted by more than their power exponent and reduce to division
// - the next few summands are shifted by less than their exponents and are unaffected by masking, due to being small
// - the next few summands may, depending on the value of the u8 coefficient be either smaller than the mod,
//   or larger, so in general, the best we can assert is that they reduce to coefficient masking
// - the last few summands have large enough exponents that masking zeroes them
// The particular indices where these happen depend on the limb (i.e. the shift value k)
pub proof fn load8_limb_X(input: &[u8], i: usize, k: nat, j_div: nat, j_id: nat, j_shift: nat)
    requires
        i + 7 < input.len(),
        k <= 12,
        forall|j: nat| 0 <= j < j_div ==> lemma_pow2_mul_div_mod_small_mul_u8_t51_cond(k, j),
        forall|j: nat| j_div <= j < j_id ==> lemma_pow2_mul_div_mod_small_div_u8_t51_cond(k, j),
        forall|j: nat| j_id <= j < j_shift ==> lemma_pow2_mul_div_mod_close_mod_u8_t51_cond(k, j),
        forall|j: nat| j_shift <= j < 8 ==> lemma_pow2_mul_div_mod_small_mod_u8_t51_cond(k, j),
    ensures
        forall|j: nat|
            0 <= j < j_div ==> #[trigger] ((input[(i + j) as int] * pow2(j * 8)) as u64 / (pow2(
                k,
            ) as u64)) % (pow2(51) as u64) == (input[(i + j) as int]) as nat / pow2(
                (k - j * 8) as nat,
            ),
        forall|j: nat|
            j_div <= j < j_id ==> #[trigger] ((input[(i + j) as int] * pow2(j * 8)) as u64 / (pow2(
                k,
            ) as u64)) % (pow2(51) as u64) == (input[(i + j) as int]) * pow2((j * 8 - k) as nat),
        forall|j: nat|
            j_id <= j < j_shift ==> #[trigger] ((input[(i + j) as int] * pow2(j * 8)) as u64 / (
            pow2(k) as u64)) % (pow2(51) as u64) == (input[(i + j) as int] as nat % pow2(
                (51 - (j * 8 - k)) as nat,
            )) * pow2((j * 8 - k) as nat),
        forall|j: nat|
            j_shift <= j < 8 ==> #[trigger] ((input[(i + j) as int] * pow2(j * 8)) as u64 / (pow2(
                k,
            ) as u64)) % (pow2(51) as u64) == 0,
        (load8_at_spec(input, i) as u64 >> k) & mask51 == (((input[i + 0] * pow2(0 * 8)) as u64) / (
        pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 1] * pow2(1 * 8)) as u64) / (
        pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 2] * pow2(2 * 8)) as u64) / (
        pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 3] * pow2(3 * 8)) as u64) / (
        pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 4] * pow2(4 * 8)) as u64) / (
        pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 5] * pow2(5 * 8)) as u64) / (
        pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 6] * pow2(6 * 8)) as u64) / (
        pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 7] * pow2(7 * 8)) as u64) / (
        pow2(k as nat) as u64)) % (pow2(51) as u64),
{
    let p51 = pow2(51) as u64;

    assert(0 < pow2(k) <= u64::MAX) by {
        lemma_pow2_pos(k);
        lemma_pow2_le_max64(k);
    }

    let pk = pow2(k) as u64;

    load8_limb_base(input, i, k as u64);

    // first: all div, no mul
    assert forall|j: nat| 0 <= j < j_div implies #[trigger] ((input[(i + j) as int] * pow2(
        j * 8,
    )) as u64 / pk) % p51 == (input[(i + j) as int]) as nat / pow2((k - j * 8) as nat) by {
        assert(lemma_pow2_mul_div_mod_small_mul_u8_t51_cond(k, j));  // trigger forall
        lemma_pow2_mul_div_mod_small_mul_u8(input[(i + j) as int], j * 8, k, 51);
    }

    // (product >> k) < 2^51
    assert forall|j: nat| j_div <= j < j_id implies #[trigger] ((input[(i + j) as int] * pow2(
        j * 8,
    )) as u64 / pk) % p51 == (input[(i + j) as int]) * pow2((j * 8 - k) as nat) by {
        assert(lemma_pow2_mul_div_mod_small_div_u8_t51_cond(k, j));  // trigger forall
        lemma_pow2_mul_div_mod_small_div_u8(input[(i + j) as int], j * 8, k, 51);
    }

    // partial shift
    assert forall|j: nat| j_id <= j < j_shift implies #[trigger] ((input[(i + j) as int] * pow2(
        j * 8,
    )) as u64 / pk) % p51 == (input[(i + j) as int] as nat % pow2((51 - (j * 8 - k)) as nat))
        * pow2((j * 8 - k) as nat) by {
        assert(lemma_pow2_mul_div_mod_close_mod_u8_t51_cond(k, j));  // trigger forall
        lemma_pow2_mul_div_mod_close_mod_u8(input[(i + j) as int], j * 8, k, 51);
    }

    // zero
    assert forall|j: nat| j_shift <= j < 8 implies #[trigger] ((input[(i + j) as int] * pow2(
        j * 8,
    )) as u64 / pk) % p51 == 0 by {
        assert(lemma_pow2_mul_div_mod_small_mod_u8_t51_cond(k, j));  // trigger forall
        lemma_pow2_mul_div_mod_small_mod_u8(input[(i + j) as int], j * 8, k, 51);
    }
}

pub proof fn load8_limb0(input: &[u8])
    requires
        0 + 7 < input.len(),
    ensures
        (load8_at_spec(input, 0) as u64) & mask51 == (input[0] * pow2(0 * 8)) + (input[1] * pow2(
            1 * 8,
        )) + (input[2] * pow2(2 * 8)) + (input[3] * pow2(3 * 8)) + (input[4] * pow2(4 * 8)) + (
        input[5] * pow2(5 * 8)) + ((input[6] as nat % pow2(3)) * pow2(6 * 8)),
{
    let i = 0;
    let k = 0;

    let j_div = 0;
    let j_id = 6;
    let j_shift = 7;

    assert(load8_at_spec(input, 0) as u64 == (load8_at_spec(input, 0) as u64 >> 0)) by {
        lemma_shr_zero_is_id(load8_at_spec(input, 0) as u64);
    }

    load8_limb_X(input, i, k, j_div, j_id, j_shift);

    // Sanity check
    assert((load8_at_spec(input, i) as u64 >> k) & mask51 == (((input[i + 0] * pow2(0 * 8)) as u64)
        / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 1] * pow2(1 * 8)) as u64) / (
    pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 2] * pow2(2 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 3] * pow2(3 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 4] * pow2(4 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 5] * pow2(5 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 6] * pow2(6 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 7] * pow2(7 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64));

    assert(pow2(0) == 1) by {
        lemma2_to64();
    }

    broadcast use lemma_div_basics_2;  // x / 1 = x

}

pub proof fn load8_limb1(input: &[u8])
    requires
        6 + 7 < input.len(),
    ensures
        ((load8_at_spec(input, 6) as u64) >> 3) & mask51 == (input[6] as nat / pow2(3)) + (input[7]
            * pow2((1 * 8 - 3) as nat)) + (input[8] * pow2((2 * 8 - 3) as nat)) + (input[9] * pow2(
            (3 * 8 - 3) as nat,
        )) + (input[10] * pow2((4 * 8 - 3) as nat)) + (input[11] * pow2((5 * 8 - 3) as nat)) + ((
        input[12] as nat % pow2(6)) * pow2((6 * 8 - 3) as nat)),
{
    let i = 6;
    let k = 3;

    let j_div = 1;
    let j_id = 6;
    let j_shift = 7;

    load8_limb_X(input, i, k, j_div, j_id, j_shift);

    // Sanity check
    assert((load8_at_spec(input, i) as u64 >> k) & mask51 == (((input[i + 0] * pow2(0 * 8)) as u64)
        / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 1] * pow2(1 * 8)) as u64) / (
    pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 2] * pow2(2 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 3] * pow2(3 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 4] * pow2(4 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 5] * pow2(5 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 6] * pow2(6 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 7] * pow2(7 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64));
}

pub proof fn load8_limb2(input: &[u8])
    requires
        12 + 7 < input.len(),
    ensures
        ((load8_at_spec(input, 12) as u64) >> 6) & mask51 == (input[12] as nat / pow2(6)) + (
        input[13] * pow2((1 * 8 - 6) as nat)) + (input[14] * pow2((2 * 8 - 6) as nat)) + (input[15]
            * pow2((3 * 8 - 6) as nat)) + (input[16] * pow2((4 * 8 - 6) as nat)) + (input[17]
            * pow2((5 * 8 - 6) as nat)) + (input[18] * pow2((6 * 8 - 6) as nat)) + ((
        input[19] as nat % pow2(1)) * pow2((7 * 8 - 6) as nat)),
{
    let i = 12;
    let k = 6;

    let j_div = 1;
    let j_id = 7;
    let j_shift = 8;

    load8_limb_X(input, i, k, j_div, j_id, j_shift);

    // Sanity check
    assert((load8_at_spec(input, i) as u64 >> k) & mask51 == (((input[i + 0] * pow2(0 * 8)) as u64)
        / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 1] * pow2(1 * 8)) as u64) / (
    pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 2] * pow2(2 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 3] * pow2(3 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 4] * pow2(4 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 5] * pow2(5 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 6] * pow2(6 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 7] * pow2(7 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64));
}

pub proof fn load8_limb3(input: &[u8])
    requires
        19 + 7 < input.len(),
    ensures
        ((load8_at_spec(input, 19) as u64) >> 1) & mask51 == (input[19] as nat / pow2(1)) + (
        input[20] * pow2((1 * 8 - 1) as nat)) + (input[21] * pow2((2 * 8 - 1) as nat)) + (input[22]
            * pow2((3 * 8 - 1) as nat)) + (input[23] * pow2((4 * 8 - 1) as nat)) + (input[24]
            * pow2((5 * 8 - 1) as nat)) + ((input[25] as nat % pow2(4)) * pow2((6 * 8 - 1) as nat)),
{
    let i = 19;
    let k = 1;

    let j_div = 1;
    let j_id = 6;
    let j_shift = 7;

    load8_limb_X(input, i, k, j_div, j_id, j_shift);

    // Sanity check
    assert((load8_at_spec(input, i) as u64 >> k) & mask51 == (((input[i + 0] * pow2(0 * 8)) as u64)
        / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 1] * pow2(1 * 8)) as u64) / (
    pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 2] * pow2(2 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 3] * pow2(3 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 4] * pow2(4 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 5] * pow2(5 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 6] * pow2(6 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 7] * pow2(7 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64));
}

pub proof fn load8_limb4(input: &[u8])
    requires
        24 + 7 < input.len(),
    ensures
        ((load8_at_spec(input, 24) as u64) >> 12) & mask51 == (input[25] as nat / pow2(4)) + (
        input[26] * pow2((2 * 8 - 12) as nat)) + (input[27] * pow2((3 * 8 - 12) as nat)) + (
        input[28] * pow2((4 * 8 - 12) as nat)) + (input[29] * pow2((5 * 8 - 12) as nat)) + (
        input[30] * pow2((6 * 8 - 12) as nat)) + ((input[31] as nat % pow2(7)) * pow2(
            (7 * 8 - 12) as nat,
        )),
{
    let i = 24;
    let k = 12;

    let j_div = 2;
    let j_id = 7;
    let j_shift = 8;

    load8_limb_X(input, i, k, j_div, j_id, j_shift);

    // Sanity check
    assert((load8_at_spec(input, i) as u64 >> k) & mask51 == (((input[i + 0] * pow2(0 * 8)) as u64)
        / (pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 1] * pow2(1 * 8)) as u64) / (
    pow2(k as nat) as u64)) % (pow2(51) as u64) + (((input[i + 2] * pow2(2 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 3] * pow2(3 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 4] * pow2(4 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 5] * pow2(5 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 6] * pow2(6 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64) + (((input[i + 7] * pow2(7 * 8)) as u64) / (pow2(
        k as nat,
    ) as u64)) % (pow2(51) as u64));

    // First term too small, swallowed by div
    assert(input[24] as nat / pow2(12) == 0) by {
        assert(input[24] < pow2(8) < pow2(12)) by {
            assert(input[24] < pow2(8)) by {
                lemma_u8_lt_pow2_8(input[24]);
            }
            assert(pow2(8) < pow2(12)) by {
                lemma_pow2_strictly_increases(8, 12);
            }
        }

        lemma_basic_div(input[24] as int, pow2(12) as int);
    }
}

fn main() {
}

} // verus!
