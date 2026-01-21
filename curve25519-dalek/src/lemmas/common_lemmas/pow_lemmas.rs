#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::seq::*;

use super::div_mod_lemmas::*;
use super::mul_lemmas::*;
use super::sum_lemmas::*;

// Proofs that unsigned integers are bounded by a power of 2
macro_rules! lemma_uN_lt_pow2 {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for any `x` of type "]
        #[doc = stringify!($uN)]
        #[doc = ", `x < 2^("]
        #[doc = stringify!($uN)]
        #[doc = "::BITS)"]
        pub proof fn $name(x: $uN)
            ensures
                x < pow2(<$uN>::BITS as nat),
        {
            let N = <$uN>::BITS;
            lemma2_to64();
            lemma2_to64_rest();
            if (N == 128) {
                assert(pow2(128) == pow2(64) * pow2(64)) by {
                    lemma_pow2_adds(64,64);
                }
                assert( x < 0x10000000000000000 * 0x10000000000000000) by (compute);
            }
        }
    }
    };
}

lemma_uN_lt_pow2!(lemma_u8_lt_pow2_8, u8);
lemma_uN_lt_pow2!(lemma_u16_lt_pow2_16, u16);
lemma_uN_lt_pow2!(lemma_u32_lt_pow2_32, u32);
lemma_uN_lt_pow2!(lemma_u64_lt_pow2_64, u64);
lemma_uN_lt_pow2!(lemma_u128_lt_pow2_128, u128);

// Converse of above, any 2^k fits into uN for k < N.
// TODO: update lemma_pow2_no_overflow in VSTD with u128 support, then remove this
macro_rules! lemma_pow2_le_max {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "Proof that for any `k` smaller than `"]
        #[doc = stringify!($uN)]
        #[doc = "::BITS`, `pow2(k) <= "]
        #[doc = stringify!($uN)]
        #[doc = "::MAX`"]
        pub proof fn $name(k: nat)
            requires
                k < <$uN>::BITS
            ensures
                pow2(k) <= <$uN>::MAX,
        {
            let N = <$uN>::BITS;
            lemma2_to64();
            lemma2_to64_rest();
            if(N == 128 && k > 64) {
                let d = (k - 64) as nat;
                assert(pow2(k) == pow2(d) * pow2(64)) by {
                    lemma_pow2_adds(d, 64);
                }
                assert(pow2(k) <= pow2(63) * pow2(64)) by {
                    lemma_pow2_pos(64);
                    lemma_mul_inequality(d as int, 63, pow2(64) as int);
                }
                assert(0x8000000000000000 * 0x10000000000000000 <= u128::MAX) by (compute);
            }
        }
    }
    };
}

lemma_pow2_le_max!(lemma_u8_pow2_le_max, u8);
lemma_pow2_le_max!(lemma_u16_pow2_le_max, u16);
lemma_pow2_le_max!(lemma_u32_pow2_le_max, u32);
lemma_pow2_le_max!(lemma_u64_pow2_le_max, u64);
lemma_pow2_le_max!(lemma_u128_pow2_le_max, u128);

verus! {

pub proof fn lemma_pow2_plus_one(n: nat)
    ensures
        pow2(n + 1) == pow2(n) + pow2(n),
{
    assert(pow2(n + 1) == pow2(n) * pow2(1)) by {
        lemma_pow2_adds(n, 1);
    }
    assert(pow2(1) == 1 + 1) by {
        lemma2_to64();
    }
    assert(pow2(n) * (1 + 1) == pow2(n) + pow2(n)) by {
        lemma_mul_is_distributive_add(pow2(n) as int, 1, 1);
        lemma_mul_basics_3(pow2(n) as int);
    }
}

/// Helper: Division bounds - if x < 2^b then x/2^a < 2^(b-a)
pub proof fn lemma_div_bound(x: nat, a: nat, b: nat)
    requires
        a <= b,
        x < pow2(b),
    ensures
        x / pow2(a) < pow2((b - a) as nat),
{
    // Key insight: 2^b / 2^a = 2^(b-a)
    // Since x < 2^b, we have x / 2^a < 2^b / 2^a = 2^(b-a)
    lemma_pow2_adds(a, (b - a) as nat);

    // Use division properties
    lemma_div_strictly_bounded(x as int, pow2(a) as int, pow2((b - a) as nat) as int);
}

// Not generalizing, marginal value for vstd
// Rewriting lemma; 2^(a + b) * x = 2^a * (2^b * x)
// Parenthesis placement matters here
pub proof fn lemma_two_factoring(a: nat, b: nat, v: u64)
    ensures
        pow2(a + b) * v == pow2(a) * (pow2(b) * v),
{
    lemma_pow2_adds(a, b);
    lemma_mul_is_associative(pow2(a) as int, pow2(b) as int, v as int);
}

// (v^(2^k))^2 = v^(2^(k + 1))
pub proof fn lemma_pow2_square(v: int, i: nat)
    ensures
        pow(v, pow2(i)) * pow(v, pow2(i)) == pow(v, pow2(i + 1)),
{
    // pow(v, pow2(i)) * pow(v, pow2(i)) = pow(v, pow2(i) + pow2(i));
    lemma_pow_adds(v as int, pow2(i), pow2(i));
    // 2 * pow2(i) = pow2(i + 1)
    lemma_pow2_unfold(i + 1);
}

// v^(2^i) >= 0
pub proof fn lemma_pow_nat_is_nat(v: nat, i: nat)
    ensures
        pow(v as int, pow2(i)) >= 0,
{
    lemma_pow2_pos(i);  // pow2(i) > 0
    if (v == 0) {
        lemma0_pow(pow2(i));
    } else {
        lemma_pow_positive(v as int, pow2(i));
    }
}

pub proof fn lemma_pow2_mul_bound_general(a: nat, s: nat, k: nat)
    requires
        a < pow2(s),
    ensures
        pow2(k) * a <= pow2(k + s) - pow2(k),
        a * pow2(k) <= pow2(k + s) - pow2(k),
        pow2(k + s) - pow2(k) < pow2(k + s),
{
    assert(a <= pow2(s) - 1);  // x < y <=> x <= y - 1

    lemma_mul_le(a as nat, (pow2(s) - 1) as nat, pow2(k), pow2(k));
    assert((pow2(s) - 1) * pow2(k) == pow2(k + s) - pow2(k)) by {
        lemma_mul_is_distributive_sub(pow2(k) as int, pow2(s) as int, 1);
        lemma_pow2_adds(k, s);
    }

    lemma_mul_is_commutative(a as int, pow2(k) as int);

    assert(pow2(k) > 0) by {
        lemma_pow2_pos(k);
    }
}

macro_rules! lemma_pow2_mul_bound {
    ($name:ident, $pow_bound:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(a: $uN, k: nat)
            ensures
                pow2(k) * a <= pow2(k + <$uN>::BITS as nat) - pow2(k),
                a * pow2(k) <= pow2(k + <$uN>::BITS as nat) - pow2(k),
                pow2(k + <$uN>::BITS as nat) - pow2(k) < pow2(k + <$uN>::BITS as nat),
        {
            let N = <$uN>::BITS as nat;
            assert(a < pow2(N)) by {
                $pow_bound(a);
            }

            lemma_pow2_mul_bound_general(a as nat, N, k);
        }
    }
    };
}

lemma_pow2_mul_bound!(lemma_u8_pow2_mul_bound, lemma_u8_lt_pow2_8, u8);

lemma_pow2_mul_bound!(lemma_u16_pow2_mul_bound, lemma_u16_lt_pow2_16, u16);

lemma_pow2_mul_bound!(lemma_u32_pow2_mul_bound, lemma_u32_lt_pow2_32, u32);

lemma_pow2_mul_bound!(lemma_u64_pow2_mul_bound, lemma_u64_lt_pow2_64, u64);

lemma_pow2_mul_bound!(lemma_u128_pow2_mul_bound, lemma_u128_lt_pow2_128, u128);

pub proof fn lemma_binary_sum_div_decomposition(a: nat, b: nat, s: nat, k: nat)
    requires
        a < pow2(s),
    ensures
        (a + b * pow2(s)) / pow2(k) == a / pow2(k) + (b * pow2(s)) / pow2(k),
{
    let ps = pow2(s);
    let pk = pow2(k);
    let x = a;
    let y = b * ps;
    let z = x + y;

    assert(pk > 0) by {
        lemma_pow2_pos(k);
    }

    assert(x == pk * (x / pk) + x % pk) by {
        lemma_fundamental_div_mod(x as int, pk as int);
    }

    assert(y == pk * (y / pk) + y % pk) by {
        lemma_fundamental_div_mod(y as int, pk as int);
    }

    assert(z % pk == x % pk + y % pk) by {
        lemma_binary_sum_mod_decomposition(a, b, s, k);
    }

    assert(z == x + y == pk * (x / pk + y / pk) + z % pk) by {
        lemma_mul_is_distributive_add(pk as int, (x / pk) as int, (y / pk) as int);
    }

    assert(z == pk * (z / pk) + z % pk) by {
        lemma_fundamental_div_mod(z as int, pk as int);
    }

    assert(z / pk == x / pk + y / pk) by {
        lemma_mul_equality_converse(pk as int, (z / pk) as int, (x / pk + y / pk) as int);
    }
}

pub proof fn lemma_binary_sum_mod_decomposition(a: nat, b: nat, s: nat, k: nat)
    requires
        a < pow2(s),
    ensures
        (a + b * pow2(s)) % pow2(k) == a % pow2(k) + (b * pow2(s)) % pow2(k),
{
    let ps = pow2(s);
    let pk = pow2(k);
    let x = a;
    let y = b * ps;

    assert(pk > 0) by {
        lemma_pow2_pos(k);
    }

    assert((x + y) % pk == ((x % pk) + (y % pk)) % pk) by {
        lemma_add_mod_noop(x as int, y as int, pk as int);
    }

    if (s >= k) {
        let d = (s - k) as nat;
        assert(y % pk == 0) by {
            assert(y == (b * pow2(d)) * pk) by {
                lemma_pow2_adds(d, k);
                lemma_mul_is_associative(b as int, pow2(d) as int, pk as int);
            }
            assert(y % pk == 0) by {
                lemma_mod_multiples_basic((b * pow2(d)) as int, pk as int);
            }
        }

        assert((x % pk) % pk == x % pk) by {
            lemma_mod_twice(x as int, pk as int);
        }

    } else {
        // s < k
        let d = (k - s) as nat;

        assert(pow2(d) > 0) by {
            lemma_pow2_pos(d);
        }

        let z = b % pow2(d);

        assert(y % pk == z * ps) by {
            lemma_pow2_mul_mod(b, s, k);
        }

        assert(x % pk == x) by {
            assert(ps < pk) by {
                lemma_pow2_strictly_increases(s, k);
            }
            lemma_small_mod(x, pk);
        }

        assert((x + z * ps) % pk == x + z * ps) by {
            assert(x + z * ps < pk) by {
                assert(z * ps <= pk - ps) by {
                    assert(z < pow2(d)) by {
                        lemma_small_mod(z, pow2(d));
                    }
                    lemma_pow2_mul_bound_general(z, d, s);
                }
            }

            lemma_small_mod(x + z * ps, pk);
        }
    }
}

// Proofs that multiplying an N bit integer by 2^k returns a value smaller than 2^(k + N) which is unaffected
// by mod operations with powers greater than k + N.
macro_rules! lemma_times_pow2_mod_is_id {
    ($name:ident, $mul_bound:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub broadcast proof fn $name(a: $uN, k: nat, s: nat)
            requires
                k + <$uN>::BITS <= s
            ensures
                #![trigger (pow2(k) * a) as nat % pow2(s), (pow2(k) * a as nat) % pow2(s)]
                #![trigger (a * pow2(k)) as nat % pow2(s), (a as nat * pow2(k)) % pow2(s)]
                (pow2(k) * a) as nat % pow2(s) == pow2(k) * a,
                (a * pow2(k)) as nat % pow2(s) == a * pow2(k),
        {
            let l = (k + <$uN>::BITS) as nat;

            assert(a * pow2(k) == pow2(k) * a) by {
                lemma_mul_is_commutative(a as int, pow2(k) as int);
            }

            assert(pow2(k) * a < pow2(l)) by {
                $mul_bound(a, k);
            }
            if (l < s) {
                assert(pow2(l) < pow2(s)) by {
                    lemma_pow2_strictly_increases(l, s);
                }
            }
            assert(pow2(s) > 0) by {
                lemma_pow2_pos(s);
            }

            assert((pow2(k) * a) as nat % pow2(s) == pow2(k) * a) by {
                lemma_small_mod((pow2(k) * a) as nat, pow2(s));
            }
        }
    }
    };
}

lemma_times_pow2_mod_is_id!(lemma_u8_times_pow2_mod_is_id, lemma_u8_pow2_mul_bound, u8);

lemma_times_pow2_mod_is_id!(lemma_u16_times_pow2_mod_is_id, lemma_u16_pow2_mul_bound, u16);

lemma_times_pow2_mod_is_id!(lemma_u32_times_pow2_mod_is_id, lemma_u32_pow2_mul_bound, u32);

lemma_times_pow2_mod_is_id!(lemma_u64_times_pow2_mod_is_id, lemma_u64_pow2_mul_bound, u64);

lemma_times_pow2_mod_is_id!(lemma_u128_times_pow2_mod_is_id, lemma_u128_pow2_mul_bound, u128);

// Proofs that a value fits into an N bit integer iff it is smaller than 2^N
macro_rules! lemma_pow2N_bound {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(a: nat)
            ensures
                a < pow2(<$uN>::BITS as nat) <==> a <= <$uN>::MAX
        {
            lemma2_to64();
            lemma2_to64_rest();

            if (<$uN>::BITS == 128) {
                assert(pow2(128) == pow2(64) * pow2(64)) by {
                    lemma_pow2_adds(64, 64);
                }
                assert((0x10000000000000000 * 0x10000000000000000 - 1) == u128::MAX) by (compute);
            }
        }
    }
    };
}

lemma_pow2N_bound!(lemma_u8_pow2_bound, u8);

lemma_pow2N_bound!(lemma_u16_pow2_bound, u16);

lemma_pow2N_bound!(lemma_u32_pow2_bound, u32);

lemma_pow2N_bound!(lemma_u64_pow2_bound, u64);

lemma_pow2N_bound!(lemma_u128_pow2_bound, u128);

// Proofs that multiplying an N bit integer with 2^k returns a value that fits into an M bit integer if N + k <= M
macro_rules! lemma_uN_times_pow2_fits_uM {
    ($name:ident, $mul_boundN:ident, $pow_boundM:ident, $uN:ty, $uM:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(a: $uN, k: nat)
            requires
                k + <$uN>::BITS <= <$uM>::BITS
            ensures
                a * pow2(k) <= <$uM>::MAX,
        {
                let d = (<$uM>::BITS - <$uN>::BITS) as nat;
                assert((a as $uM) * pow2(k) <= (a as $uM) * pow2(d)) by {
                    assert(pow2(k) <= pow2(d)) by {
                        if (k < d) {
                            lemma_pow2_strictly_increases(k, d);
                        }
                    }
                    lemma_mul_le(a as nat, a as nat, pow2(k), pow2(d));
                }

                assert(a * pow2(d) < pow2(<$uM>::BITS as nat)) by {
                    $mul_boundN(a, d);
                }

                $pow_boundM(a as nat * pow2(d));
        }
    }
    };
}

lemma_uN_times_pow2_fits_uM!(lemma_u8_times_pow2_fits_u16, lemma_u8_pow2_mul_bound, lemma_u16_pow2_bound, u8, u16);

lemma_uN_times_pow2_fits_uM!(lemma_u8_times_pow2_fits_u32, lemma_u8_pow2_mul_bound, lemma_u32_pow2_bound, u8, u32);

lemma_uN_times_pow2_fits_uM!(lemma_u8_times_pow2_fits_u64, lemma_u8_pow2_mul_bound, lemma_u64_pow2_bound, u8, u64);

lemma_uN_times_pow2_fits_uM!(lemma_u8_times_pow2_fits_u128, lemma_u8_pow2_mul_bound, lemma_u128_pow2_bound, u8, u128);

lemma_uN_times_pow2_fits_uM!(lemma_u16_times_pow2_fits_u32, lemma_u16_pow2_mul_bound, lemma_u32_pow2_bound, u16, u32);

lemma_uN_times_pow2_fits_uM!(lemma_u16_times_pow2_fits_u64, lemma_u16_pow2_mul_bound, lemma_u64_pow2_bound, u16, u64);

lemma_uN_times_pow2_fits_uM!(lemma_u16_times_pow2_fits_u128, lemma_u16_pow2_mul_bound, lemma_u128_pow2_bound, u16, u128);

lemma_uN_times_pow2_fits_uM!(lemma_u32_times_pow2_fits_u64, lemma_u32_pow2_mul_bound, lemma_u64_pow2_bound, u32, u64);

lemma_uN_times_pow2_fits_uM!(lemma_u32_times_pow2_fits_u128, lemma_u32_pow2_mul_bound, lemma_u128_pow2_bound, u32, u128);

lemma_uN_times_pow2_fits_uM!(lemma_u64_times_pow2_fits_u128, lemma_u64_pow2_mul_bound, lemma_u128_pow2_bound, u64, u128);

pub proof fn lemma_pow2_mul_mod(x: nat, k: nat, s: nat)
    requires
        k <= s,
    ensures
        (x * pow2(k)) % pow2(s) == (x % pow2((s - k) as nat)) * pow2(k),
{
    let d = (s - k) as nat;

    assert(pow2(s) == pow2(k) * pow2(d)) by {
        lemma_pow2_adds(k, d);
    }

    assert(pow2(k) * pow2(d) > 0 && pow2(d) > 0 && pow2(k) > 0) by {
        lemma_pow2_pos(s);
        lemma_pow2_pos(d);
        lemma_pow2_pos(k);
    }

    assert((pow2(k) * x) % (pow2(k) * pow2(d)) == pow2(k) * (x % pow2(d))) by {
        lemma_truncate_middle(x as int, pow2(k) as int, pow2(d) as int);
    }
}

pub proof fn lemma_pow2_div_mod(x: nat, k: nat, s: nat)
    ensures
        (x / pow2(k)) % pow2(s) == (x % pow2(s + k)) / pow2(k),
{
    let d = s + k;
    let ps = pow2(s);
    let pk = pow2(k);
    let pd = pow2(d);

    assert(pd > 0) by {
        lemma_pow2_pos(d);
    }

    assert(pd == ps * pk == pk * ps) by {
        lemma_pow2_adds(s, k);
        lemma_mul_is_commutative(ps as int, pk as int);
    }

    assert(x == pd * (x / pd) + x % pd) by {
        lemma_fundamental_div_mod(x as int, pd as int);
    }

    let x_div_pd = x / pd;
    let x_mod_pd = x % pd;

    assert(x_mod_pd < pd) by {
        lemma_mod_bound(x as int, pd as int);
    }

    // x / pk = (pd * (x / pd) + x % pd) / pk
    // ==
    // (pd * (x / pd)) / pk + (x % pd) / pk
    // ==
    // (ps * (x / pd)) + (x % pd) / pk
    assert(x / pk == ps * x_div_pd + x_mod_pd / pk) by {
        assert((pd * x_div_pd + x_mod_pd) / pk == (pd * x_div_pd) / pk + x_mod_pd / pk) by {
            lemma_mul_is_commutative(pd as int, x_div_pd as int);
            lemma_binary_sum_div_decomposition(x_mod_pd, x_div_pd, d, k);
        }
        assert((pd * x_div_pd) / pk == ps * x_div_pd) by {
            assert(pd * x_div_pd == pk * (ps * x_div_pd)) by {
                lemma_mul_is_associative(pk as int, ps as int, x_div_pd as int);
            }
            assert((pk * (ps * x_div_pd)) / pk == ps * x_div_pd) by {
                lemma_div_multiples_vanish((ps * x_div_pd) as int, pk as int);
            }
        }
    }

    // (x / pk) % ps = ((ps * (x / pd)) + (x % pd) / pk ) % ps
    // == <- (x % pd) < pd => (x % pd) / pk < pd / pk = ps
    // ((ps * (x / pd)) % ps + (x % pd) / pk ) % ps
    // ==
    // (x % pd) / pk
    assert((x / pk) % ps == x_mod_pd / pk) by {
        assert(pk > 0) by {
            lemma_pow2_pos(k);
        }
        // x_mod_pd < pd is known
        assert(x_mod_pd / pk < ps) by {
            assert(ps == pd / pk) by {
                lemma_div_by_multiple(ps as int, pk as int);
            }
            lemma_div_by_multiple_is_strongly_ordered(
                x_mod_pd as int,
                pd as int,
                ps as int,
                pk as int,
            );
        }
        // satisfies conditions for lemma_binary_sum_mod_decomposition
        assert((ps * x_div_pd + x_mod_pd / pk) % ps == (ps * x_div_pd) % ps + (x_mod_pd / pk) % ps)
            by {
            lemma_binary_sum_mod_decomposition(x_mod_pd / pk, x_div_pd, s, s);
        }
        assert((ps * x_div_pd) % ps == 0) by {
            lemma_mul_is_commutative(ps as int, x_div_pd as int);
            lemma_mod_multiples_basic(x_div_pd as int, ps as int);
        }
        assert((x_mod_pd / pk) % ps == x_mod_pd / pk) by {
            // x_mod_pd / pk < ps is known
            lemma_small_mod(x_mod_pd / pk, ps);
        }
    }
}

pub proof fn pow2_MUL_div(x: nat, k: nat, s: nat)
    requires
        k >= s,
    ensures
        (x * pow2(k)) / pow2(s) == x * pow2((k - s) as nat),
{
    assert(pow2(s) > 0) by {
        lemma_pow2_pos(s);
    }

    let d = (k - s) as nat;
    assert(pow2(k) == pow2(d) * pow2(s)) by {
        lemma_pow2_adds(d, s);
    }
    assert(x * pow2(k) == (x * pow2(d)) * pow2(s)) by {
        lemma_mul_is_associative(x as int, pow2(d) as int, pow2(s) as int);
    }
    assert(((x * pow2(d)) * pow2(s)) / pow2(s) == x * pow2(d)) by {
        lemma_div_by_multiple((x * pow2(d)) as int, pow2(s) as int);
    }
}

pub proof fn lemma_pow2_mul_div(x: nat, k: nat, s: nat)
    requires
        k <= s,
    ensures
        (x * pow2(k)) / pow2(s) == x / pow2((s - k) as nat),
{
    assert(pow2(k) > 0) by {
        lemma_pow2_pos(k);
    }

    let d = (s - k) as nat;

    assert(pow2(d) > 0) by {
        lemma_pow2_pos(d);
    }
    assert(pow2(s) == pow2(k) * pow2(d)) by {
        lemma_pow2_adds(k, d);
    }
    assert((x * pow2(k)) / pow2(s) == ((x * pow2(k)) / pow2(k) / pow2(d))) by {
        lemma_div_denominator((x * pow2(k)) as int, pow2(k) as int, pow2(d) as int)
    }
    assert((x * pow2(k)) / pow2(k) == x) by {
        lemma_div_by_multiple(x as int, pow2(k) as int);
    }
}

pub proof fn lemma_pow2_mul_div_mod_small_div(x: nat, px: nat, k: nat, s: nat, t: nat)
    requires
        x < pow2(px),
        s <= k,
        px + k - s <= t,
    ensures
        ((x * pow2(k)) / pow2(s)) % pow2(t) == x * pow2((k - s) as nat),
{
    let d = (k - s) as nat;

    assert((x * pow2(k)) / pow2(s) == x * pow2(d)) by {
        pow2_MUL_div(x, k, s);
    }

    let dd = (t - d) as nat;

    assert((x * pow2(d)) % pow2(t) == (x % pow2(dd)) * pow2(d)) by {
        lemma_pow2_mul_mod(x, d, t);
    }

    assert(x % pow2(dd) == x) by {
        assert(x < pow2(px) <= pow2(dd)) by {
            if (px < dd) {
                lemma_pow2_strictly_increases(px, dd);
            }
        }
        assert(x % pow2(dd) == x) by {
            lemma_small_mod(x, pow2(dd));
        }
    }
}

macro_rules! lemma_pow2_mul_div_mod_small_div_uN {
    ($name:ident, $pow_bound:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(x: $uN, k: nat, s: nat, t: nat)
            requires
                s <= k,
                <$uN>::BITS + k - s <= t,
            ensures
                ((x as nat * pow2(k)) / pow2(s)) % pow2(t) == x as nat * pow2((k - s) as nat)
        {
            let N = <$uN>::BITS as nat;
            assert(x < pow2(N)) by {
                $pow_bound(x as nat);
            }
            lemma_pow2_mul_div_mod_small_div(x as nat, N, k, s, t);
        }
    }
    };
}

lemma_pow2_mul_div_mod_small_div_uN!(lemma_u8_pow2_mul_div_mod_small_div, lemma_u8_pow2_bound, u8);

lemma_pow2_mul_div_mod_small_div_uN!(lemma_u16_pow2_mul_div_mod_small_div, lemma_u16_pow2_bound, u16);

lemma_pow2_mul_div_mod_small_div_uN!(lemma_u32_pow2_mul_div_mod_small_div, lemma_u32_pow2_bound, u32);

lemma_pow2_mul_div_mod_small_div_uN!(lemma_u64_pow2_mul_div_mod_small_div, lemma_u64_pow2_bound, u64);

lemma_pow2_mul_div_mod_small_div_uN!(lemma_u128_pow2_mul_div_mod_small_div, lemma_u128_pow2_bound, u128);

pub proof fn lemma_pow2_mul_div_mod_small_mul(x: nat, px: nat, k: nat, s: nat, t: nat)
    requires
        x < pow2(px),
        k <= s,
        px <= t + s - k,
    ensures
        ((x * pow2(k)) / pow2(s)) % pow2(t) == x / pow2((s - k) as nat),
{
    let d = (s - k) as nat;

    assert((x * pow2(k)) / pow2(s) == x / pow2(d)) by {
        lemma_pow2_mul_div(x, k, s);
    }

    assert(pow2(d) > 0) by {
        lemma_pow2_pos(d);
    }

    assert(x / pow2(d) < pow2(t)) by {
        assert(x < pow2(d) * pow2(t)) by {
            assert(pow2(d) * pow2(t) == pow2(d + t)) by {
                lemma_pow2_adds(d, t);
            }
            assert(pow2(px) <= pow2(t + d)) by {
                if (px < t + d) {
                    lemma_pow2_strictly_increases(px, t + d);
                }
            }
        }
        assert(x / pow2(d) < pow2(t)) by {
            lemma_multiply_divide_lt(x as int, pow2(d) as int, pow2(t) as int);
        }
    }

    assert((x / pow2(d)) % pow2(t) == x / pow2(d)) by {
        lemma_small_mod(x / pow2(d), pow2(t));
    }
}

macro_rules! lemma_pow2_mul_div_mod_small_mul_uN {
    ($name:ident, $pow_bound:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(x: $uN, k: nat, s: nat, t: nat)
            requires
                k <= s,
                <$uN>::BITS <= t + s - k,
            ensures
                ((x as nat * pow2(k)) / pow2(s)) % pow2(t) == x as nat/ pow2((s - k) as nat)
        {
            let N = <$uN>::BITS as nat;
            assert(x < pow2(N)) by {
                $pow_bound(x as nat);
            }
            lemma_pow2_mul_div_mod_small_mul(x as nat, N, k, s, t);
        }
    }
    };
}

lemma_pow2_mul_div_mod_small_mul_uN!(lemma_u8_pow2_mul_div_mod_small_mul, lemma_u8_pow2_bound, u8);

lemma_pow2_mul_div_mod_small_mul_uN!(lemma_u16_pow2_mul_div_mod_small_mul, lemma_u16_pow2_bound, u16);

lemma_pow2_mul_div_mod_small_mul_uN!(lemma_u32_pow2_mul_div_mod_small_mul, lemma_u32_pow2_bound, u32);

lemma_pow2_mul_div_mod_small_mul_uN!(lemma_u64_pow2_mul_div_mod_small_mul, lemma_u64_pow2_bound, u64);

lemma_pow2_mul_div_mod_small_mul_uN!(lemma_u128_pow2_mul_div_mod_small_mul, lemma_u128_pow2_bound, u128);

pub proof fn lemma_pow2_mul_div_mod_close_mod(x: nat, k: nat, s: nat, t: nat)
    requires
        s <= k,
        k - s <= t,
    ensures
        ((x * pow2(k)) / pow2(s)) % pow2(t) == (x % pow2((t - (k - s)) as nat) * pow2(
            (k - s) as nat,
        )),
{
    let d = (k - s) as nat;

    assert((x * pow2(k)) / pow2(s) == x * pow2(d)) by {
        pow2_MUL_div(x, k, s);
    }

    let dd = (t - d) as nat;

    assert((x * pow2(d)) % pow2(t) == (x % pow2(dd)) * pow2(d)) by {
        lemma_pow2_mul_mod(x, d, t);
    }
}

pub proof fn lemma_pow2_mul_div_mod_small_mod(x: nat, k: nat, s: nat, t: nat)
    requires
        s <= k,
        t <= k - s,
    ensures
        ((x * pow2(k)) / pow2(s)) % pow2(t) == 0,
{
    let d = (k - s) as nat;

    assert((x * pow2(k)) / pow2(s) == x * pow2(d)) by {
        pow2_MUL_div(x, k, s);
    }

    let dd = (d - t) as nat;

    assert(x * pow2(d) == (x * pow2(dd)) * pow2(t)) by {
        lemma_pow2_adds(dd, t);
        lemma_mul_is_associative(x as int, pow2(dd) as int, pow2(t) as int);
    }

    assert(pow2(t) > 0) by {
        lemma_pow2_pos(t);
    }

    assert(((x * pow2(dd)) * pow2(t)) % pow2(t) == 0) by {
        lemma_mod_multiples_basic((x * pow2(dd)) as int, pow2(t) as int);
    }
}

macro_rules! lemma_div_pow2_preserves_decomposition {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(a: $uN, b: $uN, s: nat, k: nat)
            requires
                a < pow2(s),
                a + b * pow2(s) <= <$uN>::MAX,
                k <= s < <$uN>::BITS,
            ensures
                (a as nat) / pow2(k) < pow2((s - k) as nat),
                (b * pow2(s)) as nat / pow2(k) == b * pow2((s - k) as nat),
                (a as nat) / pow2(k) + b * pow2((s - k) as nat) <= <$uN>::MAX,
        {
            let d = (s - k) as nat;

            assert(pow2(k) > 0) by {
                lemma_pow2_pos(k);
            }

            assert(pow2(s) == pow2(d) * pow2(k)) by {
                lemma_pow2_adds(d, k);
            }

            assert(a as nat / pow2(k) < pow2(d)) by {
                assert(a as nat / pow2(k) < pow2(s) / pow2(k)) by {
                    lemma_div_by_multiple_is_strongly_ordered(
                        a as int,
                        pow2(s) as int,
                        pow2(d) as int,
                        pow2(k) as int,
                    );
                }
                assert(pow2(s) / pow2(k) == pow2(d)) by {
                    lemma_div_by_multiple(pow2(d) as int, pow2(k) as int);
                }
            }

            assert((b * pow2(s)) as nat / pow2(k) == b * pow2(d)) by {
                pow2_MUL_div(b as nat, s, k);
            }
        }
    }
    };
}

lemma_div_pow2_preserves_decomposition!(lemma_u8_div_pow2_preserves_decomposition, u8);

lemma_div_pow2_preserves_decomposition!(lemma_u16_div_pow2_preserves_decomposition, u16);

lemma_div_pow2_preserves_decomposition!(lemma_u32_div_pow2_preserves_decomposition, u32);

lemma_div_pow2_preserves_decomposition!(lemma_u64_div_pow2_preserves_decomposition, u64);

lemma_div_pow2_preserves_decomposition!(lemma_u128_div_pow2_preserves_decomposition, u128);

/// Generalized: Chunk extraction commutes with modulo
/// If we extract a b-bit chunk at position k*b where k*b+b <= m, then:
/// (x / 2^(k*b)) % 2^b == ((x % 2^m) / 2^(k*b)) % 2^b
///
/// This is a fundamental property that allows us to extract fixed-size chunks
/// from a number before or after taking modulo, as long as the chunk lies
/// entirely below the modulo boundary.
///
/// Common uses:
/// - b=8 for byte extraction (256 = 2^8)
/// - b=16 for 16-bit word extraction
/// - b=32 for 32-bit word extraction
pub proof fn lemma_chunk_extraction_commutes_with_mod(x: nat, k: nat, b: nat, m: nat)
    requires
        b > 0,
        k * b + b
            <= m,  // The chunk we're extracting is entirely below the modulo boundary

    ensures
        (x / pow2(k * b)) % pow2(b) == ((x % pow2(m)) / pow2(k * b)) % pow2(b),
{
    assert((x / pow2(k * b)) % pow2(b) == (x % pow2(k * b + b)) / pow2(k * b)) by {
        lemma_pow2_div_mod(x, k * b, b);
    }

    let y = x % pow2(m);

    assert((y / pow2(k * b)) % pow2(b) == (y % pow2(k * b + b)) / pow2(k * b)) by {
        lemma_pow2_div_mod(y, k * b, b);
    }

    let s = k * b + b;
    let ps = pow2(s);

    assert(x % ps == y % ps) by {
        let d = (m - s) as nat;
        let pd = pow2(d);
        assert(pow2(m) == ps * pd) by {
            lemma_pow2_adds(s, d);
        }

        assert((x % (ps * pd)) % ps == x % ps) by {
            lemma_pow2_pos(d);
            lemma_pow2_pos(s);
            lemma_mod_mod(x as int, ps as int, pd as int);
        }
    }
}

macro_rules! pow2_sum {
    ($name:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub open spec fn $name(coefs: &[$uN], offset: nat, step: nat, k: nat) -> nat
            decreases k,
            {
                if (k == 0) {
                    coefs[offset as int] as nat * pow2(0)
                } else {
                    // k > 0
                    $name(
                        coefs,
                        offset,
                        step,
                        (k - 1) as nat
                    ) + coefs[(offset + k) as int] as nat * pow2(k * step)
                }
            }
    }
    };
}

pow2_sum!(pow2_sum_u8, u8);

pow2_sum!(pow2_sum_u16, u16);

pow2_sum!(pow2_sum_u32, u32);

pow2_sum!(pow2_sum_u64, u64);

pow2_sum!(pow2_sum_u128, u128);

macro_rules! lemma_pow2_sum_bounds {
    ($name:ident, $pow2_sum_uN:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(coefs: &[$uN], offset: nat, step: nat, k: nat)
            requires
                offset + k <= coefs.len(),
                forall|i: nat| 0 <= i <= k ==> #[trigger] coefs[(offset + i) as int] < pow2(step),
            ensures
                $pow2_sum_uN(coefs, offset, step, k) < pow2((k + 1) * step),
            decreases k,
        {
            if (k == 0) {
                assert(pow2(0) == 1) by {
                    lemma2_to64();
                }
                assert(coefs[offset as int] * pow2(0) == coefs[offset as int]) by {
                    lemma_mul_basics_3(coefs[offset as int] as int);
                }
                // trigger forall
                assert(coefs[(offset + 0) as int] < pow2(step));
                // Reveal the spec to show what pow2_sum equals
                assert($pow2_sum_uN(coefs, offset, step, 0) == coefs[offset as int] as nat * pow2(0)) by {
                    reveal_with_fuel($pow2_sum_uN, 1);
                }
                // (0 + 1) * step == 1 * step == step
                assert(1 * step == step) by {
                    lemma_mul_basics_3(step as int);
                }
                assert((0 + 1) * step == step);
                // Explicit final
                assert($pow2_sum_uN(coefs, offset, step, k) < pow2((k + 1) * step));
            } else {
                assert($pow2_sum_uN(coefs, offset, step, k) == $pow2_sum_uN(coefs, offset, step, (k - 1) as nat)
                    + coefs[(offset + k) as int] * pow2(k * step)) by {
                    reveal_with_fuel($pow2_sum_uN, 1);
                }

                assert($pow2_sum_uN(coefs, offset, step, (k - 1) as nat) < pow2(k * step)) by {
                    $name(coefs, offset, step, (k - 1) as nat);
                }

                assert(coefs[(offset + k) as int] * pow2(k * step) <= pow2((k + 1) * step) - pow2(k * step))
                    by {
                    assert((k + 1) * step == k * step + step) by {
                        lemma_mul_is_distributive_add_other_way(step as int, k as int, 1);
                    }
                    assert(coefs[(offset + k) as int] * pow2(k * step) <= pow2(k * step + step) - pow2(
                        k * step,
                    )) by {
                        lemma_pow2_mul_bound_general(coefs[(offset + k) as int] as nat, step, k * step);
                    }
                }

                // Final step: combine the bounds
                // sum(k-1) < pow2(k * step) AND coefs[k] * pow2(k * step) <= pow2((k+1) * step) - pow2(k * step)
                // => sum(k) = sum(k-1) + coefs[k] * pow2(k * step) < pow2((k+1) * step)
                assert($pow2_sum_uN(coefs, offset, step, k) < pow2((k + 1) * step));
            }
        }
    }
    };
}

lemma_pow2_sum_bounds!(lemma_pow2_sum_u8_bounds, pow2_sum_u8, u8);

lemma_pow2_sum_bounds!(lemma_pow2_sum_u16_bounds, pow2_sum_u16, u16);

lemma_pow2_sum_bounds!(lemma_pow2_sum_u32_bounds, pow2_sum_u32, u32);

lemma_pow2_sum_bounds!(lemma_pow2_sum_u64_bounds, pow2_sum_u64, u64);

lemma_pow2_sum_bounds!(lemma_pow2_sum_u128_bounds, pow2_sum_u128, u128);

/// Modular Bit Partitioning Theorem
/// If we add a value 'a' (fitting in k bits) to 'b' shifted left by k positions,
/// and take the result mod 2^n, we can partition the contributions:
/// - The low k bits come from 'a' (masked to k bits)
/// - The high (n-k) bits come from 'b' (masked to n-k bits, then shifted)
///
/// This works because:
/// 1. When a < 2^k, 'a' only affects bits [0, k-1]
/// 2. When we shift 'b' left by k, it only affects bits [k, n-1]
/// 3. No carry occurs between the two regions
/// 4. The sum fits within n bits
pub proof fn lemma_modular_bit_partitioning(a: nat, b: nat, k: nat, n: nat)
    requires
        k <= n,
        a < pow2(k),
    ensures
        (a + b * pow2(k)) % pow2(n) == (a % pow2(k)) + ((b % pow2((n - k) as nat)) * pow2(k)),
{
    assert((a + b * pow2(k)) % pow2(n) == a % pow2(n) + (b * pow2(k)) % pow2(n)) by {
        lemma_binary_sum_mod_decomposition(a, b, k, n);
    }

    assert((b * pow2(k)) % pow2(n) == (b % pow2((n - k) as nat)) * pow2(k)) by {
        lemma_pow2_mul_mod(b, k, n);
    }

    assert(a % pow2(k) == a == a % pow2(n)) by {
        assert(pow2(k) <= pow2(n)) by {
            if (k < n) {
                lemma_pow2_strictly_increases(k, n);
            }
        }
        lemma_small_mod(a, pow2(k));
        lemma_small_mod(a, pow2(n));
    }
}

// Proof that pow2(n) is even for n >= 1
pub proof fn lemma_pow2_even(n: nat)
    requires
        n >= 1,
    ensures
        pow2(n) % 2 == 0,
    decreases n,
{
    if n == 1 {
        assert(pow2(1) == 2) by {
            lemma2_to64();
        };
        assert(2int % 2int == 0) by { lemma_mod_self_0(2) };
    } else {
        let m = (n - 1) as nat;
        lemma_pow2_adds(1, m);
        assert(pow2(n) == pow2(1) * pow2(m));
        assert(pow2(1) == 2) by { lemma2_to64() };

        lemma_mul_mod_noop_right(2 as int, pow2(m) as int, 2 as int);

        lemma_pow2_even(m);

        assert((2 * (pow2(m) as int % 2)) % 2 == 0);
        assert(pow2(n) as int % 2 == 0);
    }
}

// If x ≡ 1 (mod m) then x^n ≡ 1 (mod m)
pub proof fn lemma_pow_mod_one(x: int, n: nat, m: int)
    requires
        m > 1,
        x % m == 1,
    ensures
        pow(x, n) % m == 1,
    decreases n,
{
    if n == 0 {
        assert(pow(x, 0) == 1) by { lemma_pow0(x) };
        assert(1int % m == 1) by { lemma_small_mod(1nat, m as nat) };
        assert(pow(x, n) % m == 1);
    } else {
        lemma_pow_mod_one(x, (n - 1) as nat, m);
        // pow(x,n) == pow(x,n-1) * x
        assert(pow(x, n) == pow(x, (n - 1) as nat) * x) by {
            lemma_pow_adds(x, 1, (n - 1) as nat);
            lemma_pow1(x);
        };

        // x^n = x^(n - 1) * x (mod m)
        assert(pow(x, n) % m == (pow(x, (n - 1) as nat) * x) % m);
        assert(pow(x, n) % m == ((pow(x, (n - 1) as nat) % m) * (x % m)) % m) by {
            lemma_mul_mod_noop(pow(x, (n - 1) as nat), x, m);
        };

        assert(pow(x, n) % m == (1int * 1int) % m);
        assert(pow(x, n) % m == 1int % m);
        assert(1int % m == 1) by { lemma_small_mod(1nat, m as nat) };
        assert(pow(x, n) % m == 1);
    }
}

// Helper lemmas for pow22501 proof
// Proves: (2^n - 1) * 2^n + (2^n - 1) = 2^(2n) - 1
pub proof fn lemma_pow2_geometric_double(n: nat)
    ensures
        (pow2(n) - 1) * pow2(n) + (pow2(n) - 1) == pow2(2 * n) - 1,
{
    lemma2_to64();
    lemma_pow2_adds(n, n);
    assert(pow2(2 * n) == pow2(n) * pow2(n)) by {
        assert(n + n == 2 * n);
    }
    // (2^n - 1) * 2^n + (2^n - 1)
    // = 2^n * 2^n - 2^n + 2^n - 1
    // = 2^(2n) - 1
    lemma_mul_is_distributive_sub(pow2(n) as int, pow2(n) as int, 1);
}

// Proves: (2^a - 1) * 2^b + (2^b - 1) = 2^(a+b) - 1
pub proof fn lemma_pow2_geometric(a: nat, b: nat)
    ensures
        (pow2(a) - 1) * pow2(b) + (pow2(b) - 1) == pow2(a + b) - 1,
{
    lemma2_to64();
    lemma_pow2_adds(a, b);
    // (2^a - 1) * 2^b + (2^b - 1)
    // = 2^a * 2^b - 2^b + 2^b - 1
    // = 2^(a+b) - 1
    lemma_mul_is_distributive_sub(pow2(b) as int, pow2(a) as int, 1);
}

// Modular congruence preserves powers
pub proof fn lemma_pow_mod_congruent(a: int, b: int, n: nat, m: int)
    requires
        m > 0,
        a % m == b % m,
    ensures
        pow(a, n) % m == pow(b, n) % m,
{
    lemma_pow_mod_noop(a, n, m);
    lemma_pow_mod_noop(b, n, m);
}

/// Lemma: Powers of non-negative integers are always non-negative
///
/// For any non-negative integer base and natural number exponent n,
/// pow(base, n) >= 0.
///
/// This is a fundamental property: multiplying non-negative numbers
/// always yields non-negative results.
///
/// This lemma extends vstd's `lemma_pow_positive` to handle the case when base = 0.
pub proof fn lemma_pow_nonnegative(base: int, n: nat)
    requires
        base >= 0,
    ensures
        pow(base, n) >= 0,
{
    if base > 0 {
        // Delegate to vstd's lemma_pow_positive for the positive case
        lemma_pow_positive(base, n);
    } else {
        // base == 0 case
        if n == 0 {
            // pow(0, 0) == 1 >= 0
            lemma_pow0(0);
        } else {
            // pow(0, n) == 0 >= 0 for n > 0
            lemma0_pow(n);
        }
    }
}

/// Lemma: Modular exponentiation composition
///
/// Proves: ((x^a % m)^b % m) = (x^(a*b) % m)
///
/// This is essential for chaining power operations in modular arithmetic.
/// For example, in the invert proof we compute: (x^(2^250-1))^(2^5) = x^((2^250-1)*2^5)
pub proof fn lemma_pow_mod_composition(x: nat, a: nat, b: nat, m: nat)
    requires
        a > 0,
        b > 0,
        m > 0,
    ensures
        (pow(((pow(x as int, a) as nat) % m) as int, b) as nat) % m == (pow(x as int, a * b) as nat)
            % m,
{
    // =================================================================
    // PART 1: Core mathematical proof on int level
    // =================================================================
    // Prove: pow(pow(x, a) % m, b) % m == pow(pow(x, a), b) % m
    assert(pow(pow(x as int, a) % (m as int), b) % (m as int) == pow(pow(x as int, a), b) % (
    m as int)) by {
        lemma_pow_mod_noop(pow(x as int, a), b, m as int);
    }

    // Prove: pow(pow(x, a), b) == pow(x, a*b)
    assert(pow(pow(x as int, a), b) == pow(x as int, a * b)) by {
        lemma_pow_multiplies(x as int, a, b);
    }

    // Combining the above: pow(pow(x, a) % m, b) % m == pow(x, a*b) % m (on int level)

    // =================================================================
    // PART 2: Bridge int-level proof to nat-level postcondition
    // =================================================================
    // The mathematical proof is complete on the int level:
    //   pow(pow(x, a) % m, b) % m == pow(x, a*b) % m  (on int)
    //
    // To bridge to the nat-level postcondition, we prove int/nat modulo equivalence:
    //   For v >= 0, m > 0: v % (m as int) == ((v as nat) % m) as int

    // Bridge 1: pow(x, a) % m on int is same as ((pow(x, a) as nat) % m) as int
    assert(pow(x as int, a) % (m as int) == ((pow(x as int, a) as nat) % m) as int) by {
        assert(pow(x as int, a) >= 0) by {
            lemma_pow_nonnegative(x as int, a);
        }
        lemma_int_nat_mod_equiv(pow(x as int, a), m);
    }

    // Bridge 2: pow((pow(x, a) % m), b) % m
    let base_int = pow(x as int, a) % (m as int);
    assert(pow(base_int, b) % (m as int) == ((pow(base_int, b) as nat) % m) as int) by {
        assert(base_int >= 0) by {
            lemma_fundamental_div_mod(pow(x as int, a), m as int);
        }
        assert(pow(base_int, b) >= 0) by {
            lemma_pow_nonnegative(base_int, b);
        }
        lemma_int_nat_mod_equiv(pow(base_int, b), m);
    }

    // Bridge 3: pow(x, a*b) % m on int is same as ((pow(x, a*b) as nat) % m) as int
    assert(pow(x as int, a * b) % (m as int) == ((pow(x as int, a * b) as nat) % m) as int) by {
        assert(a * b > 0) by {
            assert(a >= 1 && b >= 1);
            assert(a * b >= 1) by (nonlinear_arith)
                requires
                    a >= 1,
                    b >= 1,
            ;
        }
        assert(pow(x as int, a * b) >= 0) by {
            lemma_pow_nonnegative(x as int, a * b);
        }
        lemma_int_nat_mod_equiv(pow(x as int, a * b), m);
    }

    // The int-level equality now carries over to the nat-level postcondition ✓
}

/// Lemma: Modular power addition
///
/// Proves that (x^a % m * x^b % m) % m == x^(a+b) % m
///
/// This lemma combines:
/// - Power addition: x^(a+b) = x^a * x^b (from lemma_pow_adds)
/// - Modular multiplication property (from lemma_mul_mod_noop_general)
/// - Int/nat modulo equivalence (via lemma_int_nat_mod_equiv)
pub proof fn lemma_modular_power_addition(x: nat, a: nat, b: nat, m: nat)
    requires
        a > 0,
        b > 0,
        m > 0,
    ensures
        ((pow(x as int, a) as nat) % m) * ((pow(x as int, b) as nat) % m) % m == (pow(
            x as int,
            a + b,
        ) as nat) % m,
{
    // =================================================================
    // PART 1: Core mathematical proof on int level
    // =================================================================
    // Prove: pow(x, a + b) == pow(x, a) * pow(x, b)
    assert(pow(x as int, a + b) == pow(x as int, a) * pow(x as int, b)) by {
        lemma_pow_adds(x as int, a, b);
    }

    // Prove: (pow(x, a) * pow(x, b)) % m == ((pow(x, a) % m) * (pow(x, b) % m)) % m
    assert((pow(x as int, a) * pow(x as int, b)) % (m as int) == ((pow(x as int, a) % (m as int))
        * (pow(x as int, b) % (m as int))) % (m as int)) by {
        lemma_mul_mod_noop_general(pow(x as int, a), pow(x as int, b), m as int);
    }

    // Combining the above: pow(x, a+b) % m == ((pow(x, a) % m) * (pow(x, b) % m)) % m (on int level)

    // =================================================================
    // PART 2: Bridge int-level proof to nat-level postcondition
    // =================================================================

    // Bridge 1: pow(x, a) % m on int is same as ((pow(x, a) as nat) % m) as int
    assert(pow(x as int, a) % (m as int) == ((pow(x as int, a) as nat) % m) as int) by {
        assert(pow(x as int, a) >= 0) by {
            lemma_pow_nonnegative(x as int, a);
        }
        lemma_int_nat_mod_equiv(pow(x as int, a), m);
    }

    // Bridge 2: pow(x, b) % m on int is same as ((pow(x, b) as nat) % m) as int
    assert(pow(x as int, b) % (m as int) == ((pow(x as int, b) as nat) % m) as int) by {
        assert(pow(x as int, b) >= 0) by {
            lemma_pow_nonnegative(x as int, b);
        }
        lemma_int_nat_mod_equiv(pow(x as int, b), m);
    }

    // Bridge 3: pow(x, a+b) % m on int is same as ((pow(x, a+b) as nat) % m) as int
    assert(pow(x as int, a + b) % (m as int) == ((pow(x as int, a + b) as nat) % m) as int) by {
        assert(pow(x as int, a + b) >= 0) by {
            lemma_pow_nonnegative(x as int, a + b);
        }
        lemma_int_nat_mod_equiv(pow(x as int, a + b), m);
    }

    // Bridge 4: The product (pow(x, a) % m) * (pow(x, b) % m) on int
    let pow_a_mod = pow(x as int, a) % (m as int);
    let pow_b_mod = pow(x as int, b) % (m as int);

    // Prove the product is non-negative
    assert(pow_a_mod >= 0) by {
        lemma_fundamental_div_mod(pow(x as int, a), m as int);
    }
    assert(pow_b_mod >= 0) by {
        lemma_fundamental_div_mod(pow(x as int, b), m as int);
    }
    assert(pow_a_mod * pow_b_mod >= 0) by (nonlinear_arith)
        requires
            pow_a_mod >= 0,
            pow_b_mod >= 0,
    ;

    // Bridge the product modulo
    assert((pow_a_mod * pow_b_mod) % (m as int) == (((pow_a_mod * pow_b_mod) as nat) % m) as int)
        by {
        lemma_int_nat_mod_equiv(pow_a_mod * pow_b_mod, m);
    }

    // The int-level equality now carries over to the nat-level postcondition ✓
}

pub proof fn lemma_pow2_distributivity_over_word(
    word: nat,
    byte0: nat,
    byte1: nat,
    byte2: nat,
    byte3: nat,
    byte4: nat,
    byte5: nat,
    byte6: nat,
    byte7: nat,
    exp: nat,
)
    requires
        word == byte0 * pow2(0) + byte1 * pow2(8) + byte2 * pow2(16) + byte3 * pow2(24) + byte4
            * pow2(32) + byte5 * pow2(40) + byte6 * pow2(48) + byte7 * pow2(56),
    ensures
        word * pow2(exp) == byte0 * pow2(exp) + byte1 * pow2(exp + 8) + byte2 * pow2(exp + 16)
            + byte3 * pow2(exp + 24) + byte4 * pow2(exp + 32) + byte5 * pow2(exp + 40) + byte6
            * pow2(exp + 48) + byte7 * pow2(exp + 56),
{
    // Step 1: Apply distributivity over the sum
    let x1 = (byte0 * pow2(0)) as int;
    let x2 = (byte1 * pow2(8)) as int;
    let x3 = (byte2 * pow2(16)) as int;
    let x4 = (byte3 * pow2(24)) as int;
    let x5 = (byte4 * pow2(32)) as int;
    let x6 = (byte5 * pow2(40)) as int;
    let x7 = (byte6 * pow2(48)) as int;
    let x8 = (byte7 * pow2(56)) as int;

    lemma_mul_distributive_8_terms(pow2(exp) as int, x1, x2, x3, x4, x5, x6, x7, x8);

    assert(word * pow2(exp) == byte0 * pow2(0) * pow2(exp) + byte1 * pow2(8) * pow2(exp) + byte2
        * pow2(16) * pow2(exp) + byte3 * pow2(24) * pow2(exp) + byte4 * pow2(32) * pow2(exp) + byte5
        * pow2(40) * pow2(exp) + byte6 * pow2(48) * pow2(exp) + byte7 * pow2(56) * pow2(exp));

    // Step 2: Simplify each term using pow2(a) * pow2(b) == pow2(a+b)
    lemma_pow2_adds(0, exp);
    lemma_mul_is_associative(byte0 as int, pow2(0) as int, pow2(exp) as int);
    assert(byte0 * pow2(0) * pow2(exp) == byte0 * pow2(exp));

    lemma_pow2_adds(8, exp);
    lemma_mul_is_associative(byte1 as int, pow2(8) as int, pow2(exp) as int);
    assert(byte1 * pow2(8) * pow2(exp) == byte1 * pow2(exp + 8));

    lemma_pow2_adds(16, exp);
    lemma_mul_is_associative(byte2 as int, pow2(16) as int, pow2(exp) as int);
    assert(byte2 * pow2(16) * pow2(exp) == byte2 * pow2(exp + 16));

    lemma_pow2_adds(24, exp);
    lemma_mul_is_associative(byte3 as int, pow2(24) as int, pow2(exp) as int);
    assert(byte3 * pow2(24) * pow2(exp) == byte3 * pow2(exp + 24));

    lemma_pow2_adds(32, exp);
    lemma_mul_is_associative(byte4 as int, pow2(32) as int, pow2(exp) as int);
    assert(byte4 * pow2(32) * pow2(exp) == byte4 * pow2(exp + 32));

    lemma_pow2_adds(40, exp);
    lemma_mul_is_associative(byte5 as int, pow2(40) as int, pow2(exp) as int);
    assert(byte5 * pow2(40) * pow2(exp) == byte5 * pow2(exp + 40));

    lemma_pow2_adds(48, exp);
    lemma_mul_is_associative(byte6 as int, pow2(48) as int, pow2(exp) as int);
    assert(byte6 * pow2(48) * pow2(exp) == byte6 * pow2(exp + 48));

    lemma_pow2_adds(56, exp);
    lemma_mul_is_associative(byte7 as int, pow2(56) as int, pow2(exp) as int);
    assert(byte7 * pow2(56) * pow2(exp) == byte7 * pow2(exp + 56));
}

} // verus!
