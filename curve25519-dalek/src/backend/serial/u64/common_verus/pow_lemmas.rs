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

verus! {

pub proof fn u8_lt_pow2_8(a: u8)
    ensures
        a < pow2(8),
{
    assert(u8::MAX < pow2(8)) by {
        lemma2_to64();
    }
}

// Auxiliary lemma for exponentiation
pub proof fn pow2_le_max64(k: nat)
    requires
        k < 64,
    ensures
        pow2(k) <= u64::MAX,
{
    lemma2_to64();
    lemma2_to64_rest();
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

pub proof fn pow2_mul_general(a: nat, s: nat, k: nat)
    requires
        a < pow2(s),
    ensures
        pow2(k) * a <= pow2(k + s) - pow2(k),
        a * pow2(k) <= pow2(k + s) - pow2(k),
        pow2(k + s) - pow2(k) < pow2(k + s),
{
    assert(a <= pow2(s) - 1);  // x < y <=> x <= y - 1

    mul_le(a as nat, (pow2(s) - 1) as nat, pow2(k), pow2(k));
    assert((pow2(s) - 1) * pow2(k) == pow2(k + s) - pow2(k)) by {
        lemma_mul_is_distributive_sub(pow2(k) as int, pow2(s) as int, 1);
        lemma_pow2_adds(k, s);
    }

    lemma_mul_is_commutative(a as int, pow2(k) as int);

    assert(pow2(k) > 0) by {
        lemma_pow2_pos(k);
    }
}

pub proof fn pow2_mul_u8(a: u8, k: nat)
    ensures
        pow2(k) * a <= pow2(k + 8) - pow2(k),
        a * pow2(k) <= pow2(k + 8) - pow2(k),
        pow2(k + 8) - pow2(k) < pow2(k + 8),
{
    assert(a < pow2(8)) by {
        lemma2_to64();
    }

    pow2_mul_general(a as nat, 8, k);
}

pub proof fn sum_div_decomposition(a: nat, b: nat, s: nat, k: nat)
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
        sum_mod_decomposition(a, b, s, k);
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

pub proof fn sum_mod_decomposition(a: nat, b: nat, s: nat, k: nat)
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
            mask_pow2(b, s, k);
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
                    pow2_mul_general(z, d, s);
                }
            }

            lemma_small_mod(x + z * ps, pk);
        }
    }
}

pub proof fn u8_times_pow2_mod_is_id(a: u8, k: nat, s: nat)
    requires
        k + 8 <= s,
    ensures
        (pow2(k) * a) as nat % pow2(s) == pow2(k) * a,
{
    assert(pow2(k) * a < pow2(k + 8)) by {
        pow2_mul_u8(a, k);
    }
    if (k + 8 < s) {
        assert(pow2(k + 8) < pow2(s)) by {
            lemma_pow2_strictly_increases(k + 8, s);
        }
    }
    assert(pow2(s) > 0) by {
        lemma_pow2_pos(s);
    }

    assert((pow2(k) * a) as nat % pow2(s) == pow2(k) * a) by {
        lemma_small_mod((pow2(k) * a) as nat, pow2(s));
    }
}

pub proof fn u8_times_pow2_fits_u64(a: u8, k: nat)
    requires
        k <= 56,
    ensures
        (a as u64) * pow2(k) <= u64::MAX,
{
    assert((a as u64) * pow2(k) <= (a as u64) * pow2(56)) by {
        assert(pow2(k) <= pow2(56)) by {
            if (k < 56) {
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
        k <= s,
    ensures
        (x * pow2(k)) % pow2(s) == (x % pow2((s - k) as nat)) * pow2(k),
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

pub proof fn mask_div2(x: nat, k: nat, s: nat)
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
            sum_div_decomposition(x_mod_pd, x_div_pd, d, k);
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
        // satisfies conditions for sum_mod_decomposition
        assert((ps * x_div_pd + x_mod_pd / pk) % ps == (ps * x_div_pd) % ps + (x_mod_pd / pk) % ps)
            by {
            sum_mod_decomposition(x_mod_pd / pk, x_div_pd, s, s);
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

pub proof fn pow2_mul_DIV(x: nat, k: nat, s: nat)
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

pub proof fn pow2_MUL_div_MOD(x: nat, px: nat, k: nat, s: nat, t: nat)
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
        mask_pow2(x, d, t);
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

pub proof fn pow2_MUL_div_MOD_u8(x: u8, k: nat, s: nat, t: nat)
    requires
        s <= k,
        8 + k - s <= t,
    ensures
        ((x as nat * pow2(k)) / pow2(s)) % pow2(t) == x as nat * pow2((k - s) as nat),
{
    assert(x < pow2(8)) by {
        lemma2_to64();  // pow2(8)
    }
    pow2_MUL_div_MOD(x as nat, 8, k, s, t);
}

pub proof fn pow2_mul_DIV_MOD(x: nat, px: nat, k: nat, s: nat, t: nat)
    requires
        x < pow2(px),
        k <= s,
        px <= t + s - k,
    ensures
        ((x * pow2(k)) / pow2(s)) % pow2(t) == x / pow2((s - k) as nat),
{
    let d = (s - k) as nat;

    assert((x * pow2(k)) / pow2(s) == x / pow2(d)) by {
        pow2_mul_DIV(x, k, s);
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

pub proof fn pow2_mul_DIV_MOD_u8(x: u8, k: nat, s: nat, t: nat)
    requires
        k <= s,
        8 <= t + s - k,
    ensures
        ((x as nat * pow2(k)) / pow2(s)) % pow2(t) == x as nat / pow2((s - k) as nat),
{
    assert(x < pow2(8)) by {
        lemma2_to64();  // pow2(8)
    }
    pow2_mul_DIV_MOD(x as nat, 8, k, s, t);
}

pub proof fn pow2_MUL_div_Mod(x: nat, px: nat, k: nat, s: nat, t: nat)
    requires
        x < pow2(px),
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
        mask_pow2(x, d, t);
    }
}

pub proof fn pow2_MUL_div_Mod_u8(x: u8, k: nat, s: nat, t: nat)
    requires
        s <= k,
        k - s <= t,
    ensures
        ((x as nat * pow2(k)) / pow2(s)) % pow2(t) == (x as nat % pow2((t - (k - s)) as nat) * pow2(
            (k - s) as nat,
        )),
{
    assert(x < pow2(8)) by {
        lemma2_to64();  // pow2(8)
    }
    pow2_MUL_div_Mod(x as nat, 8, k, s, t);
}

pub proof fn pow2_MUL_div_mod(x: nat, px: nat, k: nat, s: nat, t: nat)
    requires
        x < pow2(px),
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

pub proof fn pow2_MUL_div_mod_u8(x: u8, k: nat, s: nat, t: nat)
    requires
        s <= k,
        t <= k - s,
    ensures
        ((x as nat * pow2(k)) / pow2(s)) % pow2(t) == 0,
{
    assert(x < pow2(8)) by {
        lemma2_to64();  // pow2(8)
    }
    pow2_MUL_div_mod(x as nat, 8, k, s, t);
}

pub proof fn div_pow2_preserves_decomposition(a: u64, b: u64, s: nat, k: nat)
    requires
        a < pow2(s),
        a + b * pow2(s) <= u64::MAX,
        k <= s < 64,
    ensures
        (a as nat) / pow2(k) < pow2((s - k) as nat),
        (b * pow2(s)) as nat / pow2(k) == b * pow2((s - k) as nat),
        (a as nat) / pow2(k) + b * pow2((s - k) as nat) <= u64::MAX,
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
        mask_div2(x, k * b, b); 
    }

    let y = x % pow2(m);

    assert((y / pow2(k * b)) % pow2(b) == (y % pow2(k * b + b)) / pow2(k * b)) by {
        mask_div2(x, k * b, b);
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

pub open spec fn pow2_sum(coefs: &[u8], offset: nat, step: nat, k: nat) -> nat
    decreases k,
{
    if (k == 0) {
        coefs[offset as int] as nat * pow2(0)
    } else {
        // k > 0
        pow2_sum(coefs, offset, step, (k - 1) as nat) + coefs[(offset + k) as int] as nat * pow2(
            k * step,
        )
    }
}

pub proof fn pow2_sum_bounds(coefs: &[u8], offset: nat, step: nat, k: nat)
    requires
        offset + k <= coefs.len(),
        forall|i: nat| 0 <= i <= k ==> #[trigger] coefs[(offset + i) as int] < pow2(step),
    ensures
        pow2_sum(coefs, offset, step, k) < pow2((k + 1) * step),
    decreases k,
{
    if (k == 0) {
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(coefs[offset as int] * pow2(0) == coefs[offset as int]) by {
            lemma_mul_basics_3(coefs[offset as int] as int);
        }
    } else {
        assert(pow2_sum(coefs, offset, step, k) == pow2_sum(coefs, offset, step, (k - 1) as nat)
            + coefs[(offset + k) as int] * pow2(k * step)) by {
            reveal_with_fuel(pow2_sum, 1);
        }

        assert(pow2_sum(coefs, offset, step, (k - 1) as nat) < pow2(k * step)) by {
            pow2_sum_bounds(coefs, offset, step, (k - 1) as nat);
        }

        assert(coefs[(offset + k) as int] * pow2(k * step) <= pow2((k + 1) * step) - pow2(k * step))
            by {
            assert((k + 1) * step == k * step + step) by {
                lemma_mul_is_distributive_add_other_way(step as int, k as int, 1);
            }
            assert(coefs[(offset + k) as int] * pow2(k * step) <= pow2(k * step + step) - pow2(
                k * step,
            )) by {
                pow2_mul_general(coefs[(offset + k) as int] as nat, step, k * step);
            }
        }
    }
}

fn main() {
}

} // verus!
