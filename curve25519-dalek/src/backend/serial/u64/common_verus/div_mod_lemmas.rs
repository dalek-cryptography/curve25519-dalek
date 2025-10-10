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
/// Lemma: Uniqueness of quotient in division
/// If value = q * d + r with 0 <= r < d, then value / d = q
///
/// This establishes that the quotient in the fundamental div/mod theorem is unique.
pub proof fn lemma_div_quotient_unique(value: int, d: int, q: int, r: int)
    requires
        d > 0,
        value == q * d + r,
        0 <= r < d,
    ensures
        value / d == q,
{
    use vstd::arithmetic::mul::*;

    // Use fundamental division theorem
    lemma_fundamental_div_mod(value, d);
    lemma_mod_bound(value, d);

    let q_actual = value / d;
    let r_actual = value % d;

    // From fundamental theorem, we get the relationship (but stated with multiplication on the left)
    assert(value == d * q_actual + r_actual);
    assert(0 <= r_actual < d);

    // Convert to multiplication on the right for easier comparison
    assert(d * q_actual == q_actual * d) by { lemma_mul_is_commutative(d, q_actual); }
    assert(value == q_actual * d + r_actual);

    // From given: value = q * d + r where 0 <= r < d
    assert(value == q * d + r);

    // Therefore: q * d + r = q_actual * d + r_actual
    assert(q * d + r == q_actual * d + r_actual);

    // Rearrange: q * d = q_actual * d + (r_actual - r)
    assert(q * d == q_actual * d + (r_actual - r));

    // Factor out d: d * q = d * q_actual + (r_actual - r)
    assert(d * q == q * d) by { lemma_mul_is_commutative(d, q); }
    assert(d * q_actual == q_actual * d) by { lemma_mul_is_commutative(d, q_actual); }
    assert(d * q == d * q_actual + (r_actual - r));

    // Therefore: d * (q - q_actual) = r_actual - r
    assert(d * (q - q_actual) == r_actual - r) by {
        lemma_mul_is_distributive_sub(d, q, q_actual);
    }

    // Key insight: Since both r and r_actual are in [0, d), their difference is in (-d, d)
    // But d * (q - q_actual) must be a multiple of d
    // The only multiple of d in the range (-d, d) is 0
    // Therefore: d * (q - q_actual) = 0, which means q = q_actual

    if q != q_actual {
        // If q != q_actual, then |q - q_actual| >= 1
        let diff = q - q_actual;
        assert(diff != 0);

        // Therefore |d * (q - q_actual)| >= d
        if diff > 0 {
            assert(diff >= 1);
            lemma_mul_left_inequality(d, 1, diff);
            assert(d * diff >= d);
            assert(d * (q - q_actual) >= d);
        } else {
            assert(diff <= -1);
            lemma_mul_inequality(diff, -1, d);
            assert(d * diff <= -d);
            assert(d * (q - q_actual) <= -d);
        }

        // But we know: d * (q - q_actual) = r_actual - r
        // And: -d < r_actual - r < d
        // Because 0 <= r_actual < d and 0 <= r < d
        assert(-d < r_actual - r < d);

        // This is a contradiction: d * (q - q_actual) cannot be both >= d (or <= -d) and in (-d, d)
        assert(false);
    }

    assert(q == q_actual);
}

/// Lemma: For x < d, x % d = x
/// This is a fundamental property of modulo for values less than the divisor.
pub proof fn lemma_mod_of_less_than_divisor(x: int, d: int)
    requires
        d > 0,
        0 <= x < d,
    ensures
        x % d == x,
{
    use vstd::arithmetic::mul::*;

    // Use fundamental div-mod: x = (x/d) * d + (x%d)
    lemma_fundamental_div_mod(x, d);

    // Get the quotient and remainder
    let q = x / d;
    let r = x % d;

    // From fundamental div-mod: x = d * q + r (note the order)
    assert(x == d * q + r);
    // Convert to: x = q * d + r
    assert(d * q == q * d) by { lemma_mul_is_commutative(d, q); }
    assert(x == q * d + r);

    // We know 0 <= r < d from modulo properties
    lemma_mod_bound(x, d);
    assert(0 <= r < d);

    // Since 0 <= x < d and x = q * d + r with 0 <= r < d:
    // If q >= 1, then q * d >= d, so x >= d, which contradicts x < d
    // If q <= -1, then q * d <= -d, so x <= -d + r < 0, which contradicts x >= 0
    // Therefore q = 0

    if q >= 1 {
        lemma_mul_left_inequality(d, 1, q);
        assert(d * q >= d);
        assert(q * d >= d) by { lemma_mul_is_commutative(q, d); }
        assert(x >= d);
        assert(false); // Contradiction with x < d
    }

    if q <= -1 {
        lemma_mul_inequality(q, -1, d);
        assert(d * q <= -d);
        assert(q * d <= -d) by { lemma_mul_is_commutative(q, d); }
        assert(x == q * d + r <= -d + r);
        assert(r < d);
        assert(x < 0);
        assert(false); // Contradiction with x >= 0
    }

    assert(q == 0);

    // Therefore: x = 0 * d + r = r
    assert(0 * d == 0) by (compute);
    assert(x == q * d + r);
    assert(x == 0 * d + r);
    assert(x == 0 + r);
    assert(x == r);
    assert(r == x % d);
    assert(x == x % d);
}

fn main() {}

}
