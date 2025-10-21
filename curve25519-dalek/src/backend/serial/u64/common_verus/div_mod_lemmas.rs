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
    // Use fundamental division theorem
    lemma_fundamental_div_mod(value, d);
    lemma_mod_bound(value, d);

    let q_actual = value / d;
    let r_actual = value % d;

    // From fundamental theorem, we get the relationship (but stated with multiplication on the left)

    // Convert to multiplication on the right for easier comparison
    assert(d * q_actual == q_actual * d) by { lemma_mul_is_commutative(d, q_actual); }
    assert(d * q == q * d) by { lemma_mul_is_commutative(d, q); }
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

        // Therefore |d * (q - q_actual)| >= d
        if diff > 0 {
            lemma_mul_left_inequality(d, 1, diff);
        } else {
            lemma_mul_inequality(diff, -1, d);
        }
    }

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
    // Use fundamental div-mod: x = (x/d) * d + (x%d)
    lemma_fundamental_div_mod(x, d);

    // Get the quotient and remainder
    let q = x / d;
    let r = x % d;

    // From fundamental div-mod: x = d * q + r (note the order)
    // Convert to: x = q * d + r
    assert(d * q == q * d) by { lemma_mul_is_commutative(d, q); }

    // We know 0 <= r < d from modulo properties
    lemma_mod_bound(x, d);

    // Since 0 <= x < d and x = q * d + r with 0 <= r < d:
    // If q >= 1, then q * d >= d, so x >= d, which contradicts x < d
    // If q <= -1, then q * d <= -d, so x <= -d + r < 0, which contradicts x >= 0
    // Therefore q = 0

    if q >= 1 {
        lemma_mul_left_inequality(d, 1, q);
    }

    if q <= -1 {
        lemma_mul_inequality(q, -1, d);
    }


    // Therefore: x = 0 * d + r = r
    assert(x == 0 * d + r);
}


/// Helper lemma: Division with strict upper bound
/// If x < a * b and a > 0, then x / a < b
pub proof fn lemma_div_strictly_bounded(x: int, a: int, b: int)
    requires
        a > 0,
        b >= 0,
        x < a * b,
    ensures
        x / a < b,
{
   // (b * a) / a == b
   lemma_div_by_multiple(b, a);
   // x < b * a && a > 0 => x / a < (b * a) / a
   lemma_div_by_multiple_is_strongly_ordered(x, a * b, b, a);
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

/// Helper lemma: if a * b <= c and b > 0, then a <= c / b
pub proof fn lemma_mul_le_implies_div_le(a: nat, b: nat, c: nat)
    requires
        b > 0,
        a * b <= c,
    ensures
        a <= c / b,
{
    // Proof by contradiction: assume a > c / b
    if a > c / b {
        // From fundamental div/mod: c = b * (c / b) + (c % b)
        lemma_fundamental_div_mod(c as int, b as int);
        let q = c / b;
        let r = c % b;

        // We know: 0 <= r < b
        lemma_mod_bound(c as int, b as int);

        // From a > q, we have a >= q + 1 (since both are natural numbers)
        // Therefore: a * b >= (q + 1) * b = q * b + b
        assert(a * b >= (q + 1) * b) by (nonlinear_arith)
            requires a >= q + 1, b > 0;
        assert((q + 1) * b == q * b + b) by (nonlinear_arith);
    }
}

fn main() {}

}
