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
        k * b + b <= m,  // The chunk we're extracting is entirely below the modulo boundary
    ensures
        (x / pow2(k * b)) % pow2(b) == ((x % pow2(m)) / pow2(k * b)) % pow2(b),
{
    // Proof strategy:
    // 1. Decompose: x = (x / 2^m) * 2^m + (x % 2^m)
    // 2. Show: ((x / 2^m) * 2^m) / 2^(k*b) is a multiple of 2^b
    // 3. Use that multiples of 2^b vanish in % 2^b

    let kb = k * b;
    let x_mod_m = x % pow2(m);

    // Step 1: Decompose x using the division theorem
    lemma_pow2_pos(b);
    lemma_pow2_pos(m);
    lemma_fundamental_div_mod(x as int, pow2(m) as int);
    // lemma_fundamental_div_mod gives: x == pow2(m) * (x / pow2(m)) + (x % pow2(m))
    assert(x == pow2(m) * (x / pow2(m)) + x_mod_m);
    lemma_mul_is_commutative(pow2(m) as int, (x / pow2(m)) as int);
    assert(x == (x / pow2(m)) * pow2(m) + x_mod_m);

    // Step 2: Divide both sides by pow2(k*b)
    // x / pow2(k*b) = ((x / pow2(m)) * pow2(m)) / pow2(k*b) + (x % pow2(m)) / pow2(k*b)

    // Key fact: Since k*b + b <= m, we have m = k*b + (m - k*b) where (m - k*b) >= b
    let m_minus_kb = (m - kb) as nat;
    assert(m_minus_kb >= b);

    // Therefore: pow2(m) = pow2(k*b) * pow2(m - k*b)
    lemma_pow2_adds(kb, m_minus_kb);
    assert(pow2(m) == pow2(kb) * pow2(m_minus_kb));

    // Step 3: Show that pow2(m - k*b) is a multiple of 2^b (since m - k*b >= b)
    // pow2(m - k*b) = pow2(b) * pow2(m - k*b - b)
    assert(m_minus_kb >= b);
    let m_minus_kb_minus_b = (m_minus_kb - b) as nat;
    assert(m_minus_kb == b + m_minus_kb_minus_b);
    lemma_pow2_adds(b, m_minus_kb_minus_b);
    assert(pow2(m_minus_kb) == pow2(b) * pow2(m_minus_kb_minus_b));

    // Step 4: Calculate ((x / pow2(m)) * pow2(m)) / pow2(k*b)
    // = (x / pow2(m)) * (pow2(k*b) * pow2(m - k*b)) / pow2(k*b)
    // = (x / pow2(m)) * pow2(m - k*b)
    // = (x / pow2(m)) * pow2(b) * pow2(m - k*b - b)

    let high_part = (x / pow2(m)) * pow2(m);
    let low_part = x_mod_m;

    assert(x == high_part + low_part);

    // Divide the sum by pow2(k*b)
    lemma_pow2_pos(kb);

    // We need to show: (high_part / pow2(k*b)) % pow2(b) == 0
    // high_part / pow2(k*b) = (x / pow2(m)) * pow2(m) / pow2(k*b)
    //                       = (x / pow2(m)) * (pow2(k*b) * pow2(m_minus_kb)) / pow2(k*b)
    //                       = (x / pow2(m)) * pow2(m_minus_kb)

    // Prove high_part in factored form: high_part = pow2(kb) * ((x / pow2(m)) * pow2(m_minus_kb))
    lemma_mul_is_associative((x / pow2(m)) as int, pow2(kb) as int, pow2(m_minus_kb) as int);
    assert(high_part == ((x / pow2(m)) * pow2(kb)) * pow2(m_minus_kb));
    lemma_mul_is_commutative((x / pow2(m)) as int, pow2(kb) as int);
    lemma_mul_is_associative(pow2(kb) as int, (x / pow2(m)) as int, pow2(m_minus_kb) as int);
    let q = (x / pow2(m)) * pow2(m_minus_kb);
    assert(high_part == pow2(kb) * q);

    // high_part / pow2(k*b) = (x / pow2(m)) * pow2(m_minus_kb) = q
    assert(high_part / pow2(kb) == q) by {
        // Use: (d * q) / d == q when d > 0
        assert((pow2(kb) * q) / pow2(kb) == q) by (nonlinear_arith)
            requires pow2(kb) > 0;
        assert(high_part / pow2(kb) == q);
    }
    assert(high_part / pow2(kb) == (x / pow2(m)) * pow2(m_minus_kb));

    // Now: (x / pow2(m)) * pow2(m_minus_kb) = (x / pow2(m)) * pow2(b) * pow2(m_minus_kb_minus_b)
    lemma_mul_is_associative((x / pow2(m)) as int, pow2(b) as int, pow2(m_minus_kb_minus_b) as int);
    // We have: q = (x / pow2(m)) * pow2(m_minus_kb) = (x / pow2(m)) * (pow2(b) * pow2(m_minus_kb_minus_b))
    //           = ((x / pow2(m)) * pow2(b)) * pow2(m_minus_kb_minus_b)
    assert(q == ((x / pow2(m)) * pow2(b)) * pow2(m_minus_kb_minus_b)) by {
        assert(pow2(m_minus_kb) == pow2(b) * pow2(m_minus_kb_minus_b));
        assert(q == (x / pow2(m)) * pow2(m_minus_kb));
        assert((x / pow2(m)) * pow2(m_minus_kb) == (x / pow2(m)) * (pow2(b) * pow2(m_minus_kb_minus_b)));
    }
    lemma_mul_is_associative((x / pow2(m)) as int, pow2(b) as int, pow2(m_minus_kb_minus_b) as int);
    lemma_mul_is_commutative((x / pow2(m)) as int, pow2(b) as int);
    lemma_mul_is_associative(pow2(b) as int, (x / pow2(m)) as int, pow2(m_minus_kb_minus_b) as int);
    assert(q == pow2(b) * ((x / pow2(m)) * pow2(m_minus_kb_minus_b)));

    // So: (high_part / pow2(k*b)) % pow2(b) == 0
    let high_part_shifted = high_part / pow2(kb);
    assert(high_part_shifted == q);
    assert(high_part_shifted == pow2(b) * ((x / pow2(m)) * pow2(m_minus_kb_minus_b)));

    // This is pow2(b) * something, so its mod pow2(b) is 0
    lemma_mod_multiples_vanish((x / pow2(m)) * pow2(m_minus_kb_minus_b) as int, 0, pow2(b) as int);
    assert(high_part_shifted % pow2(b) == 0);

    // Step 5: Show that high_part is exactly divisible by pow2(k*b)
    // We have: high_part = (x / pow2(m)) * pow2(m) = (x / pow2(m)) * pow2(kb) * pow2(m_minus_kb)
    // So: high_part % pow2(kb) == 0
    assert(high_part % pow2(kb) == 0) by {
        // We proved above that: high_part == pow2(kb) * ((x / pow2(m)) * pow2(m_minus_kb))
        assert(high_part == pow2(kb) * ((x / pow2(m)) * pow2(m_minus_kb)));

        // This is pow2(kb) * something, so mod pow2(kb) is 0
        lemma_mod_multiples_vanish((x / pow2(m)) * pow2(m_minus_kb) as int, 0, pow2(kb) as int);
        assert((pow2(kb) * ((x / pow2(m)) * pow2(m_minus_kb))) % pow2(kb) == 0);
        assert(high_part % pow2(kb) == 0);
    }

    // Step 6: Show that when high_part is divisible by pow2(kb), we can split the division
    // We need: (high_part + low_part) / pow2(kb) = high_part / pow2(kb) + low_part / pow2(kb) (with proper handling of remainder)

    // Since high_part / pow2(kb) = j, we can write:
    // x / pow2(kb) = (j * pow2(kb) + low_part) / pow2(kb)

    let j = high_part / pow2(kb);
    assert(high_part == j * pow2(kb)) by {
        lemma_fundamental_div_mod(high_part as int, pow2(kb) as int);
        assert(high_part == pow2(kb) * j + (high_part % pow2(kb)));
        assert(high_part % pow2(kb) == 0);
        assert(high_part == pow2(kb) * j);
        lemma_mul_is_commutative(pow2(kb) as int, j as int);
    }

    // Now use lemma_hoist_over_denominator: low_part / pow2(kb) + j == (low_part + j * pow2(kb)) / pow2(kb)
    lemma_hoist_over_denominator(low_part as int, j as int, pow2(kb));
    assert((low_part + j * pow2(kb)) / pow2(kb) == low_part / pow2(kb) + j);

    // We have: x = high_part + low_part = j * pow2(kb) + low_part = low_part + j * pow2(kb)
    assert(x == low_part + j * pow2(kb));
    assert(x / pow2(kb) == low_part / pow2(kb) + j);

    // Step 7: Take mod pow2(b) of both sides
    // (x / pow2(kb)) % pow2(b) = (low_part / pow2(kb) + j) % pow2(b)
    assert((x / pow2(kb)) % pow2(b) == (low_part / pow2(kb) + j) % pow2(b));

    // We know j is a multiple of pow2(b)
    assert(j == (x / pow2(m)) * pow2(b) * pow2(m_minus_kb_minus_b));
    assert(j % pow2(b) == 0) by {
        lemma_mod_multiples_vanish((x / pow2(m)) * pow2(m_minus_kb_minus_b) as int, 0, pow2(b) as int);
    }

    // Use lemma_add_mod_noop: (a + b) % m = (a % m + b % m) % m
    lemma_pow2_pos(b);
    lemma_add_mod_noop((low_part / pow2(kb)) as int, j as int, pow2(b) as int);
    assert((low_part / pow2(kb) + j) % pow2(b) == ((low_part / pow2(kb)) % pow2(b) + j % pow2(b)) % pow2(b));
    assert((low_part / pow2(kb) + j) % pow2(b) == ((low_part / pow2(kb)) % pow2(b) + 0) % pow2(b));

    // (a % m + 0) % m = a % m
    lemma_mod_twice((low_part / pow2(kb)) as int, pow2(b) as int);
    assert((low_part / pow2(kb) + j) % pow2(b) == (low_part / pow2(kb)) % pow2(b));

    // Step 8: Conclude
    // (x / pow2(kb)) % pow2(b) = (low_part / pow2(kb)) % pow2(b)
    // And low_part = x % pow2(m)
    assert((x / pow2(kb)) % pow2(b) == (low_part / pow2(kb)) % pow2(b));
    assert(low_part == x % pow2(m));
    assert((x / pow2(k * b)) % pow2(b) == ((x % pow2(m)) / pow2(k * b)) % pow2(b));
}

pub proof fn lemma_u8_cast_is_mod_256(x: u64)
    ensures
        (x as u8) == (x as nat) % 256
{
    assert(x as nat % 256 == x % 256);
    assert((x as u8) == x % 256) by (bit_vector);
}

fn main() {}

}
