#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::pow_lemmas::*;

verus! {

// Proofs express the fundamental div/mod theorem with >> and &
macro_rules! lemma_div_and_mod {
    ($name:ident, $pow_le_max:ident, $shr_is_div:ident, $mask_is_mod:ident, $uN:ty) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(ai: $uN, bi: $uN, v: $uN, k: nat)
            requires
                k < <$uN>::BITS,
                ai == v >> k,
                bi == v & (low_bits_mask(k) as $uN),
            ensures
                ai == v / (pow2(k) as $uN),
                bi == v % (pow2(k) as $uN),
                v == ai * pow2(k) + bi,
        {
            assert(0 < pow2(k) <= <$uN>::MAX) by {
                lemma_pow2_pos(k);
                $pow_le_max(k)
            }

            assert(ai == v / (pow2(k) as $uN)) by {
                $shr_is_div(v, k as $uN);
            }

            // v & low_bits_mask(k) = v % pow2(k);
            assert(bi == v % (pow2(k) as $uN)) by {
                $mask_is_mod(v, k);
            }

            assert(v == pow2(k) * (v as nat / pow2(k)) + v as nat % pow2(k)) by {
                lemma_fundamental_div_mod(v as int, pow2(k) as int);
            }

            lemma_mul_is_commutative(ai as int, pow2(k) as int);
        }
    }
    };
}

lemma_div_and_mod!(lemma_u8_div_and_mod, lemma_u8_pow2_le_max, lemma_u8_shr_is_div, lemma_u8_low_bits_mask_is_mod, u8);

lemma_div_and_mod!(lemma_u16_div_and_mod, lemma_u16_pow2_le_max, lemma_u16_shr_is_div, lemma_u16_low_bits_mask_is_mod, u16);

lemma_div_and_mod!(lemma_u32_div_and_mod, lemma_u32_pow2_le_max, lemma_u32_shr_is_div, lemma_u32_low_bits_mask_is_mod, u32);

lemma_div_and_mod!(lemma_u64_div_and_mod, lemma_u64_pow2_le_max, lemma_u64_shr_is_div, lemma_u64_low_bits_mask_is_mod, u64);

// TODO: missing VSTD lemmas for u128
// lemma_div_and_mod!(lemma_u128_div_and_mod, lemma_u128_pow2_le_max, lemma_u128_shr_is_div, lemma_u128_low_bits_mask_is_mod, u128);
// Combination of mod lemmas, (b +- a * m) % m = b % m
pub proof fn lemma_mod_sum_factor(a: int, b: int, m: int)
    requires
        m > 0,
    ensures
        (a * m + b) % m == b % m,
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
        (b - a * m) % m == b % m,
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
        (a % k) + (b % k) < k  // also implies k != 0
        ,
    ensures
        (a + b) / k == a / k + b / k,
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

/// Helper lemma: if a * b <= c and b > 0, then a <= c / b
pub proof fn lemma_mul_le_implies_div_le(a: nat, b: nat, c: nat)
    requires
        b > 0,
        a * b <= c,
    ensures
        a <= c / b,
{
    lemma_div_is_ordered((a * b) as int, c as int, b as int);
    lemma_div_by_multiple(a as int, b as int);
}

// Proofs that downcasting is the same as taking a mod
macro_rules! lemma_cast_is_mod {
    ($name:ident, $uM:ty, $uN:ty, $maxPlusOne:expr) => {
        #[cfg(verus_keep_ghost)]
        verus! {
        #[doc = "TODO"]
        pub proof fn $name(x: $uM)
            requires
                <$uM>::BITS > <$uN>::BITS
            ensures
                (x as $uN) == (x as nat) % $maxPlusOne,
        {
            assert(x as nat % $maxPlusOne == x % $maxPlusOne);
            assert((x as $uN) == x % $maxPlusOne) by (bit_vector);
        }
    }
    };
}

lemma_cast_is_mod!(lemma_u128_cast_u8_is_mod, u128, u8, 0x100);

lemma_cast_is_mod!(lemma_u64_cast_u8_is_mod, u64, u8, 0x100);

lemma_cast_is_mod!(lemma_u32_cast_u8_is_mod, u32, u8, 0x100);

lemma_cast_is_mod!(lemma_u16_cast_u8_is_mod, u16, u8, 0x100);

lemma_cast_is_mod!(lemma_u128_cast_u16_is_mod, u128, u16, 0x10000);

lemma_cast_is_mod!(lemma_u64_cast_u16_is_mod, u64, u16, 0x10000);

lemma_cast_is_mod!(lemma_u32_cast_u16_is_mod, u32, u16, 0x10000);

lemma_cast_is_mod!(lemma_u128_cast_u32_is_mod, u128, u32, 0x100000000);

lemma_cast_is_mod!(lemma_u64_cast_u32_is_mod, u64, u32, 0x100000000);

lemma_cast_is_mod!(lemma_u128_cast_64_is_mod, u128, u64, 0x10000000000000000);

/// Helper: Sum of two numbers both divisible by d is divisible by d
///
/// Mathematical property: Closure of divisibility under addition
/// If d | a and d | b, then d | (a + b)
pub proof fn lemma_mod_sum_both_divisible(a: nat, b: nat, d: nat)
    requires
        d > 0,
        a % d == 0,
        b % d == 0,
    ensures
        (a + b) % d == 0,
{
    // Since a % d == 0 and b % d == 0, we have (0 + 0) % d == (a + b) % d
    assert((a + b) % d == 0) by {
        lemma_add_mod_noop(a as int, b as int, d as int);
        assert((0 + 0) % d == 0) by (nonlinear_arith)
            requires
                d > 0,
        ;
    }
}

/// Helper: Divisibility factorization
///
/// If n is divisible by (a·b), then (n/a) is divisible by b.
///
/// Mathematical property: Divisibility distribution across division
pub proof fn lemma_divisibility_factor(n: nat, a: nat, b: nat)
    requires
        n % (a * b) == 0,
        a > 0,
        b > 0,
    ensures
        (n / a) % b == 0,
{
    // Use lemma_mod_breakdown: n % (a * b) = a * ((n / a) % b) + n % a
    // Since n % (a * b) == 0: 0 = a * ((n / a) % b) + n % a
    // Both terms are non-negative and sum to 0, so both must be 0
    assert((n / a) % b == 0) by {
        lemma_mod_breakdown(n as int, a as int, b as int);
        let qb = (n / a) % b;
        let ra = n % a;
        assert(0 == a * qb + ra);
        assert(qb >= 0);
        assert(ra >= 0);
        assert(a * qb == 0);
        assert(qb == 0) by (nonlinear_arith)
            requires
                a > 0,
                qb >= 0,
                a * qb == 0,
        ;
    }
}

/// Lemma: int modulo and nat modulo are equivalent for non-negative values
///
/// For v >= 0 and m > 0, computing v % m gives the same result whether
/// we use int modulo or nat modulo operations.
///
/// This bridges the type-level gap between `int % int` and `nat % nat`.
pub proof fn lemma_int_nat_mod_equiv(v: int, m: nat)
    requires
        v >= 0,
        m > 0,
    ensures
        v % (m as int) == ((v as nat) % m) as int,
{
    let v_nat = v as nat;
    let r_nat = v_nat % m;
    let q_nat = v_nat / m;

    assert(v_nat == q_nat * m + r_nat) by {
        lemma_fundamental_div_mod(v, m as int);
    }

    lemma_fundamental_div_mod_converse_mod(v, m as int, q_nat as int, r_nat as int);
}

/// Multiplication distributes with modular negation: a * (-b mod m) ≡ -(a*b) (mod m)
///
/// This is the unsigned representation version, where -x is encoded as (m - x % m).
/// Key insight: a * (-b) = -(a*b) in integer arithmetic.
pub proof fn lemma_mul_distributes_over_neg_mod(a: nat, b: nat, m: nat)
    requires
        m > 1,
    ensures
        (a * ((m - b % m) as nat)) % m == ((m - (a * b) % m) as nat) % m,
{
    let b_mod = b % m;
    let neg_b: nat = (m - b_mod) as nat;
    let ab_mod = (a * b) % m;
    let neg_ab: nat = (m - ab_mod) as nat;

    // Step 1: (m - b_mod) ≡ -b_mod (mod m)
    assert((neg_b as int) % (m as int) == (-(b_mod as int)) % (m as int)) by {
        lemma_mod_add_multiples_vanish(-(b_mod as int), m as int);
    };

    // Step 2: a * (m - b_mod) ≡ a * (-b_mod) (mod m)
    assert(((a as int) * (neg_b as int)) % (m as int) == ((a as int) * (-(b_mod as int))) % (
    m as int)) by {
        lemma_mul_mod_noop_right(a as int, neg_b as int, m as int);
        lemma_mul_mod_noop_right(a as int, -(b_mod as int), m as int);
    };

    // Step 3: a * (-b_mod) = -(a * b_mod) in integer arithmetic
    assert((a as int) * (-(b_mod as int)) == -((a as int) * (b_mod as int))) by (nonlinear_arith);

    // Step 4: (a * b_mod) % m == (a * b) % m [mod absorption]
    assert((a * b_mod) % m == ab_mod) by {
        lemma_mul_mod_noop_right(a as int, b as int, m as int);
    };

    // Step 5: -(a*b_mod) ≡ -(ab_mod) (mod m)
    assert((-(a as int * b_mod as int)) % (m as int) == (-(ab_mod as int)) % (m as int)) by {
        lemma_sub_mod_noop(0int, (a * b_mod) as int, m as int);
    };

    // Step 6: -(ab_mod) ≡ (m - ab_mod) (mod m)
    assert((-(ab_mod as int)) % (m as int) == (neg_ab as int) % (m as int)) by {
        lemma_mod_add_multiples_vanish(-(ab_mod as int), m as int);
    };
}

/// Double negation in modular arithmetic: -(-x) ≡ x (mod m)
///
/// For x with 0 ≤ x < m: (m - (m - x)) % m = x
pub proof fn lemma_double_neg_mod(x: nat, m: nat)
    requires
        m > 1,
        x < m,
    ensures
        ((m - ((m - x) as nat) % m) as nat) % m == x,
{
    // (m - x) < m since 0 ≤ x < m implies 0 < m - x ≤ m
    // Actually m - x could be m when x = 0, so (m - x) % m handles that
    let neg_x = (m - x) as nat;

    if x == 0 {
        // neg_x = m, so neg_x % m = 0
        assert(neg_x % m == 0) by {
            lemma_mod_self_0(m as int);
        };
        // (m - 0) % m = m % m = 0 = x
        assert(((m - 0nat) as nat) % m == 0);
    } else {
        // 0 < x < m, so 0 < m - x < m, so (m - x) % m = m - x
        assert(neg_x < m);
        assert(neg_x % m == neg_x) by {
            lemma_small_mod(neg_x, m);
        };
        // (m - neg_x) = (m - (m - x)) = x
        assert((m - neg_x) as nat == x);
        assert(((m - neg_x) as nat) % m == x) by {
            lemma_small_mod(x, m);
        };
    }
}

/// Multiplication by (m-1) is negation modulo m: a*(m-1) % m = (m - a%m) % m
///
/// Proof: a*(m-1) = a*m - a ≡ 0 - a ≡ m - a%m (mod m)
///
/// This is useful for proving that multiplying by -1 (represented as m-1 in
/// unsigned arithmetic) produces the additive inverse modulo m.
pub proof fn lemma_mul_by_minus_one_is_negation(a: nat, m: nat)
    requires
        m > 0,
    ensures
        (a * ((m - 1) as nat)) % m == ((m - a % m) as nat) % m,
{
    let a_mod = a % m;
    let m_minus_1: nat = (m - 1) as nat;
    let neg_a: nat = (m - a_mod) as nat;

    // Step 1: a * (m-1) = a*m - a [distributive]
    assert(a * m_minus_1 == a * m - a) by {
        lemma_mul_is_distributive_sub(a as int, m as int, 1int);
    };

    // Step 2: (a*m) % m = 0
    assert((a * m) % m == 0) by {
        lemma_mod_multiples_basic(a as int, m as int);
    };

    // Step 3: (a*m - a) % m = (0 - a_mod) % m [by sub_mod_noop]
    assert(((a * m) as int - a as int) % (m as int) == (0int - a_mod as int) % (m as int)) by {
        lemma_sub_mod_noop((a * m) as int, a as int, m as int);
    };

    // Step 4: (0 - a_mod) % m = (m - a_mod) % m [add m to get positive representative]
    assert((0int - a_mod as int) % (m as int) == (m as int - a_mod as int) % (m as int)) by {
        lemma_mod_add_multiples_vanish(-(a_mod as int), m as int);
    };

    // Step 5: Connect int form to nat form
    assert((m as int - a_mod as int) % (m as int) == (neg_a as int) % (m as int));

    // Step 6: Show a*m >= a (so subtraction is non-negative)
    assert((a as int) * (m as int) >= a as int) by {
        lemma_mul_inequality(1int, m as int, a as int);
        lemma_mul_is_commutative(1int, a as int);
        lemma_mul_is_commutative(m as int, a as int);
    };

    // Step 7: Connect nat % nat form
    assert((a * m_minus_1) as int == (a as int) * (m as int) - (a as int));
    assert((a * m_minus_1) as int >= 0);
    assert((a * m_minus_1) % m == neg_a % m);
}

/// If a ≡ b (mod m), then (a + c) ≡ (b + c) (mod m)
///
/// This is a fundamental property of modular congruence: adding the same
/// value to both sides preserves the congruence.
///
/// Proof: By lemma_add_mod_noop, (x + y) % m == (x % m + y % m) % m
/// Since a % m == b % m, both (a + c) % m and (b + c) % m equal
/// ((a % m) + (c % m)) % m.
pub proof fn lemma_mod_add_eq(a: int, b: int, c: int, m: int)
    requires
        m > 0,
        a % m == b % m,
    ensures
        (a + c) % m == (b + c) % m,
{
    lemma_add_mod_noop(a, c, m);
    lemma_add_mod_noop(b, c, m);
}

} // verus!
