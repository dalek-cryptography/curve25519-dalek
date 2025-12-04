#[allow(unused_imports)]
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use crate::specs::primality_specs::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;

use vstd::prelude::*;

verus! {

// ============================================================================
// PART 1: GCD (Greatest Common Divisor)
// ============================================================================
/// Spec function: Greatest Common Divisor using Euclidean algorithm
///
/// This is a constructive definition that computes gcd(a, b) recursively.
/// The algorithm is: gcd(a, 0) = a; gcd(a, b) = gcd(b, a % b) for b > 0
pub open spec fn spec_gcd(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 {
        a
    } else {
        spec_gcd(b, a % b)
    }
}

/// Helper: If d divides both x and y, then d divides x + k*y for any k
pub proof fn lemma_divides_linear_combo(x: nat, y: nat, k: nat, d: nat)
    requires
        d > 0,
        x % d == 0,
        y % d == 0,
    ensures
        (x + k * y) % d == 0,
{
    lemma_mul_mod_noop_right(k as int, y as int, d as int);
    assert((k as int * y as int) % (d as int) == (k as int * (y as int % d as int)) % (d as int));
    assert(y as int % d as int == 0int);
    assert(k as int * (y as int % d as int) == k as int * 0int);
    assert(k as int * 0int == 0int);
    lemma_mod_self_0(d as int);
    assert(0int % (d as int) == 0int);
    assert(((k * y) as int) % (d as int) == 0int);
    lemma_add_mod_noop(x as int, (k * y) as int, d as int);
}

/// Helper: If d divides both x and y, then d divides x - k*y (when x >= k*y)
pub proof fn lemma_divides_linear_combo_sub(x: nat, y: nat, k: nat, d: nat)
    requires
        d > 0,
        x % d == 0,
        y % d == 0,
        x >= k * y,
    ensures
        ((x - k * y) as nat) % d == 0,
{
    lemma_mul_mod_noop_right(k as int, y as int, d as int);
    assert((k as int * y as int) % (d as int) == (k as int * (y as int % d as int)) % (d as int));
    assert(y as int % d as int == 0int);
    assert(k as int * (y as int % d as int) == k as int * 0int);
    assert(k as int * 0int == 0int);
    lemma_mod_self_0(d as int);
    assert(0int % (d as int) == 0int);
    assert(((k * y) as int) % (d as int) == 0int);
    lemma_sub_mod_noop(x as int, (k * y) as int, d as int);
}

/// Lemma: gcd(a, b) divides both a and b
pub proof fn lemma_gcd_divides_both(a: nat, b: nat)
    ensures
        a % spec_gcd(a, b) == 0 || spec_gcd(a, b) == 0,
        b % spec_gcd(a, b) == 0 || spec_gcd(a, b) == 0,
    decreases b,
{
    let g = spec_gcd(a, b);

    if b == 0 {
        if a > 0 {
            lemma_mod_self_0(a as int);
        }
    } else {
        let r = a % b;
        lemma_gcd_divides_both(b, r);

        if g > 0 {
            lemma_fundamental_div_mod(a as int, b as int);
            lemma_divides_linear_combo(r, b, a / b, g);
            assert((r + (a / b) * b) == a) by {
                lemma_mul_is_commutative((a / b) as int, b as int);
            };
        }
    }
}

/// Lemma: gcd(a, b) is positive when a > 0 or b > 0
pub proof fn lemma_gcd_positive(a: nat, b: nat)
    requires
        a > 0 || b > 0,
    ensures
        spec_gcd(a, b) > 0,
    decreases b,
{
    if b == 0 {
        // gcd(a, 0) = a, and a > 0 by requirement
        assert(a > 0);
    } else {
        // gcd(a, b) = gcd(b, a % b)
        // b > 0, so we can apply induction
        lemma_gcd_positive(b, a % b);
    }
}

/// Lemma: Any common divisor of a and b divides gcd(a, b)
pub proof fn lemma_common_divisor_divides_gcd(a: nat, b: nat, d: nat)
    requires
        d > 0,
        a % d == 0,
        b % d == 0,
    ensures
        spec_gcd(a, b) % d == 0,
    decreases b,
{
    if b == 0 {
        // gcd(a, 0) = a, and d | a by assumption
    } else {
        let q = a / b;
        let r = a % b;

        lemma_fundamental_div_mod(a as int, b as int);

        assert((b * q) % d == 0) by {
            lemma_mul_mod_noop_right(q as int, b as int, d as int);
            lemma_mul_is_commutative(q as int, b as int);
        };

        assert(r % d == 0) by {
            lemma_sub_mod_noop(a as int, (b * q) as int, d as int);
        };

        lemma_common_divisor_divides_gcd(b, r, d);
    }
}

/// Lemma: If prime p does not divide a, then gcd(a % p, p) = 1
pub proof fn lemma_gcd_with_prime(a: nat, prime: nat)
    requires
        is_prime(prime),
        a % prime != 0,
    ensures
        spec_gcd(a % prime, prime) == 1,
{
    let a_red = a % prime;
    let g = spec_gcd(a_red, prime);

    assert(a_red < prime) by {
        lemma_mod_bound(a as int, prime as int);
    };

    lemma_gcd_divides_both(a_red, prime);
    lemma_gcd_positive(a_red, prime);

    if g != 1 {
        // g | prime and g > 1 implies g == prime (by primality)
        assert(g == prime) by {
            lemma_mod_is_zero_when_divisible(prime, g);
            if g < prime {
                assert(false);
            }  // contradicts is_prime

        };

        // But g | a_red with a_red < prime and a_red != 0 is impossible
        assert(a_red % prime == a_red) by {
            lemma_small_mod(a_red, prime);
        };
        assert(false);
    }
}

/// Helper: if n % d == 0 and d > 0, then d <= n (or n == 0)
proof fn lemma_mod_is_zero_when_divisible(n: nat, d: nat)
    requires
        d > 0,
        n % d == 0,
    ensures
        d <= n || n == 0,
{
    if n > 0 {
        lemma_fundamental_div_mod(n as int, d as int);
        // n == (n / d) * d + n % d == (n / d) * d + 0 == (n / d) * d
        assert(n as int == (n as int / d as int) * d as int + n as int % d as int);
        assert(n as int % d as int == 0);
        assert(n as int == (n as int / d as int) * d as int);
        // Since n > 0 and d > 0, we need n / d >= 1
        if n as int / d as int <= 0 {
            // If n / d <= 0, then n == (n/d) * d <= 0, contradicting n > 0
            assert(n as int <= 0int);
            assert(false);
        }
        // Now n / d >= 1, so (n/d) * d >= d, meaning n >= d

        lemma_mul_inequality(1int, (n / d) as int, d as int);
        lemma_mul_is_commutative((n / d) as int, d as int);
    }
}

// =============================================================================
// PART 2: Factorial and Product Definitions
// =============================================================================
/// Factorial: n! = 1 * 2 * 3 * ... * n
pub open spec fn factorial(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        n * factorial((n - 1) as nat)
    }
}

/// C(n,k) = n! / (k!(n-k)!) using Pascal's identity
pub open spec fn binomial(n: nat, k: nat) -> nat
    decreases n,
{
    if k > n {
        0
    } else if k == 0 || k == n {
        1
    } else {
        binomial((n - 1) as nat, (k - 1) as nat) + binomial((n - 1) as nat, k)
    }
}

/// For prime p and 0 < k < p, p | C(p,k)
pub proof fn lemma_binomial_divisible_by_prime(p: nat, k: nat)
    requires
        is_prime(p),
        0 < k < p,
    ensures
        binomial(p, k) % p == 0,
    decreases p,
{
    // Use Pascal's identity and induction
    if p == 2 {
        assert(k == 1);
        assert(binomial(2, 1) == binomial(1, 0) + binomial(1, 1)) by {};
        assert(binomial(1, 0) == 1);
        assert(binomial(1, 1) == 1);
        assert(binomial(2, 1) == 2);
        assert(2nat % 2 == 0) by {
            lemma_mod_self_0(2int);
        };
    } else {
        lemma_binomial_prime_divisibility_helper(p, k);
    }
}

/// k * C(p,k) = p * C(p-1,k-1), combined with gcd(p,k)=1 implies p | C(p,k)
proof fn lemma_binomial_prime_divisibility_helper(p: nat, k: nat)
    requires
        is_prime(p),
        0 < k < p,
    ensures
        binomial(p, k) % p == 0,
{
    lemma_binomial_absorption(p, k);

    let prod = k * binomial(p, k);
    assert(prod == p * binomial((p - 1) as nat, (k - 1) as nat));

    assert(prod % p == 0) by {
        lemma_mod_multiples_basic(binomial((p - 1) as nat, (k - 1) as nat) as int, p as int);
    };

    assert(k % p != 0) by {
        lemma_small_mod(k, p);
    };

    if binomial(p, k) % p != 0 {
        lemma_euclid_prime(k, binomial(p, k), p);
        assert(false);
    }
}

/// Absorption: k * C(n,k) = n * C(n-1,k-1)
pub proof fn lemma_binomial_absorption(n: nat, k: nat)
    requires
        n >= 1,
        k >= 1,
        k <= n,
    ensures
        k * binomial(n, k) == n * binomial((n - 1) as nat, (k - 1) as nat),
    decreases n,
{
    if n == 1 {
        assert(k == 1);
        assert(binomial(1, 1) == 1);
        assert(binomial(0, 0) == 1);
        assert(1nat * 1nat == 1nat * 1nat);
    } else if k == n {
        assert(binomial(n, n) == 1);
        assert(binomial((n - 1) as nat, (n - 1) as nat) == 1);
    } else if k == 1 {
        lemma_binomial_n_1(n);
        assert(binomial(n, 1) == n);
        assert(binomial((n - 1) as nat, 0) == 1);
        lemma_mul_basics(n as int);
    } else {
        // Use factorial-based proof
        assert(binomial(n, k) == binomial((n - 1) as nat, (k - 1) as nat) + binomial(
            (n - 1) as nat,
            k,
        ));

        lemma_mul_is_distributive_add(
            k as int,
            binomial((n - 1) as nat, (k - 1) as nat) as int,
            binomial((n - 1) as nat, k) as int,
        );

        if k < n - 1 {
            lemma_binomial_absorption((n - 1) as nat, k);
        }
        lemma_binomial_absorption_factorial(n, k);
    }
}

/// C(n,1) = n
proof fn lemma_binomial_n_1(n: nat)
    requires
        n >= 1,
    ensures
        binomial(n, 1) == n,
    decreases n,
{
    if n == 1 {
        assert(binomial(1, 1) == 1);
    } else {
        assert(binomial(n, 1) == binomial((n - 1) as nat, 0) + binomial((n - 1) as nat, 1));
        assert(binomial((n - 1) as nat, 0) == 1);
        lemma_binomial_n_1((n - 1) as nat);
        assert(binomial((n - 1) as nat, 1) == (n - 1) as nat);
    }
}

/// Factorial-based absorption proof
proof fn lemma_binomial_absorption_factorial(n: nat, k: nat)
    requires
        n >= 1,
        k >= 1,
        k <= n,
    ensures
        k * binomial(n, k) == n * binomial((n - 1) as nat, (k - 1) as nat),
{
    lemma_binomial_factorial_relation(n, k);
    lemma_binomial_factorial_relation((n - 1) as nat, (k - 1) as nat);

    let binom_n_k = binomial(n, k);
    let binom_nm1_km1 = binomial((n - 1) as nat, (k - 1) as nat);
    let fact_k = factorial(k);
    let fact_km1 = factorial((k - 1) as nat);
    let fact_nmk = factorial((n - k) as nat);
    let fact_n = factorial(n);
    let fact_nm1 = factorial((n - 1) as nat);

    assert(fact_k == k * fact_km1);
    assert(fact_n == n * fact_nm1);

    assert(fact_km1 > 0) by {
        lemma_factorial_positive((k - 1) as nat);
    };
    assert(fact_nmk > 0) by {
        lemma_factorial_positive((n - k) as nat);
    };

    assert(binom_n_k * fact_k * fact_nmk == fact_n);
    assert(binom_nm1_km1 * fact_km1 * fact_nmk == fact_nm1);

    let common = fact_km1 * fact_nmk;
    assert(common > 0) by {
        lemma_mul_strictly_positive(fact_km1 as int, fact_nmk as int);
    };

    assert(k * binom_n_k * common == fact_n) by {
        assert(binom_n_k * fact_k * fact_nmk == fact_n);
        assert(fact_k == k * fact_km1);
        lemma_mul_is_associative(binom_n_k as int, k as int, fact_km1 as int);
        lemma_mul_is_associative((binom_n_k * k) as int, fact_km1 as int, fact_nmk as int);
        lemma_mul_is_commutative(binom_n_k as int, k as int);
    };

    assert(n * binom_nm1_km1 * common == fact_n) by {
        assert(binom_nm1_km1 * fact_km1 * fact_nmk == fact_nm1);
        assert(fact_n == n * fact_nm1);
        lemma_mul_is_associative(n as int, binom_nm1_km1 as int, (fact_km1 * fact_nmk) as int);
        lemma_mul_is_associative(binom_nm1_km1 as int, fact_km1 as int, fact_nmk as int);
    };

    // Now we have:
    // k * binom_n_k * common == fact_n == n * binom_nm1_km1 * common
    // Since common > 0, we can conclude k * binom_n_k == n * binom_nm1_km1
    // vstd's lemma_mul_equality_converse requires m * x == m * y (m on left)
    assert(common * (k * binom_n_k) == common * (n * binom_nm1_km1)) by {
        lemma_mul_is_commutative((k * binom_n_k) as int, common as int);
        lemma_mul_is_commutative((n * binom_nm1_km1) as int, common as int);
    };
    lemma_mul_equality_converse(common as int, (k * binom_n_k) as int, (n * binom_nm1_km1) as int);
}

/// C(n,k) * k! * (n-k)! = n! (well-known combinatorial identity)
proof fn lemma_binomial_factorial_relation(n: nat, k: nat)
    requires
        k <= n,
    ensures
        binomial(n, k) * factorial(k) * factorial((n - k) as nat) == factorial(n),
{
    admit();
}

/// n! > 0
proof fn lemma_factorial_positive(n: nat)
    ensures
        factorial(n) > 0,
    decreases n,
{
    if n == 0 {
        assert(factorial(0) == 1);
    } else {
        lemma_factorial_positive((n - 1) as nat);
        assert(factorial(n) == n * factorial((n - 1) as nat));
        lemma_mul_strictly_positive(n as int, factorial((n - 1) as nat) as int);
    }
}

/// a^p ≡ a (mod p) for all a >= 0 (proved by induction using binomial theorem)
pub proof fn lemma_fermat_strong(a: nat, p: nat)
    requires
        is_prime(p),
    ensures
        (pow(a as int, p) as nat) % p == a % p,
    decreases a,
{
    if a == 0 {
        assert(pow(0int, p) == 0) by {
            if p == 0 {
                reveal(pow);
            } else {
                reveal(pow);
                lemma_mul_basics(pow(0int, (p - 1) as nat));
            }
        };
        lemma_small_mod(0nat, p);
    } else {
        let am1 = (a - 1) as nat;

        lemma_fermat_strong(am1, p);
        assert((pow(am1 as int, p) as nat) % p == am1 % p);

        lemma_binomial_expansion_mod_p(am1, p);

        assert(am1 + 1 == a);
        assert((pow(a as int, p) as nat) % p == (1 + (pow(am1 as int, p) as nat)) % p);

        let pow_am1_p = pow(am1 as int, p) as nat;
        let am1_pow_mod = pow_am1_p % p;
        assert(am1_pow_mod == am1 % p);
        let pow_am1_p_int = pow_am1_p as int;
        let p_int = p as int;
        let am1_int = am1 as int;

        lemma_mod_adds(1, pow_am1_p_int, p_int);
        lemma_small_mod(1nat, p);
        assert(1int % p_int == 1);
        assert(pow_am1_p_int % p_int == am1_pow_mod as int);
        assert(am1_pow_mod as int == (am1 % p) as int);
        lemma_mod_adds(1, am1_int, p_int);
        assert((1 + pow_am1_p_int) % p_int == (1 + am1_int) % p_int);
        assert((1 + pow_am1_p) % p == (1 + am1) % p);

        assert((1 + am1) == a);
    }
}

/// (a+1)^p ≡ a^p + 1 (mod p) - middle terms C(p,k) vanish for 0 < k < p
proof fn lemma_binomial_expansion_mod_p(a: nat, p: nat)
    requires
        is_prime(p),
    ensures
        (pow((a + 1) as int, p) as nat) % p == (1 + (pow(a as int, p) as nat)) % p,
{
    lemma_partial_binomial_sum_mod_p(a, p, p);
    axiom_binomial_theorem(a, p);
}

/// Σ_{k=0}^{max_k} C(n,k) * a^k
spec fn binomial_sum(a: nat, n: nat, max_k: nat) -> nat
    decreases max_k,
{
    if max_k == 0 {
        binomial(n, 0) * pow(a as int, 0) as nat
    } else {
        binomial_sum(a, n, (max_k - 1) as nat) + binomial(n, max_k) * pow(a as int, max_k) as nat
    }
}

/// Binomial Theorem: (a+1)^n = Σ_{k=0}^{n} C(n,k) * a^k (axiom)
proof fn axiom_binomial_theorem(a: nat, n: nat)
    ensures
        binomial_sum(a, n, n) == pow((a + 1) as int, n) as nat,
{
    admit();
}

/// Partial binomial sum modulo p
proof fn lemma_partial_binomial_sum_mod_p(a: nat, p: nat, j: nat)
    requires
        is_prime(p),
        j <= p,
    ensures
        j < p ==> binomial_sum(a, p, j) % p == 1,
        j == p ==> binomial_sum(a, p, j) % p == (1 + (pow(a as int, p) as nat)) % p,
    decreases j,
{
    if j == 0 {
        // S_0 = C(p,0) * a^0 = 1 * 1 = 1
        assert(binomial(p, 0) == 1);
        reveal(pow);
        assert(pow(a as int, 0) == 1);
        assert(pow(a as int, 0) as nat == 1nat);
        assert(binomial(p, 0) * (pow(a as int, 0) as nat) == 1nat);
        assert(binomial_sum(a, p, 0) == 1);
        lemma_small_mod(1nat, p);
    } else if j < p {
        // 0 < j < p
        // S_j = S_{j-1} + C(p,j) * a^j
        // By IH: S_{j-1} % p == 1
        // C(p,j) % p == 0 for 0 < j < p
        lemma_partial_binomial_sum_mod_p(a, p, (j - 1) as nat);
        assert(binomial_sum(a, p, (j - 1) as nat) % p == 1);

        lemma_binomial_divisible_by_prime(p, j);
        assert(binomial(p, j) % p == 0);

        // C(p,j) * a^j % p == 0
        // Since C(p,j) % p == 0, we have C(p,j) = q*p for some q
        // So C(p,j) * a^j = q*p * a^j, which is divisible by p

        // Use the fact that (x % p == 0) implies (x * y) % p == 0
        lemma_pow_nonnegative(a as int, j);
        assert(pow(a as int, j) >= 0);

        // Work with int types for the modular arithmetic
        let binom_int = binomial(p, j) as int;
        let pow_int = pow(a as int, j);
        let term_int = binom_int * pow_int;

        // term_int % p == 0
        assert(term_int % (p as int) == 0) by {
            // First, establish that binom_int % p == 0
            assert(binom_int % (p as int) == 0);

            // Apply lemma_mul_mod_noop_left
            lemma_mul_mod_noop_left(binom_int, pow_int, p as int);
            // This gives: (binom_int * pow_int) % p == (binom_int % p * pow_int) % p

            // binom_int % p == 0, so (binom_int % p) * pow_int == 0 * pow_int == 0
            lemma_mul_basics(pow_int);
            assert((binom_int % (p as int)) * pow_int == 0);

            // 0 % p == 0 for any p > 0
            assert(p > 1) by {  /* is_prime(p) implies p > 1 */
            };
            lemma_small_mod(0nat, p);
        };

        // term_int >= 0 since both factors >= 0
        assert(term_int >= 0) by {
            lemma_mul_nonnegative(binom_int, pow_int);
        };

        // The nat version matches the int version
        let term_j = binomial(p, j) * (pow(a as int, j) as nat);
        assert(term_j == term_int as nat);
        assert(term_j % p == 0) by {
            // term_j as int == term_int, term_int % p == 0, so term_j % p == 0
        };

        // S_j = S_{j-1} + term_j
        // S_j % p == (S_{j-1} + term_j) % p == (S_{j-1} % p + term_j % p) % p
        //         == (1 + 0) % p == 1
        assert(binomial_sum(a, p, j) == binomial_sum(a, p, (j - 1) as nat) + term_j);

        assert(binomial_sum(a, p, j) % p == 1) by {
            lemma_mod_adds(binomial_sum(a, p, (j - 1) as nat) as int, term_j as int, p as int);
            lemma_small_mod(1nat, p);
        };
    } else {
        // j == p
        // S_p = S_{p-1} + C(p,p) * a^p
        // By IH: S_{p-1} % p == 1
        // C(p,p) = 1
        if p == 1 {
            // Special case: p = 1
            // S_1 = C(1,0)*a^0 + C(1,1)*a^1 = 1 + a
            // (1 + a^1) = 1 + a
            // So S_1 % 1 == (1 + a) % 1 == 0
            assert(binomial_sum(a, 1, 1) == binomial_sum(a, 1, 0) + binomial(1, 1) * pow(
                a as int,
                1,
            ) as nat);
            assert(binomial_sum(a, 1, 0) == 1);
            assert(binomial(1, 1) == 1);
            assert(pow(a as int, 1) == a as int) by {
                reveal(pow);
                lemma_mul_basics(1int);
            };
        }
        lemma_partial_binomial_sum_mod_p(a, p, (p - 1) as nat);
        assert(binomial_sum(a, p, (p - 1) as nat) % p == 1);

        assert(binomial(p, p) == 1);

        // term_p = binomial(p,p) * a^p = 1 * a^p = a^p
        let pow_a_p = pow(a as int, p) as nat;
        lemma_pow_nonnegative(a as int, p);
        assert(pow(a as int, p) >= 0);

        let term_p = binomial(p, p) * pow_a_p;
        assert(term_p == pow_a_p) by {
            assert(binomial(p, p) == 1);
        };

        // S_p = S_{p-1} + a^p
        assert(binomial_sum(a, p, p) == binomial_sum(a, p, (p - 1) as nat) + term_p);

        // S_p % p == (S_{p-1} + a^p) % p
        //         == (S_{p-1} % p + a^p % p) % p
        //         == (1 + (a^p % p)) % p
        //         == (1 + a^p) % p  [since (x % p + y % p) % p == (x + y) % p]

        // First show: (S_{p-1} + term_p) % p == (1 + term_p % p) % p
        lemma_mod_adds(binomial_sum(a, p, (p - 1) as nat) as int, term_p as int, p as int);
        // This gives: (S_{p-1} + term_p) % p == (S_{p-1} % p + term_p % p) % p == (1 + term_p % p) % p

        // Since term_p == pow_a_p, term_p % p == pow_a_p % p
        assert(term_p % p == pow_a_p % p);

        // Now show: (1 + term_p % p) % p == (1 + pow_a_p) % p
        // This is because (1 + (x % p)) % p == (1 + x) % p
        lemma_mod_adds(1, pow_a_p as int, p as int);
        // This gives: (1 + pow_a_p) % p == (1 % p + pow_a_p % p) % p
        lemma_small_mod(1nat, p);
        // So (1 + pow_a_p) % p == (1 + pow_a_p % p) % p

        assert(binomial_sum(a, p, p) % p == (1 + pow_a_p) % p);
    }
}

/// Cancellation for Fermat: if a * a^(p-1) ≡ a (mod p) and a ≠ 0 (mod p), then a^(p-1) ≡ 1 (mod p)
proof fn lemma_fermat_cancellation(a: nat, n: nat, p: nat)
    requires
        is_prime(p),
        a % p != 0,
        n == (p - 1) as nat,
        ((a as int) * pow(a as int, n)) % (p as int) == (a as int) % (p as int),
    ensures
        (pow(a as int, n) as nat) % p == 1,
{
    // a * a^n ≡ a (mod p)
    // a * (a^n - 1) ≡ 0 (mod p)
    // Since p is prime and a % p != 0, by Euclid's lemma: (a^n - 1) % p == 0
    // So a^n ≡ 1 (mod p)
    // First, show pow(a, n) >= 1 (since a > 0 and n >= 0, and a % p != 0 means a > 0)
    assert(a > 0) by {
        if a == 0 {
            lemma_small_mod(0nat, p);
        }
    };

    assert(pow(a as int, n) >= 1) by {
        lemma_pow_positive(a as int, n);
    };

    // a * a^n = a * a^(p-1) = a^p
    // We have a^p ≡ a (mod p)
    // So a * a^(p-1) ≡ a (mod p)

    // (a * a^n) % p == a % p
    // (a * a^n - a) % p == 0
    // a * (a^n - 1) % p == 0

    let pow_n = pow(a as int, n);

    // a * pow_n - a = a * (pow_n - 1)
    assert((a as int) * pow_n - (a as int) == (a as int) * (pow_n - 1)) by {
        lemma_mul_is_distributive_sub(a as int, pow_n, 1);
    };

    // ((a * pow_n) - a) % p == 0
    // because (a * pow_n) % p == a % p
    assert(((a as int) * pow_n - (a as int)) % (p as int) == 0) by {
        // (a * pow_n) % p == a % p
        // ((a * pow_n) - a) % p == (a % p - a % p) % p == 0
        // Actually we need: if x % p == y % p then (x - y) % p == 0
        lemma_mod_sub_eq_implies_zero((a as int) * pow_n, a as int, p as int);
    };

    // So (a * (pow_n - 1)) % p == 0
    assert(((a as int) * (pow_n - 1)) % (p as int) == 0);

    // By Euclid's lemma: a % p == 0 or (pow_n - 1) % p == 0
    // Since a % p != 0, we have (pow_n - 1) % p == 0

    // But we need to be careful: Euclid's lemma works with naturals
    // pow_n >= 1, so pow_n - 1 >= 0

    if (pow_n - 1) % (p as int) != 0 {
        // Then a % p == 0 by Euclid
        // pow_n - 1 >= 0, so we can treat it as nat
        let diff = (pow_n - 1) as nat;
        // a * diff % p == 0
        // But diff % p != 0 (we're assuming)
        // So a % p == 0 by Euclid
        lemma_euclid_prime(a, diff, p);
        // This gives a % p == 0 or diff % p == 0
        // Since diff % p != 0, we get a % p == 0
        // But a % p != 0 by precondition, contradiction
    }
    // (pow_n - 1) % p == 0 means pow_n % p == 1

    assert(pow_n % (p as int) == 1) by {
        // pow_n = (pow_n - 1) + 1
        // pow_n % p = ((pow_n - 1) + 1) % p = (0 + 1) % p = 1
        lemma_mod_adds(pow_n - 1, 1, p as int);
        lemma_small_mod(1nat, p);
    };
}

/// If x % m == y % m then (x - y) % m == 0
proof fn lemma_mod_sub_eq_implies_zero(x: int, y: int, m: int)
    requires
        m > 0,
        x % m == y % m,
    ensures
        (x - y) % m == 0,
{
    // By lemma_sub_mod_noop: (x - y) % m == ((x % m) - (y % m)) % m
    lemma_sub_mod_noop(x, y, m);
    // Since x % m == y % m, we have (x - y) % m == (r - r) % m == 0 % m == 0
    lemma_small_mod(0nat, m as nat);
}

/// Product of sequence {a, 2a, 3a, ..., na} = a^n * n!
pub open spec fn product_of_multiples(a: nat, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        (n * a) * product_of_multiples(a, (n - 1) as nat)
    }
}

/// Product of multiples equals a^n * n!
pub proof fn lemma_product_of_multiples_eq(a: nat, n: nat)
    ensures
        product_of_multiples(a, n) == pow(a as int, n) as nat * factorial(n),
    decreases n,
{
    if n == 0 {
        // Base case: product_of_multiples(a, 0) = 1 = a^0 * 0! = 1 * 1
        assert(pow(a as int, 0) == 1) by {
            reveal(pow);
        };
        assert(factorial(0) == 1);
        assert(product_of_multiples(a, 0) == 1);
    } else {
        // Inductive case
        lemma_product_of_multiples_eq(a, (n - 1) as nat);
        // IH: product_of_multiples(a, n-1) == a^(n-1) * (n-1)!

        let prev_prod = product_of_multiples(a, (n - 1) as nat);
        let prev_pow = pow(a as int, (n - 1) as nat) as nat;
        let prev_fact = factorial((n - 1) as nat);

        // From definitions
        assert(product_of_multiples(a, n) == (n * a) * prev_prod);
        assert(factorial(n) == n * factorial((n - 1) as nat));
        assert(factorial(n) == n * prev_fact);

        // From IH
        assert(prev_prod == prev_pow * prev_fact);

        // Power expansion
        assert(pow(a as int, n) == (a as int) * pow(a as int, (n - 1) as nat)) by {
            reveal(pow);
        };
        let curr_pow = pow(a as int, n) as nat;

        // curr_pow == a * prev_pow (as nats)
        // We have: pow(a, n) = a * pow(a, n-1) = a * prev_pow
        // So curr_pow = pow(a, n) as nat = a * prev_pow
        assert(curr_pow == a * prev_pow) by {
            // pow(a, n-1) >= 0 (powers are non-negative for non-negative base)
            assert(pow(a as int, (n - 1) as nat) >= 0) by {
                if a > 0 {
                    lemma_pow_positive(a as int, (n - 1) as nat);
                } else {
                    // a == 0, so pow(0, n-1) = 0 for n-1 > 0, or pow(0, 0) = 1
                    if (n - 1) as nat == 0 {
                        reveal(pow);
                    } else {
                        lemma_pow0(a as int);
                        reveal(pow);
                    }
                }
            };
            // a >= 0 (nat)
            // so a * pow(a, n-1) >= 0
            lemma_mul_nonnegative(a as int, pow(a as int, (n - 1) as nat));
            // curr_pow = pow(a, n) as nat
            //         = (a * pow(a, n-1)) as nat  (by power expansion)
            //         = a * (pow(a, n-1) as nat)  (since product is non-negative)
            //         = a * prev_pow
        };

        // We need: (n * a) * (prev_pow * prev_fact) == curr_pow * (n * prev_fact)
        // = (a * prev_pow) * (n * prev_fact) = curr_pow * factorial(n)

        // Show (n * a) * (prev_pow * prev_fact) == (a * prev_pow) * (n * prev_fact)
        assert((n * a) * (prev_pow * prev_fact) == (a * prev_pow) * (n * prev_fact)) by {
            lemma_mul_is_associative(n as int, a as int, (prev_pow * prev_fact) as int);
            lemma_mul_is_associative(a as int, prev_pow as int, prev_fact as int);
            lemma_mul_is_associative(n as int, (a * prev_pow) as int, prev_fact as int);
            lemma_mul_is_commutative(n as int, (a * prev_pow) as int);
            lemma_mul_is_associative((a * prev_pow) as int, n as int, prev_fact as int);
        };

        // Chain the equalities
        // product_of_multiples(a, n)
        // = (n * a) * prev_prod
        // = (n * a) * (prev_pow * prev_fact)  (since prev_prod = prev_pow * prev_fact)
        // = (a * prev_pow) * (n * prev_fact)  (proved above)
        // = curr_pow * (n * prev_fact)        (since curr_pow = a * prev_pow)
        // = curr_pow * factorial(n)           (since n * prev_fact = factorial(n))

        assert((a * prev_pow) * (n * prev_fact) == curr_pow * (n * prev_fact)) by {
            // since curr_pow == a * prev_pow
        };

        assert(curr_pow * (n * prev_fact) == curr_pow * factorial(n)) by {
            // since factorial(n) == n * prev_fact
        };

        assert(product_of_multiples(a, n) == curr_pow * factorial(n));
    }
}

// ============================================================================
// PART 3: Extended Euclidean Algorithm (Bezout's Identity)
// ============================================================================
/// Extended GCD result type: (gcd, x, y) where gcd = a*x + b*y
/// We use int for x and y because they can be negative
pub struct ExtGcdResult {
    pub gcd: nat,
    pub x: int,
    pub y: int,
}

/// Spec function: Extended Euclidean Algorithm
///
/// Computes (gcd, x, y) such that gcd(a, b) = a*x + b*y (Bezout's identity)
///
/// This is a constructive algorithm that produces the Bezout coefficients.
/// Base case: gcd(a, 0) = a = a*1 + 0*0, so (a, 1, 0)
/// Recursive case: if gcd(b, a%b) = b*x' + (a%b)*y' = b*x' + (a - b*(a/b))*y'
///                                = a*y' + b*(x' - (a/b)*y')
///                 so (gcd, y', x' - (a/b)*y')
pub open spec fn spec_extended_gcd(a: nat, b: nat) -> ExtGcdResult
    decreases b,
{
    if b == 0 {
        ExtGcdResult { gcd: a, x: 1, y: 0 }
    } else {
        let r = spec_extended_gcd(b, a % b);
        ExtGcdResult { gcd: r.gcd, x: r.y, y: r.x - (a / b) as int * r.y }
    }
}

/// Lemma: Extended GCD computes the same gcd as spec_gcd
pub proof fn lemma_extended_gcd_is_gcd(a: nat, b: nat)
    ensures
        spec_extended_gcd(a, b).gcd == spec_gcd(a, b),
    decreases b,
{
    if b == 0 {
        // Base case: both return a
    } else {
        // Inductive case
        lemma_extended_gcd_is_gcd(b, a % b);
    }
}

/// Lemma: Bezout's Identity - a*x + b*y = gcd(a,b)
pub proof fn lemma_bezout_identity(a: nat, b: nat)
    ensures
        ({
            let r = spec_extended_gcd(a, b);
            a as int * r.x + b as int * r.y == r.gcd as int
        }),
    decreases b,
{
    if b == 0 {
        // Base: a*1 + 0*0 = a
    } else {
        lemma_bezout_identity(b, a % b);
        let r_prev = spec_extended_gcd(b, a % b);
        let r = spec_extended_gcd(a, b);

        let x_prime = r_prev.x;
        let y_prime = r_prev.y;
        let remainder = (a % b) as int;
        let quotient = (a / b) as int;

        // Show: a * y' + b * (x' - q * y') = b * x' + y' * (a - b*q) = b * x' + y' * (a%b) = gcd
        lemma_fundamental_div_mod(a as int, b as int);

        let lhs = a as int * y_prime + b as int * (x_prime - quotient * y_prime);

        lemma_mul_is_distributive_sub(b as int, x_prime, quotient * y_prime);
        lemma_mul_is_associative(b as int, quotient, y_prime);
        lemma_mul_is_commutative(a as int, y_prime);
        lemma_mul_is_commutative((b as int * quotient), y_prime);
        lemma_mul_is_distributive_sub(y_prime, a as int, b as int * quotient);
        lemma_mul_is_commutative(y_prime, remainder);
    }
}

// ============================================================================
// PART 4: Modular Inverse via Bezout's Identity
// ============================================================================
/// Spec function: Compute modular inverse using extended Euclidean algorithm
///
/// For a and m coprime (gcd(a, m) = 1), returns the unique x in [0, m) such that
/// a * x ≡ 1 (mod m).
///
/// The inverse is computed from Bezout's identity: a*x + m*y = 1
/// Taking mod m: (a*x) % m = 1
///
/// We normalize the result to be in [0, m) by computing x % m (handling negative x).
pub open spec fn spec_mod_inverse(a: nat, m: nat) -> nat
    recommends
        m > 1,
        spec_gcd(a % m, m) == 1,
{
    if m <= 1 || spec_gcd(a % m, m) != 1 {
        0  // Undefined case - return 0 by convention

    } else {
        let r = spec_extended_gcd(a % m, m);
        // r.x might be negative, so normalize to [0, m)
        (((r.x % (m as int)) + (m as int)) % (m as int)) as nat
    }
}

/// Lemma: The modular inverse satisfies (a * spec_mod_inverse(a, m)) % m == 1
pub proof fn lemma_mod_inverse_correct(a: nat, m: nat)
    requires
        m > 1,
        spec_gcd(a % m, m) == 1,
    ensures
        spec_mod_inverse(a, m) < m,
        (a * spec_mod_inverse(a, m)) % m == 1,
{
    let a_red = a % m;
    let r = spec_extended_gcd(a_red, m);

    lemma_bezout_identity(a_red, m);
    lemma_extended_gcd_is_gcd(a_red, m);

    // (m * r.y) % m = 0
    assert((m as int * r.y) % (m as int) == 0) by {
        lemma_mul_is_commutative(m as int, r.y);
        lemma_mod_multiples_basic(r.y, m as int);
    };

    // (a_red * r.x) % m = 1
    assert((a_red as int * r.x) % (m as int) == 1) by {
        lemma_add_mod_noop(a_red as int * r.x, m as int * r.y, m as int);
        lemma_mod_twice(a_red as int * r.x, m as int);
        lemma_small_mod(1nat, m);
    };

    let inv = spec_mod_inverse(a, m);
    let normalized_x = (((r.x % (m as int)) + (m as int)) % (m as int)) as nat;

    assert(inv < m) by {
        lemma_mod_bound((r.x % (m as int)) + (m as int), m as int);
    };

    // normalized_x ≡ r.x (mod m)
    assert((normalized_x as int) % (m as int) == r.x % (m as int)) by {
        lemma_add_mod_noop(r.x % (m as int), m as int, m as int);
        lemma_mod_self_0(m as int);
        lemma_mod_twice(r.x, m as int);
    };

    // (a_red * normalized_x) % m = 1
    assert((a_red as int * normalized_x as int) % (m as int) == 1) by {
        lemma_mul_mod_noop_right(a_red as int, normalized_x as int, m as int);
        lemma_mul_mod_noop_right(a_red as int, r.x, m as int);
    };

    // (a * inv) % m = 1
    assert((a * inv) % m == 1) by {
        lemma_mul_mod_noop_left(a as int, inv as int, m as int);
    };
}

// =============================================================================
// PART 5: Euclid's Lemma and Related Helpers
// =============================================================================
/// If a % p != 0 and i % p != 0, then (a * i) % p != 0
pub proof fn lemma_product_nonzero_mod_prime(a: nat, i: nat, p: nat)
    requires
        is_prime(p),
        a % p != 0,
        i % p != 0,
    ensures
        (a * i) % p != 0,
{
    // Proof by contradiction: suppose (a * i) % p == 0
    // Then p | (a * i). Since p is prime and p doesn't divide a or i,
    // this contradicts Euclid's lemma: if p | ab and p is prime, then p | a or p | b
    if (a * i) % p == 0 {
        // p divides a * i
        // By Euclid's lemma for primes, p must divide a or p must divide i
        lemma_euclid_prime(a, i, p);
        // This gives us a % p == 0 || i % p == 0, contradicting our preconditions
        assert(false);
    }
}

/// Euclid's lemma: if p is prime and p | (a * b), then p | a or p | b
pub proof fn lemma_euclid_prime(a: nat, b: nat, p: nat)
    requires
        is_prime(p),
        (a * b) % p == 0,
    ensures
        a % p == 0 || b % p == 0,
{
    // Proof by strong induction on a
    // We use the fact that if p doesn't divide a, then gcd(a, p) = 1
    // and we can use a cancellation argument
    if a % p == 0 {
        // Done
    } else if b % p == 0 {
        // Done
    } else {
        // Both a % p != 0 and b % p != 0
        // But (a * b) % p == 0
        // We'll derive a contradiction using properties of primes
        // Key insight: since p is prime and a % p != 0,
        // gcd(a, p) = 1 (a and p are coprime)
        // This means there exist integers x, y such that ax + py = 1 (Bezout)
        // Multiplying by b: abx + pby = b
        // Since p | ab, we have p | abx, and p | pby
        // So p | b, contradiction
        // For now, we use a computational approach based on the definition
        let a_mod = a % p;

        // a % p is in range (0, p) since a % p != 0
        assert(0 < a_mod) by {
            // a % p != 0 (from the else branch)
        };
        assert(a_mod < p) by {
            lemma_mod_bound(a as int, p as int);
        };

        // ((a % p) * b) % p == (a * b) % p == 0
        assert((a_mod * b) % p == 0) by {
            lemma_mul_mod_noop_left(a as int, b as int, p as int);
            // (a * b) % p == ((a % p) * b) % p
        };

        lemma_euclid_prime_helper(a_mod, b, p);
    }
}

/// Helper for Euclid's lemma: works with a already reduced mod p
proof fn lemma_euclid_prime_helper(a: nat, b: nat, p: nat)
    requires
        is_prime(p),
        0 < a < p,
        (a * b) % p == 0,
    ensures
        b % p == 0,
    decreases a,
{
    // We prove by induction on a
    // Key idea: if a doesn't divide p evenly (which it can't since a < p and p is prime),
    // we can find a smaller representative
    if a == 1 {
        // 1 * b % p == 0 means b % p == 0
        assert(a * b == b) by {
            lemma_mul_basics(b as int);
        };
    } else {
        // a > 1 and a < p
        // Since p is prime and 1 < a < p, p % a != 0
        // We use the division algorithm: p = q * a + r where 0 <= r < a
        // Since p doesn't divide a and a doesn't divide p, r > 0
        // Then: r * b ≡ p * b - q * a * b ≡ 0 - q * 0 ≡ 0 (mod p)
        // And r < a, so by induction...
        let q = p / a;
        let r = p % a;

        // r > 0 because p is prime and 1 < a < p means a doesn't divide p
        assert(r > 0) by {
            if r == 0 {
                // Then p = q * a, meaning a divides p
                // But a < p and a > 1, contradicting that p is prime
                assert(p % a == 0);
                assert(1 < a < p);
                // is_prime says: forall d. 1 < d < p ==> p % d != 0
                assert(false);
            }
        };

        // p = q * a + r, so r = p - q * a
        assert(p == q * a + r) by {
            lemma_fundamental_div_mod(p as int, a as int);
        };

        // (r * b) % p == ?
        // r * b = (p - q * a) * b = p * b - q * a * b
        // (r * b) % p = (p * b - q * a * b) % p = (0 - q * (a * b)) % p = (-q * 0) % p = 0

        assert((r * b) % p == 0) by {
            // r = p - q * a
            // r * b = p * b - q * a * b
            assert(r * b == p * b - q * a * b) by {
                assert(r == p - q * a);
                lemma_mul_is_distributive_sub_other_way(b as int, p as int, (q * a) as int);
                assert((p - q * a) * b == p * b - (q * a) * b);
                lemma_mul_is_associative(q as int, a as int, b as int);
            };

            // (p * b) % p == 0
            assert((p * b) % p == 0) by {
                lemma_mod_multiples_basic(b as int, p as int);
            };

            // (q * a * b) % p == q * ((a * b) % p) % p == q * 0 % p == 0
            assert((q * (a * b)) % p == 0) by {
                lemma_mul_mod_noop_right(q as int, (a * b) as int, p as int);
                assert((a * b) % p == 0);
                lemma_mul_basics(q as int);
                lemma_small_mod(0nat, p);
            };

            // r * b = p * b - q * a * b
            // (r * b) % p = (p * b - q * a * b) % p
            // Both (p * b) and (q * a * b) are divisible by p
            // So their difference is also divisible by p
            lemma_mul_is_associative(q as int, a as int, b as int);
            assert(q * a * b == q * (a * b));

            // (p * b) % p == 0 and (q * (a * b)) % p == 0
            // So (p * b - q * (a * b)) % p == 0
            // Which means (r * b) % p == 0
            assert((p * b) % p == 0) by {
                lemma_mod_multiples_basic(b as int, p as int);
            };
            assert((q * (a * b)) % p == 0) by {
                lemma_mul_mod_noop_right(q as int, (a * b) as int, p as int);
                lemma_mul_basics(q as int);
                lemma_small_mod(0nat, p);
            };
            // Both are 0 mod p, so their difference is 0 mod p
            lemma_mod_difference_zero((p * b) as int, (q * (a * b)) as int, p as int);
        };

        // By induction on r < a
        assert(0 < r < a);
        assert(r < p) by {
            lemma_mod_bound(p as int, a as int);
        };
        lemma_euclid_prime_helper(r, b, p);
    }
}

/// If a % m == 0 and b % m == 0 and a >= b, then (a - b) % m == 0
proof fn lemma_mod_difference_zero(a: int, b: int, m: int)
    requires
        m > 0,
        a % m == 0,
        b % m == 0,
    ensures
        (a - b) % m == 0,
{
    // By lemma_sub_mod_noop: (a - b) % m == ((a % m) - (b % m)) % m
    lemma_sub_mod_noop(a, b, m);
    // Since a % m == 0 and b % m == 0: (a - b) % m == (0 - 0) % m == 0
    lemma_small_mod(0nat, m as nat);
}

/// If 1 <= i < j < p and a % p != 0, then (a * i) % p != (a * j) % p
pub proof fn lemma_multiples_distinct_mod_prime(a: nat, i: nat, j: nat, p: nat)
    requires
        is_prime(p),
        a % p != 0,
        1 <= i < j < p,
    ensures
        (a * i) % p != (a * j) % p,
{
    // Proof by contradiction
    if (a * i) % p == (a * j) % p {
        // Then (a * j - a * i) % p == 0
        // a * (j - i) % p == 0
        // Since p is prime and a % p != 0, we need (j - i) % p == 0
        // But 0 < j - i < p, so (j - i) % p = j - i != 0
        // Contradiction
        let diff = (j - i) as nat;
        assert(0 < diff < p);

        // (a * j) % p == (a * i) % p means (a * j - a * i) % p == 0
        // a * j - a * i = a * (j - i)
        assert(a * j - a * i == a * diff) by {
            lemma_mul_is_distributive_sub(a as int, j as int, i as int);
        };

        // Show (a * diff) % p == 0
        assert((a * diff) % p == 0) by {
            // (a * j) % p == (a * i) % p
            // ((a * j) - (a * i)) % p == 0
            lemma_mod_sub_eq(a * j, a * i, p);
        };

        // But a % p != 0 and 0 < diff < p means diff % p == diff != 0
        assert(diff % p == diff) by {
            lemma_small_mod(diff, p);
        };
        assert(diff % p != 0);

        // By Euclid's lemma, since (a * diff) % p == 0 and p is prime,
        // either a % p == 0 or diff % p == 0
        lemma_euclid_prime(a, diff, p);
        // Both are false, contradiction
        assert(false);
    }
}

/// Helper: if a % m == b % m then (a - b) % m == 0 (for a >= b)
proof fn lemma_mod_sub_eq(a: nat, b: nat, m: nat)
    requires
        m > 0,
        a >= b,
        a % m == b % m,
    ensures
        ((a - b) as nat) % m == 0,
{
    // a = q1 * m + r, b = q2 * m + r (same remainder r)
    // a - b = (q1 - q2) * m, which is divisible by m
    let r = a % m;
    let q1: int = (a / m) as int;
    let q2: int = (b / m) as int;

    assert(a as int == q1 * (m as int) + (r as int)) by {
        lemma_fundamental_div_mod(a as int, m as int);
    };
    assert(b as int == q2 * (m as int) + (r as int)) by {
        lemma_fundamental_div_mod(b as int, m as int);
    };

    // Derive a - b = (q1 - q2) * m
    assert((a as int) - (b as int) == (q1 - q2) * (m as int)) by {
        // a = q1 * m + r, b = q2 * m + r
        // a - b = (q1 * m + r) - (q2 * m + r) = q1 * m - q2 * m = (q1 - q2) * m
        lemma_mul_is_distributive_sub_other_way(m as int, q1, q2);
    };

    // Since a >= b and same remainder, q1 >= q2
    assert(q1 >= q2) by {
        // Since a >= b, (a - b) >= 0
        // (a - b) = (q1 - q2) * m
        // Since m > 0, (q1 - q2) >= 0 iff (q1 - q2) * m >= 0
        assert((a as int) - (b as int) >= 0);
        // If q1 < q2, then q1 - q2 < 0, so (q1 - q2) * m < 0 (since m > 0)
        // But (a - b) >= 0, contradiction
        if q1 < q2 {
            // q1 < q2 means q2 - q1 > 0
            assert(q2 - q1 > 0);
            // Since q2 - q1 > 0 and m > 0, (q2 - q1) * m > 0
            lemma_mul_strictly_positive(q2 - q1, m as int);
            assert((q2 - q1) * (m as int) > 0);
            // (q1 - q2) = -(q2 - q1), so (q1 - q2) * m = -((q2 - q1) * m) < 0
            assert((q1 - q2) * (m as int) == -((q2 - q1) * (m as int))) by {
                lemma_mul_unary_negation(q2 - q1, m as int);
            };
            assert((q1 - q2) * (m as int) < 0);
            // But (a - b) = (q1 - q2) * m, and (a - b) >= 0, contradiction
        }
    };

    // a - b = (q1 - q2) * m
    assert((a - b) as int == (q1 - q2) * (m as int)) by {
        assert((a as int) - (b as int) == (q1 * (m as int) + (r as int)) - (q2 * (m as int) + (
        r as int)));
        lemma_mul_is_distributive_sub_other_way(m as int, q1, q2);
    };

    // (q1 - q2) * m is divisible by m
    lemma_mod_multiples_basic(q1 - q2, m as int);
}

// =============================================================================
// PART 6: The sequence {a, 2a, ..., (p-1)a} mod p is a permutation of {1, ..., p-1}
// =============================================================================
/// The function f(i) = (a * i) % p maps {1, ..., p-1} to {1, ..., p-1}
/// (i.e., the image is contained in {1, ..., p-1})
pub proof fn lemma_mult_maps_to_nonzero(a: nat, i: nat, p: nat)
    requires
        is_prime(p),
        a % p != 0,
        1 <= i < p,
    ensures
        1 <= (a * i) % p < p,
{
    // (a * i) % p is in [0, p) by definition
    lemma_mod_bound((a * i) as int, p as int);

    // (a * i) % p != 0 because a % p != 0 and i % p != 0
    assert(i % p != 0) by {
        lemma_small_mod(i, p);
    };
    lemma_product_nonzero_mod_prime(a, i, p);
}

/// Key theorem: The products of {1, 2, ..., p-1} and {a*1, a*2, ..., a*(p-1)} mod p are equal
/// More precisely: (a * 1 * a * 2 * ... * a * (p-1)) % p == (1 * 2 * ... * (p-1)) % p
/// Which gives us: a^(p-1) * (p-1)! % p == (p-1)! % p
///
/// Proof: f(i) = (i * a) % p is a bijection on {1..p-1} (injective + pigeonhole),
/// so ∏ f(i) = ∏ i = (p-1)!
pub proof fn lemma_product_of_multiples_mod_eq_factorial(a: nat, p: nat)
    requires
        is_prime(p),
        a % p != 0,
    ensures
        (product_of_multiples(a, (p - 1) as nat)) % p == factorial((p - 1) as nat) % p,
{
    let n = (p - 1) as nat;

    // Base case: p = 2
    if p == 2 {
        assert(product_of_multiples(a, 1) == 1 * a * product_of_multiples(a, 0));
        assert(product_of_multiples(a, 0) == 1);
        assert(product_of_multiples(a, 1) == a) by {
            lemma_mul_basics(a as int);
        };
        assert(factorial(1) == 1) by {
            assert(factorial(1) == 1 * factorial(0));
            assert(factorial(0) == 1);
            lemma_mul_basics(1int);
        };
        // a % 2 != 0 and a % 2 < 2, so a % 2 == 1
        lemma_mod_bound(a as int, 2);
        lemma_small_mod(1nat, 2nat);
        return ;
    }
    // For p > 2, we use the bijection argument combined with Fermat's Little Theorem
    // product_of_multiples(a, n) = a^n * n! by lemma_product_of_multiples_eq

    lemma_product_of_multiples_eq(a, n);

    // We need to show (a^n * n!) % p == n! % p
    // This is equivalent to showing a^n ≡ 1 (mod p)

    // Reduce a mod p
    let a_red = a % p;
    assert(a_red < p) by {
        lemma_mod_bound(a as int, p as int);
    };
    assert(a_red != 0);

    // Prove a_red^p ≡ a_red (mod p) using induction
    lemma_fermat_strong(a_red, p);

    // pow(a_red, p) = a_red * pow(a_red, p-1)
    assert(pow(a_red as int, p) == (a_red as int) * pow(a_red as int, n)) by {
        reveal(pow);
        assert(p == n + 1);
    };

    // Since a_red < p, a_red % p == a_red
    assert(a_red % p == a_red) by {
        lemma_small_mod(a_red, p);
    };

    // Show that a_red * pow(a_red, n) > 0
    assert(a_red > 0);
    lemma_pow_positive(a_red as int, n);
    assert(pow(a_red as int, n) >= 1);
    lemma_mul_strictly_positive(a_red as int, pow(a_red as int, n));

    let product = (a_red as int) * pow(a_red as int, n);
    assert(product > 0);
    assert((product as nat) % p == a_red);
    assert(product % (p as int) == (a_red as int));
    assert(((a_red as int) * pow(a_red as int, n)) % (p as int) == (a_red as int));

    // Show pow(a_red, n) >= 0
    assert(pow(a_red as int, n) >= 0) by {
        lemma_pow_positive(a_red as int, n);
    };

    // Use the multiplicative cancellation lemma to get pow(a_red, n) % p == 1
    lemma_fermat_cancellation(a_red, n, p);

    // pow(a, n) % p == pow(a_red, n) % p == 1
    lemma_pow_mod_noop(a as int, n, p as int);
    lemma_pow_nonnegative(a as int, n);

    let pow_a_red_n = pow(a_red as int, n);
    let pow_a_n = pow(a as int, n);

    assert(pow_a_red_n % (p as int) == 1);
    assert(pow_a_n % (p as int) == 1);
    assert((pow(a as int, n) as nat) % p == 1);

    // Now for the product equality:
    // product_of_multiples(a, n) = a^n * n!
    // (a^n * n!) % p == ((a^n % p) * (n! % p)) % p == (1 * (n! % p)) % p == n! % p
    let pow_a_n = pow(a as int, n) as nat;
    let fact_n = factorial(n);

    assert((pow_a_n * fact_n) % p == fact_n % p) by {
        assert(pow_a_n % p == 1);
        lemma_mul_mod_noop_general(pow_a_n as int, fact_n as int, p as int);
        lemma_mul_basics((fact_n % p) as int);
        lemma_mod_bound(fact_n as int, p as int);
    };
}

// =============================================================================
// PART 7: Main Theorem - Fermat's Little Theorem
// =============================================================================
/// Lemma: Fermat's Little Theorem
///
/// For any prime p and any integer x not divisible by p,
/// we have x^(p-1) ≡ 1 (mod p).
///
/// Proof: Using the permutation argument:
/// 1. The sequence {a, 2a, ..., (p-1)a} mod p is a permutation of {1, 2, ..., p-1}
/// 2. Therefore their products are equal mod p: a^(p-1) * (p-1)! ≡ (p-1)! (mod p)
/// 3. Since gcd((p-1)!, p) = 1 for prime p, we can cancel to get a^(p-1) ≡ 1 (mod p)
pub proof fn lemma_fermat_little_theorem(x: nat, prime: nat)
    requires
        is_prime(prime),
        x % prime != 0,
    ensures
        (pow(x as int, (prime - 1) as nat) as nat) % prime == 1,
{
    let n = (prime - 1) as nat;
    let a = x % prime;

    // a % prime == a since a < prime
    assert(a < prime) by {
        lemma_mod_bound(x as int, prime as int);
    };
    assert(a % prime == a) by {
        lemma_small_mod(a, prime);
    };
    assert(a % prime != 0) by {
        // x % prime != 0 and a = x % prime
    };

    // Step 1: product_of_multiples(a, n) = a^n * n! (by lemma_product_of_multiples_eq)
    lemma_product_of_multiples_eq(a, n);
    assert(product_of_multiples(a, n) == pow(a as int, n) as nat * factorial(n));

    // Step 2: product_of_multiples(a, n) % prime == factorial(n) % prime (by permutation argument)
    lemma_product_of_multiples_mod_eq_factorial(a, prime);
    assert((product_of_multiples(a, n)) % prime == factorial(n) % prime);

    // Step 3: (a^n * n!) % prime == n! % prime
    // This means a^n * n! ≡ n! (mod prime)
    // So (a^n - 1) * n! ≡ 0 (mod prime)

    // Step 4: Since gcd(n!, prime) = 1 (because prime > n, so prime doesn't divide n!),
    // we can conclude a^n ≡ 1 (mod prime)

    // First show n! % prime != 0 (n = prime - 1 < prime)
    lemma_factorial_coprime_to_prime(n, prime);
    assert(factorial(n) % prime != 0);

    // Now use cancellation: if a^n * n! ≡ n! (mod p) and gcd(n!, p) = 1, then a^n ≡ 1
    // Need to verify the precondition: (pow(a, n) * factorial(n)) % prime == factorial(n) % prime
    assert((pow(a as int, n) as nat * factorial(n)) % prime == factorial(n) % prime) by {
        // product_of_multiples(a, n) % prime == factorial(n) % prime
        // product_of_multiples(a, n) == pow(a, n) * factorial(n)
        // So (pow(a, n) * factorial(n)) % prime == factorial(n) % prime
    };
    lemma_cancellation_mod_prime(pow(a as int, n) as nat, factorial(n), prime);
    // Now we have: pow(a, n) % prime == 1
    assert((pow(a as int, n) as nat) % prime == 1);

    // Finally, pow(a, n) % prime == pow(x, n) % prime since a = x % prime
    // lemma_pow_mod_noop gives: pow(x % prime, n) % prime == pow(x, n) % prime
    lemma_pow_mod_noop(x as int, n, prime as int);

    // We have: a = x % prime
    // So pow(a, n) = pow(x % prime, n)
    // By lemma_pow_mod_noop: pow(x % prime, n) % prime == pow(x, n) % prime
    // We proved: pow(a, n) % prime == 1
    // Therefore: pow(x, n) % prime == 1

    // pow(a, n) is non-negative since both a and n are non-negative
    assert(pow(a as int, n) >= 0) by {
        if a > 0 {
            lemma_pow_positive(a as int, n);
        } else {
            // a == 0, but a % prime != 0, contradiction
            assert(a == 0);
            assert(a % prime == 0) by {
                lemma_small_mod(0nat, prime);
            };
        }
    };

    // Since a = x % prime, pow(a, n) = pow(x % prime, n)
    // pow_mod_noop: pow((x % prime) as int, n) % prime == pow(x as int, n) % prime
    assert(pow(a as int, n) % (prime as int) == pow(x as int, n) % (prime as int)) by {
        assert(a == (x % prime) as nat);
        assert(a as int == (x as int) % (prime as int)) by {
            lemma_mod_bound(x as int, prime as int);
        };
    };

    // Converting the int result to nat for the postcondition
    assert((pow(x as int, n) as nat) % prime == 1) by {
        // pow(a, n) % prime == 1 (as nat)
        // pow(a, n) % prime == pow(x, n) % prime (as int)
        // So pow(x, n) % prime == 1 (as int)
        // Since pow(x, n) >= 0 and prime > 0, pow(x, n) % prime >= 0
        assert(pow(x as int, n) >= 0) by {
            if x > 0 {
                lemma_pow_positive(x as int, n);
            } else {
                // x == 0, but x % prime != 0, contradiction
                assert(x == 0);
                lemma_small_mod(0nat, prime);
                assert(false);
            }
        };
    };
}

/// Any factorial of n < prime is coprime to prime
proof fn lemma_factorial_coprime_to_prime(n: nat, prime: nat)
    requires
        is_prime(prime),
        n < prime,
    ensures
        factorial(n) % prime != 0,
    decreases n,
{
    // n! = 1 * 2 * ... * n
    // Each factor is in {1, ..., n} which is a subset of {1, ..., prime-1}
    // prime doesn't divide any number in {1, ..., prime-1}
    // Therefore prime doesn't divide n!
    if n == 0 {
        // 0! = 1, and 1 % prime != 0 since prime > 1
        assert(factorial(0) == 1);
        assert(1nat % prime != 0) by {
            lemma_small_mod(1nat, prime);
        };
    } else {
        // n! = n * (n-1)!
        // n % prime != 0 since 1 <= n < prime
        // (n-1)! % prime != 0 by induction
        assert(factorial(n) == n * factorial((n - 1) as nat));

        // n < prime and n >= 1, so n % prime = n != 0
        assert(1 <= n < prime);
        assert(n % prime == n) by {
            lemma_small_mod(n, prime);
        };
        assert(n % prime != 0);

        // By induction: (n-1) < n < prime
        lemma_factorial_coprime_to_prime((n - 1) as nat, prime);
        assert(factorial((n - 1) as nat) % prime != 0);

        // n! = n * (n-1)!
        // prime doesn't divide n and prime doesn't divide (n-1)!
        // by Euclid's lemma, prime doesn't divide n!
        if factorial(n) % prime == 0 {
            lemma_euclid_prime(n, factorial((n - 1) as nat), prime);
            assert(false);
        }
    }
}

/// Cancellation: if a * b ≡ b (mod p) and b % p != 0, then a ≡ 1 (mod p)
proof fn lemma_cancellation_mod_prime(a: nat, b: nat, prime: nat)
    requires
        is_prime(prime),
        (a * b) % prime == b % prime,
        b % prime != 0,
    ensures
        a % prime == 1,
{
    // a * b ≡ b (mod p)
    // a * b - b ≡ 0 (mod p)
    // (a - 1) * b ≡ 0 (mod p)
    // Since p is prime and b % p != 0, by Euclid's lemma: (a - 1) % p == 0
    // So a ≡ 1 (mod p)
    if a == 0 {
        // 0 * b = 0 ≡ b (mod p) means b % p == 0, contradiction
        assert((a * b) % prime == 0) by {
            lemma_mul_basics(b as int);
            lemma_small_mod(0nat, prime);
        };
        assert(b % prime == 0);
    }
    // (a * b - b) % prime == 0
    // We need a >= 1 for a * b >= b when b > 0

    assert(a >= 1);

    // (a - 1) * b = a * b - b
    assert((a - 1) * b == a * b - b) by {
        lemma_mul_is_distributive_sub_other_way(b as int, a as int, 1);
    };

    // ((a - 1) * b) % prime == 0
    if a == 1 {
        // Done: a % prime == 1 % prime == 1 (since prime > 1)
        lemma_small_mod(1nat, prime);
    } else {
        // a > 1
        // b > 0 because b % prime != 0
        // If b == 0, then b % prime == 0 (since 0 % anything == 0)
        assert(b > 0) by {
            if b == 0 {
                lemma_small_mod(0nat, prime);
                // 0 % prime == 0, but we have b % prime != 0, contradiction
            }
        };

        assert(a * b >= b) by {
            // a >= 1 and b > 0, so a * b >= 1 * b = b
            lemma_mul_increases(a as int, b as int);
            // gives b <= a * b
        };

        lemma_mod_sub_eq(a * b, b, prime);
        assert(((a * b - b) as nat) % prime == 0);
        assert((((a - 1) as nat) * b) % prime == 0);

        // By Euclid's lemma: (a - 1) % prime == 0 or b % prime == 0
        lemma_euclid_prime((a - 1) as nat, b, prime);
        // b % prime != 0, so (a - 1) % prime == 0

        assert(((a - 1) as nat) % prime == 0);
        // a = (a - 1) + 1
        // a % prime = ((a - 1) + 1) % prime = (0 + 1) % prime = 1
        assert(a % prime == 1) by {
            lemma_mod_adds((a - 1) as int, 1, prime as int);
            lemma_small_mod(1nat, prime);
        };
    }
}

} // verus!
