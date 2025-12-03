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

// ============================================================================
// PART 2: Extended Euclidean Algorithm (Bezout's Identity)
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
// PART 3: Modular Inverse via Bezout's Identity
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

// ============================================================================
// PART 4: Fermat's Little Theorem
// ============================================================================
/// Lemma: Fermat's Little Theorem
///
/// For any prime p and any integer x not divisible by p,
/// we have x^(p-1) ≡ 1 (mod p).
///
/// This is one of the fundamental theorems in number theory and the basis
/// for many cryptographic constructions, including:
/// - Computing multiplicative inverses: x^(-1) ≡ x^(p-2) (mod p)
/// - Primality testing
/// - Public-key cryptography
///
/// **Proof Status**: Currently admitted. A complete proof would require:
/// 1. Defining the multiplicative group (ℤ/pℤ)*
/// 2. Proving Lagrange's theorem (order of element divides order of group)
/// 3. Showing |（ℤ/pℤ)*| = p - 1 (Euler's totient for primes)
///
/// While provable from the is_prime definition, this would require substantial
/// group theory infrastructure that is currently beyond the scope of this
/// verification effort.
pub proof fn lemma_fermat_little_theorem(x: nat, prime: nat)
    requires
        is_prime(prime),
        x % prime != 0,
    ensures
        (pow(x as int, (prime - 1) as nat) as nat) % prime == 1,
{
    admit();
}

} // verus!
