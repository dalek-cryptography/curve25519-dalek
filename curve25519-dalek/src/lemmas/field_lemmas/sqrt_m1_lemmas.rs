//! Lemmas about i = sqrt(-1) in GF(p) where p = 2^255 - 19
//!
//! This module contains lemmas about the specific field element `sqrt_m1()`,
//! which is the square root of -1 in the curve25519 prime field.
//!
//! ## Axioms
//!
//! These are concrete numerical facts about i that are mathematically proven
//! but complex to formalize in Verus:
//! - `axiom_sqrt_m1_squared` — i² = -1 (mod p)
//! - `axiom_sqrt_m1_not_square` — i is not a square (Euler's criterion)
//! - `axiom_neg_sqrt_m1_not_square` — -i is not a square
//!
//! ## Derived Lemmas
//!
//! - `lemma_multiply_by_i_flips_sign` — (r·i)² ≡ -r² (mod p)
//! - `lemma_i_inverse_is_neg_i` — i⁻¹ = -i
//! - `lemma_u_times_inv_iu_is_neg_i` — u · inv(i·u) = -i
//! - `lemma_neg_u_times_inv_iu_is_i` — (-u) · inv(i·u) = i
#![allow(unused_imports)]
use crate::constants;
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::primality_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// AXIOMS: Number-Theoretic Facts about i = sqrt(-1) in F_p where p = 2^255 - 19
//
// These are concrete numerical facts that are mathematically proven but
// complex to formalize in Verus. Each axiom includes its justification.
// =============================================================================
/// AXIOM: SQRT_M1 has 51-bit bounded limbs (it is a canonical field element constant)
///
/// Each limb of SQRT_M1 is less than 2^51 = 2251799813685248:
///   limbs = [1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133]
///   max limb = 2233514472574048 < 2251799813685248
pub proof fn axiom_sqrt_m1_limbs_bounded()
    ensures
        fe51_limbs_bounded(&constants::SQRT_M1, 51),
        fe51_limbs_bounded(&constants::SQRT_M1, 54),
{
    // SQRT_M1 limbs = [1718705420411056, 234908883556509, 2233514472574048, 2117202627021982, 765476049583133]
    // 2^51 = 2251799813685248, 2^54 = 18014398509481984
    // All limbs < 2^51 < 2^54, so both bounds hold.
    admit();
}

/// AXIOM: i² = -1 (mod p) — Definition of SQRT_M1
///
/// Mathematical justification:
/// - SQRT_M1 is a specific constant computed to satisfy i² ≡ -1 (mod p)
/// - The value is approximately 2^252.3 (a ~252-bit number)
/// - Verification would require BigInt computation of the actual product
///
/// Used in: lemma_sqrt_m1_neq_one, lemma_sqrt_m1_neq_neg_one,
///          lemma_multiply_by_i_flips_sign, lemma_no_square_root_when_times_i
pub proof fn axiom_sqrt_m1_squared()
    ensures
        (sqrt_m1() * sqrt_m1()) % p() == (p() - 1),
{
    admit();
}

/// AXIOM: i = sqrt(-1) is not a square in F_p
///
/// Mathematical justification:
/// - p = 2^255 - 19 ≡ 5 (mod 8)
/// - For p ≡ 5 (mod 8), the Euler criterion gives:
///   i^((p-1)/2) = (i²)^((p-1)/4) = (-1)^((p-1)/4)
/// - (p-1)/4 = (2^255 - 20)/4 = 2^253 - 5, which is odd
/// - Therefore (-1)^((p-1)/4) = -1 ≠ 1
/// - By Euler's criterion, i is NOT a square
///
/// Used in: lemma_no_square_root_when_times_i
pub proof fn axiom_sqrt_m1_not_square()
    ensures
        !is_square(sqrt_m1()),
{
    admit();
}

/// AXIOM: -i = -(sqrt(-1)) is not a square in F_p
///
/// Mathematical justification:
/// - (-i)^((p-1)/2) = (-1)^((p-1)/2) · i^((p-1)/2)
/// - (p-1)/2 = 2^254 - 10, which is even, so (-1)^((p-1)/2) = 1
/// - From axiom_sqrt_m1_not_square: i^((p-1)/2) = -1
/// - Therefore (-i)^((p-1)/2) = 1 · (-1) = -1 ≠ 1
/// - By Euler's criterion, -i is NOT a square
///
/// Used in: lemma_no_square_root_when_times_i
pub proof fn axiom_neg_sqrt_m1_not_square()
    ensures
        !is_square((p() - sqrt_m1()) as nat),
{
    admit();
}

// =============================================================================
// Basic properties of sqrt_m1
// =============================================================================
/// sqrt_m1() is nonzero (both as a value and mod p).
///
/// Proof: If i = 0, then i^2 = 0, but axiom says i^2 = p-1 > 0.
pub proof fn lemma_sqrt_m1_nonzero()
    ensures
        sqrt_m1() != 0,
        sqrt_m1() % p() != 0,
        sqrt_m1() < p(),
{
    let i = sqrt_m1();
    let pn = p();
    p_gt_2();
    assert(i < pn) by {
        lemma_mod_bound(fe51_as_nat(&constants::SQRT_M1) as int, pn as int);
    };
    if i == 0 {
        axiom_sqrt_m1_squared();
        assert((0nat * 0nat) % pn == 0) by {
            lemma_small_mod(0nat, pn);
        };
        assert(false);
    }
    assert(i % pn != 0) by {
        lemma_small_mod(i, pn);
    };
}

//=============================================================================
// Derived lemmas: multiplication by i
//=============================================================================
/// Lemma: (r·i)² ≡ -r² (mod p)
///
/// Mathematical proof:
///   (r·i)² = r²·i²           [product square: (ab)² = a²b²]
///         ≡ r²·(-1)          [i² = -1 by definition]
///         ≡ -r²              [multiplication by -1]
///         ≡ p - r² mod p     [representation of negation]
///
/// Used in: lemma_sqrt_ratio_correctness
pub proof fn lemma_multiply_by_i_flips_sign(r: nat)
    ensures
        field_square(field_mul(r, sqrt_m1())) == field_neg(field_square(r)),
        // Expanded form for callers that need explicit modular arithmetic
        ((r * sqrt_m1()) % p() * (r * sqrt_m1()) % p()) % p() == ((p() as int - ((r * r)
            % p()) as int) % p() as int) as nat,
{
    pow255_gt_19();  // Needed: establishes p() > 0 for modular arithmetic

    let i = sqrt_m1();
    let pn = p();
    let ri = r * i;
    let ri_mod = field_mul(r, i);  // = (r * i) % p
    let r2 = r * r;
    let r2_mod = field_square(r);  // = (r * r) % p
    let i2 = i * i;
    let pn_minus_1: nat = (pn - 1) as nat;

    // Step 1: (ri)² % p = r² · i² % p = r² · (p-1) % p
    assert((ri * ri) % pn == (r2 * pn_minus_1) % pn) by {
        // (ri)² = r²·i²  [product square factorization]
        assert(ri * ri == r2 * i2) by {
            lemma_product_square_factorize(r as int, i as int);
        };

        // i² % p = p - 1 (from axiom)
        assert(i2 % pn == pn_minus_1) by {
            axiom_sqrt_m1_squared();
        };

        // (r²·i²) % p = (r²·(p-1)) % p
        lemma_mul_mod_noop_right(r2 as int, i2 as int, pn as int);
    };

    // Step 2: r²·(p-1) % p = (p - r²%p) % p = -r² mod p
    assert(r2_mod < pn) by {
        lemma_mod_bound(r2 as int, pn as int);
    };
    let neg_r2: nat = ((pn as int - r2_mod as int) % (pn as int)) as nat;
    assert((r2 * pn_minus_1) % pn == neg_r2) by {
        lemma_mul_by_minus_one_is_negation(r2, pn);
    };

    // Step 3: Connect to math_field functions
    // LHS: field_square(ri_mod) = (ri_mod * ri_mod) % p
    //    = ((ri % p) * (ri % p)) % p = (ri * ri) % p  [by mod absorption]
    assert(field_square(ri_mod) == (ri * ri) % pn) by {
        // ri_mod = ri % p
        // (ri_mod * ri_mod) % p = ((ri%p) * (ri%p)) % p = (ri * ri) % p
        lemma_mul_mod_noop_left(ri as int, ri as int, pn as int);
        lemma_mul_mod_noop_right((ri % pn) as int, ri as int, pn as int);
    };

    // RHS: field_neg(r2_mod) = (p - r2_mod % p) % p
    assert(field_neg(r2_mod) == neg_r2) by {
        lemma_small_mod(r2_mod, pn);
    };

    // Connect to the expanded form for backward compatibility
    assert((((ri % pn) * ri) % pn) % pn == (ri * ri) % pn) by {
        assert(((ri % pn) * ri) % pn == (ri * ri) % pn) by {
            lemma_mul_mod_noop_left(ri as int, ri as int, pn as int);
        };
        lemma_mod_twice(((ri % pn) * ri) as int, pn as int);
    };
}

/// Lemma: i⁻¹ = -i
///
/// ## Mathematical Proof
/// ```text
/// i² = -1           (by axiom_sqrt_m1_squared)
/// i · (-i) = -i²    (factor out)
///         = -(-1)   (substitute i² = -1)
///         = 1       (negation of -1)
///
/// Therefore: -i = i⁻¹  (by definition of multiplicative inverse)
/// ```
///
pub proof fn lemma_i_inverse_is_neg_i()
    ensures
        field_mul(sqrt_m1(), field_neg(sqrt_m1())) == 1,
        field_inv(sqrt_m1()) == field_neg(sqrt_m1()),
{
    let i = sqrt_m1();
    let p = p();
    p_gt_2();

    // Step 1: Show i < p (since sqrt_m1() = fe51_as_canonical_nat(...) % p)
    assert(i < p) by {
        lemma_mod_bound(fe51_as_nat(&constants::SQRT_M1) as int, p as int);
    };

    // Step 2: Define -i = (p - i) % p = p - i (since i < p and i > 0)
    let neg_i = field_neg(i);

    // i ≠ 0
    assert(i != 0) by {
        lemma_sqrt_m1_nonzero();
    };

    // Step 3: neg_i = p - i (since i < p and i ≠ 0, we have 0 < p - i < p)
    assert(neg_i == (p - i) as nat) by {
        // field_neg(i) = (p - i % p) % p = (p - i) % p
        lemma_small_mod(i, p);  // i % p = i
        // (p - i) < p since i > 0
        assert(0 < p - i && p - i < p);
        lemma_small_mod((p - i) as nat, p);  // (p - i) % p = p - i
    };

    // Step 4: Show i · neg_i ≡ 1 (mod p)
    // Key: i · (p - i) = i·p - i² ≡ 0 - (-1) = 1 (mod p)
    assert(((i % p) * neg_i) % p == 1) by {
        // i % p = i (since i < p)
        lemma_small_mod(i, p);

        // neg_i = p - i
        assert(neg_i == (p - i) as nat);

        // Goal: show (i * (p - i)) % p == 1

        // Step 4a: i·p % p = 0
        assert((i * p) % p == 0) by {
            lemma_mod_multiples_basic(i as int, p as int);
        };

        // Step 4b: i² % p = p - 1 (from axiom)
        let i2_mod: nat = (p - 1) as nat;
        assert((i * i) % p == i2_mod) by {
            axiom_sqrt_m1_squared();
        };

        // Step 4c: i * (p - i) = i*p - i² by distributivity
        let product = i * (p - i);
        assert(product == i * p - i * i) by {
            lemma_mul_is_distributive_sub(i as int, p as int, i as int);
        };

        // Step 4d: Use sub_mod_noop to relate (i*p - i*i) % p to (i*p % p - i*i % p) % p
        // lemma_sub_mod_noop gives: ((x % m) - (y % m)) % m == (x - y) % m
        lemma_sub_mod_noop((i * p) as int, (i * i) as int, p as int);
        // This gives: ((i*p % p) - (i*i % p)) % p == (i*p - i*i) % p
        // i.e., (0 - i2_mod) % p == product % p

        // Step 4e: (0 - (p-1)) % p = (-(p-1)) % p
        // In modular arithmetic, -x % p = (p - (x % p)) % p for x > 0
        // Since i2_mod = p - 1 < p, we have:
        // (0 - i2_mod) % p = (-(p-1)) % p = (p - (p-1)) % p = 1 % p = 1

        // The key: (0 - (p-1)) is 1 - p, which is negative
        // (1 - p) % p in Euclidean mod = ((1 - p) % p + p) % p = 1
        assert((0int - i2_mod as int) % (p as int) == 1) by {
            // 0 - (p - 1) = 1 - p = -(p - 1)
            assert(0int - i2_mod as int == 1 - p as int);

            // We need: (1 - p) % p == 1
            // Using: (-p + 1) % p == 1 % p == 1
            // lemma_mod_sub_multiples_vanish: (-m + b) % m == b % m
            lemma_mod_sub_multiples_vanish(1int, p as int);
            // This gives: (-p + 1) % p == 1 % p
            lemma_small_mod(1, p);  // 1 % p = 1
        };

        // Step 4f: Chain together
        // product % p = (i*p - i*i) % p  [by def of product]
        //             = ((i*p % p) - (i*i % p)) % p  [by lemma_sub_mod_noop]
        //             = (0 - i2_mod) % p  [by Steps 4a, 4b]
        //             = 1  [by Step 4e]

        // The final assertion
        assert(((i * (p - i)) as int) % (p as int) == 1);
        assert((((i % p) * (p - i)) as int) % (p as int) == 1) by {
            lemma_mul_mod_noop_left(i as int, ((p - i) as nat) as int, p as int);
        };
    };

    // Step 5: field_mul(i, neg_i) = (i * neg_i) % p = 1
    assert(field_mul(i, neg_i) == 1) by {
        // field_mul(i, neg_i) = (i * neg_i) % p
        // We showed (i % p * neg_i) % p = 1
        // Since i % p = i, we have (i * neg_i) % p = 1
        lemma_small_mod(i, p);
        lemma_mul_mod_noop_left(i as int, neg_i as int, p as int);
    };

    // Step 6: By uniqueness of inverse, inv(i) = neg_i
    assert(field_inv(i) == neg_i) by {
        // We have: i % p ≠ 0, neg_i < p, and (i % p) * neg_i % p = 1
        // By field_inv_unique, neg_i = inv(i)
        assert(i % p != 0) by {
            lemma_small_mod(i, p);
        };
        assert(neg_i < p);
        field_inv_unique(i, neg_i);
    };
}

/// Lemma: u · inv(i·u) = -i
///
/// Algebraic chain:
///   u · inv(i·u) = u · inv(u·i)           [commutativity]
///                = inv(i)                  [by lemma_a_times_inv_ab_is_inv_b]
///                = -i                      [by lemma_i_inverse_is_neg_i]
pub proof fn lemma_u_times_inv_iu_is_neg_i(u: nat, i: nat)
    requires
        u % p() != 0,
        i == sqrt_m1(),
        i % p() != 0,
    ensures
        ({
            let iu = field_mul(i, u);
            let inv_iu = field_inv(iu);
            field_mul(u, inv_iu) == field_neg(i)
        }),
{
    p_gt_2();  // Needed for field operations

    let iu = field_mul(i, u);
    let ui = field_mul(u, i);
    let inv_iu = field_inv(iu);
    let inv_ui = field_inv(ui);
    let inv_i = field_inv(i);

    // Step 1: i·u = u·i (commutativity)
    assert(iu == ui && inv_iu == inv_ui) by {
        lemma_field_mul_comm(i, u);
    };

    // Step 2: u · inv(u·i) = inv(i)
    assert(field_mul(u, inv_ui) == inv_i) by {
        lemma_a_times_inv_ab_is_inv_b(u, i);
    };

    // Step 3: inv(i) = -i
    assert(inv_i == field_neg(i)) by {
        lemma_i_inverse_is_neg_i();
    };
}

/// Lemma: (-u) · inv(i·u) = i
///
/// Algebraic chain:
///   (-u) · inv(i·u) = (-u) · inv(u·i)     [commutativity]
///                   = (-1) · inv(i)        [by lemma_neg_a_times_inv_ab]
///                   = (-1) · (-i)          [by lemma_i_inverse_is_neg_i]
///                   = i                    [by neg_one_times + neg_neg]
pub proof fn lemma_neg_u_times_inv_iu_is_i(u: nat, i: nat)
    requires
        u % p() != 0,
        i == sqrt_m1(),
        i % p() != 0,
    ensures
        ({
            let neg_u = field_neg(u);
            let iu = field_mul(i, u);
            let inv_iu = field_inv(iu);
            field_mul(neg_u, inv_iu) == i % p()
        }),
{
    let p = p();
    p_gt_2();  // Needed for field operations

    let neg_u = field_neg(u);
    let iu = field_mul(i, u);
    let ui = field_mul(u, i);
    let inv_iu = field_inv(iu);
    let inv_ui = field_inv(ui);
    let inv_i = field_inv(i);
    let neg_one = field_neg(1);
    let neg_i = field_neg(i);

    // Step 1: i·u = u·i (commutativity)
    assert(iu == ui && inv_iu == inv_ui) by {
        lemma_field_mul_comm(i, u);
    };

    // Step 2: (-u) · inv(u·i) = (-1) · inv(i)
    assert(field_mul(neg_u, inv_ui) == field_mul(neg_one, inv_i)) by {
        lemma_neg_a_times_inv_ab(u, i);
    };

    // Step 3: inv(i) = -i
    assert(inv_i == neg_i) by {
        lemma_i_inverse_is_neg_i();
    };

    // Step 4: (-1) · (-i) = i by double negation
    assert(i < p) by {
        lemma_mod_bound(fe51_as_nat(&constants::SQRT_M1) as int, p as int);
    };
    assert(i != 0) by {
        lemma_sqrt_m1_nonzero();
    };
    assert(field_mul(neg_one, neg_i) == i) by {
        // (-1)·(-i) = -(-(i)) = i % p = i
        lemma_neg_one_times_is_neg(field_neg(i));
        lemma_neg_neg(i);
        lemma_small_mod(i, p);
    };

    // Postcondition: i % p = i (since i < p)
    lemma_small_mod(i, p);
}

// =============================================================================
// 4th root of unity lemma
// =============================================================================
/// Helper: if q = (y * inv_i) % p and inv_i is the inverse of i,
/// then (q * i) % p == y % p.
///
/// Used in both branches of lemma_square_root_of_neg_one to avoid code duplication.
proof fn lemma_q_times_i_eq_y(y: nat, i: nat, inv_i: nat, q: nat, pn: nat)
    requires
        pn == p(),
        pn > 2,
        inv_i < pn,
        q == field_mul(y, inv_i),
        (i % pn * inv_i) % pn == 1,
        i < pn,
    ensures
        (q * i) % pn == y % pn,
{
    // q = (y * inv_i) % p
    // (q * i) % p = ((y * inv_i) % p * i) % p = (y * inv_i * i) % p
    lemma_mul_mod_noop_left((y * inv_i) as int, i as int, pn as int);
    // = (y * (inv_i * i)) % p
    lemma_mul_is_associative(y as int, inv_i as int, i as int);
    // (inv_i * i) % p == 1
    assert((inv_i * i) % pn == 1) by {
        lemma_mul_is_commutative(inv_i as int, i as int);
        lemma_small_mod(i, pn);
    };
    // (y * (inv_i * i)) % p == (y * 1) % p = y % p
    lemma_mul_mod_noop_right(y as int, (inv_i * i) as int, pn as int);
    lemma_mul_basics(y as int);
}

/// Lemma: If y^2 ≡ -1 (mod p), then y ≡ i or y ≡ -i (mod p)
///
/// Mathematical proof:
///   y^2 ≡ -1 ≡ i^2 (mod p)           [since i^2 = -1]
///   (y/i)^2 = y^2 / i^2 = (-1)/(-1) = 1
///   By lemma_square_root_of_unity: y/i ∈ {1, -1}
///   If y/i = 1: y = i
///   If y/i = -1: y = -i
pub proof fn lemma_square_root_of_neg_one(y: nat, i: nat)
    requires
        i == sqrt_m1(),
        i < p(),
        i % p() != 0,
        (y * y) % p() == (p() - 1) as nat,  // y^2 ≡ -1 (mod p)

    ensures
        y % p() == i || y % p() == (p() - i) as nat,
{
    let pn = p();
    p_gt_2();
    axiom_p_is_prime();

    // i^2 ≡ -1 (mod p)
    axiom_sqrt_m1_squared();
    let neg_one = (pn - 1) as nat;

    // y^2 ≡ i^2 (mod p) [both are -1]
    assert((y * y) % pn == (i * i) % pn);

    // Compute inv(i)
    let inv_i = field_inv(i);
    field_inv_property(i);
    // inv_i < p and (i % p) * inv_i % p == 1
    assert(inv_i < pn);

    // Compute q = y * inv_i (in the field)
    let q = field_mul(y, inv_i);
    assert(q < pn) by {
        lemma_mod_bound((y * inv_i) as int, pn as int);
    };

    // Show q^2 = y^2 * inv_i^2 = (-1) * (-1)^{-1} = 1
    // First: inv_i^2 = inv(i^2) by lemma_inv_of_square
    // i^2 (as field element) = neg_one
    let i_sq = field_square(i);
    assert(i_sq == neg_one) by {
        lemma_small_mod(neg_one, pn);
    };

    // q^2 = field_mul(q, q) = field_mul(y * inv_i, y * inv_i)
    //      = (y * inv_i * y * inv_i) % p = (y * y * inv_i * inv_i) % p
    //      = field_mul(field_square(y), field_square(inv_i))
    // But we need to show this step by step

    // field_square(q) = (q * q) % p
    // q = (y * inv_i) % p
    // So q * q % p = (y * inv_i)^2 % p = y^2 * inv_i^2 % p
    assert((q * q) % pn == ((y * inv_i) * (y * inv_i)) % pn) by {
        lemma_mul_mod_noop((y * inv_i) as int, (y * inv_i) as int, pn as int);
    };

    // (y * inv_i) * (y * inv_i) = (y * y) * (inv_i * inv_i)
    assert(((y * inv_i) * (y * inv_i)) == (y * y) * (inv_i * inv_i)) by {
        lemma_product_square_factorize(y as int, inv_i as int);
    };

    // (y * y) * (inv_i * inv_i) % p = field_mul(y*y, inv_i*inv_i)
    // = field_mul(neg_one_field, inv_neg_one)
    // where neg_one_field = (y*y) % p = p-1
    // and inv_neg_one = (inv_i * inv_i) % p

    // y*y % p == i*i % p == neg_one
    let y_sq_mod = (y * y) % pn;
    assert(y_sq_mod == neg_one);

    // (inv_i * inv_i) % p: this is field_inv(i^2) = field_inv(neg_one)
    let inv_i_sq = (inv_i * inv_i) % pn;

    // We know (i % p) * inv_i % p == 1
    // So ((i%p) * inv_i)^2 % p == 1
    // Which is (i^2 * inv_i^2) % p == 1
    assert(((i * inv_i) * (i * inv_i)) % pn == 1) by {
        // (i % p) * inv_i % p == 1
        let product = field_mul(i % pn, inv_i);
        assert(product == 1);
        // product = ((i%p) * inv_i) % p = (i * inv_i) % p (since i < p)
        lemma_small_mod(i, pn);
        assert(product == (i * inv_i) % pn);
        // product^2 % p == 1
        assert((product * product) % pn == 1) by {
            lemma_small_mod(1nat, pn);
        };
        // ((i*inv_i) % p * (i*inv_i) % p) % p == 1
        // ((i*inv_i) * (i*inv_i)) % p == 1
        lemma_mul_mod_noop((i * inv_i) as int, (i * inv_i) as int, pn as int);
    };

    // (i*inv_i)*(i*inv_i) == i*i * inv_i*inv_i
    assert((i * inv_i) * (i * inv_i) == (i * i) * (inv_i * inv_i)) by {
        lemma_product_square_factorize(i as int, inv_i as int);
    };

    // So (i*i * inv_i*inv_i) % p == 1
    // Which means (neg_one * inv_i_sq_raw) % p == 1
    // where inv_i_sq_raw = inv_i * inv_i
    assert(((i * i) * (inv_i * inv_i)) % pn == 1);

    // Now compute (y*y * inv_i*inv_i) % p
    // = ((y*y % p) * (inv_i*inv_i % p)) % p    [by mod absorption]
    // = (neg_one * inv_i_sq) % p
    // = ((i*i % p) * (inv_i*inv_i % p)) % p    [since y*y % p == i*i % p]
    // = (i*i * inv_i*inv_i) % p                 [by mod absorption backwards]
    // = 1
    assert(((y * y) * (inv_i * inv_i)) % pn == 1) by {
        // ((y*y) * (inv_i*inv_i)) % p == ((y*y % p) * (inv_i*inv_i)) % p
        lemma_mul_mod_noop_left((y * y) as int, (inv_i * inv_i) as int, pn as int);
        // = ((i*i % p) * (inv_i*inv_i)) % p since y*y % p == i*i % p
        // = ((i*i) * (inv_i*inv_i)) % p
        lemma_mul_mod_noop_left((i * i) as int, (inv_i * inv_i) as int, pn as int);
    };

    // Chain: q*q % p == (y*inv_i)^2 % p == (y*y)*(inv_i*inv_i) % p == 1
    assert((q * q) % pn == 1);

    // Apply lemma_square_root_of_unity
    lemma_square_root_of_unity(q, pn);
    // q % p ∈ {1, p-1}

    // Since q < p: q % p == q
    lemma_small_mod(q, pn);

    // Shared fact for both branches: (q * i) % p == y % p
    lemma_q_times_i_eq_y(y, i, inv_i, q, pn);

    if q == 1 {
        // q == 1, so (1 * i) % p == y % p, hence y ≡ i (mod p)
        assert(i == y % pn) by {
            lemma_mul_basics(i as int);
            lemma_small_mod(i, pn);
        };
    } else {
        assert(q == neg_one);
        // q == p - 1, so ((p-1) * i) % p == y % p
        // (p-1)*i ≡ -i (mod p)
        assert((i * ((pn - 1) as nat)) % pn == (pn - i) as nat) by {
            lemma_mul_by_minus_one_is_negation(i, pn);
            lemma_small_mod(i, pn);
            lemma_small_mod((pn - i) as nat, pn);
        };
        assert(((pn - 1) as nat) * i == i * ((pn - 1) as nat)) by {
            lemma_mul_is_commutative(((pn - 1) as nat) as int, i as int);
        };
        assert(y % pn == (pn - i) as nat);
    }
}

/// Lemma: x^((p-1)/4) is a 4th root of unity in F_p
///
/// For nonzero x in F_p where p = 2^255 - 19:
///   x^((p-1)/4) ∈ {1, p-1, i, p-i}
///
/// Proof:
///   Let y = x^((p-1)/4). Then y^2 = x^((p-1)/2).
///   By Euler's criterion, y^2 ∈ {1, -1}.
///   If y^2 = 1: by lemma_square_root_of_unity, y ∈ {1, -1}
///   If y^2 = -1: by lemma_square_root_of_neg_one, y ∈ {i, -i}
pub proof fn lemma_fourth_root_of_unity(x: nat)
    requires
        x % p() != 0,
    ensures
        ({
            let y = (pow(x as int, ((p() - 1) / 4) as nat) as nat) % p();
            let i = sqrt_m1();
            y == 1 || y == (p() - 1) as nat || y == i || y == (p() - i) as nat
        }),
{
    let pn = p();
    p_gt_2();
    axiom_p_is_prime();

    let quarter = ((pn - 1) / 4) as nat;
    let half = ((pn - 1) / 2) as nat;

    // quarter * 2 == half (from lemma_p_divisibility_facts)
    assert(quarter * 2 == half) by {
        lemma_p_divisibility_facts();
    };

    // y_raw = x^quarter (as int, before mod)
    let y_pow = pow(x as int, quarter);
    assert(y_pow >= 0) by {
        lemma_pow_nonnegative(x as int, quarter);
    };
    let y = (y_pow as nat) % pn;

    // y_pow^2 = x^(quarter*2) = x^half
    assert(pow(y_pow, 2) == pow(x as int, half)) by {
        lemma_pow_multiplies(x as int, quarter, 2);
    };

    // (y * y) % p == x^half % p
    assert((y * y) % pn == (pow(x as int, half) as nat) % pn) by {
        lemma_mul_mod_noop(y_pow as int, y_pow as int, pn as int);
        lemma_pow_2_is_mul(y_pow);
    };

    // By Euler's criterion: x^half % p ∈ {1, p-1}
    lemma_euler_criterion(x, pn);
    let x_half_mod = (pow(x as int, half) as nat) % pn;
    assert(x_half_mod == 1 || x_half_mod == (pn - 1) as nat);

    // Therefore (y * y) % p ∈ {1, p-1}

    if x_half_mod == 1 {
        // y^2 ≡ 1 (mod p)
        assert((y * y) % pn == 1);
        lemma_square_root_of_unity(y, pn);
        // y % p ∈ {1, p-1}
        assert(y % pn == 1 || y % pn == (pn - 1) as nat);
        // Since y < p, y % p == y
        lemma_small_mod(y, pn);
    } else {
        // y^2 ≡ -1 (mod p)
        assert((y * y) % pn == (pn - 1) as nat);
        let i = sqrt_m1();
        lemma_sqrt_m1_nonzero();
        lemma_square_root_of_neg_one(y, i);
        // y % p ∈ {i, p-i}
        // Since y < p, y % p == y
        lemma_small_mod(y, pn);
    }
}

} // verus!
