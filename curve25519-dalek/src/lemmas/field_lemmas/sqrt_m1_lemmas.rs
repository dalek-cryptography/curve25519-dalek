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
/// Used in: lemma_flipped_sign_becomes_correct
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
            assert((r * i) * (r * i) == (r * r) * (i * i)) by (nonlinear_arith);
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

    // Show i ≠ 0: If i = 0, then i² = 0, but i² ≡ -1 (mod p), contradiction
    assert(i != 0) by {
        if i == 0 {
            // 0 * 0 = 0, so (0 * 0) % p = 0
            assert(0 * 0 == 0nat);
            assert(0nat % p == 0) by {
                lemma_small_mod(0nat, p);
            };
            // But axiom says i² % p = p - 1
            assert((i * i) % p == (p - 1) as nat) by {
                axiom_sqrt_m1_squared();
            };
            // Since i = 0, we have 0 = p - 1, but p > 2
            assert(false);
        }
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
///                   = i                    [by lemma_double_negation]
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
        if i == 0 {
            axiom_sqrt_m1_squared();
            lemma_small_mod(0nat, p);
            assert((0nat * 0nat) % p == 0);
            assert(field_neg(1nat) != 0);  // -1 ≠ 0
            assert(false);
        }
    };
    assert(field_mul(neg_one, neg_i) == i) by {
        lemma_double_negation(i);
    };

    // Postcondition: i % p = i (since i < p)
    lemma_small_mod(i, p);
}

} // verus!
