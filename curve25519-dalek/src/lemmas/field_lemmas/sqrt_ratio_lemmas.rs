//! This file contains lemmas needed to verify sqrt_ratio_i (field.rs) and
//! related decompress proofs.
//!
//! ## Main Lemmas (Public API)
//!
//! - `lemma_is_sqrt_ratio_to_field` — converts fe51_is_sqrt_ratio to math_field form
//! - `lemma_no_square_root_when_times_i` — failure case: x²·v = i·u implies no r with r²·v = ±u
//! - `lemma_algebraic_chain_base` — proves q² = (r²·v) · inv(i·u)
//! - `lemma_sqrt_ratio_correctness` — nat-level correctness of the 4 postconditions
//! - `lemma_sqrt_ratio_check_value` — check = u · w^((p-1)/4)
//! - `lemma_negate_makes_nonnegative` — parity/bounds after conditional negate
//!
//! ## Dependencies
//!
//! This module uses lemmas from `sqrt_m1_lemmas` for properties of i = sqrt(-1),
//! and `field_algebra_lemmas` for general field-negation facts.
//!
//! ## Lemma Dependency Graph (field.rs callers)
//!
//! ```text
//! field.rs::sqrt_ratio_i (inline proof block)
//!     ├──► lemma_negate_makes_nonnegative
//!     ├──► lemma_sqrt_ratio_correctness
//!     │        ├──► lemma_multiply_by_i_flips_sign (sqrt_m1_lemmas)
//!     │        └──► lemma_eq_neg_times_i_implies_zero
//!     ├──► lemma_sqrt_ratio_check_value
//!     ├──► lemma_field_mul_square_canonical (field_algebra_lemmas)
//!     └──► lemma_fourth_root_of_unity (sqrt_m1_lemmas)
//!
//! step1_lemmas.rs ──► lemma_no_square_root_when_times_i
//!                 ──► lemma_is_sqrt_ratio_to_field
//! ```
#![allow(unused_imports)]
use crate::backend::serial::u64::field::FieldElement51;
use crate::backend::serial::u64::subtle_assumes::*;
use crate::constants;
#[allow(unused_imports)]
use crate::field::FieldElement;
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::lemmas::field_lemmas::as_bytes_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::primality_specs::*;
use subtle::Choice;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

//=============================================================================
// Lemmas for sqrt_ratio_i algorithm (using generic u, v parameters)
//
// These prove properties of the sqrt_ratio_i computation:
//   r = (uv³)(uv⁷)^((p-5)/8)
//   check = v * r²
//
// The algorithm checks if check ∈ {u, -u, u·i, -u·i} to determine
// whether u/v has a square root.
//=============================================================================
/// Prove: fe51_is_sqrt_ratio implies the math_field form
///
/// When sqrt_ratio_i returns true and v ≠ 0:
///   fe51_is_sqrt_ratio(u, v, X) holds
///   which means: (x * x * v) % p == u
///   which equals: field_mul(field_square(x), v) == u
pub proof fn lemma_is_sqrt_ratio_to_field(
    x: nat,  // fe51_as_canonical_nat(&X)
    u: nat,  // fe51_as_canonical_nat(&u_field_elem)
    v: nat,  // fe51_as_canonical_nat(&v_field_elem)
)
    requires
        is_sqrt_ratio(u, v, x),
    ensures
        field_mul(field_square(x), v) == u % p(),
{
    let p = p();
    p_gt_2();

    // field_square(x) = (x * x) % p
    let x2 = field_square(x);

    // Apply mod absorption: (x*x * v) % p == ((x*x % p) * (v % p)) % p
    // This gives us field_mul((x*x) % p, v % p) == u % p
    assert(((x * x) * v) % p == (((x * x) % p) * (v % p)) % p) by {
        lemma_mul_mod_noop_general((x * x) as int, v as int, p as int);
    };

    // Since x2 = (x*x) % p, we have field_mul(x2, v % p) == u % p
    // And field_mul(x2, v % p) == field_mul(x2, v) by mod absorption
    assert(field_mul(x2, v) == u % p) by {
        lemma_mul_mod_noop_right(x2 as int, v as int, p as int);
    };
}

/// Unified algebraic chain: proves q² = (r²·v) · inv(i·u)
///
/// This is the geometric/structural part shared by both Case 1 and Case 2.
/// The v terms cancel out, leaving q² = (r²·v) · inv(i·u).
///
/// Given:
///   - x²·v = i·u
///   - q = r/x
///
/// Derives r_squared_v = r²·v internally, then proves: q² = r_squared_v · inv(i·u)
///
/// The caller then uses:
/// - lemma_u_times_inv_iu_is_neg_i (when r²·v = u) to get q² = -i
/// - lemma_neg_u_times_inv_iu_is_i (when r²·v = -u) to get q² = i
proof fn lemma_algebraic_chain_base(u: nat, v: nat, x: nat, r: nat, i: nat)
    requires
        v % p() != 0,
        u % p() != 0,
        x % p() != 0,
        x < p(),
        r < p(),
        i == sqrt_m1(),
        i % p() != 0,
        field_mul(field_square(x), v) == (i * u) % p(),
    ensures
        ({
            let q = field_mul(r, field_inv(x));
            let r_squared_v = field_mul(field_square(r), v);
            let iu = field_mul(i, u);
            let inv_iu = field_inv(iu);
            field_square(q) == field_mul(r_squared_v, inv_iu)
        }),
{
    let p = p();
    p_gt_2();

    // Define key values
    let r2 = field_square(r);
    let x2 = field_square(x);
    let inv_v = field_inv(v);
    let inv_x = field_inv(x);
    let q = field_mul(r, inv_x);
    let q2 = field_square(q);
    let iu = field_mul(i, u);
    let r_squared_v = field_mul(r2, v);  // Derive r²·v from r and v

    // --- Step 1: q² = r² · inv(x²) ---
    let inv_x2 = field_inv(x2);
    assert(q2 == field_mul(r2, inv_x2)) by {
        lemma_quotient_of_squares(r, x);
    };

    // r_squared_v < p (field operation result)
    assert(r_squared_v < p) by {
        lemma_mod_bound((r2 * v) as int, p as int);
    };

    // --- Step 2: Derive r² = r_squared_v · inv(v) from r²·v = r_squared_v ---
    assert(r2 % p == field_mul(r_squared_v, inv_v)) by {
        // r_squared_v < p, so r_squared_v % p == r_squared_v
        lemma_small_mod(r_squared_v, p);
        assert(field_mul(r2, v) == r_squared_v % p);
        lemma_solve_for_left_factor(r2, v, r_squared_v);
    };

    // --- Step 3: Derive x² = (i·u) · inv(v) from x²·v = i·u ---
    assert(x2 % p == field_mul(iu, inv_v)) by {
        lemma_mod_twice((i * u) as int, p as int);
        assert(iu % p == (i * u) % p);
        lemma_solve_for_left_factor(x2, v, iu);
        lemma_mul_mod_noop_left((i * u) as int, inv_v as int, p as int);
    };

    // --- Step 4: Compute inv(x²) = inv(i·u) · v ---

    // First show (i·u) % p != 0
    assert(iu % p != 0) by {
        lemma_mod_bound((i * u) as int, p as int);
        lemma_mod_twice((i * u) as int, p as int);
        if (i * u) % p == 0 {
            axiom_p_is_prime();
            lemma_euclid_prime(i, u, p);
            assert(false);
        }
    };

    // Show inv_v % p != 0
    assert(inv_v % p != 0) by {
        field_inv_property(v);
        lemma_small_mod(inv_v, p);
        if inv_v == 0 {
            assert(((v % p) * 0) % p == 0);
            lemma_small_mod(0, p);
            assert(false);
        }
    };

    let iu_times_inv_v = field_mul(iu, inv_v);

    // x2 = iu_times_inv_v (both are < p field elements)
    assert(x2 == iu_times_inv_v) by {
        lemma_mod_twice((x * x) as int, p as int);
    };

    let inv_iu = field_inv(iu);

    // inv_x2 = inv(iu) · v
    assert(inv_x2 == field_mul(inv_iu, v)) by {
        lemma_inv_of_product(iu, inv_v);
        lemma_inv_of_inv(v);
        lemma_mod_bound(v as int, p as int);
        lemma_mul_mod_noop_right(inv_iu as int, v as int, p as int);
    };

    // --- Step 5: Compute r2 as field element ---
    let r_squared_v_times_inv_v = field_mul(r_squared_v, inv_v);
    assert(r2 == r_squared_v_times_inv_v) by {
        lemma_mod_twice((r * r) as int, p as int);
    };

    // --- Step 6: q² = r_squared_v · inv(i·u) (v terms cancel) ---
    let r_squared_v_times_inv_iu = field_mul(r_squared_v, inv_iu);

    assert(q2 == r_squared_v_times_inv_iu) by {
        // q² = r² · inv_x2 = (r_squared_v · inv_v) · (inv_iu · v)
        // The v terms cancel: inv_v · v = 1
        assert(field_mul(inv_v, v) == 1) by {
            field_inv_property(v);
            lemma_mul_mod_noop_left(v as int, inv_v as int, p as int);
            lemma_field_mul_comm(inv_v, v);
        };

        lemma_mul_mod_noop((r_squared_v * inv_v) as int, (inv_iu * v) as int, p as int);

        // (r_squared_v * inv_v) * (inv_iu * v) = r_squared_v * inv_iu * (inv_v * v)
        assert((r_squared_v * inv_v) * (inv_iu * v) == r_squared_v * inv_iu * (inv_v * v)) by {
            lemma_mul_is_associative(r_squared_v as int, inv_v as int, (inv_iu * v) as int);
            lemma_mul_is_associative(inv_v as int, inv_iu as int, v as int);
            lemma_mul_is_commutative(inv_v as int, inv_iu as int);
            lemma_mul_is_associative(inv_iu as int, inv_v as int, v as int);
            lemma_mul_is_associative(r_squared_v as int, inv_iu as int, (inv_v * v) as int);
        };

        assert((inv_v * v) % p == 1) by {
            field_inv_property(v);
            lemma_mul_mod_noop_left(v as int, inv_v as int, p as int);
            lemma_mul_is_commutative(inv_v as int, v as int);
        };

        assert((r_squared_v * inv_iu * (inv_v * v)) % p == (r_squared_v * inv_iu) % p) by {
            lemma_mul_mod_noop_right((r_squared_v * inv_iu) as int, (inv_v * v) as int, p as int);
            lemma_mul_basics((r_squared_v * inv_iu) as int);
        };
    };
}

/// Lemma: If r²·v = i·u (where i = sqrt(-1)), then no r' exists with r'²·v = ±u
///
/// This is the key lemma for proving sqrt_ratio_i failure implies invalid y.
///
/// Mathematical reasoning (proof by contradiction):
///
/// Case 1: Suppose r'²·v = u for some r'
///   - We have x²·v = i·u (precondition)
///   - Then (r'/x)² = (r'²·v)/(x²·v) = u/(i·u) = 1/i
///   - Now 1/i = i⁻¹ = i³ (since i⁴ = 1) = i²·i = (-1)·i = -i
///   - So (r'/x)² = -i
///   - But -i is not a square (axiom_neg_sqrt_m1_not_square)
///   - Contradiction! ∎
///
/// Case 2: Suppose r'²·v = -u for some r'
///   - We have x²·v = i·u (precondition)
///   - Then (r'/x)² = (r'²·v)/(x²·v) = -u/(i·u) = -1/i = -i⁻¹ = -(-i) = i
///   - But i is not a square (axiom_sqrt_m1_not_square)
///   - Contradiction! ∎
pub proof fn lemma_no_square_root_when_times_i(u: nat, v: nat, r: nat)
    requires
        v % p() != 0,
        u % p() != 0,
        r < p(),
        // There exists x with x²·v = i·u
        exists|x: nat|
            x < p() && #[trigger] field_mul(field_square(x), v) == field_mul(sqrt_m1(), u),
    ensures
// r²·v ≠ u and r²·v ≠ -u

        field_mul(field_square(r), v) != field_canonical(u) && field_mul(field_square(r), v)
            != field_neg(u),
{
    let the_p = p();
    let i = sqrt_m1();

    // Get the witness x with x²·v = i·u
    let x = choose|x: nat|
        x < p() && #[trigger] field_mul(field_square(x), v) == field_mul(sqrt_m1(), u);

    // ========== Common Setup ==========
    // These facts are needed by both cases

    // x ≠ 0 (if x = 0, then 0 = i·u, but u ≠ 0 and i ≠ 0)
    assert(x != 0) by {
        if x == 0 {
            assert(field_square(0) == 0) by {
                lemma_small_mod(0, the_p);
            };
            assert(field_mul(0, v) == 0) by {
                assert(0 * v == 0);  // 0 * anything = 0
                lemma_small_mod(0, the_p);  // 0 % p = 0
            };
            assert(i != 0) by {
                lemma_sqrt_m1_nonzero();
            };
            assert((i * u) % the_p != 0) by {
                if (i * u) % the_p == 0 {
                    axiom_p_is_prime();
                    lemma_euclid_prime(i, u, the_p);
                    assert(i % the_p != 0) by {
                        lemma_small_mod(i, the_p);
                    };
                    // Contradiction: Euclid says i % p == 0 or u % p == 0,
                    // but i % p != 0 (above) and u % p != 0 (from requires)
                    assert(false);
                }
            };
            // Contradiction: x=0 implies LHS=0, but (i*u) % p != 0 means RHS != 0
            assert(false);
        }
    };

    // x % p != 0
    assert(x % the_p != 0) by {
        lemma_small_mod(x, the_p);
    };

    // i ≠ 0, i < p, i % p != 0
    assert(i != 0 && i < the_p && i % the_p != 0) by {
        lemma_sqrt_m1_nonzero();
    };

    // Define q = r/x (used in both cases)
    let x_inv = field_inv(x);
    let q = field_mul(r, x_inv);

    // q < p (since q is a field element)
    assert(q < the_p) by {
        lemma_mod_bound((r * x_inv) as int, the_p as int);
    };

    // ========== Case 1: r²·v = u ==========
    // If true, then q² = -i, but -i is not a square → contradiction
    if field_mul(field_square(r), v) == u % the_p {
        let r_squared_v = u % the_p;
        let iu = field_mul(i, u);
        let inv_iu = field_inv(iu);
        let q2 = field_square(q);
        let neg_i = (the_p - i) as nat;

        // Step 1: r_squared_v < p
        assert(r_squared_v < the_p) by {
            lemma_mod_bound(u as int, the_p as int);
        };

        // Step 2: q² = r_squared_v · inv(i·u) (from algebraic chain)
        assert(q2 == field_mul(r_squared_v, inv_iu)) by {
            lemma_algebraic_chain_base(u, v, x, r, i);
            // lemma ensures q² = field_mul(field_square(r), v) · inv_iu
            // and the if-condition gives field_mul(field_square(r), v) == r_squared_v
        };

        // Step 3: u · inv(i·u) = -i
        assert(field_mul(u, inv_iu) == field_neg(i)) by {
            lemma_u_times_inv_iu_is_neg_i(u, i);
        };

        // Step 4: Connect r_squared_v to u for field multiplication
        assert(field_mul(r_squared_v, inv_iu) == field_mul(u, inv_iu)) by {
            lemma_mul_mod_noop_left(u as int, inv_iu as int, the_p as int);
        };

        // Step 5: Therefore q² = -i
        assert(q2 == field_neg(i));

        // Step 6: Connect field_neg(i) to (p - i)
        assert(field_neg(i) == neg_i) by {
            lemma_small_mod(i, the_p);
            lemma_small_mod((the_p - i) as nat, the_p);
        };

        // Step 7: -i is not a square (axiom) — CONTRADICTION
        assert(!is_square(neg_i)) by {
            axiom_neg_sqrt_m1_not_square();
        };

        // But q² = -i means -i IS a square (q is the witness)
        assert(field_mul(q, q) == field_canonical(neg_i)) by {
            lemma_small_mod(q2, the_p);
            lemma_small_mod(neg_i, the_p);
        };
        assert(is_square(neg_i));

        // Contradiction: -i is both a square and not a square
        assert(false);
    }
    // ========== Case 2: r²·v = -u ==========
    // If true, then q² = i, but i is not a square → contradiction

    if field_mul(field_square(r), v) == field_neg(u) {
        let r_squared_v = field_neg(u);
        let iu = field_mul(i, u);
        let inv_iu = field_inv(iu);
        let q2 = field_square(q);

        // Step 1: r_squared_v < p
        assert(r_squared_v < the_p) by {
            lemma_mod_bound((the_p - (u % the_p)) as int, the_p as int);
        };

        // Step 2: q² = (-u) · inv(i·u) (from algebraic chain)
        assert(q2 == field_mul(r_squared_v, inv_iu)) by {
            lemma_algebraic_chain_base(u, v, x, r, i);
            // lemma ensures q² = field_mul(field_square(r), v) · inv_iu
            // and the if-condition gives field_mul(field_square(r), v) == r_squared_v
        };

        // Step 3: (-u) · inv(i·u) = i
        assert(field_mul(field_neg(u), inv_iu) == i % the_p) by {
            lemma_neg_u_times_inv_iu_is_i(u, i);
        };

        // Step 4: Therefore q² = i % p
        assert(q2 == i % the_p);

        // Step 5: i is not a square (axiom) — CONTRADICTION
        assert(!is_square(i)) by {
            axiom_sqrt_m1_not_square();
        };

        // But q² = i means i IS a square (q is the witness)
        assert(field_mul(q, q) == field_canonical(i)) by {
            lemma_small_mod(q2, the_p);
            lemma_small_mod(i, the_p);
        };
        assert(is_square(i));

        // Contradiction: i is both a square and not a square
        assert(false);
    }
}

// =============================================================================
// Main lemma: check = u * w^((p-1)/4) where w = u * v^7
// =============================================================================
/// The core algebraic identity for sqrt_ratio_i:
///
/// Given the computation in sqrt_ratio_i:
///   v3 = v^2 * v
///   v7 = v3^2 * v
///   w  = u * v7
///   r  = (u * v3) * pow_p58(w)     [pow_p58 computes w^((p-5)/8)]
///   check = v * r^2
///
/// This lemma proves:
///   check = field_mul(u % p, w^((p-1)/4) % p)
///
/// Mathematical derivation:
///   check = v * r^2
///         = v * (u*v^3)^2 * (w^((p-5)/8))^2
///         = v * u^2 * v^6 * w^((p-5)/4)
///         = u * (u*v^7) * w^((p-5)/4)
///         = u * w * w^((p-5)/4)
///         = u * w^(1 + (p-5)/4)
///         = u * w^((p-1)/4)
pub proof fn lemma_sqrt_ratio_check_value(u_val: nat, v_val: nat)
    requires
        v_val % p() != 0,
    ensures
        ({
            let v3 = field_mul(field_square(v_val), v_val);
            let v7 = field_mul(field_square(v3), v_val);
            let w = field_mul(u_val, v7);
            let uv3 = field_mul(u_val, v3);
            let k = ((p() - 5) / 8) as nat;
            let pow_result = (pow(w as int, k) as nat) % p();
            let r = field_mul(uv3, pow_result);
            let check = field_mul(v_val, field_square(r));
            let quarter = ((p() - 1) / 4) as nat;
            let fourth_root = (pow(w as int, quarter) as nat) % p();
            &&& pow(w as int, k) >= 0
            &&& pow(w as int, quarter) >= 0
            &&& check == field_mul(u_val, fourth_root)
        }),
{
    let pn = p();
    p_gt_2();

    let v3 = field_mul(field_square(v_val), v_val);
    let v7 = field_mul(field_square(v3), v_val);
    let w = field_mul(u_val, v7);
    let uv3 = field_mul(u_val, v3);
    let k = ((pn - 5) / 8) as nat;
    lemma_pow_nonnegative(w as int, k);
    let pow_w_k = pow(w as int, k);
    let b = (pow_w_k as nat) % pn;  // b = w^k mod p
    let r = field_mul(uv3, b);
    let check = field_mul(v_val, field_square(r));
    let quarter = ((pn - 1) / 4) as nat;

    // === Step 1: field_square(r) = field_mul(field_square(uv3), field_square(b)) ===
    lemma_product_of_squares_eq_square_of_product(uv3, b);
    let sq_uv3 = field_square(uv3);
    let sq_b = field_square(b);
    assert(field_square(r) == field_mul(sq_uv3, sq_b));

    // === Step 2: check = field_mul(v, field_mul(sq_uv3, sq_b)) ===
    //           = field_mul(field_mul(v, sq_uv3), sq_b)  [by associativity]
    assert(check == field_mul(field_mul(v_val, sq_uv3), sq_b)) by {
        lemma_field_mul_assoc(v_val, sq_uv3, sq_b);
    };

    // === Step 3: field_mul(v, sq_uv3) = field_mul(u, w) ===
    lemma_v_times_sq_uv3_eq_u_times_w(u_val, v_val);
    assert(field_mul(v_val, sq_uv3) == field_mul(u_val, w));

    // === Step 4: check = field_mul(field_mul(u, w), sq_b) ===
    assert(check == field_mul(field_mul(u_val, w), sq_b));

    // === Step 5: sq_b = w^(2k) % p ===
    lemma_field_square_of_pow_mod(w as int, k);
    assert(sq_b == (pow(w as int, 2 * k) as nat) % pn);

    // === Step 6: field_mul(w, sq_b) = w^(2k+1) % p ===
    // Rewrite: check = field_mul(u, field_mul(w, sq_b))  [by associativity]
    assert(check == field_mul(u_val, field_mul(w, sq_b))) by {
        lemma_field_mul_assoc(u_val, w, sq_b);
    };

    // field_mul(w, sq_b) = (w * sq_b) % p
    // sq_b = pow(w, 2k) % p
    // (w * (pow(w, 2k) % p)) % p = (w * pow(w, 2k)) % p   [mod absorption]
    // = pow(w, 2k + 1) % p                                   [pow addition]
    let two_k = (2 * k) as nat;
    lemma_pow_nonnegative(w as int, two_k);

    assert(field_mul(w, sq_b) == (pow(w as int, (two_k + 1) as nat) as nat) % pn) by {
        // (w * (pow(w, 2k) % p)) % p = (w * pow(w, 2k)) % p
        lemma_mul_mod_noop_right(w as int, (pow(w as int, two_k) as nat) as int, pn as int);

        // w * pow(w, 2k) = pow(w, 1) * pow(w, 2k)
        assert(w as int * pow(w as int, two_k) == pow(w as int, 1) * pow(w as int, two_k)) by {
            lemma_pow1(w as int);
        };

        // pow(w, 1) * pow(w, 2k) = pow(w, 2k + 1)
        lemma_pow_adds(w as int, 1, two_k);

        // Nonneg for the result
        lemma_pow_nonnegative(w as int, (two_k + 1) as nat);
    };

    // === Step 7: 2k + 1 = (p-1)/4 ===
    assert(two_k + 1 == quarter) by {
        lemma_p_divisibility_facts();
    };

    // === Final: check = field_mul(u, pow(w, quarter) % p) ===
    lemma_pow_nonnegative(w as int, quarter);
}

/// After conditional_negate with is_negative, the result has even parity.
/// That is: if r_nat was odd, field_neg(r_nat) is even; if r_nat was even, it stays even.
pub proof fn lemma_conditional_negate_makes_even(r_nat: nat, negated: bool)
    requires
        r_nat < p(),
        negated == (r_nat % 2 == 1),
    ensures
        negated ==> (field_neg(r_nat) as nat) % 2 == 0,
        !negated ==> r_nat % 2 == 0,
        (if negated {
            field_neg(r_nat)
        } else {
            r_nat
        }) % 2 == 0,
{
    if negated {
        // r_nat is odd and 0 < r_nat < p
        assert(r_nat != 0) by {
            // 0 % 2 == 0, but we need odd
        };
        assert(r_nat % 2 == 1);
        // field_neg(r_nat) = (p - r_nat % p) % p
        // Since r_nat < p: r_nat % p == r_nat
        lemma_small_mod(r_nat, p());
        // field_neg(r_nat) = (p - r_nat) % p
        // Since 0 < r_nat < p: 0 < p - r_nat < p
        assert(0 < (p() - r_nat) as int);
        assert((p() - r_nat) < p());
        lemma_small_mod((p() - r_nat) as nat, p());
        // field_neg(r_nat) = p - r_nat
        assert(field_neg(r_nat) == (p() - r_nat) as nat);
        // p is odd, r_nat is odd → p - r_nat is even
        lemma_p_is_odd();
        assert(p() % 2 == 1);
        // odd - odd = even
        assert(((p() - r_nat) as nat) % 2 == 0) by {
            lemma_sub_mod_noop(p() as int, r_nat as int, 2int);
        };
    }
    // else: r_nat is even, stays as is

}

/// FE51 bridge: after `is_negative` + `conditional_negate_field_element`,
/// the result is nonnegative (even parity) and 52-bit bounded.
///
/// This thin wrapper bridges FE51 types to the value-level
/// `lemma_conditional_negate_makes_even`.
pub proof fn lemma_negate_makes_nonnegative(
    r_before: &FieldElement51,
    r_after: &FieldElement51,
    is_neg: Choice,
)
    requires
        fe51_limbs_bounded(r_before, 52),
        choice_is_true(is_neg) == (spec_fe51_as_bytes(r_before)[0] & 1 == 1),
        fe51_limbs_bounded(r_after, 54),
        choice_is_true(is_neg) ==> fe51_limbs_bounded(r_after, 52),
        !choice_is_true(is_neg) ==> *r_after == *r_before,
        fe51_as_canonical_nat(r_after) == if choice_is_true(is_neg) {
            field_neg(fe51_as_canonical_nat(r_before))
        } else {
            fe51_as_canonical_nat(r_before)
        },
    ensures
        fe51_as_canonical_nat(r_after) % 2 == 0,
        fe51_limbs_bounded(r_after, 52),
{
    lemma_is_negative_equals_parity(r_before);
    let r_nat = fe51_as_canonical_nat(r_before);
    p_gt_2();
    lemma_mod_bound(u64_5_as_nat(r_before.limbs) as int, p() as int);
    lemma_conditional_negate_makes_even(r_nat, choice_is_true(is_neg));
}

/// If u == (-u)*i in the field (where i = sqrt_m1), then u == 0.
///
/// Proof outline: u = (-u)*i. Multiply by i: u*i = (-u)*i^2 = (-u)*(-1) = u.
/// So u*i = u, meaning u*(i-1) = 0 mod p. Since p is prime and i != 1, u = 0.
pub proof fn lemma_eq_neg_times_i_implies_zero(u: nat)
    requires
        u < p(),
        u == field_mul(field_neg(u), sqrt_m1()),
    ensures
        u == 0,
{
    let pn = p();
    let i = sqrt_m1();
    p_gt_2();

    if u != 0 {
        // Step 1: field_mul(u, i) = field_mul(field_mul(field_neg(u), i), i)  [since u == (-u)*i]
        //       = field_mul(field_neg(u), field_mul(i, i))  [associativity]
        //       = field_mul(field_neg(u), field_square(i))
        //       = field_mul(field_neg(u), field_neg(1))     [i^2 = -1]
        //       = u                                          [double negation distributes]
        // i^2 = field_neg(1) (from sqrt_m1 squared)
        // axiom gives (i*i)%p == p-1. field_square(i) = (i*i)%p. field_neg(1) = (p - 1%p)%p = p-1.
        axiom_sqrt_m1_squared();
        lemma_small_mod(1nat, pn);
        lemma_small_mod((pn - 1) as nat, pn);
        let i_sq = field_square(i);
        assert(i_sq == (pn - 1) as nat);
        assert(field_neg(1nat) == (pn - 1) as nat);
        assert(i_sq == field_neg(1nat));

        // field_mul(u, i) = field_mul(field_mul(field_neg(u), i), i) by substitution
        // = field_mul(field_neg(u), field_mul(i, i)) by associativity
        lemma_field_mul_assoc(field_neg(u), i, i);

        // field_mul(field_neg(u), field_neg(1)) = (-u)*(-1) = field_neg(field_neg(u)) = u
        lemma_neg_one_times_is_neg(field_neg(u));
        lemma_field_mul_comm(field_neg(u), field_neg(1nat));
        lemma_field_neg_neg(u);
        lemma_small_mod(u, pn);
        assert(field_mul(u, i) == u);

        // Step 2: Show i >= 2 (i != 0 and i != 1)
        assert(i != 0) by {
            lemma_sqrt_m1_nonzero();
        };
        assert(i != 1) by {
            // If i == 1: (1*1)%p = 1, but (i*i)%p = p-1. Since p > 2, 1 != p-1. Contradiction.
            if i == 1 {
                assert((1 as nat * 1 as nat) % pn == 1) by {
                    lemma_small_mod(1nat, pn);
                };
                assert(false);
            }
        };
        assert(i >= 2);

        // Step 3: field_mul(u, i) == u means (u*i) % p == u.
        //   So u*i - u ≡ 0 (mod p), i.e., u*(i-1) ≡ 0 (mod p).
        //   This gives field_mul(u, i-1) == 0.
        let i_minus_1 = (i - 1) as nat;
        assert(i_minus_1 > 0);
        assert(i_minus_1 < pn);
        lemma_small_mod(u, pn);

        // (u*i) % p = u = u % p, so (u*i - u) % p = 0
        lemma_mod_sub_eq_implies_zero((u * i) as int, u as int, pn as int);
        // u*(i-1) = u*i - u
        assert(u * i_minus_1 == u * i - u) by {
            lemma_mul_is_distributive_sub(u as int, i as int, 1int);
            lemma_mul_basics(u as int);
        };
        assert(field_mul(u, i_minus_1) == 0);

        // Step 4: By nonzero_product: u%p != 0 && (i-1)%p != 0 => field_mul(u, i-1) != 0
        //   But field_mul(u, i-1) == 0. Contradiction.
        lemma_small_mod(u, pn);
        lemma_small_mod(i_minus_1, pn);
        lemma_nonzero_product(u, i_minus_1);
        assert(false);
    }
}

/// Proves w = u*v^7 is nonzero when u and v are nonzero in F_p.
///
/// The chain: v^2 != 0, v^3 != 0, v^6 != 0, v^7 != 0, u*v^7 != 0.
pub proof fn lemma_uv7_nonzero(u_nat: nat, v_nat: nat)
    requires
        u_nat < p(),
        v_nat < p(),
        u_nat != 0,
        v_nat != 0,
    ensures
        ({
            let v3 = field_mul(field_square(v_nat), v_nat);
            let v7 = field_mul(field_square(v3), v_nat);
            let w = field_mul(u_nat, v7);
            w % p() != 0
        }),
{
    let pn = p();
    p_gt_2();
    lemma_small_mod(v_nat, pn);
    lemma_small_mod(u_nat, pn);

    let v_sq = field_square(v_nat);
    assert(v_sq % pn != 0) by {
        lemma_nonzero_product(v_nat, v_nat);
        lemma_mod_bound(v_sq as int, pn as int);
        lemma_small_mod(v_sq, pn);
    };
    let v3 = field_mul(v_sq, v_nat);
    assert(v3 % pn != 0) by {
        lemma_nonzero_product(v_sq, v_nat);
        lemma_mod_bound(v3 as int, pn as int);
        lemma_small_mod(v3, pn);
    };
    let v3_sq = field_square(v3);
    assert(v3_sq % pn != 0) by {
        lemma_nonzero_product(v3, v3);
        lemma_mod_bound(v3_sq as int, pn as int);
        lemma_small_mod(v3_sq, pn);
    };
    let v7 = field_mul(v3_sq, v_nat);
    assert(v7 % pn != 0) by {
        lemma_nonzero_product(v3_sq, v_nat);
        lemma_mod_bound(v7 as int, pn as int);
        lemma_small_mod(v7, pn);
    };
    let w = field_mul(u_nat, v7);
    assert(w % pn != 0) by {
        lemma_nonzero_product(u_nat, v7);
        lemma_mod_bound(w as int, pn as int);
        lemma_small_mod(w, pn);
    };
}

/// Proves the fourth-root-of-unity pattern for check = v * r^2.
///
/// When u != 0 and v != 0, check must be one of {u, -u, u*i, -u*i}.
/// This follows from check = u * w^((p-1)/4) and w^((p-1)/4) being a 4th root of unity.
pub proof fn lemma_check_fourth_root_pattern(
    u_nat: nat,
    v_nat: nat,
    check_nat: nat,
    r_orig_nat: nat,
)
    requires
        u_nat < p(),
        v_nat < p(),
        check_nat < p(),
        u_nat != 0,
        v_nat != 0,
        check_nat == field_mul(v_nat, field_square(r_orig_nat)),
        // r_orig = field_mul(uv3, pow_result) — i.e., the sqrt_ratio_i computation
        ({
            let v3 = field_mul(field_square(v_nat), v_nat);
            let v7 = field_mul(field_square(v3), v_nat);
            let w = field_mul(u_nat, v7);
            let uv3 = field_mul(u_nat, v3);
            let k = ((p() - 5) / 8) as nat;
            let pow_result = (pow(w as int, k) as nat) % p();
            r_orig_nat == field_mul(uv3, pow_result)
        }),
    ensures
        check_nat == u_nat || check_nat == field_neg(u_nat) || check_nat == field_mul(
            u_nat,
            sqrt_m1(),
        ) || check_nat == field_mul(field_neg(u_nat), sqrt_m1()),
{
    let pn = p();
    p_gt_2();
    lemma_small_mod(v_nat, pn);
    lemma_small_mod(u_nat, pn);

    lemma_sqrt_ratio_check_value(u_nat, v_nat);
    let v3 = field_mul(field_square(v_nat), v_nat);
    let v7 = field_mul(field_square(v3), v_nat);
    let w = field_mul(u_nat, v7);
    let quarter = ((pn - 1) / 4) as nat;
    let fourth_root = (pow(w as int, quarter) as nat) % pn;

    // Establish w != 0
    lemma_uv7_nonzero(u_nat, v_nat);

    // Fourth root of w
    lemma_fourth_root_of_unity(w);
    let i = sqrt_m1();

    // Case split: check = u * fourth_root, and fourth_root in {1, -1, i, -i}
    assert(check_nat == u_nat || check_nat == field_neg(u_nat) || check_nat == field_mul(u_nat, i)
        || check_nat == field_mul(field_neg(u_nat), i)) by {
        lemma_field_mul_one_right(u_nat);
        lemma_small_mod(1nat, pn);
        lemma_small_mod((pn - 1) as nat, pn);
        lemma_neg_one_times_is_neg(u_nat);
        lemma_field_mul_comm(u_nat, (pn - 1) as nat);
        lemma_field_mul_neg(u_nat, i);
        lemma_field_neg_mul_left(u_nat, i);
        axiom_sqrt_m1_squared();
        lemma_sqrt_m1_nonzero();
        lemma_small_mod(i, pn);
        lemma_small_mod((pn - i) as nat, pn);
        assert(field_neg(i) == (pn - i) as nat);
        lemma_field_mul_comm(u_nat, (pn - i) as nat);
    };
}

/// Zero propagation: when u=0 or v=0, r_orig=0 and check=0.
///
/// This encapsulates the tedious zero-product chains for both cases.
pub proof fn lemma_sqrt_ratio_zero_propagation(
    u_nat: nat,
    v_nat: nat,
    r_orig_nat: nat,
    check_nat: nat,
)
    requires
        check_nat == field_mul(v_nat, field_square(r_orig_nat)),
        ({
            let v3 = field_mul(field_square(v_nat), v_nat);
            let v7 = field_mul(field_square(v3), v_nat);
            let w = field_mul(u_nat, v7);
            let uv3 = field_mul(u_nat, v3);
            let k = ((p() - 5) / 8) as nat;
            let pow_result = (pow(w as int, k) as nat) % p();
            r_orig_nat == field_mul(uv3, pow_result)
        }),
    ensures
        u_nat == 0 ==> (r_orig_nat == 0 && check_nat == 0),
        v_nat == 0 ==> (r_orig_nat == 0 && check_nat == 0),
{
    let pn = p();
    p_gt_2();

    if u_nat == 0 {
        lemma_small_mod(0nat, pn);
        assert(r_orig_nat == 0) by {
            let v3 = field_mul(field_square(v_nat), v_nat);
            lemma_field_mul_zero_left(0, v3);
            let v7 = field_mul(field_square(v3), v_nat);
            let w = field_mul(0nat, v7);
            lemma_field_mul_zero_left(0, v7);
            let k = ((pn - 5) / 8) as nat;
            let pow_result = (pow(w as int, k) as nat) % pn;
            lemma_field_mul_zero_left(0, pow_result);
        };
        assert(check_nat == 0) by {
            assert(field_square(0nat) == 0) by {
                lemma_small_mod(0nat, pn);
            };
            lemma_field_mul_zero_right(v_nat, 0);
        };
    }
    if v_nat == 0 {
        lemma_small_mod(0nat, pn);
        // When v=0: field_square(0)=0, and field_mul(x, 0)=0 for all x.
        // So v3=0, v7=0, w=0, uv3=0, r_orig=0, check=0.
        assert(0nat * 0nat == 0nat);
        assert(field_square(0nat) == 0);
        // v3 = field_mul(field_square(0), 0) = field_mul(0, 0)
        lemma_field_mul_zero_left(0, 0nat);
        // v7 = field_mul(field_square(0), 0) = 0 (same pattern)
        lemma_field_mul_zero_right(0, 0nat);
        // w = field_mul(u, 0) = 0, uv3 = field_mul(u, 0) = 0
        lemma_field_mul_zero_right(u_nat, 0nat);
        // r_orig = field_mul(0, pow_result) = 0
        let k = ((pn - 5) / 8) as nat;
        let w_zero = field_mul(u_nat, 0nat);
        let pow_result = (pow(w_zero as int, k) as nat) % pn;
        lemma_field_mul_zero_left(0, pow_result);
        assert(r_orig_nat == 0);
        // check = field_mul(0, field_square(0)) = 0
        lemma_field_mul_zero_left(0, field_square(r_orig_nat));
        assert(check_nat == 0);
    }
}

/// Helper: is_sqrt_ratio(0, v, 0) holds trivially since 0*0*v = 0.
proof fn lemma_zero_is_sqrt_ratio(v_nat: nat)
    ensures
        is_sqrt_ratio(0, v_nat, 0),
{
    p_gt_2();
    lemma_small_mod(0nat, p());
    assert(0 * 0 * v_nat == 0) by {
        lemma_mul_basics(v_nat as int);
    };
}

// =============================================================================
// Main sqrt_ratio_i correctness lemma (math level)
// =============================================================================
/// Proves all four mathematical postconditions of sqrt_ratio_i.
///
/// Operates on canonical nat values. The requires clauses capture:
/// - check = v * r_orig^2 (from the computation)
/// - ct_eq results as canonical_nat comparisons
/// - conditional_assign semantics
/// - Fourth root of unity pattern (when v,u != 0)
/// - Zero-propagation (when u=0 or v=0)
pub proof fn lemma_sqrt_ratio_correctness(
    u_nat: nat,
    v_nat: nat,
    check_nat: nat,
    r_orig_nat: nat,
    r_nat: nat,
    correct_sign: bool,
    flipped_sign: bool,
    flipped_sign_i: bool,
    was_nonzero_sq: bool,
)
    requires
        u_nat < p(),
        v_nat < p(),
        check_nat < p(),
        r_orig_nat < p(),
        r_nat < p(),
        // check = v * r_orig^2
        check_nat == field_mul(v_nat, field_square(r_orig_nat)),
        // ct_eq results (canonical nat comparison)
        correct_sign == (check_nat == u_nat),
        flipped_sign == (check_nat == field_neg(u_nat)),
        flipped_sign_i == (check_nat == field_mul(field_neg(u_nat), sqrt_m1())),
        // was_nonzero_square
        was_nonzero_sq == (correct_sign || flipped_sign),
        // conditional_assign: r = i*r_orig if any flipped, else r_orig
        r_nat == if (flipped_sign || flipped_sign_i) {
            field_mul(sqrt_m1(), r_orig_nat)
        } else {
            r_orig_nat
        },
        // When v != 0 and u != 0: check follows fourth root pattern
        (v_nat != 0 && u_nat != 0) ==> (check_nat == u_nat || check_nat == field_neg(u_nat)
            || check_nat == field_mul(u_nat, sqrt_m1()) || check_nat == field_mul(
            field_neg(u_nat),
            sqrt_m1(),
        )),
        // When u == 0: r_orig == 0 and check == 0
        (u_nat == 0) ==> (r_orig_nat == 0 && check_nat == 0),
        // When v == 0: r_orig == 0 and check == 0
        (v_nat == 0) ==> (r_orig_nat == 0 && check_nat == 0),
    ensures
        (u_nat == 0) ==> (was_nonzero_sq && r_nat == 0),
        (v_nat == 0 && u_nat != 0) ==> (!was_nonzero_sq && r_nat == 0),
        (was_nonzero_sq && v_nat != 0) ==> is_sqrt_ratio(u_nat, v_nat, r_nat),
        (!was_nonzero_sq && v_nat != 0 && u_nat != 0) ==> is_sqrt_ratio_times_i(
            u_nat,
            v_nat,
            r_nat,
        ),
{
    let pn = p();
    p_gt_2();
    let i = sqrt_m1();

    // --- Postcondition 1: u == 0 ==> (true, 0) ---
    if u_nat == 0 {
        assert(check_nat == 0);
        assert(r_orig_nat == 0);
        assert(correct_sign);
        assert(was_nonzero_sq);
        // r = 0 in both branches
        assert(r_nat == 0) by {
            lemma_small_mod(0nat, pn);
            if flipped_sign || flipped_sign_i {
                lemma_field_mul_zero_right(i, 0);
            }
        };
    }
    // --- Postcondition 2: v == 0 && u != 0 ==> (false, 0) ---

    if v_nat == 0 && u_nat != 0 {
        assert(check_nat == 0);
        assert(r_orig_nat == 0);
        assert(!correct_sign);
        assert(!flipped_sign) by {
            lemma_small_mod(u_nat, pn);
            lemma_field_neg_nonzero(u_nat);
        };
        assert(!was_nonzero_sq);
        assert(r_nat == 0) by {
            lemma_small_mod(0nat, pn);
            if flipped_sign_i {
                lemma_field_mul_zero_right(i, 0);
            }
        };
    }
    // --- Postcondition 3: was_nonzero_sq && v != 0 ==> is_sqrt_ratio ---

    if was_nonzero_sq && v_nat != 0 {
        // is_sqrt_ratio means: field_canonical(r^2 * v) == field_canonical(u)
        // i.e., field_mul(field_square(r_nat), v_nat) == u_nat % p
        // Since u_nat < p: u_nat % p == u_nat
        lemma_small_mod(u_nat, pn);

        if correct_sign && !(flipped_sign || flipped_sign_i) {
            // Case A: r = r_orig, check = u_nat, so v * r^2 = u directly
            assert(r_nat == r_orig_nat);
            assert(check_nat == u_nat);
            assert(is_sqrt_ratio(u_nat, v_nat, r_nat)) by {
                lemma_field_mul_square_canonical(r_nat, v_nat);
            };
        } else if flipped_sign {
            // Case B: flipped_sign is true, so r = i * r_orig.
            // v*(i*r_orig)^2 = -(v*r_orig^2) = -check.
            assert(flipped_sign || flipped_sign_i);
            assert(r_nat == field_mul(i, r_orig_nat));

            if correct_sign {
                // Sub-case B1: check == u AND check == -u, so u == -u => u == 0.
                assert(u_nat == 0) by {
                    lemma_p_is_odd();
                    lemma_small_mod(u_nat, pn);
                    if u_nat > 0 {
                        lemma_small_mod((pn - u_nat) as nat, pn);
                        // u == p - u => 2u == p, but p is odd
                        assert(u_nat + u_nat == pn);
                        assert(pn % 2 == 0) by {
                            lemma_mod_multiples_basic(1int, 2int);
                        };
                        assert(false);
                    }
                };
                assert(r_orig_nat == 0);
                assert(r_nat == 0) by {
                    lemma_field_mul_zero_right(i, 0);
                };
                lemma_zero_is_sqrt_ratio(v_nat);
            } else {
                // Sub-case B2: check == -u, r = i * r_orig.
                // v*(i*r)^2 = -(v*r_orig^2) = -check = -(-u) = u.
                assert(field_square(r_nat) == field_neg(field_square(r_orig_nat))) by {
                    lemma_multiply_by_i_flips_sign(r_orig_nat);
                    lemma_field_mul_comm(i, r_orig_nat);
                };
                assert(field_mul(v_nat, field_square(r_nat)) == field_neg(check_nat)) by {
                    lemma_field_mul_neg(v_nat, field_square(r_orig_nat));
                };
                assert(field_mul(v_nat, field_square(r_nat)) == u_nat) by {
                    lemma_field_neg_neg(u_nat);
                    lemma_small_mod(u_nat, pn);
                };
                assert(field_canonical(r_nat * r_nat * v_nat) == u_nat) by {
                    lemma_field_mul_square_canonical(r_nat, v_nat);
                };
            }
        } else if correct_sign && flipped_sign_i {
            // Case C: check == u AND check == (-u)*i, so u == (-u)*i.
            // This implies u == 0 (since p is an odd prime and i != 1).
            // Proof: u = (-u)*i. Multiply by i: u*i = (-u)*i^2 = (-u)*(-1) = u.
            // So u*i = u, i.e. u*(i-1) = 0 mod p. Since p is prime and i != 1, u = 0.
            assert(r_nat == field_mul(i, r_orig_nat));
            assert(u_nat == 0) by {
                lemma_eq_neg_times_i_implies_zero(u_nat);
            };
            assert(r_orig_nat == 0);
            assert(r_nat == 0) by {
                lemma_field_mul_zero_right(i, 0);
            };
            lemma_zero_is_sqrt_ratio(v_nat);
        } else {
            // Case D: !correct_sign && !flipped_sign.
            // was_nonzero_sq = correct_sign || flipped_sign = false.
            // Contradicts outer condition.
            assert(false);
        }
    }
    // --- Postcondition 4: !was_nonzero_sq && v != 0 && u != 0 ==> is_sqrt_ratio_times_i ---

    if !was_nonzero_sq && v_nat != 0 && u_nat != 0 {
        // check != u and check != -u
        assert(!correct_sign);
        assert(!flipped_sign);
        // By fourth root: check is u*i or -u*i
        // is_sqrt_ratio_times_i means: field_canonical(r^2 * v) == field_mul(sqrt_m1(), u)
        let ui = field_mul(u_nat, i);
        let neg_ui = field_mul(field_neg(u_nat), i);

        if !flipped_sign_i {
            // Neither flip triggered, so r = r_orig, check = u*i
            assert(r_nat == r_orig_nat);
            assert(check_nat == ui);
            assert(is_sqrt_ratio_times_i(u_nat, v_nat, r_nat)) by {
                lemma_field_mul_square_canonical(r_nat, v_nat);
                lemma_field_mul_comm(u_nat, i);
            };
        } else {
            // flipped_sign_i: check == -u*i, r = i * r_orig
            assert(r_nat == field_mul(i, r_orig_nat));
            assert(field_square(r_nat) == field_neg(field_square(r_orig_nat))) by {
                lemma_multiply_by_i_flips_sign(r_orig_nat);
                lemma_field_mul_comm(i, r_orig_nat);
            };
            assert(field_mul(v_nat, field_square(r_nat)) == field_neg(check_nat)) by {
                lemma_field_mul_neg(v_nat, field_square(r_orig_nat));
            };
            assert(field_neg(check_nat) == ui) by {
                lemma_field_neg_mul_left(u_nat, i);
                assert(check_nat == field_neg(ui));
                lemma_field_neg_neg(ui);
                lemma_mod_bound(ui as int, pn as int);
                lemma_small_mod(ui, pn);
            };
            assert(is_sqrt_ratio_times_i(u_nat, v_nat, r_nat)) by {
                lemma_field_mul_square_canonical(r_nat, v_nat);
                lemma_field_mul_comm(u_nat, i);
            };
        }
    }
}

/// Lemma: Two nonneg elements with the same square in F_p must be equal.
///
/// If r, s < p, both even (nonneg), and r² = s² (mod p), then r = s.
///
/// Proof:
///   1. r² - s² = (r-s)(r+s) = 0 in F_p (difference of squares).
///   2. By Euclid's lemma (p prime): r ≡ s or r ≡ -s (mod p).
///   3. If r = p-s (i.e. r ≡ -s), then r+s = p which is odd,
///      but r even + s even = even. Contradiction.
///   4. Therefore r = s.
pub proof fn lemma_nonneg_square_root_unique(r: nat, s: nat)
    requires
        r < p(),
        s < p(),
        r % 2 == 0,
        s % 2 == 0,
        field_square(r) == field_square(s),
    ensures
        r == s,
{
    let pn = p();
    p_gt_2();
    axiom_p_is_prime();

    // r² - s² = 0 in F_p
    assert(field_sub(field_square(r), field_square(s)) == 0) by {
        lemma_field_sub_self(field_square(r));
    };
    // (r-s)(r+s) = r² - s²
    assert(field_mul(field_sub(r, s), field_add(r, s)) == 0) by {
        lemma_field_diff_of_squares(r, s);
    };

    let a = field_sub(r, s);
    let b = field_add(r, s);
    assert(a < pn) by {
        lemma_mod_bound(((r % pn + pn) as int - (s % pn) as int) as int, pn as int);
    };
    assert(b < pn) by {
        lemma_mod_bound((r + s) as int, pn as int);
    };

    // field_mul(a, b) = 0, so (a * b) % p = 0
    assert((a * b) % pn == 0) by {
        lemma_small_mod(a, pn);
        lemma_small_mod(b, pn);
        lemma_mul_mod_noop_left(a as int, b as int, pn as int);
        lemma_mul_mod_noop_right((a % pn) as int, b as int, pn as int);
    };

    // By Euclid: a % p = 0 or b % p = 0
    lemma_euclid_prime(a, b, pn);

    if a % pn == 0 {
        // field_sub(r, s) ≡ 0 (mod p), both < p => r = s
        lemma_small_mod(a, pn);
        assert(a == 0);
        lemma_small_mod(r, pn);
        lemma_small_mod(s, pn);
        lemma_field_add_sub_cancel(r, s);
        assert(field_add(0nat, s) == r);
        // field_add(0, s) = (0 + s) % p = s
        assert(field_add(0nat, s) == s) by {
            lemma_small_mod(s, pn);
        };
    } else {
        // field_add(r, s) ≡ 0 (mod p), so r + s ≡ 0 (mod p)
        lemma_small_mod(b, pn);
        assert(b == 0);
        // b = field_add(r, s) = (r + s) % p
        // field_add(r, s) is defined as (r + s) % p when both < p
        lemma_small_mod(r, pn);
        lemma_small_mod(s, pn);
        assert(b == (r + s) % pn) by {
            // field_add(r, s) = ((r % p) + (s % p)) % p = (r + s) % p
            lemma_add_mod_noop(r as int, s as int, pn as int);
        };
        assert((r + s) % pn == 0);
        if r == 0 && s == 0 {
            // Both zero, trivially equal
        } else {
            // r + s = p (the only nonzero multiple of p in range [1, 2p-1])
            let sum: int = (r + s) as int;
            let pp: int = pn as int;
            lemma_fundamental_div_mod(sum, pp);
            assert(r + s == pn) by (nonlinear_arith)
                requires
                    sum == pp * (sum / pp) + sum % pp,
                    sum % pp == 0int,
                    sum == r as int + s as int,
                    pp == pn as int,
                    (r as int) >= 0,
                    (s as int) >= 0,
                    (r as int) < pp,
                    (s as int) < pp,
                    !(r as int == 0 && s as int == 0),
                    pp > 0,
            ;
            // r + s = p, but r even + s even = even, and p is odd => contradiction
            lemma_p_is_odd();
            assert((r + s) % 2 == 0) by (nonlinear_arith)
                requires
                    r % 2 == 0,
                    s % 2 == 0,
            ;
            assert(false);
        }
    }
}

/// Lemma: nat_invsqrt(a) satisfies the invsqrt relation and is nonneg.
///
/// For nonzero a (mod p), nat_invsqrt(a) is a nonneg value s < p such that
/// s²·a ≡ 1 or s²·a ≡ √(-1) (mod p).
///
/// Proof:
///   1. check = a·r_raw² where r_raw = a³·(a⁷)^k, k = (p-5)/8.
///      By lemma_sqrt_ratio_check_value, check = (a⁷)^((p-1)/4) mod p.
///   2. By lemma_fourth_root_of_unity, check ∈ {1, -1, i, -i}.
///   3. Adjustment: if check ∈ {-1, -i}, multiply r by i.
///      Since (i·r)² = -r², we get a·r_adj² = -check ∈ {1, i}.
///   4. Sign correction (negate if odd) preserves the square,
///      so a·s² = a·r_adj² ∈ {1, i}, giving is_sqrt_ratio or is_sqrt_ratio_times_i.
pub proof fn lemma_nat_invsqrt_satisfies_relation(a: nat)
    requires
        a % p() != 0,
    ensures
        ({
            let s = nat_invsqrt(a);
            &&& s < p()
            &&& s % 2 == 0
            &&& (is_sqrt_ratio(1, a, s) || is_sqrt_ratio_times_i(1, a, s))
        }),
{
    let pn = p();
    p_gt_2();
    let i = sqrt_m1();

    // Mirror nat_invsqrt(a) definition (else branch, since a % p != 0)
    let a3 = field_mul(field_square(a), a);
    let a7 = field_mul(field_square(a3), a);
    let k = ((pn - 5) / 8) as nat;
    lemma_pow_nonnegative(a7 as int, k);
    let pow_a7_k = (pow(a7 as int, k) as nat) % pn;
    let r_raw = field_mul(a3, pow_a7_k);
    let check = field_mul(a, field_square(r_raw));
    let neg_one = field_neg(1nat);
    let neg_i = field_neg(i);
    let r_adj = if check == neg_one || check == neg_i {
        field_mul(sqrt_m1(), r_raw)
    } else {
        r_raw
    };
    let s = if is_negative(r_adj) {
        field_neg(r_adj)
    } else {
        r_adj
    };

    // Bounds: field operation results are < p
    assert(a3 < pn) by {
        lemma_mod_bound((field_square(a) as int * a as int), pn as int);
    };
    assert(a7 < pn) by {
        lemma_mod_bound((field_square(a3) as int * a as int), pn as int);
    };
    assert(r_raw < pn) by {
        lemma_mod_bound((a3 as int * pow_a7_k as int), pn as int);
    };

    // a7 % p != 0 (chain through nonzero products in prime field)
    assert(field_square(a) % pn != 0) by {
        lemma_nonzero_product(a, a);
        lemma_mod_bound((a * a) as int, pn as int);
        lemma_small_mod(field_square(a), pn);
    };
    assert(a3 % pn != 0) by {
        lemma_nonzero_product(field_square(a), a);
        lemma_small_mod(a3, pn);
    };
    assert(field_square(a3) % pn != 0) by {
        lemma_nonzero_product(a3, a3);
        lemma_mod_bound((a3 * a3) as int, pn as int);
        lemma_small_mod(field_square(a3), pn);
    };
    assert(a7 % pn != 0) by {
        lemma_nonzero_product(field_square(a3), a);
        lemma_small_mod(a7, pn);
    };

    // === Step 1: check ∈ {1, neg_one, i, neg_i} ===

    // lemma_sqrt_ratio_check_value(1, a) proves:
    //   check_lemma = field_mul(1, fourth_root) where fourth_root = (pow(w, quarter))%p
    lemma_sqrt_ratio_check_value(1nat, a);

    // Define the same locals as the postcondition block
    let w = field_mul(1nat, a7);
    let quarter = ((pn - 1) / 4) as nat;
    lemma_pow_nonnegative(w as int, quarter);
    let fourth_root = (pow(w as int, quarter) as nat) % pn;

    // Bridge: field_mul(1, x) = x when x < p
    assert(w == a7) by {
        lemma_field_mul_one_left(a7);
        lemma_small_mod(a7, pn);
    };
    assert(field_mul(1nat, a3) == a3) by {
        lemma_field_mul_one_left(a3);
        lemma_small_mod(a3, pn);
    };

    // From postcondition: check == field_mul(1, fourth_root) = fourth_root
    assert(fourth_root < pn) by {
        lemma_mod_bound(pow(w as int, quarter) as int, pn as int);
    };
    assert(check == fourth_root) by {
        lemma_field_mul_one_left(fourth_root);
        lemma_small_mod(fourth_root, pn);
    };

    // fourth_root_of_unity: (pow(a7, quarter))%p ∈ {1, p-1, i, p-i}
    lemma_fourth_root_of_unity(a7);

    // Connect neg_one and neg_i to canonical forms
    assert(neg_one == (pn - 1) as nat) by {
        lemma_small_mod(1nat, pn);
        lemma_small_mod((pn - 1) as nat, pn);
    };
    lemma_sqrt_m1_nonzero();
    assert(i < pn) by {
        lemma_mod_bound(fe51_as_nat(&constants::SQRT_M1) as int, pn as int);
    };
    assert(neg_i == (pn - i) as nat) by {
        lemma_small_mod(i, pn);
        lemma_small_mod((pn - i) as nat, pn);
    };

    assert(check == 1 || check == neg_one || check == i || check == neg_i);

    // === Step 2: After adjustment, field_mul(a, field_square(r_adj)) ∈ {1, i} ===

    if check == neg_one || check == neg_i {
        // r_adj = field_mul(i, r_raw), (i·r)² = -r²
        assert(field_square(r_adj) == field_neg(field_square(r_raw))) by {
            lemma_multiply_by_i_flips_sign(r_raw);
            lemma_field_mul_comm(i, r_raw);
        };

        // a·r_adj² = a·(-r²) = -(a·r²) = -check
        assert(field_mul(a, field_square(r_adj)) == field_neg(check)) by {
            lemma_field_mul_neg(a, field_square(r_raw));
        };

        if check == neg_one {
            assert(field_mul(a, field_square(r_adj)) == 1) by {
                lemma_field_neg_neg(1nat);
                lemma_small_mod(1nat, pn);
            };
        } else {
            assert(field_mul(a, field_square(r_adj)) == i) by {
                lemma_field_neg_neg(i);
                lemma_small_mod(i, pn);
            };
        }
    } else {
        // No adjustment: r_adj = r_raw, check ∈ {1, i}
        assert(check == 1 || check == i);
    }

    // === Step 3: r_adj < p ===
    assert(r_adj < pn) by {
        if check == neg_one || check == neg_i {
            lemma_mod_bound((i as int * r_raw as int), pn as int);
        }
    };

    // === Step 4: Sign correction preserves the square ===

    assert(s < pn) by {
        if is_negative(r_adj) {
            lemma_small_mod(r_adj, pn);
            lemma_mod_bound((pn as int - r_adj as int), pn as int);
        }
    };

    assert(s % 2 == 0) by {
        lemma_small_mod(r_adj, pn);
        lemma_conditional_negate_makes_even(r_adj, is_negative(r_adj));
    };

    // (-x)² = x² in the field
    assert(field_square(s) == field_square(r_adj)) by {
        if is_negative(r_adj) {
            lemma_neg_square_eq(r_adj);
            lemma_small_mod(r_adj, pn);
        }
    };

    // === Step 5: Connect to is_sqrt_ratio / is_sqrt_ratio_times_i ===

    assert(field_mul(a, field_square(s)) == field_canonical(s * s * a)) by {
        lemma_field_mul_square_canonical(s, a);
    };

    assert(field_canonical(1nat) == 1) by {
        lemma_small_mod(1nat, pn);
    };

    assert(field_mul(i, 1nat) == i) by {
        lemma_field_mul_one_right(i);
        lemma_small_mod(i, pn);
    };

    if field_mul(a, field_square(r_adj)) == 1 {
        assert(field_canonical(s * s * a) == field_canonical(1nat));
        assert(is_sqrt_ratio(1, a, s));
    } else {
        assert(field_mul(a, field_square(r_adj)) == i);
        assert(field_canonical(s * s * a) == field_mul(i, 1nat));
        assert(is_sqrt_ratio_times_i(1, a, s));
    }
}

/// Lemma: nonneg invsqrt is unique.
///
/// If r is nonneg and satisfies r²·a ≡ 1 or r²·a ≡ √(-1) (mod p),
/// then r equals nat_invsqrt(a).
///
/// Proof:
///   1. Let s = nat_invsqrt(a). By lemma_nat_invsqrt_satisfies_relation,
///      s is nonneg and satisfies the same relation type.
///   2. Mixed cases (r in sqrt, s in sqrt*i or vice versa) are impossible
///      by lemma_no_square_root_when_times_i.
///   3. Same case: cancel a (nonzero) to get r² = s².
///   4. By lemma_nonneg_square_root_unique: r = s.
pub proof fn lemma_invsqrt_unique(a: nat, r: nat)
    requires
        a % p() != 0,
        r < p(),
        !is_negative(r),
        is_sqrt_ratio(1, a, r) || is_sqrt_ratio_times_i(1, a, r),
    ensures
        r == nat_invsqrt(a),
{
    let pn = p();
    p_gt_2();

    let s = nat_invsqrt(a);
    lemma_nat_invsqrt_satisfies_relation(a);

    assert(r % 2 == 0) by {
        lemma_small_mod(r, pn);
    };

    // 1 % p != 0 (needed as precondition for lemma_no_square_root_when_times_i)
    assert(1nat % pn != 0) by {
        lemma_small_mod(1nat, pn);
    };

    // Case analysis: same-case or mixed-case.
    // Mixed cases are contradictions via lemma_no_square_root_when_times_i.
    if is_sqrt_ratio(1, a, r) && is_sqrt_ratio_times_i(1, a, s) {
        // s is the witness: s²·a = i·1 = i
        assert(field_mul(field_square(s), a) == field_mul(sqrt_m1(), 1)) by {
            lemma_field_mul_square_canonical(s, a);
        };
        // Contradicts: r²·a = 1 = field_canonical(1)
        assert(field_mul(field_square(r), a) == field_canonical(1)) by {
            lemma_field_mul_square_canonical(r, a);
        };
        lemma_no_square_root_when_times_i(1, a, r);
        assert(false);
    } else if is_sqrt_ratio_times_i(1, a, r) && is_sqrt_ratio(1, a, s) {
        // r is the witness: r²·a = i·1 = i
        assert(field_mul(field_square(r), a) == field_mul(sqrt_m1(), 1)) by {
            lemma_field_mul_square_canonical(r, a);
        };
        // Contradicts: s²·a = 1 = field_canonical(1)
        assert(field_mul(field_square(s), a) == field_canonical(1)) by {
            lemma_field_mul_square_canonical(s, a);
        };
        lemma_no_square_root_when_times_i(1, a, s);
        assert(false);
    }
    // Same case: r²·a == s²·a. Cancel a to get r² == s².

    assert(field_mul(field_square(r), a) == field_mul(field_square(s), a)) by {
        lemma_field_mul_square_canonical(r, a);
        lemma_field_mul_square_canonical(s, a);
    };

    assert(field_square(r) == field_square(s)) by {
        lemma_field_mul_comm(field_square(r), a);
        lemma_field_mul_comm(field_square(s), a);
        lemma_field_mul_left_cancel(a, field_square(r), field_square(s));
        assert(field_square(r) < pn) by {
            lemma_mod_bound((r * r) as int, pn as int);
        };
        assert(field_square(s) < pn) by {
            lemma_mod_bound((s * s) as int, pn as int);
        };
        lemma_small_mod(field_square(r), pn);
        lemma_small_mod(field_square(s), pn);
    };

    lemma_nonneg_square_root_unique(r, s);
}

/// is_sqrt_ratio and is_sqrt_ratio_times_i are mutually exclusive when u != 0.
///
/// Proof: Two cases on v % p.
///   v ≡ 0: is_sqrt_ratio requires (r²v) % p = u % p, but r²·0 ≡ 0 ≢ u. Contradiction.
///   v ≢ 0: is_sqrt_ratio_times_i gives a witness for lemma_no_square_root_when_times_i,
///          whose conclusion includes r²·v ≢ u, i.e. ¬is_sqrt_ratio.
pub proof fn lemma_sqrt_ratio_mutual_exclusion(u: nat, v: nat, r: nat)
    requires
        u % p() != 0,
    ensures
        !(is_sqrt_ratio(u, v, r) && is_sqrt_ratio_times_i(u, v, r)),
{
    let the_p = p();
    assert(pow2(255) > 19) by {
        pow255_gt_19();
    };

    if is_sqrt_ratio(u, v, r) && is_sqrt_ratio_times_i(u, v, r) {
        // Bridge: field_mul(field_square(r), v) == field_canonical(r * r * v)
        assert(field_mul(field_square(r), v) == field_canonical(r * r * v)) by {
            lemma_field_mul_square_canonical(r, v);
        };

        if v % the_p == 0 {
            // v ≡ 0 mod p ⟹ (r*r*v) % p == 0, contradicts u % p != 0.
            assert(((r * r) * (v % the_p)) % the_p == ((r * r) * v) % the_p) by {
                lemma_mul_mod_noop_right((r * r) as int, v as int, the_p as int);
            };
            assert((r * r) * 0 == 0) by {
                lemma_mul_basics((r * r) as int);
            };
            assert(0nat % the_p == 0) by {
                lemma_small_mod(0nat, the_p);
            };
            assert(false);
        } else {
            // v % p != 0. Use r_mod = r % p as existential witness.
            let r_mod = (r % the_p) as nat;
            assert(r_mod < the_p) by {
                lemma_mod_bound(r as int, the_p as int);
            };

            assert(field_square(r_mod) == field_square(r)) by {
                lemma_mul_mod_noop_general(r as int, r as int, the_p as int);
            };

            assert(field_mul(field_square(r_mod), v) == field_mul(sqrt_m1(), u));

            // r²·v ≠ u (mod p) — contradicts is_sqrt_ratio via bridge
            assert(field_mul(field_square(r_mod), v) != field_canonical(u)) by {
                lemma_no_square_root_when_times_i(u, v, r_mod);
            };
            assert(false);
        }
    }
}

/// fe51_as_canonical_nat is always < p() for any FieldElement.
pub proof fn lemma_canonical_nat_lt_p(x: &FieldElement)
    ensures
        fe51_as_canonical_nat(x) < p(),
{
    assert(pow2(255) > 19) by {
        pow255_gt_19();
    };
    assert(fe51_as_canonical_nat(x) < p()) by {
        lemma_mod_bound(fe51_as_nat(x) as int, p() as int);
    };
}

/// Exec I matches nat_invsqrt for the decode computation.
///
/// When v·u2² ≠ 0: uses lemma_invsqrt_unique (nonneg invsqrt is unique).
/// When v·u2² = 0: invsqrt(0) = 0 by definition of nat_invsqrt.
pub proof fn lemma_invsqrt_matches_spec(big_i_nat: nat, v_u2_sqr_nat: nat)
    requires
        big_i_nat % 2 == 0,
        (v_u2_sqr_nat == 0) ==> (big_i_nat == 0),
        (v_u2_sqr_nat != 0) ==> (is_sqrt_ratio(1, v_u2_sqr_nat, big_i_nat) || is_sqrt_ratio_times_i(
            1,
            v_u2_sqr_nat,
            big_i_nat,
        )),
        big_i_nat < p(),
        v_u2_sqr_nat < p(),
    ensures
        big_i_nat == nat_invsqrt(v_u2_sqr_nat),
{
    if v_u2_sqr_nat != 0 {
        assert(!is_negative(big_i_nat)) by {
            lemma_small_mod(big_i_nat, p());
        };
        assert(big_i_nat == nat_invsqrt(v_u2_sqr_nat)) by {
            assert(v_u2_sqr_nat % p() == v_u2_sqr_nat) by {
                lemma_small_mod(v_u2_sqr_nat, p());
            };
            lemma_invsqrt_unique(v_u2_sqr_nat, big_i_nat);
        };
    } else {
        assert(0nat % p() == 0) by {
            lemma_small_mod(0nat, p());
        };
    }
}

/// Invsqrt alignment and mutual exclusion for decode.
///
/// Combines lemma_invsqrt_matches_spec with lemma_sqrt_ratio_mutual_exclusion.
pub proof fn lemma_decode_invsqrt_facts(big_i_nat: nat, v_u2_sqr_nat: nat)
    requires
        big_i_nat % 2 == 0,
        (v_u2_sqr_nat == 0) ==> (big_i_nat == 0),
        (v_u2_sqr_nat != 0) ==> (is_sqrt_ratio(1, v_u2_sqr_nat, big_i_nat) || is_sqrt_ratio_times_i(
            1,
            v_u2_sqr_nat,
            big_i_nat,
        )),
        big_i_nat < p(),
        v_u2_sqr_nat < p(),
    ensures
        big_i_nat == nat_invsqrt(v_u2_sqr_nat),
        v_u2_sqr_nat != 0 ==> !(is_sqrt_ratio(1, v_u2_sqr_nat, big_i_nat) && is_sqrt_ratio_times_i(
            1,
            v_u2_sqr_nat,
            big_i_nat,
        )),
{
    lemma_invsqrt_matches_spec(big_i_nat, v_u2_sqr_nat);
    if v_u2_sqr_nat != 0 {
        assert(!(is_sqrt_ratio(1, v_u2_sqr_nat, big_i_nat) && is_sqrt_ratio_times_i(
            1,
            v_u2_sqr_nat,
            big_i_nat,
        ))) by {
            assert(1nat % p() == 1) by {
                lemma_small_mod(1nat, p());
            };
            lemma_sqrt_ratio_mutual_exclusion(1, v_u2_sqr_nat, big_i_nat);
        };
    }
}

/// Bridge: `fe.is_negative()` matches the spec-level `is_negative(n)` when
/// `fe51_as_canonical_nat(fe) == n`.
///
/// Combines `lemma_is_negative_equals_parity`, `lemma_canonical_nat_lt_p`,
/// and `lemma_small_mod` into a single call.
pub proof fn lemma_is_negative_bridge(fe: &FieldElement, n: nat)
    requires
        fe51_as_canonical_nat(fe) == n,
    ensures
        (spec_fe51_as_bytes(fe)[0] & 1 == 1) == is_negative(n),
{
    lemma_is_negative_equals_parity(fe);
    assert(n < p()) by {
        lemma_canonical_nat_lt_p(fe);
    };
    assert(field_canonical(n) == n) by {
        lemma_small_mod(n, p());
    };
}

/// Lifting: is_sqrt_ratio(1, u*v, s) implies is_sqrt_ratio(u, v, s*u)
/// and is_sqrt_ratio_times_i(1, u*v, s) implies is_sqrt_ratio_times_i(u, v, s*u).
///
/// Core algebra: s²·(uv) ≡ 1 ⟹ (su)²·v = s²·u²·v = u·(s²·uv) = u·1 = u.
pub proof fn lemma_sqrt_ratio_lift_to_uv(u: nat, v: nat, s: nat)
    requires
        u < p(),
        v < p(),
        s < p(),
    ensures
        is_sqrt_ratio(1, field_mul(u, v), s) ==> is_sqrt_ratio(u, v, field_mul(s, u)),
        is_sqrt_ratio_times_i(1, field_mul(u, v), s) ==> is_sqrt_ratio_times_i(
            u,
            v,
            field_mul(s, u),
        ),
{
    let pn = p();
    p_gt_2();
    let uv = field_mul(u, v);
    let su = field_mul(s, u);

    // (su)²·v in canonical form
    assert(field_canonical(su * su * v) == field_mul(field_mul(su, su), v)) by {
        lemma_field_mul_square_canonical(su, v);
    };

    // Key identity: (su)²·v == (s²·uv)·u (mod p)
    // Work at the field_mul level using algebra lemmas.

    // LHS: field_canonical(su * su * v) == field_mul(field_square(su), v)
    assert(field_canonical(su * su * v) == field_mul(field_square(su), v)) by {
        lemma_field_mul_square_canonical(su, v);
    };

    // field_square(su) = field_mul(su, su) = field_mul(field_mul(s,u), field_mul(s,u))
    // Expand using assoc/comm: su·su = s·u·s·u = s·s·u·u = s²·u²
    assert(field_mul(su, su) == field_mul(field_square(s), field_square(u))) by {
        // su·su = (s·u)·(s·u) = s·(u·(s·u))  [assoc]
        lemma_field_mul_assoc(s, u, su);
        // = s·(u·s·u) = s·(s·u·u)  [comm u,s in inner]
        lemma_field_mul_comm(u, su);
        // field_mul(u, su) = field_mul(su, u) = field_mul(field_mul(s,u), u) = s·(u·u) [assoc]
        lemma_field_mul_assoc(s, u, u);
        // So su·su = field_mul(s, field_mul(su, u)) = field_mul(s, field_mul(s, field_mul(u, u)))
        // = field_mul(s, field_mul(s, u²))
        // = s²·u²  [assoc]
        lemma_field_mul_assoc(s, s, field_square(u));
    };

    // RHS chain: s²·u²·v = s²·(u·uv)  [since u²·v = u·(uv)]
    assert(field_mul(field_mul(field_square(s), field_square(u)), v) == field_mul(
        field_square(s),
        field_mul(u, uv),
    )) by {
        lemma_field_mul_assoc(field_square(s), field_square(u), v);
        lemma_field_mul_assoc(u, u, v);
    };

    // s²·(u·uv) = s²·(uv·u) = (s²·uv)·u  [comm + assoc]
    assert(field_mul(field_square(s), field_mul(u, uv)) == field_mul(
        field_mul(field_square(s), uv),
        u,
    )) by {
        lemma_field_mul_comm(u, uv);
        lemma_field_mul_assoc(field_square(s), uv, u);
    };

    // Now use the key identity in both cases.

    if is_sqrt_ratio(1, uv, s) {
        // s²·uv ≡ 1 ⟹ (su)²·v ≡ u
        assert(field_canonical(s * s * uv) == 1) by {
            lemma_small_mod(1nat, pn);
        };
        assert(field_mul(field_square(s), uv) == 1) by {
            lemma_field_mul_square_canonical(s, uv);
            lemma_small_mod(1nat, pn);
        };
        assert(field_mul(1nat, u) == u % pn) by {
            lemma_field_mul_one_left(u);
        };
        assert(field_canonical(su * su * v) == field_canonical(u));
    }
    if is_sqrt_ratio_times_i(1, uv, s) {
        // s²·uv ≡ i ⟹ (su)²·v ≡ i·u
        let i = sqrt_m1();
        assert(field_canonical(s * s * uv) == field_mul(i, 1nat));
        assert(field_mul(i, 1nat) == i % pn) by {
            lemma_field_mul_one_right(i);
        };
        assert(field_mul(field_square(s), uv) == i % pn) by {
            lemma_field_mul_square_canonical(s, uv);
        };
        assert(field_mul(i % pn, u) == field_mul(i, u)) by {
            lemma_mul_mod_noop_left(i as int, u as int, pn as int);
        };
        assert(field_canonical(su * su * v) == field_mul(sqrt_m1(), u));
    }
}

/// field_abs preserves is_sqrt_ratio / is_sqrt_ratio_times_i.
///
/// Algebra: (−r)² = r² in GF(p), so (−r)²·v = r²·v, preserving both
///   r²·v ≡ u  and  r²·v ≡ √(−1)·u.
pub proof fn lemma_nonneg_preserves_sqrt_ratio(u: nat, v: nat, r: nat)
    requires
        r < p(),
    ensures
        is_sqrt_ratio(u, v, r) ==> is_sqrt_ratio(u, v, field_abs(r)),
        is_sqrt_ratio_times_i(u, v, r) ==> is_sqrt_ratio_times_i(u, v, field_abs(r)),
{
    let pn = p();
    p_gt_2();
    let nr = field_abs(r);

    if is_negative(r) {
        // nr = field_neg(r), need: nr²·v = r²·v
        assert(nr == field_neg(r));
        assert(field_square(nr) == field_square(r % pn)) by {
            lemma_neg_square_eq(r);
        };
        assert(field_square(r % pn) == field_square(r)) by {
            lemma_small_mod(r, pn);
        };
        // field_canonical(nr * nr * v) == field_canonical(r * r * v) via field_mul_square_canonical
        assert(field_canonical(nr * nr * v) == field_canonical(r * r * v)) by {
            lemma_field_mul_square_canonical(nr, v);
            lemma_field_mul_square_canonical(r, v);
        };
    }
    // If !is_negative(r): nr == r, trivial.

}

/// Combine invsqrt relation with lift: field_abs(nat_invsqrt(u·v)·u) satisfies
/// is_sqrt_ratio(u, v, _) or is_sqrt_ratio_times_i(u, v, _).
///
/// Chain: nat_invsqrt(uv) gives s with s²·(uv) ∈ {1, i}
///   ⟹ (s·u)²·v ∈ {u, i·u}    [lemma_sqrt_ratio_lift_to_uv]
///   ⟹ |s·u|²·v ∈ {u, i·u}    [lemma_nonneg_preserves_sqrt_ratio]
pub proof fn lemma_nonneg_invsqrt_mul_satisfies_sqrt_ratio(u: nat, v: nat)
    requires
        u < p(),
        v < p(),
        field_mul(u, v) % p() != 0,
    ensures
        ({
            let r = field_abs(field_mul(nat_invsqrt(field_mul(u, v)), u));
            is_sqrt_ratio(u, v, r) || is_sqrt_ratio_times_i(u, v, r)
        }),
{
    let pn = p();
    p_gt_2();
    let uv = field_mul(u, v);
    let s = nat_invsqrt(uv);
    let su = field_mul(s, u);
    let r = field_abs(su);

    // Step 1: s satisfies is_sqrt_ratio(1, uv, s) or is_sqrt_ratio_times_i(1, uv, s)
    lemma_nat_invsqrt_satisfies_relation(uv);
    assert(s < pn);

    // Step 2: Lift from (1, uv) to (u, v)
    lemma_sqrt_ratio_lift_to_uv(u, v, s);

    // su < p (field_mul result)
    assert(su < pn) by {
        lemma_mod_bound((s as int * u as int), pn as int);
    };

    // Step 3: field_abs preserves the relation
    lemma_nonneg_preserves_sqrt_ratio(u, v, su);
}

/// Uniqueness of nonneg square root ratios for general (u, v).
///
/// If r, t are both nonneg, < p, and satisfy is_sqrt_ratio ∨ is_sqrt_ratio_times_i
/// for the same (u, v) with u ≢ 0, v ≢ 0, then r = t.
///
/// Algebra:
///   1. Mixed cases (r²v = u, t²v = iu) give a contradiction because
///      u/v would be both a QR and a QNR.
///   2. Same case: r²v = t²v ⟹ r² = t² (cancel v ≠ 0)
///      ⟹ r = t (nonneg square-root uniqueness in GF(p)).
pub proof fn lemma_nonneg_sqrt_ratio_unique(u: nat, v: nat, r: nat, t: nat)
    requires
        v % p() != 0,
        u % p() != 0,
        r < p(),
        t < p(),
        !is_negative(r),
        !is_negative(t),
        is_sqrt_ratio(u, v, r) || is_sqrt_ratio_times_i(u, v, r),
        is_sqrt_ratio(u, v, t) || is_sqrt_ratio_times_i(u, v, t),
    ensures
        r == t,
{
    let pn = p();
    p_gt_2();
    axiom_p_is_prime();

    assert(field_mul(field_square(r), v) == field_canonical(r * r * v)) by {
        lemma_field_mul_square_canonical(r, v);
    };
    assert(field_mul(field_square(t), v) == field_canonical(t * t * v)) by {
        lemma_field_mul_square_canonical(t, v);
    };

    assert(r % 2 == 0) by {
        lemma_small_mod(r, pn);
    };
    assert(t % 2 == 0) by {
        lemma_small_mod(t, pn);
    };

    if is_sqrt_ratio(u, v, r) && is_sqrt_ratio_times_i(u, v, t) {
        assert(field_mul(field_square(t), v) == field_mul(sqrt_m1(), u));
        lemma_no_square_root_when_times_i(u, v, r);
        assert(false);
    }
    if is_sqrt_ratio_times_i(u, v, r) && is_sqrt_ratio(u, v, t) {
        assert(field_mul(field_square(r), v) == field_mul(sqrt_m1(), u));
        lemma_no_square_root_when_times_i(u, v, t);
        assert(false);
    }
    // Both satisfy the same predicate; equate field_mul(field_square(_), v).

    if is_sqrt_ratio(u, v, r) {
        assert(field_mul(field_square(r), v) == field_canonical(u));
        assert(field_mul(field_square(t), v) == field_canonical(u));
    } else {
        assert(field_mul(field_square(r), v) == field_mul(sqrt_m1(), u));
        assert(field_mul(field_square(t), v) == field_mul(sqrt_m1(), u));
    }

    assert(field_square(r) == field_square(t)) by {
        lemma_field_mul_comm(field_square(r), v);
        lemma_field_mul_comm(field_square(t), v);
        lemma_field_mul_left_cancel(v, field_square(r), field_square(t));
        assert(field_square(r) < pn) by {
            lemma_mod_bound((r * r) as int, pn as int);
        };
        assert(field_square(t) < pn) by {
            lemma_mod_bound((t * t) as int, pn as int);
        };
        lemma_small_mod(field_square(r), pn);
        lemma_small_mod(field_square(t), pn);
    };

    lemma_nonneg_square_root_unique(r, t);
}

/// sqrt_ratio_i matches the spec: r = |invsqrt(u·v) · u|, is_sq ⟺ is_sqrt_ratio.
///
/// Cases:
///   u = 0 ⟹ r = 0 = spec_r, is_sq = true.
///   v = 0, u ≠ 0 ⟹ r = 0 = spec_r, is_sq = false.
///   u ≠ 0, v ≠ 0 ⟹ spec_r satisfies the sqrt_ratio disjunction
///     [lemma_nonneg_invsqrt_mul_satisfies_sqrt_ratio], so r = spec_r by
///     uniqueness [lemma_nonneg_sqrt_ratio_unique], and is_sq matches by
///     mutual exclusion of is_sqrt_ratio / is_sqrt_ratio_times_i.
pub proof fn lemma_sqrt_ratio_matches_invsqrt_mul(u: nat, v: nat, r: nat, is_sq: bool)
    requires
        r < p(),
        r % 2 == 0,
        u < p(),
        v < p(),
        (v != 0 && is_sq) ==> is_sqrt_ratio(u, v, r),
        (v != 0 && !is_sq && u != 0) ==> is_sqrt_ratio_times_i(u, v, r),
        (u == 0) ==> (r == 0 && is_sq),
        (v == 0 && u != 0) ==> (r == 0 && !is_sq),
    ensures
        r == field_abs(field_mul(nat_invsqrt(field_mul(u, v)), u)),
        is_sq == is_sqrt_ratio(u, v, field_abs(field_mul(nat_invsqrt(field_mul(u, v)), u))),
{
    let pn = p();
    p_gt_2();

    let uv = field_mul(u, v);
    let s = nat_invsqrt(uv);
    let su = field_mul(s, u);
    let spec_r = field_abs(su);

    if u == 0 {
        assert(uv == 0) by {
            assert(0nat * v == 0);
            lemma_small_mod(0nat, pn);
        };
        assert(s == 0) by {
            lemma_small_mod(0nat, pn);
        };
        assert(su == 0) by {
            assert(0nat * 0nat == 0);
            lemma_small_mod(0nat, pn);
        };
        assert(spec_r == 0) by {
            lemma_small_mod(0nat, pn);
        };
        assert(is_sqrt_ratio(u, v, spec_r)) by {
            lemma_small_mod(0nat, pn);
        };
    } else if v == 0 {
        assert(uv == 0) by {
            assert(u * 0nat == 0);
            lemma_small_mod(0nat, pn);
        };
        assert(s == 0) by {
            lemma_small_mod(0nat, pn);
        };
        assert(su == 0) by {
            assert(0nat * u == 0);
            lemma_small_mod(0nat, pn);
        };
        assert(spec_r == 0) by {
            lemma_small_mod(0nat, pn);
        };
        assert(!is_sqrt_ratio(u, v, spec_r)) by {
            lemma_small_mod(0nat, pn);
            lemma_small_mod(u, pn);
        };
    } else {
        // v != 0 && u != 0.
        axiom_p_is_prime();

        assert(uv % pn != 0) by {
            lemma_small_mod(u, pn);
            lemma_small_mod(v, pn);
            lemma_mod_bound((u * v) as int, pn as int);
            lemma_small_mod(uv, pn);
            if (u * v) % pn == 0 {
                lemma_euclid_prime(u, v, pn);
                assert(false);
            }
        };

        lemma_nonneg_invsqrt_mul_satisfies_sqrt_ratio(u, v);

        assert(su < pn) by {
            lemma_mod_bound((s as int * u as int), pn as int);
        };

        lemma_small_mod(su, pn);
        lemma_conditional_negate_makes_even(su, su % 2 == 1);
        assert(spec_r % 2 == 0) by {
            lemma_small_mod(su, pn);
        };

        assert(spec_r < pn) by {
            if is_negative(su) {
                lemma_small_mod(su, pn);
                lemma_mod_bound((pn as int - su as int), pn as int);
            }
        };

        assert(!is_negative(spec_r)) by {
            lemma_small_mod(spec_r, pn);
        };

        assert(!is_negative(r)) by {
            lemma_small_mod(r, pn);
        };

        assert(u % pn != 0) by {
            lemma_small_mod(u, pn);
        };
        assert(v % pn != 0) by {
            lemma_small_mod(v, pn);
        };

        lemma_nonneg_sqrt_ratio_unique(u, v, r, spec_r);

        if is_sq {
            // is_sqrt_ratio(u,v,r) holds; r == spec_r, so is_sqrt_ratio(u,v,spec_r) holds.
        } else {
            // is_sqrt_ratio_times_i(u,v,r) holds; by mutual exclusion, !is_sqrt_ratio(u,v,r).
            lemma_sqrt_ratio_mutual_exclusion(u, v, r);
        }
    }
}

} // verus!
