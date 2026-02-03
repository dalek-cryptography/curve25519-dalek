//! Abstract field algebra lemmas for GF(p) where p = 2^255 - 19
//!
//! This module contains spec-level proofs about field operations that are
//! independent of the specific limb representation. These lemmas work with
//! the `math_field_*` functions defined in `field_specs.rs`.
//!
//! ## Key Properties
//!
//! - `lemma_field_inv_one`: inv(1) = 1
//! - `lemma_neg_square_eq`: (-x)² = x²
//! - `lemma_field_mul_distributes_over_add`: a(b+c) = ab + ac
//! - `lemma_square_mod_noop`: (x%p)² = x²
//! - `lemma_field_add_sub_rearrange`: a+b = c-1 ⟹ a+1 = c-b
//!
//! ## Inverse/Division Properties
//!
//! - `lemma_inv_of_product`: inv(a·b) = inv(a)·inv(b)
//! - `lemma_inv_of_square`: inv(x²) = inv(x)²
//! - `lemma_quotient_of_squares`: a²/b² = (a/b)²
//! - `lemma_product_of_squares_eq_square_of_product`: x²·y² = (x·y)²
#![allow(unused_imports)]
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::primality_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::prelude::*;

verus! {

/// Lemma: If a ≡ 0 (mod p), then a·b ≡ 0 (mod p) in field arithmetic
///
/// This is useful for zero-case handling in proofs.
pub proof fn lemma_field_mul_zero_left(a: nat, b: nat)
    requires
        a % p() == 0,
    ensures
        math_field_mul(a, b) == 0,
{
    let p = p();
    p_gt_2();
    // Chain: (a * b) % p == ((a % p) * b) % p == (0 * b) % p == 0 % p == 0
    assert((a * b) % p == 0) by {
        lemma_mul_mod_noop_left(a as int, b as int, p as int);
        assert((0 * b) == 0) by {
            lemma_mul_basics(b as int);
        };
        lemma_small_mod(0, p);
    };
}

/// Lemma: If b ≡ 0 (mod p), then a·b ≡ 0 (mod p) in field arithmetic
///
/// This is useful for zero-case handling in proofs.
pub proof fn lemma_field_mul_zero_right(a: nat, b: nat)
    requires
        b % p() == 0,
    ensures
        math_field_mul(a, b) == 0,
{
    let p = p();
    p_gt_2();
    // Chain: (a * b) % p == (a * (b % p)) % p == (a * 0) % p == 0 % p == 0
    assert((a * b) % p == 0) by {
        lemma_mul_mod_noop_right(a as int, b as int, p as int);
        assert((a * 0) == 0) by {
            lemma_mul_basics(a as int);
        };
        lemma_small_mod(0, p);
    };
}

// =============================================================================
// Multiplicative Identity Lemmas
// =============================================================================
/// Lemma: inv(1) = 1
///
/// Uses field_inv_property: ((a % p) * inv(a)) % p = 1
pub proof fn lemma_field_inv_one()
    ensures
        math_field_inv(1) == 1,
{
    // Goal: inv(1) = 1
    //
    // From field_inv_property: 1 * inv(1) ≡ 1 (mod p)
    // So inv(1) ≡ 1 (mod p)
    // Since inv(1) < p, we have inv(1) = 1
    p_gt_2();  // Needed for p > 0
    let inv = math_field_inv(1);

    // 1 % p = 1 and (1 * inv) % p = 1 and inv < p
    assert(1nat % p() == 1 && ((1nat % p()) * inv) % p() == 1 && inv < p()) by {
        lemma_small_mod(1, p());
        field_inv_property(1);
    };

    // Since (1 * inv) % p = 1 and inv < p, we have inv = 1
    assert(inv == 1) by {
        lemma_small_mod(inv, p());
    };
}

// =============================================================================
// Negation and Square Lemmas
// =============================================================================
/// Lemma: (-x)² = x² (mod p)
///
/// Mathematical proof: (p-a)² = p² - 2pa + a² ≡ a² (mod p)
pub proof fn lemma_neg_square_eq(x: nat)
    ensures
        math_field_square(math_field_neg(x)) == math_field_square(x % p()),
{
    let a = x % p();
    let neg_x = math_field_neg(x);
    let p = p();
    p_gt_2();

    if a == 0 {
        // neg_x = (p - 0) % p = 0, so (-0)² = 0 = 0²
        lemma_mod_self_0(p as int);
        lemma_small_mod(0, p);
    } else {
        // a > 0: neg_x = p - a, use (p-a)² ≡ a² (mod p)
        lemma_small_mod((p - a) as nat, p);
        lemma_product_of_complements(a, a, p);
    }
}

// =============================================================================
// Field Distributivity Lemmas
// =============================================================================
/// Lemma: a · (b + c) = a·b + a·c (mod p)
///
/// ## Mathematical Proof
/// ```text
/// a · (b + c) % p
///   = a · ((b + c) % p) % p     [mod absorbs on right]
///   = (a·b + a·c) % p           [integer distributivity]
///   = ((a·b)%p + (a·c)%p) % p   [mod distributes over add]
/// ```
pub proof fn lemma_field_mul_distributes_over_add(a: nat, b: nat, c: nat)
    ensures
        math_field_mul(a, math_field_add(b, c)) == math_field_add(
            math_field_mul(a, b),
            math_field_mul(a, c),
        ),
{
    let p = p();
    p_gt_2();

    // Goal: a · (b + c) = a·b + a·c in the field
    assert(math_field_mul(a, math_field_add(b, c)) == math_field_add(
        math_field_mul(a, b),
        math_field_mul(a, c),
    )) by {
        // Step 1: a * ((b+c) % p) ≡ a * (b+c) (mod p)
        lemma_mul_mod_noop_right(a as int, (b + c) as int, p as int);

        // Step 2: a * (b+c) = a*b + a*c (integer distributivity)
        lemma_mul_is_distributive_add(a as int, b as int, c as int);

        // Step 3: (a*b + a*c) % p = ((a*b)%p + (a*c)%p) % p
        lemma_add_mod_noop((a * b) as int, (a * c) as int, p as int);
    };
}

/// Lemma: (x % p)² = x² (mod p)
pub proof fn lemma_square_mod_noop(x: nat)
    ensures
        math_field_square(x % p()) == math_field_square(x),
{
    // ((x%p) * (x%p)) % p = (x * x) % p by mod absorption on both factors
    let p = p();
    p_gt_2();  // Needed for p > 0

    assert(math_field_square(x % p) == math_field_square(x)) by {
        lemma_mul_mod_noop_left(x as int, x as int, p as int);
        lemma_mul_mod_noop_right((x % p) as int, x as int, p as int);
    };
}

/// Lemma: Concrete squaring matches math_field_square spec
///
/// When y2_raw is the result of squaring y_raw (via pow(y_raw, 2)),
/// this equals math_field_square applied to the reduced value.
///
/// ## Mathematical Proof
/// ```text
/// y2_raw % p = pow(y_raw, 2) % p              [precondition]
///            = (y_raw * y_raw) % p            [pow(x, 2) = x * x]
///            = ((y_raw % p) * (y_raw % p)) % p [by lemma_mul_mod_noop_general]
///            = math_field_square(y_raw % p)   [definition]
/// ```
pub proof fn lemma_square_matches_math_field_square(y_raw: nat, y2_raw: nat)
    requires
        y2_raw % p() == pow(y_raw as int, 2) as nat % p(),
    ensures
        y2_raw % p() == math_field_square(y_raw % p()),
{
    let p = p();
    p_gt_2();

    // pow(y_raw, 2) = y_raw * y_raw
    assert(pow(y_raw as int, 2) == y_raw as int * y_raw as int) by {
        reveal(pow);
        assert(pow(y_raw as int, 1) == y_raw as int * pow(y_raw as int, 0));
    };

    // Apply mod absorption: (y_raw * y_raw) % p == ((y_raw % p) * (y_raw % p)) % p
    assert((y_raw * y_raw) % p == ((y_raw % p) * (y_raw % p)) % p) by {
        lemma_mul_mod_noop_general(y_raw as int, y_raw as int, p as int);
    };

    // math_field_mul(y, y) = math_field_square(y) by definition
    assert(math_field_mul(y_raw % p, y_raw % p) == math_field_square(y_raw % p));
}

// =============================================================================
// Field Equation Rearrangement Lemmas
// =============================================================================
/// Lemma: If a + b ≡ c - 1, then a + 1 ≡ c - b (mod p)
///
/// ## Mathematical Proof
/// ```text
/// Given: a + b ≡ c - 1 (mod p)
/// Add 1:     a + b + 1 ≡ c (mod p)
/// Subtract b: a + 1 ≡ c - b (mod p)  ✓
/// ```
///
pub proof fn lemma_field_add_sub_rearrange(a: nat, b: nat, c: nat)
    requires
        a < p(),
        b < p(),
        c < p(),
        math_field_add(a, b) == math_field_sub(c, 1),
    ensures
        math_field_add(a, 1) == math_field_sub(c, b),
{
    let p = p();
    let (a_int, b_int, c_int, p_int) = (a as int, b as int, c as int, p as int);
    p_gt_2();

    // Goal: (a + 1) % p = (c - b) % p
    assert(math_field_add(a, 1) == math_field_sub(c, b)) by {
        // Small mod simplifications
        lemma_small_mod(c, p);
        lemma_small_mod(1, p);
        lemma_small_mod(b, p);

        // Step 1: (a + b + 1) % p = c
        lemma_add_mod_noop(a_int + b_int, 1, p_int);
        lemma_add_mod_noop(c_int + p_int - 1, 1, p_int);
        lemma_mod_add_multiples_vanish(c_int, p_int);
        assert((a_int + b_int + 1) % p_int == c_int);

        // Step 2: (a + 1) % p = (c - b) % p
        lemma_sub_mod_noop(a_int + b_int + 1, b_int, p_int);

        // Step 3: (c - b) % p = (c + p - b) % p
        lemma_mod_add_multiples_vanish(c_int - b_int, p_int);
    };
}

// =============================================================================
// Field Element Reduction Lemma
// =============================================================================
/// Lemma: A value that is the result of a mod p operation is reduced.
///
/// If x < p (which is always true for results of % p), then x % p == x.
/// This captures a common pattern where we need to show a field element is reduced.
pub proof fn lemma_field_element_reduced(x: nat)
    requires
        x < p(),
    ensures
        x % p() == x,
{
    lemma_small_mod(x, p());
}

// =============================================================================
// Multiplicative Identity Lemmas (one)
// =============================================================================
/// Lemma: 1 · a = a (mod p)
pub proof fn lemma_field_mul_one_left(a: nat)
    ensures
        math_field_mul(1, a) == a % p(),
{
    let p = p();
    p_gt_2();
    lemma_mul_basics(a as int);  // 1 * a = a
    lemma_small_mod(a % p, p);
    lemma_mul_mod_noop_left(1 as int, a as int, p as int);
}

/// Lemma: a · 1 = a (mod p)
pub proof fn lemma_field_mul_one_right(a: nat)
    ensures
        math_field_mul(a, 1) == a % p(),
{
    let p = p();
    p_gt_2();
    lemma_mul_basics(a as int);  // a * 1 = a
    lemma_small_mod(a % p, p);
    lemma_mul_mod_noop_right(a as int, 1 as int, p as int);
}

// =============================================================================
// Inverse Cancellation Lemmas
// =============================================================================
/// Lemma: inv(a) · a = 1 when a ≠ 0 (mod p)
///
/// This is the core inverse property expressed in field multiplication notation.
pub proof fn lemma_inv_mul_cancel(a: nat)
    requires
        a % p() != 0,
    ensures
        math_field_mul(math_field_inv(a), a) == 1,
{
    let p = p();
    p_gt_2();

    let inv_a = math_field_inv(a);

    // From field_inv_property: ((a % p) * inv(a)) % p = 1
    field_inv_property(a);
    assert(((a % p) * inv_a) % p == 1);

    // By commutativity: (inv(a) * a) % p = (a * inv(a)) % p
    lemma_mul_is_commutative(inv_a as int, a as int);

    // By mod absorption: (inv(a) * a) % p = ((inv(a) % p) * a) % p = (inv(a) * (a % p)) % p
    lemma_mul_mod_noop_left(a as int, inv_a as int, p as int);
    lemma_mul_mod_noop_right(inv_a as int, a as int, p as int);
}

// =============================================================================
// Subtraction and Negation Lemmas
// =============================================================================
/// Lemma: sub(b, a) = neg(sub(a, b)) in field arithmetic (antisymmetry)
///
/// Field subtraction is antisymmetric: reversing the operands negates the result.
///
/// ## Mathematical Proof
/// ```text
/// Case a ≡ b (mod p): sub(a,b) = 0, sub(b,a) = 0, neg(0) = 0 ✓
/// Case a > b (mod p): sub(a,b) = a-b, sub(b,a) = p-(a-b), neg(a-b) = p-(a-b) ✓
/// Case a < b (mod p): sub(a,b) = p-(b-a), sub(b,a) = b-a, neg(p-(b-a)) = b-a ✓
/// ```
pub proof fn lemma_field_sub_antisymmetric(a: nat, b: nat)
    ensures
        math_field_sub(b, a) == math_field_neg(math_field_sub(a, b)),
{
    let p = p();
    p_gt_2();

    let a_mod = a % p;
    let b_mod = b % p;

    // sub(a, b) = ((a_mod + p) - b_mod) % p
    // sub(b, a) = ((b_mod + p) - a_mod) % p
    let sub_ab = math_field_sub(a, b);
    let sub_ba = math_field_sub(b, a);

    // Both are < p by definition of mod
    assert(sub_ab < p) by {
        lemma_mod_bound(((a_mod + p) - b_mod) as int, p as int);
    }
    assert(sub_ba < p) by {
        lemma_mod_bound(((b_mod + p) - a_mod) as int, p as int);
    }

    // Case analysis based on a_mod vs b_mod
    if a_mod == b_mod {
        // sub_ab = p % p = 0, sub_ba = p % p = 0, neg(0) = p % p = 0
        assert(sub_ab == 0) by {
            lemma_mod_self_0(p as int);
        }
        assert(sub_ba == 0) by {
            lemma_mod_self_0(p as int);
        }
        assert(math_field_neg(sub_ab) == 0) by {
            lemma_mod_self_0(p as int);
        }
    } else if a_mod > b_mod {
        // sub_ab = (a_mod + p - b_mod) % p = (a_mod - b_mod) since sum > p
        // sub_ba = (b_mod + p - a_mod) % p = (p - (a_mod - b_mod)) since sum < p
        let diff = (a_mod - b_mod) as nat;
        assert(sub_ab == diff) by {
            assert(a_mod + p - b_mod == p + diff);
            lemma_mod_add_multiples_vanish(diff as int, p as int);
            lemma_small_mod(diff, p);
        }
        assert(sub_ba == p - diff) by {
            assert(b_mod + p - a_mod == p - diff);
            lemma_small_mod((p - diff) as nat, p);
        }
        // neg(sub_ab) = (p - diff) % p = p - diff (since diff > 0, so p - diff < p)
        assert(math_field_neg(sub_ab) == p - diff) by {
            lemma_small_mod(diff, p);
            lemma_small_mod((p - diff) as nat, p);
        }
    } else {
        // a_mod < b_mod
        // sub_ab = (a_mod + p - b_mod) % p = (p - (b_mod - a_mod)) since sum < p
        // sub_ba = (b_mod + p - a_mod) % p = (b_mod - a_mod) since sum > p
        let diff = (b_mod - a_mod) as nat;
        assert(sub_ab == p - diff) by {
            assert(a_mod + p - b_mod == p - diff);
            lemma_small_mod((p - diff) as nat, p);
        }
        assert(sub_ba == diff) by {
            assert(b_mod + p - a_mod == p + diff);
            lemma_mod_add_multiples_vanish(diff as int, p as int);
            lemma_small_mod(diff, p);
        }
        // neg(sub_ab) = (p - (p - diff)) % p = diff % p = diff
        assert(math_field_neg(sub_ab) == diff) by {
            assert(p - (p - diff) == diff);
            lemma_small_mod((p - diff) as nat, p);
            lemma_small_mod(diff, p);
        }
    }
}

/// Lemma: sub(a, b) = add(a, neg(b)) in field arithmetic
///
/// Field subtraction is addition with the additive inverse.
/// This is a fundamental property of field arithmetic.
///
/// Proof sketch:
/// - sub(a, b) = ((a % p) + p - (b % p)) % p
/// - neg(b) = (p - (b % p)) % p
/// - add(a, neg(b)) = ((a % p) + neg(b)) % p = ((a % p) + (p - (b % p))) % p
/// Both compute (a + p - b) % p.
pub proof fn lemma_field_sub_eq_add_neg(a: nat, b: nat)
    ensures
        math_field_sub(a, b) == math_field_add(a, math_field_neg(b)),
{
    let p = p();
    p_gt_2();

    let a_mod = a % p;
    let b_mod = b % p;
    let neg_b_raw: nat = (p - b_mod) as nat;

    assert(a_mod < p) by {
        lemma_mod_bound(a as int, p as int);
    };
    assert(b_mod < p) by {
        lemma_mod_bound(b as int, p as int);
    };

    // neg(b) = (p - (b % p)) % p = neg_b_raw % p
    assert(math_field_neg(b) == neg_b_raw % p);

    // sub(a, b) = ((a % p) + p - (b % p)) % p = (a_mod + neg_b_raw) % p
    assert(math_field_sub(a, b) == (a_mod + neg_b_raw) % p) by {
        assert(((a_mod + p) - b_mod) as nat == a_mod + neg_b_raw);
    };

    // add(a, neg(b)) = (a + neg(b)) % p = (a_mod + neg_b_raw) % p
    assert(math_field_add(a, math_field_neg(b)) == (a_mod + neg_b_raw) % p) by {
        // (a + (neg_b_raw % p)) % p == (a + neg_b_raw) % p
        assert((a + math_field_neg(b)) % p == (a + neg_b_raw) % p) by {
            lemma_add_mod_noop(a as int, (neg_b_raw % p) as int, p as int);
            lemma_add_mod_noop(a as int, neg_b_raw as int, p as int);
            lemma_mod_twice(neg_b_raw as int, p as int);
        };

        // (a + neg_b_raw) % p == (a_mod + neg_b_raw) % p
        assert((a + neg_b_raw) % p == (a_mod + neg_b_raw) % p) by {
            lemma_add_mod_noop(a as int, neg_b_raw as int, p as int);
            lemma_add_mod_noop(a_mod as int, neg_b_raw as int, p as int);
            lemma_small_mod(a_mod, p);
        };
    };
}

/// Lemma: add(a, neg(b)) = sub(a, b) when a and b are field elements (< p)
///
/// This is the converse of lemma_field_sub_eq_add_neg for reduced inputs.
pub proof fn lemma_field_add_neg_eq_sub(a: nat, b: nat)
    requires
        a < p(),
        b < p(),
    ensures
        math_field_add(a, math_field_neg(b)) == math_field_sub(a, b),
{
    lemma_field_sub_eq_add_neg(a, b);
}

/// Lemma: c · neg(b) = neg(c · b) in field arithmetic
///
/// Multiplication distributes into negation.
/// Uses lemma_mul_distributes_over_neg_mod from div_mod_lemmas.
pub proof fn lemma_field_mul_neg(c: nat, b: nat)
    ensures
        math_field_mul(c, math_field_neg(b)) == math_field_neg(math_field_mul(c, b)),
{
    let p = p();
    p_gt_2();

    let b_mod = b % p;
    let neg_b_raw: nat = (p - b_mod) as nat;

    // (c * ((p - b % p) as nat)) % p == ((p - (c * b) % p) as nat) % p
    lemma_mul_distributes_over_neg_mod(c, b, p);

    // Rewrite the LHS into the form used by lemma_mul_distributes_over_neg_mod.
    assert(math_field_mul(c, math_field_neg(b)) == (c * neg_b_raw) % p) by {
        // math_field_mul(c, math_field_neg(b))
        // = (c * ((p - (b % p)) as nat % p)) % p
        // = (c * ((p - (b % p)) as nat)) % p
        lemma_mul_mod_noop_right(c as int, neg_b_raw as int, p as int);
    };

    // Rewrite the RHS into the form used by lemma_mul_distributes_over_neg_mod.
    assert(math_field_neg(math_field_mul(c, b)) == ((p - (c * b) % p) as nat) % p) by {
        lemma_mod_twice((c * b) as int, p as int);
    };
}

// =============================================================================
// Distributivity over Subtraction
// =============================================================================
/// Lemma: (a - b) · c = a·c - b·c (mod p)
///
/// Distributivity of field multiplication over subtraction (on the right).
/// Uses the helper lemmas: sub = add + neg, mul distributes over add, mul of neg = neg of mul.
pub proof fn lemma_field_mul_distributes_over_sub_right(a: nat, b: nat, c: nat)
    ensures
        math_field_mul(math_field_sub(a, b), c) == math_field_sub(
            math_field_mul(a, c),
            math_field_mul(b, c),
        ),
{
    let p = p();
    p_gt_2();

    let neg_b = math_field_neg(b);
    let ac = math_field_mul(a, c);
    let bc = math_field_mul(b, c);

    // Step 1: sub(a, b) = add(a, neg(b))
    lemma_field_sub_eq_add_neg(a, b);
    assert(math_field_sub(a, b) == math_field_add(a, neg_b));

    // Step 2: sub(a,b) * c = add(a, neg(b)) * c = (a + neg(b)) * c
    // By commutativity: = c * (a + neg(b)) = c*a + c*neg(b)
    lemma_field_mul_comm(math_field_sub(a, b), c);
    lemma_field_mul_comm(math_field_add(a, neg_b), c);
    lemma_field_mul_distributes_over_add(c, a, neg_b);
    assert(math_field_mul(c, math_field_add(a, neg_b)) == math_field_add(
        math_field_mul(c, a),
        math_field_mul(c, neg_b),
    ));

    // Step 3: c*a = a*c and c*neg(b) = neg(c*b) = neg(b*c)
    lemma_field_mul_comm(c, a);
    lemma_field_mul_comm(c, b);
    lemma_field_mul_neg(c, b);
    assert(math_field_mul(c, neg_b) == math_field_neg(bc));

    // Step 4: add(ac, neg(bc)) = sub(ac, bc)
    // ac and bc are already < p (field elements)
    assert(ac < p) by {
        lemma_mod_bound((a * c) as int, p as int);
    };
    assert(bc < p) by {
        lemma_mod_bound((b * c) as int, p as int);
    };
    lemma_field_add_neg_eq_sub(ac, bc);
    assert(math_field_add(ac, math_field_neg(bc)) == math_field_sub(ac, bc));

    // Chain: sub(a,b)*c = c*add(a,neg(b)) = c*a + c*neg(b) = ac + neg(bc) = sub(ac, bc)
}

// =============================================================================
// Inverse of Products Lemmas
// =============================================================================
/// Lemma: inv(a · b) = inv(a) · inv(b) (mod p)
///
/// ## Mathematical Proof
/// ```text
/// We show inv(a) · inv(b) is the inverse of (a · b):
///   (a · b) · (inv(a) · inv(b))
///   = a · (b · inv(b)) · inv(a)    [associativity & commutativity]
///   = a · 1 · inv(a)               [b · inv(b) = 1]
///   = a · inv(a)
///   = 1                            [a · inv(a) = 1]
///
/// By uniqueness of inverse: inv(a · b) = inv(a) · inv(b)
/// ```
pub proof fn lemma_inv_of_product(a: nat, b: nat)
    ensures
        math_field_inv(math_field_mul(a, b)) == math_field_mul(
            math_field_inv(a),
            math_field_inv(b),
        ),
{
    let p = p();
    p_gt_2();

    let ab = math_field_mul(a, b);
    let inv_a = math_field_inv(a);
    let inv_b = math_field_inv(b);
    let inv_a_inv_b = math_field_mul(inv_a, inv_b);

    // Handle zero cases: if a % p == 0 or b % p == 0, both sides are 0
    // since inv(0) == 0 by convention
    if a % p == 0 || b % p == 0 {
        // LHS: ab = 0, so inv(ab) = inv(0) = 0
        assert(math_field_inv(ab) == 0) by {
            assert(ab == 0) by {
                if a % p == 0 {
                    lemma_field_mul_zero_left(a, b);
                } else {
                    lemma_field_mul_zero_right(a, b);
                }
            };
        };

        // RHS: inv(a) = 0 or inv(b) = 0, so inv(a) * inv(b) = 0
        assert(inv_a_inv_b == 0) by {
            if a % p == 0 {
                assert(inv_a == 0);
                assert(inv_a % p == 0) by {
                    lemma_small_mod(0, p);
                };
            } else {
                assert(inv_b == 0);
                assert(inv_b % p == 0) by {
                    lemma_small_mod(0, p);
                };
            }
        };
        return ;
    }
    // Non-zero case: proceed with the original proof
    // Step 1: Get inverse properties: inv_a < p, inv_b < p, and they satisfy inverse equations

    assert(inv_a < p && inv_b < p && ((a % p) * inv_a) % p == 1 && ((b % p) * inv_b) % p == 1) by {
        field_inv_property(a);
        field_inv_property(b);
    };

    // Step 2: Show ab % p != 0 (product of non-zero elements is non-zero)
    // This follows from p being prime
    assert(ab % p != 0) by {
        // ab = (a * b) % p
        // If ab % p == 0, then (a * b) % p == 0, so p | (a * b)
        // By Euclid's lemma (p prime), p | a or p | b
        // But a % p != 0 and b % p != 0
        if ab % p == 0 {
            // ab = (a * b) % p, so ab % p = (a * b) % p % p = (a * b) % p
            lemma_mod_twice((a * b) as int, p as int);
            assert((a * b) % p == 0);

            axiom_p_is_prime();
            lemma_euclid_prime(a, b, p);
            // This gives a % p == 0 or b % p == 0
            // Both contradict our preconditions
        }
    };

    // Step 3: Show that inv_a * inv_b is the inverse of ab
    // Need to prove: (ab % p) * inv_a_inv_b % p == 1
    // Note: ab = (a * b) % p, so ab % p = ab

    // First prove the integer equality: (a*b)*(inv_a*inv_b) = (a*inv_a)*(b*inv_b)
    // Using step-by-step intermediate assertions
    let step1 = (a * b) * (inv_a * inv_b);
    let step2 = ((a * b) * inv_a) * inv_b;
    let step3 = (a * (b * inv_a)) * inv_b;
    let step4 = (a * (inv_a * b)) * inv_b;
    let step5 = ((a * inv_a) * b) * inv_b;
    let step6 = (a * inv_a) * (b * inv_b);

    assert(step1 == step2) by {
        lemma_mul_is_associative((a * b) as int, inv_a as int, inv_b as int);
    };
    assert(step2 == step3) by {
        lemma_mul_is_associative(a as int, b as int, inv_a as int);
    };
    assert(step3 == step4) by {
        lemma_mul_is_commutative(b as int, inv_a as int);
    };
    assert(step4 == step5) by {
        lemma_mul_is_associative(a as int, inv_a as int, b as int);
    };
    assert(step5 == step6) by {
        lemma_mul_is_associative((a * inv_a) as int, b as int, inv_b as int);
    };

    // Chain the equalities
    assert(step1 == step6);
    assert((a * b) * (inv_a * inv_b) == (a * inv_a) * (b * inv_b));

    // Now prove (a * inv_a) % p = 1 and (b * inv_b) % p = 1
    assert((a * inv_a) % p == 1) by {
        lemma_mul_mod_noop_left(a as int, inv_a as int, p as int);
    };
    assert((b * inv_b) % p == 1) by {
        lemma_mul_mod_noop_left(b as int, inv_b as int, p as int);
    };

    // Therefore ((a*inv_a) * (b*inv_b)) % p = 1
    assert(((a * inv_a) * (b * inv_b)) % p == 1) by {
        lemma_mul_mod_noop((a * inv_a) as int, (b * inv_b) as int, p as int);
        lemma_small_mod(1, p);
    };

    // And so ((a*b) * (inv_a*inv_b)) % p = 1
    assert(((a * b) * (inv_a * inv_b)) % p == 1);

    // Finally connect to ab and inv_a_inv_b
    assert(((ab % p) * inv_a_inv_b) % p == 1) by {
        // ab % p = ab (since ab < p)
        lemma_mod_bound((a * b) as int, p as int);
        lemma_small_mod(ab, p);

        // inv_a_inv_b = (inv_a * inv_b) % p, so inv_a_inv_b < p
        lemma_mod_bound((inv_a * inv_b) as int, p as int);

        // (ab * inv_a_inv_b) % p = ((a*b) % p * (inv_a*inv_b) % p) % p = ((a*b)*(inv_a*inv_b)) % p
        lemma_mul_mod_noop((a * b) as int, (inv_a * inv_b) as int, p as int);
    };

    // Step 4: inv_a_inv_b < p (since it's a field element)
    assert(inv_a_inv_b < p) by {
        lemma_mod_bound((inv_a * inv_b) as int, p as int);
    };

    // Step 5: By uniqueness of inverse
    assert(math_field_inv(ab) == inv_a_inv_b) by {
        field_inv_unique(ab, inv_a_inv_b);
    };
}

/// Lemma: inv(x²) = inv(x)² (mod p)
///
/// Special case of inv(a·b) = inv(a)·inv(b) where a = b = x
pub proof fn lemma_inv_of_square(x: nat)
    ensures
        math_field_inv(math_field_square(x)) == math_field_square(math_field_inv(x)),
{
    p_gt_2();  // Needed for field operations

    // inv(x * x) = inv(x) * inv(x) by lemma_inv_of_product with a = b = x
    assert(math_field_inv(math_field_mul(x, x)) == math_field_mul(
        math_field_inv(x),
        math_field_inv(x),
    )) by {
        lemma_inv_of_product(x, x);
    };

    // math_field_mul(x, x) = math_field_square(x) and
    // math_field_mul(inv(x), inv(x)) = math_field_square(inv(x))
    assert(math_field_mul(x, x) == math_field_square(x));
    assert(math_field_mul(math_field_inv(x), math_field_inv(x)) == math_field_square(
        math_field_inv(x),
    ));
}

/// Lemma: a²/b² = (a/b)² (mod p)
///
/// Where a/b means a · inv(b)
///
/// ## Mathematical Proof
/// ```text
/// a²/b² = a² · inv(b²)
///       = a² · inv(b)²           [by lemma_inv_of_square]
///       = (a · inv(b))²          [since (xy)² = x²y²]
///       = (a/b)²
/// ```
pub proof fn lemma_quotient_of_squares(a: nat, b: nat)
    ensures
        math_field_mul(math_field_square(a), math_field_inv(math_field_square(b)))
            == math_field_square(math_field_mul(a, math_field_inv(b))),
{
    p_gt_2();  // Needed for field operations

    let a2 = math_field_square(a);
    let b2 = math_field_square(b);
    let inv_b = math_field_inv(b);
    let inv_b2 = math_field_inv(b2);
    let a_div_b = math_field_mul(a, inv_b);

    // Step 1: inv(b²) = inv(b)²
    assert(inv_b2 == math_field_square(inv_b)) by {
        lemma_inv_of_square(b);
    };

    // Step 2: a² · inv(b)² = (a · inv(b))² (product-of-squares property)
    assert(math_field_mul(a2, math_field_square(inv_b)) == math_field_square(a_div_b)) by {
        lemma_product_of_squares_eq_square_of_product(a, inv_b);
    };

    // Chain: a² · inv(b²) = a² · inv(b)² = (a · inv(b))²
    assert(math_field_mul(a2, inv_b2) == math_field_mul(a2, math_field_square(inv_b)));
}

/// Lemma: x² · y² = (x · y)² (mod p)
///
/// ## Mathematical Proof
/// ```text
/// (x · y)² = (x · y) · (x · y)
///         = x · y · x · y          [flatten]
///         = x · x · y · y          [commutativity: swap middle y,x]
///         = x² · y²
/// ```
pub proof fn lemma_product_of_squares_eq_square_of_product(x: nat, y: nat)
    ensures
        math_field_mul(math_field_square(x), math_field_square(y)) == math_field_square(
            math_field_mul(x, y),
        ),
{
    let p = p();
    p_gt_2();

    let x2 = math_field_square(x);  // (x * x) % p
    let y2 = math_field_square(y);  // (y * y) % p
    let xy = math_field_mul(x, y);  // (x * y) % p
    let xy2 = math_field_square(xy);  // ((x * y) % p * (x * y) % p) % p

    // Goal: (x² * y²) % p = ((xy) * (xy)) % p
    assert(math_field_mul(x2, y2) == xy2) by {
        // Step 1: Apply mod absorption for both sides
        // LHS: ((x*x) % p * (y*y) % p) % p = ((x*x) * (y*y)) % p
        lemma_mul_mod_noop((x * x) as int, (y * y) as int, p as int);

        // RHS: ((x*y) % p * (x*y) % p) % p = ((x*y) * (x*y)) % p
        lemma_mul_mod_noop((x * y) as int, (x * y) as int, p as int);

        // Step 2: Show (x*x)*(y*y) = (x*y)*(x*y) as integers
        // (x*y)*(x*y) = x*(y*x)*y = x*(x*y)*y = (x*x)*(y*y)
        assert((x * y) * (x * y) == (x * x) * (y * y)) by {
            // (x*y)*(x*y) = x * (y * (x * y))
            lemma_mul_is_associative(x as int, y as int, (x * y) as int);
            // y * (x * y) = (y * x) * y
            lemma_mul_is_associative(y as int, x as int, y as int);
            // y * x = x * y
            lemma_mul_is_commutative(y as int, x as int);
            // So x * (y * (x * y)) = x * ((x * y) * y) = x * (x * (y * y))
            lemma_mul_is_associative(x as int, y as int, y as int);
            // x * (x * (y * y)) = (x * x) * (y * y)
            lemma_mul_is_associative(x as int, x as int, (y * y) as int);
        };
    };
}

// =============================================================================
// Double Inverse and Solving Equations Lemmas
// =============================================================================
/// Lemma: inv(inv(x)) = x (mod p)
///
/// ## Mathematical Proof
/// ```text
/// Let y = inv(x). Then x · y = 1.
/// Rearranging: y · x = 1.
/// So x is the inverse of y = inv(x).
/// By uniqueness: x = inv(inv(x)).
/// ```
pub proof fn lemma_inv_of_inv(x: nat)
    ensures
        math_field_inv(math_field_inv(x)) == x % p(),
{
    let p = p();
    p_gt_2();  // Needed for field operations

    let inv_x = math_field_inv(x);
    let x_mod = x % p;

    // Handle zero case: if x % p == 0, then inv(x) = 0 and inv(inv(x)) = inv(0) = 0 = x % p
    if x % p == 0 {
        assert(math_field_inv(inv_x) == x_mod) by {
            // inv(x) = 0 when x % p == 0
            assert(inv_x == 0);
            // inv(0) = 0 since 0 % p == 0
            assert(math_field_inv(0) == 0) by {
                assert(0nat % p == 0) by {
                    lemma_small_mod(0, p);
                };
            };
        };
        return ;
    }
    // Non-zero case: proceed with original proof
    // Step 1: Get properties of inv(x): inv_x < p and (x % p) * inv_x % p == 1

    assert(inv_x < p && ((x % p) * inv_x) % p == 1) by {
        field_inv_property(x);
    };

    // Step 2: inv_x % p != 0 (otherwise (x % p) * 0 = 0 ≠ 1)
    assert(inv_x % p != 0) by {
        lemma_small_mod(inv_x, p);
        if inv_x == 0 {
            // If inv_x == 0, then (x % p) * inv_x = (x % p) * 0 = 0
            // But we know ((x % p) * inv_x) % p == 1
            // So 0 % p == 1, but 0 % p == 0, contradiction
            assert((x % p) * 0 == 0) by {
                lemma_mul_basics((x % p) as int);
            };
            lemma_small_mod(0, p);
            // Now we have 0 % p == 1 (from Step 1) but also 0 % p == 0, contradiction
        }
    };

    // Step 3: x_mod < p
    assert(x_mod < p) by {
        lemma_mod_bound(x as int, p as int);
    };

    // Step 4: ((inv_x % p) * x_mod) % p == 1 (by commutativity)
    assert(((inv_x % p) * x_mod) % p == 1) by {
        lemma_small_mod(inv_x, p);
        lemma_mul_is_commutative(inv_x as int, x_mod as int);
    };

    // Step 5: By uniqueness of inverse, x_mod = inv(inv_x)
    assert(math_field_inv(inv_x) == x_mod) by {
        field_inv_unique(inv_x, x_mod);
    };
}

/// Lemma: If a · b = c (in field), then a = c · inv(b)
///
/// Useful for solving for one factor in a field equation.
///
/// ## Mathematical Proof
/// ```text
/// Given: a · b ≡ c (mod p)
/// Multiply both sides by inv(b):
///   a · b · inv(b) ≡ c · inv(b) (mod p)
///   a · 1 ≡ c · inv(b) (mod p)
///   a ≡ c · inv(b) (mod p)
/// ```
pub proof fn lemma_solve_for_left_factor(a: nat, b: nat, c: nat)
    requires
        b % p() != 0,
        math_field_mul(a, b) == c % p(),
    ensures
        a % p() == math_field_mul(c, math_field_inv(b)),
{
    let p = p();
    p_gt_2();  // Needed for field operations

    let inv_b = math_field_inv(b);
    let ab_mod = math_field_mul(a, b);

    // Establish inv_b properties: inv_b < p and (b % p) * inv_b % p == 1
    assert(inv_b < p && ((b % p) * inv_b) % p == 1) by {
        field_inv_property(b);
    };

    // Step 1: math_field_mul(a, b) = (a * b) % p = c % p
    assert(ab_mod == c % p);

    // Step 2: a · b · inv(b) ≡ a (mod p)
    // Because b · inv(b) ≡ 1
    assert((a * b * inv_b) % p == a % p) by {
        // (a * b * inv_b) % p = (a * (b * inv_b)) % p [associativity]
        lemma_mul_is_associative(a as int, b as int, inv_b as int);

        // = (a * ((b % p) * inv_b) % p) % p [mod absorption]
        // = (a * 1) % p [since (b%p) * inv_b % p = 1]
        // = a % p

        // We need: (b * inv_b) % p == 1
        assert(((b % p) * inv_b) % p == 1);
        lemma_mul_mod_noop_left(b as int, inv_b as int, p as int);
        assert((b * inv_b) % p == 1);

        // Now: (a * (b * inv_b)) % p = (a * 1) % p = a % p
        lemma_mul_mod_noop_right(a as int, (b * inv_b) as int, p as int);
        // ((a * ((b * inv_b) % p)) % p = (a * (b * inv_b)) % p
        // ((a * 1) % p) = (a * (b * inv_b)) % p
        lemma_mul_basics(a as int);  // a * 1 = a
    };

    // Step 3: (a · b) · inv(b) % p = (c % p) · inv(b) % p = c · inv(b) % p
    assert((ab_mod * inv_b) % p == math_field_mul(c, inv_b)) by {
        // ab_mod = c % p
        // (ab_mod * inv_b) % p = ((c % p) * inv_b) % p
        // = (c * inv_b) % p by mod absorption
        lemma_mul_mod_noop_left(c as int, inv_b as int, p as int);
    };

    // Step 4: Connect (a * b * inv_b) % p to (ab_mod * inv_b) % p
    assert((a * b * inv_b) % p == (ab_mod * inv_b) % p) by {
        // ab_mod = (a * b) % p
        // ((a * b) % p * inv_b) % p = (a * b * inv_b) % p
        lemma_mul_mod_noop_left((a * b) as int, inv_b as int, p as int);
    };

    // Step 5: Chain: a % p = (a*b*inv_b) % p = (ab_mod * inv_b) % p = c * inv_b % p
}

/// Lemma: Field multiplication is associative
///
/// (a · b) · c = a · (b · c) in field arithmetic
pub proof fn lemma_field_mul_assoc(a: nat, b: nat, c: nat)
    ensures
        math_field_mul(math_field_mul(a, b), c) == math_field_mul(a, math_field_mul(b, c)),
{
    let p = p();
    p_gt_2();

    let ab = math_field_mul(a, b);
    let bc = math_field_mul(b, c);

    // LHS = ((a*b) % p * c) % p
    // RHS = (a * (b*c) % p) % p

    // By mod absorption, both equal (a * b * c) % p
    assert(math_field_mul(ab, c) == math_field_mul(a, bc)) by {
        lemma_mul_mod_noop_left((a * b) as int, c as int, p as int);
        lemma_mul_mod_noop_right(a as int, (b * c) as int, p as int);
        lemma_mul_is_associative(a as int, b as int, c as int);
    };
}

/// Lemma: Field multiplication is commutative
///
/// a · b = b · a in field arithmetic
pub proof fn lemma_field_mul_comm(a: nat, b: nat)
    ensures
        math_field_mul(a, b) == math_field_mul(b, a),
{
    lemma_mul_is_commutative(a as int, b as int);
}

/// Lemma: a · inv(a·b) = inv(b)
///
/// ## Mathematical Proof
/// ```text
/// a · inv(a·b) = a · inv(a) · inv(b)     [by lemma_inv_of_product]
///              = (a · inv(a)) · inv(b)   [by associativity]
///              = 1 · inv(b)              [by inverse property]
///              = inv(b)
/// ```
pub proof fn lemma_a_times_inv_ab_is_inv_b(a: nat, b: nat)
    requires
        a % p() != 0,
    ensures
        math_field_mul(a, math_field_inv(math_field_mul(a, b))) == math_field_inv(b),
{
    let p = p();
    p_gt_2();

    let ab = math_field_mul(a, b);
    let inv_a = math_field_inv(a);
    let inv_b = math_field_inv(b);
    let inv_ab = math_field_inv(ab);

    // Handle zero case: if b % p == 0, then inv(b) = 0 and ab = 0
    // LHS = a · inv(ab) = a · 0 = 0 = inv(b) = RHS
    if b % p == 0 {
        // LHS = a · inv(ab) = 0
        assert(math_field_mul(a, inv_ab) == 0) by {
            assert(inv_ab == 0) by {
                assert(ab == 0) by {
                    lemma_field_mul_zero_right(a, b);
                };
            };
            assert(inv_ab % p == 0) by {
                lemma_small_mod(0, p);
            };
            lemma_field_mul_zero_right(a, inv_ab);
        };
        // RHS = inv(b) = 0
        assert(inv_b == 0);
        return ;
    }
    // Non-zero case: b % p != 0
    // ab % p != 0 (since a ≠ 0 and b ≠ 0 and p is prime)

    assert(ab % p != 0) by {
        lemma_mod_bound((a * b) as int, p as int);
        lemma_mod_twice((a * b) as int, p as int);
        if (a * b) % p == 0 {
            axiom_p_is_prime();
            lemma_euclid_prime(a, b, p);
            assert(false);
        }
    };

    // Step 1: inv(a·b) = inv(a) · inv(b)
    let inv_a_times_inv_b = math_field_mul(inv_a, inv_b);
    assert(inv_ab == inv_a_times_inv_b) by {
        lemma_inv_of_product(a, b);
    };

    // Step 2: Build the chain explicitly
    //
    // LHS = (a * inv_ab) % p
    //     = (a * ((inv_a * inv_b) % p)) % p     [since inv_ab = (inv_a * inv_b) % p]
    //     = (a * (inv_a * inv_b)) % p           [by lemma_mul_mod_noop_right]
    //     = ((a * inv_a) * inv_b) % p           [by associativity]
    //     = (1 * inv_b) % p                     [since (a * inv_a) % p = 1]
    //     = inv_b                               [since inv_b < p]

    let a_times_inv_ab = math_field_mul(a, inv_ab);

    // Step 2a: (a * ((inv_a * inv_b) % p)) % p = (a * (inv_a * inv_b)) % p
    assert((a * inv_a_times_inv_b) % p == (a * (inv_a * inv_b)) % p) by {
        lemma_mul_mod_noop_right(a as int, (inv_a * inv_b) as int, p as int);
    };

    // Step 2b: a * (inv_a * inv_b) = (a * inv_a) * inv_b (raw nat equality)
    assert(a * (inv_a * inv_b) == (a * inv_a) * inv_b) by {
        lemma_mul_is_associative(a as int, inv_a as int, inv_b as int);
    };

    // Step 2c: (a * inv_a) % p = 1
    assert((a * inv_a) % p == 1) by {
        field_inv_property(a);
        lemma_mul_mod_noop_left(a as int, inv_a as int, p as int);
    };

    // Step 2d: ((a * inv_a) * inv_b) % p = (1 * inv_b) % p
    assert((((a * inv_a) % p) * inv_b) % p == ((a * inv_a) * inv_b) % p) by {
        lemma_mul_mod_noop_left((a * inv_a) as int, inv_b as int, p as int);
    };
    assert(((1) * inv_b) % p == ((a * inv_a) * inv_b) % p) by {
        lemma_mul_mod_noop_left(1 as int, inv_b as int, p as int);
    };

    // Step 2e: (1 * inv_b) % p = inv_b
    // First: 1 * inv_b == inv_b (raw)
    // Then: inv_b % p == inv_b (since inv_b < p)
    assert(inv_b % p == inv_b) by {
        field_inv_property(b);
        lemma_small_mod(inv_b, p);
    };
    assert(((1) * inv_b) % p == inv_b) by {
        lemma_mul_basics(inv_b as int);
        // Now 1 * inv_b == inv_b, and inv_b % p == inv_b
    };

    // Chain together: a_times_inv_ab = (a * inv_ab) % p = ... = inv_b
    assert((a * inv_ab) % p == (a * inv_a_times_inv_b) % p) by {
        lemma_mul_mod_noop_left(a as int, inv_ab as int, p as int);
    };
    assert((a * inv_a_times_inv_b) % p == (a * (inv_a * inv_b)) % p) by {
        lemma_mul_mod_noop_right(a as int, (inv_a * inv_b) as int, p as int);
    };
}

/// Lemma: (-1) · a = -a  (multiplication by -1 is negation)
///
/// ## Mathematical Proof
/// ```text
/// (-1) · a = (p - 1) · a mod p       [definition of -1]
///          = (p·a - a) mod p          [distributive]
///          = -a mod p                 [since p·a ≡ 0]
///          = (p - a % p) mod p        [definition of negation]
///          = -a
/// ```
pub proof fn lemma_neg_one_times_is_neg(a: nat)
    ensures
        math_field_mul(math_field_neg(1), a) == math_field_neg(a),
{
    let p = p();
    p_gt_2();

    let neg_one = math_field_neg(1);
    let neg_a = math_field_neg(a);
    let a_mod_p = a % p;

    // neg_one = p - 1
    assert(neg_one == p - 1) by {
        lemma_small_mod(1, p);
        lemma_small_mod((p - 1) as nat, p);
    };

    // We need: ((p-1) * a) % p == neg_a
    //
    // Step 1: Work with a_mod_p instead of a (mod absorption)
    // ((p-1) * a) % p = ((p-1) * (a % p)) % p
    assert(((p - 1) as int * a as int) % (p as int) == ((p - 1) as int * (a_mod_p as int)) % (
    p as int)) by {
        lemma_mul_mod_noop_right((p - 1) as int, a as int, p as int);
    };

    // Step 2: (p-1) * a_mod_p = p * a_mod_p - a_mod_p
    assert(((p - 1) * a_mod_p) as int == (p * a_mod_p) as int - (a_mod_p as int)) by {
        lemma_mul_is_distributive_sub_other_way(a_mod_p as int, p as int, 1int);
    };

    // Step 3: a_mod_p < p
    assert(a_mod_p < p) by {
        lemma_mod_bound(a as int, p as int);
    };

    // Step 4: Handle the two cases
    if a_mod_p == 0 {
        // a % p == 0 means a is a multiple of p
        // neg_a = (p - 0) % p = p % p = 0
        lemma_mod_self_0(p as int);
        assert(neg_a == 0);

        // (p-1) * a % p = ((p-1) * (a % p)) % p = ((p-1) * 0) % p = 0 % p = 0
        assert(((p - 1) * a_mod_p) == 0);
        assert(((p - 1) as int * a_mod_p as int) % (p as int) == 0) by {
            lemma_small_mod(0, p);
        };

        // neg_one * a = (p-1) * a, and ((p-1) * a) % p = ((p-1) * a_mod_p) % p = 0 = neg_a
        assert((neg_one * a) % p == neg_a) by {
            assert(neg_one == p - 1);
            assert(neg_one * a == (p - 1) * a);
            lemma_mul_mod_noop_right((p - 1) as int, a as int, p as int);
            // ((p-1) * a) % p = ((p-1) * (a % p)) % p = ((p-1) * 0) % p = 0
            assert(a_mod_p == 0);
            lemma_mul_basics((p - 1) as int);  // (p-1) * 0 = 0
        };
    } else {
        // a_mod_p > 0, so p - a_mod_p is valid and < p
        // (p * a_mod_p - a_mod_p) = p * (a_mod_p - 1) + (p - a_mod_p)
        let k: nat = (a_mod_p - 1) as nat;
        let remainder: nat = (p - a_mod_p) as nat;

        assert(p * a_mod_p - a_mod_p == p * k + remainder) by {
            // p * a_mod_p - a_mod_p
            // = p * a_mod_p - p + p - a_mod_p
            // = p * (a_mod_p - 1) + (p - a_mod_p)
            lemma_mul_is_distributive_sub(p as int, a_mod_p as int, 1int);
        };

        // remainder < p
        assert(remainder < p);

        // (p * k + remainder) % p = remainder % p = remainder
        lemma_mod_multiples_vanish(k as int, remainder as int, p as int);
        assert(((p * k + remainder) as int) % (p as int) == (remainder as int) % (p as int));

        lemma_small_mod(remainder, p);
        assert((remainder as int) % (p as int) == remainder as int);

        // neg_a = (p - a_mod_p) % p = remainder
        assert(neg_a == remainder) by {
            // math_field_neg(a) = (p - (a % p)) % p = (p - a_mod_p) % p = remainder
            lemma_small_mod((p - a_mod_p) as nat, p);
        };

        // Chain: (neg_one * a) % p = ((p-1) * a) % p = ((p-1) * a_mod_p) % p
        //      = (p * a_mod_p - a_mod_p) % p = (p * k + remainder) % p = remainder = neg_a
        assert((((p - 1) * a_mod_p) as int) % (p as int) == remainder as int) by {
            assert(((p - 1) * a_mod_p) == p * a_mod_p - a_mod_p);
            assert(p * a_mod_p - a_mod_p == p * k + remainder);
        };

        assert(((neg_one * a) as int) % (p as int) == neg_a as int) by {
            assert(neg_one * a == (p - 1) * a);
            lemma_mul_mod_noop_right((p - 1) as int, a as int, p as int);
        };
    };
}

/// Lemma: (-a) · inv(a·b) = (-1) · inv(b)
///
/// ## Mathematical Proof (using lemma_a_times_inv_ab_is_inv_b)
/// ```text
/// (-a) · inv(a·b) = ((-1) · a) · inv(a·b)     [by lemma_neg_one_times_is_neg]
///                 = (-1) · (a · inv(a·b))     [by associativity]
///                 = (-1) · inv(b)             [by lemma_a_times_inv_ab_is_inv_b]
/// ```
pub proof fn lemma_neg_a_times_inv_ab(a: nat, b: nat)
    requires
        a % p() != 0,
    ensures
        math_field_mul(math_field_neg(a), math_field_inv(math_field_mul(a, b))) == math_field_mul(
            math_field_neg(1),
            math_field_inv(b),
        ),
{
    let p = p();
    p_gt_2();  // Needed for field operations

    let neg_a = math_field_neg(a);
    let neg_one = math_field_neg(1);
    let ab = math_field_mul(a, b);
    let inv_ab = math_field_inv(ab);
    let inv_b = math_field_inv(b);
    let a_times_inv_ab = math_field_mul(a, inv_ab);

    // Handle zero case: if b % p == 0, then inv(b) = 0 and ab = 0
    // LHS = (-a) · inv(ab) = (-a) · 0 = 0 = (-1) · 0 = (-1) · inv(b) = RHS
    if b % p == 0 {
        // LHS = (-a) · inv(ab) = 0
        assert(math_field_mul(neg_a, inv_ab) == 0) by {
            assert(inv_ab == 0) by {
                assert(ab == 0) by {
                    lemma_field_mul_zero_right(a, b);
                };
            };
            assert(inv_ab % p == 0) by {
                lemma_small_mod(0, p);
            };
        };
        // RHS = (-1) · inv(b) = 0
        assert(math_field_mul(neg_one, inv_b) == 0) by {
            assert(inv_b == 0);
            assert(inv_b % p == 0) by {
                lemma_small_mod(0, p);
            };
        };
        return ;
    }
    // Non-zero case: proceed with original proof
    // Step 1: (-a) = (-1) · a

    assert(math_field_mul(neg_one, a) == neg_a) by {
        lemma_neg_one_times_is_neg(a);
    };

    // Step 2: a · inv(a·b) = inv(b)
    assert(a_times_inv_ab == inv_b) by {
        lemma_a_times_inv_ab_is_inv_b(a, b);
    };

    // Step 3: ((-1) · a) · inv(a·b) = (-1) · (a · inv(a·b)) [associativity]
    assert(math_field_mul(math_field_mul(neg_one, a), inv_ab) == math_field_mul(
        neg_one,
        math_field_mul(a, inv_ab),
    )) by {
        lemma_field_mul_assoc(neg_one, a, inv_ab);
    };

    // Chain: (-a) · inv(a·b) = (-1) · inv(b)
    assert(math_field_mul(neg_a, inv_ab) == math_field_mul(neg_one, inv_b));
}

/// Lemma: (-1) · (-a) = a  (double negation in field)
///
/// ## Mathematical Proof
/// ```text
/// (-1) · (-a) = (p - 1) · (p - a) mod p        [definition of negation]
///             = p² - pa - p + a mod p
///             = p(p - a - 1) + a mod p
///             = a mod p                          [since p·k ≡ 0 mod p]
///             = a                                [if a < p]
/// ```
pub proof fn lemma_double_negation(a: nat)
    requires
        a < p(),
        a != 0,
    ensures
        math_field_mul(math_field_neg(1), math_field_neg(a)) == a,
{
    let p = p();
    p_gt_2();

    let neg_one = math_field_neg(1);
    let neg_a = math_field_neg(a);

    // Step 1: neg_one = p - 1 (since 1 < p)
    assert(neg_one == p - 1) by {
        lemma_small_mod(1, p);
        // math_field_neg(1) = (p - (1 % p)) % p = (p - 1) % p = p - 1
        lemma_small_mod((p - 1) as nat, p);
    };

    // Step 2: neg_a = p - a (since a < p)
    assert(neg_a == p - a) by {
        lemma_small_mod(a, p);
        // math_field_neg(a) = (p - (a % p)) % p = (p - a) % p = p - a
        lemma_small_mod((p - a) as nat, p);
    };

    // Step 3: (p-1)(p-a) % p = a
    //
    // Direct calculation:
    // (p-1)(p-a) = p*p - p*a - p + a = p*(p - a - 1) + a
    // So (p-1)(p-a) % p = (p*(p-a-1) + a) % p = a (since a < p)

    let prod = (p - 1) * (p - a);

    // Algebraic identity: (p-1)(p-a) = p*(p-a-1) + a
    // p*(p-a-1) + a = p*p - p*a - p + a
    // (p-1)*(p-a) = p*(p-a) - (p-a) = p*p - p*a - p + a ✓
    assert(prod == p * (p - a - 1) + a) by {
        assert((p - 1) * (p - a) == p * (p - a) - (p - a)) by {
            lemma_mul_is_distributive_sub_other_way((p - a) as int, p as int, 1int);
        };
        assert(p * (p - a) == p * p - p * a) by {
            lemma_mul_is_distributive_sub(p as int, p as int, a as int);
        };
        assert(p * (p - a - 1) == p * p - p * a - p) by {
            lemma_mul_is_distributive_sub(p as int, (p - a) as int, 1int);
        };
    };

    // (p*(p-a-1) + a) % p = a since a < p
    // Using lemma_mod_multiples_vanish(k, b, m): (m*k + b) % m == b % m
    assert((prod as int) % (p as int) == a as int) by {
        assert(prod == p * (p - a - 1) + a);
        // (p * (p-a-1) + a) % p == a % p
        lemma_mod_multiples_vanish((p - a - 1) as int, a as int, p as int);
        // a % p == a since a < p
        lemma_small_mod(a, p);
    };

    // Step 5: Connect to math_field_mul
    // math_field_mul(neg_one, neg_a) = (neg_one * neg_a) % p = ((p-1) * (p-a)) % p = prod % p = a
    assert((neg_one * neg_a) % p == a);
}

/// Lemma: (a·c) / (b·c) = a / b  (common factor cancellation)
///
/// ## Mathematical Proof
/// ```text
/// (a·c) · inv(b·c)
/// = (a·c) · (inv(b) · inv(c))     [by lemma_inv_of_product]
/// = a · (c · inv(c)) · inv(b)     [by assoc/comm]
/// = a · 1 · inv(b)                [by field_inv_property: c · inv(c) = 1]
/// = a · inv(b)
/// ```
pub proof fn lemma_cancel_common_factor(a: nat, b: nat, c: nat)
    requires
        b % p() != 0,
        c % p() != 0,
    ensures
        math_field_mul(math_field_mul(a, c), math_field_inv(math_field_mul(b, c)))
            == math_field_mul(a, math_field_inv(b)),
{
    let p = p();
    p_gt_2();

    let ac = math_field_mul(a, c);
    let bc = math_field_mul(b, c);
    let inv_b = math_field_inv(b);
    let inv_c = math_field_inv(c);
    let inv_bc = math_field_inv(bc);

    // bc % p != 0 (product of non-zero elements in prime field)
    assert(bc % p != 0) by {
        lemma_mod_bound((b * c) as int, p as int);
        lemma_mod_twice((b * c) as int, p as int);
        if (b * c) % p == 0 {
            axiom_p_is_prime();
            lemma_euclid_prime(b, c, p);
            assert(false);
        }
    };

    // Step 1: inv(b·c) = inv(b) · inv(c)
    assert(inv_bc == math_field_mul(inv_b, inv_c)) by {
        lemma_inv_of_product(b, c);
    };

    // Step 2: c · inv(c) = 1
    assert(math_field_mul(c, inv_c) == 1) by {
        field_inv_property(c);
        lemma_mul_mod_noop_left(c as int, inv_c as int, p as int);
        lemma_small_mod(1, p);
    };

    // Step 3: (a·c) · (inv(b) · inv(c)) = a · inv(b)
    // Rearrange using associativity and commutativity:
    // (a·c) · (inv(b) · inv(c))
    // = a · (c · (inv(b) · inv(c)))        [assoc]
    // = a · (c · (inv(c) · inv(b)))        [comm on inv(b), inv(c)]
    // = a · ((c · inv(c)) · inv(b))        [assoc]
    // = a · (1 · inv(b))                   [c · inv(c) = 1]
    // = a · inv(b)

    let inv_b_inv_c = math_field_mul(inv_b, inv_c);

    // (a·c) · inv(b·c) = (a·c) · (inv(b) · inv(c))
    assert(math_field_mul(ac, inv_bc) == math_field_mul(ac, inv_b_inv_c));

    // Now show (a·c) · (inv(b) · inv(c)) = a · inv(b)
    assert(math_field_mul(ac, inv_b_inv_c) == math_field_mul(a, inv_b)) by {
        // Work at the integer level modulo p
        // LHS = ((a*c) % p * ((inv_b * inv_c) % p)) % p
        //     = ((a*c) * (inv_b * inv_c)) % p
        lemma_mul_mod_noop((a * c) as int, (inv_b * inv_c) as int, p as int);

        // RHS = (a * inv_b) % p

        // Show (a*c) * (inv_b * inv_c) ≡ a * inv_b (mod p)

        // (a*c) * (inv_b * inv_c) = a * (c * inv_b * inv_c) [assoc]
        assert((a * c) * (inv_b * inv_c) == a * (c * (inv_b * inv_c))) by {
            lemma_mul_is_associative(a as int, c as int, (inv_b * inv_c) as int);
        };

        // c * (inv_b * inv_c) = c * (inv_c * inv_b) [comm]
        assert(c * (inv_b * inv_c) == c * (inv_c * inv_b)) by {
            lemma_mul_is_commutative(inv_b as int, inv_c as int);
        };

        // c * (inv_c * inv_b) = (c * inv_c) * inv_b [assoc]
        assert(c * (inv_c * inv_b) == (c * inv_c) * inv_b) by {
            lemma_mul_is_associative(c as int, inv_c as int, inv_b as int);
        };

        // (c * inv_c) % p = 1
        assert((c * inv_c) % p == 1) by {
            field_inv_property(c);
            lemma_mul_mod_noop_left(c as int, inv_c as int, p as int);
        };

        // ((c * inv_c) * inv_b) % p = (1 * inv_b) % p = inv_b % p = inv_b
        assert(((c * inv_c) * inv_b) % p == inv_b) by {
            lemma_mul_mod_noop_left((c * inv_c) as int, inv_b as int, p as int);
            lemma_mul_basics(inv_b as int);
            field_inv_property(b);
            lemma_small_mod(inv_b, p);
        };

        // Chain: (a * (c * (inv_b * inv_c))) % p = (a * ((c * inv_c) * inv_b)) % p
        assert((a * (c * (inv_b * inv_c))) % p == (a * ((c * inv_c) * inv_b)) % p) by {
            assert(c * (inv_b * inv_c) == (c * inv_c) * inv_b);
        };

        // (a * ((c * inv_c) * inv_b)) % p = (a * inv_b) % p
        assert((a * ((c * inv_c) * inv_b)) % p == (a * inv_b) % p) by {
            lemma_mul_mod_noop_right(a as int, ((c * inv_c) * inv_b) as int, p as int);
            // (a * (((c * inv_c) * inv_b) % p)) % p
            // = (a * inv_b) % p  [since ((c * inv_c) * inv_b) % p = inv_b]
        };
    };
}

/// Lemma: Product of non-zero field elements is non-zero
///
/// In a prime field, if a ≢ 0 and b ≢ 0, then a·b ≢ 0
pub proof fn lemma_nonzero_product(a: nat, b: nat)
    requires
        a % p() != 0,
        b % p() != 0,
    ensures
        math_field_mul(a, b) != 0,
{
    let p = p();
    p_gt_2();

    let ab = math_field_mul(a, b);

    assert(ab != 0) by {
        if ab == 0 {
            // ab = (a * b) % p = 0 means p | (a * b)
            // By Euclid's lemma for primes: p | a or p | b
            // But a % p != 0 and b % p != 0, contradiction
            lemma_mod_twice((a * b) as int, p as int);
            axiom_p_is_prime();
            lemma_euclid_prime(a, b, p);
            assert(false);
        }
    };
}

/// Lemma: Subtracting a value from itself gives zero
///
/// math_field_sub(x, x) = (((x % p) + p) - (x % p)) % p = p % p = 0
pub proof fn lemma_field_sub_self(x: nat)
    ensures
        math_field_sub(x, x) == 0,
{
    let p = p();
    p_gt_2();
    let x_mod = x % p;

    // math_field_sub(x, x) = (((x % p) + p) - (x % p)) % p
    assert(math_field_sub(x, x) == (((x_mod + p) - x_mod) as nat) % p);
    // (x_mod + p) - x_mod == p by commutativity: (a + b) - a == (b + a) - a == b
    assert((x_mod + p) - x_mod == p) by {
        assert(x_mod + p == p + x_mod);  // commutativity
        assert((p + x_mod) - x_mod == p);  // cancellation
    }
    assert(p % p == 0) by {
        vstd::arithmetic::div_mod::lemma_mod_self_0(p as int);
    }
}

} // verus!
