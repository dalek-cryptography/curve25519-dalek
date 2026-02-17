//! Abstract field algebra lemmas for GF(p) where p = 2^255 - 19
//!
//! This module contains spec-level proofs about field operations that are
//! independent of the specific limb representation. These lemmas work with
//! the `field_*` functions defined in `field_specs.rs`.
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
//! - `lemma_quotient_of_squares`: a²/b² = (a/b)²
//! - `lemma_product_of_squares_eq_square_of_product`: x²·y² = (x·y)²
//! - `lemma_field_square_of_pow_mod`: field_square(x^k % p) = x^(2k) % p
#![allow(unused_imports)]
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
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
        field_mul(a, b) == 0,
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
        field_mul(a, b) == 0,
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
        field_inv(1) == 1,
{
    // Goal: inv(1) = 1
    //
    // From field_inv_property: 1 * inv(1) ≡ 1 (mod p)
    // So inv(1) ≡ 1 (mod p)
    // Since inv(1) < p, we have inv(1) = 1
    p_gt_2();  // Needed for p > 0
    let inv = field_inv(1);

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
        field_square(field_neg(x)) == field_square(x % p()),
{
    let a = x % p();
    let neg_x = field_neg(x);
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
        field_mul(a, field_add(b, c)) == field_add(field_mul(a, b), field_mul(a, c)),
{
    let p = p();
    p_gt_2();

    // Goal: a · (b + c) = a·b + a·c in the field
    assert(field_mul(a, field_add(b, c)) == field_add(field_mul(a, b), field_mul(a, c))) by {
        // Step 1: a * ((b+c) % p) ≡ a * (b+c) (mod p)
        lemma_mul_mod_noop_right(a as int, (b + c) as int, p as int);

        // Step 2: a * (b+c) = a*b + a*c (integer distributivity)
        lemma_mul_is_distributive_add(a as int, b as int, c as int);

        // Step 3: (a*b + a*c) % p = ((a*b)%p + (a*c)%p) % p
        lemma_add_mod_noop((a * b) as int, (a * c) as int, p as int);
    };
}

/// Lemma: a + b = b + a in field arithmetic.
pub proof fn lemma_field_add_comm(a: nat, b: nat)
    ensures
        field_add(a, b) == field_add(b, a),
{
    let p = p();
    p_gt_2();
    assert(field_add(a, b) == (a + b) % p);
    assert(field_add(b, a) == (b + a) % p);
    assert((a + b) as int == (b + a) as int);
}

/// Lemma: (x + y) − (z + y) = x − z (mod p) for reduced values.
///
/// Cancellation of a common right addend under subtraction.
pub proof fn lemma_field_sub_add_common_right(x: nat, z: nat, y: nat)
    requires
        x < p(),
        z < p(),
        y < p(),
    ensures
        field_sub(field_add(x, y), field_add(z, y)) == field_sub(x, z),
{
    let p = p();
    let p_i = p as int;
    p_gt_2();

    let x1 = field_add(x, y);
    let z1 = field_add(z, y);

    assert(x1 == (x + y) % p);
    assert(z1 == (z + y) % p);
    assert(x1 < p) by {
        lemma_mod_bound((x + y) as int, p_i);
    }
    assert(z1 < p) by {
        lemma_mod_bound((z + y) as int, p_i);
    }

    assert(field_sub(x1, z1) == (((x1 + p) - z1) as nat) % p) by {
        lemma_small_mod(x1, p);
        lemma_small_mod(z1, p);
    }

    assert((x1 as int) % p_i == ((x + y) as int) % p_i) by {
        lemma_small_mod(x1, p);
        lemma_int_nat_mod_equiv((x + y) as int, p);
    }
    assert((z1 as int) % p_i == ((z + y) as int) % p_i) by {
        lemma_small_mod(z1, p);
        lemma_int_nat_mod_equiv((z + y) as int, p);
    }

    assert(((x1 + p) as int) % p_i == ((x + y + p) as int) % p_i) by {
        lemma_mod_add_multiples_vanish(x1 as int, p_i);
        lemma_mod_add_multiples_vanish((x + y) as int, p_i);
    }

    assert((((x1 + p) as int - z1 as int) % p_i) == ((((x + y + p) as int) - (z + y) as int) % p_i))
        by {
        lemma_sub_mod_noop((x1 + p) as int, z1 as int, p_i);
        lemma_sub_mod_noop((x + y + p) as int, (z + y) as int, p_i);
    }

    assert((((x + y + p) as int) - (z + y) as int) == ((x + p) as int - z as int));
    assert((((x1 + p) as int - z1 as int) % p_i) == (((x + p) as int - z as int) % p_i));
    assert((((x1 + p) - z1) as nat) % p == (((x + p) - z) as nat) % p);

    assert(field_sub(x, z) == (((x + p) - z) as nat) % p) by {
        lemma_small_mod(x, p);
        lemma_small_mod(z, p);
    }
}

/// Lemma: (a-b)(a+b) = a² - b² in field arithmetic.
///
/// The classic difference-of-squares factoring identity.
pub proof fn lemma_field_diff_of_squares(a: nat, b: nat)
    ensures
        field_mul(field_sub(a, b), field_add(a, b)) == field_sub(field_square(a), field_square(b)),
{
    let p = p();
    p_gt_2();

    let sa = field_square(a);
    let sb = field_square(b);
    let ab = field_mul(a, b);

    lemma_field_mul_distributes_over_sub_right(a, b, field_add(a, b));
    assert(field_mul(field_sub(a, b), field_add(a, b)) == field_sub(
        field_mul(a, field_add(a, b)),
        field_mul(b, field_add(a, b)),
    ));

    lemma_field_mul_distributes_over_add(a, a, b);
    lemma_field_mul_distributes_over_add(b, a, b);
    assert(field_mul(a, field_add(a, b)) == field_add(sa, ab));
    assert(field_mul(b, field_add(a, b)) == field_add(field_mul(b, a), sb));
    lemma_field_mul_comm(b, a);
    assert(field_mul(b, a) == ab);
    assert(field_add(field_mul(b, a), sb) == field_add(ab, sb));
    lemma_field_add_comm(ab, sb);
    assert(field_add(ab, sb) == field_add(sb, ab));

    assert(field_mul(field_sub(a, b), field_add(a, b)) == field_sub(
        field_add(sa, ab),
        field_add(sb, ab),
    ));

    assert(sa < p) by {
        lemma_mod_bound((a * a) as int, p as int);
    };
    assert(sb < p) by {
        lemma_mod_bound((b * b) as int, p as int);
    };
    assert(ab < p) by {
        lemma_mod_bound((a * b) as int, p as int);
    };
    lemma_field_sub_add_common_right(sa, sb, ab);
}

/// Lemma: (x % p)² = x² (mod p)
pub proof fn lemma_square_mod_noop(x: nat)
    ensures
        field_square(x % p()) == field_square(x),
{
    // ((x%p) * (x%p)) % p = (x * x) % p by mod absorption on both factors
    let p = p();
    p_gt_2();  // Needed for p > 0

    assert(field_square(x % p) == field_square(x)) by {
        lemma_mul_mod_noop_left(x as int, x as int, p as int);
        lemma_mul_mod_noop_right((x % p) as int, x as int, p as int);
    };
}

/// Lemma: Concrete squaring matches field_square spec
///
/// When y2_raw is the result of squaring y_raw (via pow(y_raw, 2)),
/// this equals field_square applied to the reduced value.
///
/// ## Mathematical Proof
/// ```text
/// y2_raw % p = pow(y_raw, 2) % p              [precondition]
///            = (y_raw * y_raw) % p            [pow(x, 2) = x * x]
///            = ((y_raw % p) * (y_raw % p)) % p [by lemma_mul_mod_noop_general]
///            = field_square(y_raw % p)   [definition]
/// ```
pub proof fn lemma_square_matches_field_square(y_raw: nat, y2_raw: nat)
    requires
        y2_raw % p() == pow(y_raw as int, 2) as nat % p(),
    ensures
        y2_raw % p() == field_square(y_raw % p()),
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

    // field_mul(y, y) = field_square(y) by definition
    assert(field_mul(y_raw % p, y_raw % p) == field_square(y_raw % p));
}

// =============================================================================
// Field Equation Rearrangement Lemmas
// =============================================================================
/// Lemma: (a+b) - (a-b) = 2b in field arithmetic.
///
/// This is a general identity in any field (here GF(p)), useful for recovering `b` from
/// the pair `(a+b, a-b)` when division by 2 is available.
pub proof fn lemma_field_add_sub_recover_double(a: nat, b: nat)
    ensures
        field_sub(field_add(a, b), field_sub(a, b)) == field_mul(2, b),
{
    let p = p();
    let p_int = p as int;
    p_gt_2();

    let am = a % p;
    let bm = b % p;

    let lhs = field_sub(field_add(a, b), field_sub(a, b));
    let rhs = field_mul(2, b);
    let rhs_simpl = field_mul(2, bm);

    // Simplify RHS to depend only on b % p.
    assert(rhs == rhs_simpl) by {
        // (2 * b) % p == (2 * (b % p)) % p
        lemma_mul_mod_noop_right(2int, b as int, p_int);
    }
    assert(rhs_simpl == (2 * bm) % p);

    // Unfold LHS and reduce to a modular arithmetic fact.
    //
    // Let A = (am + bm) and D = (am + p - bm).
    // Then:
    //   add(a,b) = A % p
    //   sub(a,b) = D % p
    // and
    //   (A % p) - (D % p) ≡ (A - D) ≡ (2bm - p) ≡ 2bm (mod p)
    let b_int = bm as int;
    let A_int = (am + bm) as int;
    let D_int = ((am + p) - bm) as int;

    // Establish the shapes of add/sub.
    assert(field_add(a, b) == (am + bm) % p) by {
        lemma_add_mod_noop(a as int, b as int, p_int);
    }
    assert(field_sub(a, b) == (((am + p) - bm) as nat) % p);

    let add_ab = field_add(a, b);
    let sub_ab = field_sub(a, b);
    assert(add_ab == (am + bm) % p);
    assert(sub_ab == (((am + p) - bm) as nat) % p);

    // Unfold the outer subtraction and simplify the internal %p's since add_ab, sub_ab are reduced (< p).
    assert(lhs == (((add_ab + p) - sub_ab) as nat) % p) by {
        assert(add_ab < p) by {
            lemma_mod_bound((am + bm) as int, p_int);
        }
        assert(sub_ab < p) by {
            lemma_mod_bound(((am + p) - bm) as int, p_int);
        }
        lemma_small_mod(add_ab, p);
        lemma_small_mod(sub_ab, p);
    }

    // Convert the nat modulo to int modulo using lemma_int_nat_mod_equiv.
    // v = add_ab + p - sub_ab is nonnegative because p > sub_ab and add_ab >= 0.
    let v_int = (add_ab as int + p_int) - sub_ab as int;
    assert(v_int >= 0) by {
        assert(sub_ab < p);
    }
    assert((v_int % p_int) as nat == (((add_ab + p) - sub_ab) as nat) % p) by {
        lemma_int_nat_mod_equiv(v_int, p);
    }

    // Rewrite v_int % p to (A_int - D_int) % p:
    // add_ab is (A_int % p), and sub_ab is (D_int % p).
    assert(add_ab as int == A_int % p_int) by {
        lemma_int_nat_mod_equiv(A_int, p);
    }
    assert(sub_ab as int == D_int % p_int) by {
        lemma_int_nat_mod_equiv(D_int, p);
    }

    // v_int % p == (A%p + p - D%p) % p == (A%p - D%p) % p
    assert(((A_int % p_int) + p_int - (D_int % p_int)) % p_int == ((A_int % p_int) - (D_int
        % p_int)) % p_int) by {
        lemma_mod_add_multiples_vanish((A_int % p_int) - (D_int % p_int), p_int);
    }

    // (A%p - D%p) % p == (A - D) % p
    lemma_sub_mod_noop(A_int, D_int, p_int);

    // A - D == 2bm - p
    assert(A_int - D_int == 2 * b_int - p_int);

    // (2bm - p) % p == (2bm) % p
    lemma_mod_add_multiples_vanish((2 * b_int) - p_int, p_int);
    assert(((2 * b_int) - p_int) % p_int == (2 * b_int) % p_int);

    // Conclude lhs == rhs_simpl == rhs.
    assert(lhs == rhs_simpl);
    assert(lhs == rhs);
}

/// Lemma: (a+b) + (a-b) = 2a in field arithmetic.
///
/// This is a general identity in any field (here GF(p)), useful for recovering `a` from
/// the pair `(a+b, a-b)` when division by 2 is available.
pub proof fn lemma_field_add_add_recover_double(a: nat, b: nat)
    ensures
        field_add(field_add(a, b), field_sub(a, b)) == field_mul(2, a),
{
    let p = p();
    let p_int = p as int;
    p_gt_2();

    let am = a % p;
    let bm = b % p;

    let lhs = field_add(field_add(a, b), field_sub(a, b));
    let rhs = field_mul(2, a);
    let rhs_simpl = field_mul(2, am);

    // Simplify RHS to depend only on a % p.
    assert(rhs == rhs_simpl) by {
        lemma_mul_mod_noop_right(2int, a as int, p_int);
    }
    assert(rhs_simpl == (2 * am) % p);

    // Rewrite the inner add/sub in terms of am,bm.
    assert(field_add(a, b) == (am + bm) % p) by {
        lemma_add_mod_noop(a as int, b as int, p_int);
    }
    assert(field_sub(a, b) == (((am + p) - bm) as nat) % p);

    let add_ab = field_add(a, b);
    let sub_ab = field_sub(a, b);
    assert(add_ab == (am + bm) % p);
    assert(sub_ab == (((am + p) - bm) as nat) % p);

    // Unfold outer add: (add_ab + sub_ab) % p
    assert(lhs == (add_ab + sub_ab) % p);

    let A_int = (am + bm) as int;
    let D_int = ((am + p) - bm) as int;

    // (A % p + D % p) % p == (A + D) % p
    lemma_add_mod_noop(A_int, D_int, p_int);

    // A + D == 2am + p
    assert(A_int + D_int == (2 * (am as int)) + p_int);
    // (2am + p) % p == (2am) % p
    lemma_mod_add_multiples_vanish(2 * (am as int), p_int);
    assert(((2 * (am as int)) + p_int) % p_int == (2 * (am as int)) % p_int);

    assert(lhs == rhs_simpl);
    assert(lhs == rhs);
}

/// Lemma: (2·a)·inv(2) = a in field arithmetic.
pub proof fn lemma_field_halve_double(a: nat)
    ensures
        field_mul(field_mul(2, a), field_inv(2)) == a % p(),
{
    let p = p();
    p_gt_2();

    // 2 is non-zero in the field since p > 2.
    assert(2nat % p != 0) by {
        lemma_small_mod(2nat, p);
    }

    // Inverse property: 2 * inv(2) = 1.
    let inv2 = field_inv(2nat);
    assert(field_mul(2nat, inv2) == 1) by {
        field_inv_property(2nat);
        lemma_small_mod(2nat, p);
    }

    // Re-associate: (2*a)*inv2 == a*(2*inv2) == a*1 == a (mod p)
    lemma_field_mul_comm(2nat, a);
    assert(field_mul(2nat, a) == field_mul(a, 2nat));
    lemma_field_mul_assoc(a, 2nat, inv2);
    assert(field_mul(field_mul(a, 2nat), inv2) == field_mul(a, field_mul(2nat, inv2)));
    assert(field_mul(a, field_mul(2nat, inv2)) == field_mul(a, 1nat));
    lemma_field_mul_one_right(a);
}

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
        field_add(a, b) == field_sub(c, 1),
    ensures
        field_add(a, 1) == field_sub(c, b),
{
    let p = p();
    let (a_int, b_int, c_int, p_int) = (a as int, b as int, c as int, p as int);
    p_gt_2();

    // Goal: (a + 1) % p = (c - b) % p
    assert(field_add(a, 1) == field_sub(c, b)) by {
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
        field_mul(1, a) == a % p(),
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
        field_mul(a, 1) == a % p(),
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
        field_mul(field_inv(a), a) == 1,
{
    let p = p();
    p_gt_2();

    let inv_a = field_inv(a);

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
// Add/Sub Cancellation Lemmas
// =============================================================================
/// Lemma: (a + b) - b = a (mod p)
pub proof fn lemma_field_sub_add_cancel(a: nat, b: nat)
    requires
        a < p(),
        b < p(),
    ensures
        field_sub(field_add(a, b), b) == a,
{
    let p = p();
    p_gt_2();

    let s = field_add(a, b);
    assert(s == (a + b) % p);
    assert(s < p) by {
        lemma_mod_bound((a + b) as int, p as int);
    }

    assert(field_sub(s, b) == (((s + p) - b) as nat) % p) by {
        lemma_small_mod(s, p);
        lemma_small_mod(b, p);
    }
    assert((s + p) % p == ((a + b) + p) % p) by {
        assert((s as int) % (p as int) == ((a + b) as int) % (p as int)) by {
            lemma_small_mod(s, p);
            lemma_int_nat_mod_equiv((a + b) as int, p);
        }
        lemma_mod_add_eq(s as int, (a + b) as int, p as int, p as int);
    }
    assert(((s + p) as int - b as int) % (p as int) == (((a + b + p) as int) - b as int) % (
    p as int)) by {
        lemma_sub_mod_noop((s + p) as int, b as int, p as int);
        lemma_sub_mod_noop((a + b + p) as int, b as int, p as int);
    }
    assert((((s + p) - b) as nat) % p == (((a + b + p) - b) as nat) % p);
    assert(((a + b + p) - b) as nat == a + p);
    lemma_mod_add_multiples_vanish(a as int, p as int);
    lemma_small_mod(a, p);
}

/// Lemma: (a - b) + b = a (mod p)
pub proof fn lemma_field_add_sub_cancel(a: nat, b: nat)
    requires
        a < p(),
        b < p(),
    ensures
        field_add(field_sub(a, b), b) == a,
{
    let p = p();
    p_gt_2();

    let d = field_sub(a, b);
    assert(d < p) by {
        lemma_mod_bound(((a + p) - b) as int, p as int);
    }
    assert(field_add(d, b) == (d + b) % p);
    assert(field_sub(a, b) == (((a + p) - b) as nat) % p) by {
        lemma_small_mod(a, p);
        lemma_small_mod(b, p);
    }
    assert((d + b) % p == ((((a + p) - b) + b) as nat) % p) by {
        assert((d as int) % (p as int) == (((a + p) - b) as int) % (p as int)) by {
            lemma_small_mod(d, p);
            lemma_int_nat_mod_equiv(((a + p) - b) as int, p);
        }
        lemma_mod_add_eq(d as int, (((a + p) - b) as int), b as int, p as int);
    }
    assert((((a + p) - b) + b) as nat == a + p);
    lemma_mod_add_multiples_vanish(a as int, p as int);
    lemma_small_mod(a, p);
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
        field_sub(b, a) == field_neg(field_sub(a, b)),
{
    let p = p();
    p_gt_2();

    let a_mod = a % p;
    let b_mod = b % p;

    // sub(a, b) = ((a_mod + p) - b_mod) % p
    // sub(b, a) = ((b_mod + p) - a_mod) % p
    let sub_ab = field_sub(a, b);
    let sub_ba = field_sub(b, a);

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
            assert(a_mod + p - b_mod == p) by {
                assert(b_mod < p) by {
                    lemma_mod_bound(b as int, p as int);
                }
            }
            lemma_mod_self_0(p as int);
        }
        assert(sub_ba == 0) by {
            lemma_mod_self_0(p as int);
        }
        assert(field_neg(sub_ab) == 0) by {
            assert(field_canonical(0) == 0) by {
                lemma_small_mod(0, p);
            }
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
        assert(field_neg(sub_ab) == p - diff) by {
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
        assert(field_neg(sub_ab) == diff) by {
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
        field_sub(a, b) == field_add(a, field_neg(b)),
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
    assert(field_neg(b) == neg_b_raw % p);

    // sub(a, b) = ((a % p) + p - (b % p)) % p = (a_mod + neg_b_raw) % p
    assert(field_sub(a, b) == (a_mod + neg_b_raw) % p) by {
        assert(((a_mod + p) - b_mod) as nat == a_mod + neg_b_raw);
    };

    // add(a, neg(b)) = (a + neg(b)) % p = (a_mod + neg_b_raw) % p
    assert(field_add(a, field_neg(b)) == (a_mod + neg_b_raw) % p) by {
        // (a + (neg_b_raw % p)) % p == (a + neg_b_raw) % p
        assert((a + field_neg(b)) % p == (a + neg_b_raw) % p) by {
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

/// Lemma: c · neg(b) = neg(c · b) in field arithmetic
///
/// Multiplication distributes into negation.
/// Uses lemma_mul_distributes_over_neg_mod from div_mod_lemmas.
pub proof fn lemma_field_mul_neg(c: nat, b: nat)
    ensures
        field_mul(c, field_neg(b)) == field_neg(field_mul(c, b)),
{
    let p = p();
    p_gt_2();

    let b_mod = b % p;
    let neg_b_raw: nat = (p - b_mod) as nat;

    // (c * ((p - b % p) as nat)) % p == ((p - (c * b) % p) as nat) % p
    lemma_mul_distributes_over_neg_mod(c, b, p);

    // Rewrite the LHS into the form used by lemma_mul_distributes_over_neg_mod.
    assert(field_mul(c, field_neg(b)) == (c * neg_b_raw) % p) by {
        // field_mul(c, field_neg(b))
        // = (c * ((p - (b % p)) as nat % p)) % p
        // = (c * ((p - (b % p)) as nat)) % p
        lemma_mul_mod_noop_right(c as int, neg_b_raw as int, p as int);
    };

    // Rewrite the RHS into the form used by lemma_mul_distributes_over_neg_mod.
    assert(field_neg(field_mul(c, b)) == ((p - (c * b) % p) as nat) % p) by {
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
        field_mul(field_sub(a, b), c) == field_sub(field_mul(a, c), field_mul(b, c)),
{
    let p = p();
    p_gt_2();

    let neg_b = field_neg(b);
    let ac = field_mul(a, c);
    let bc = field_mul(b, c);

    // Step 1: sub(a, b) = add(a, neg(b))
    lemma_field_sub_eq_add_neg(a, b);
    assert(field_sub(a, b) == field_add(a, neg_b));

    // Step 2: sub(a,b) * c = add(a, neg(b)) * c = (a + neg(b)) * c
    // By commutativity: = c * (a + neg(b)) = c*a + c*neg(b)
    lemma_field_mul_comm(field_sub(a, b), c);
    lemma_field_mul_comm(field_add(a, neg_b), c);
    lemma_field_mul_distributes_over_add(c, a, neg_b);
    assert(field_mul(c, field_add(a, neg_b)) == field_add(field_mul(c, a), field_mul(c, neg_b)));

    // Step 3: c*a = a*c and c*neg(b) = neg(c*b) = neg(b*c)
    lemma_field_mul_comm(c, a);
    lemma_field_mul_comm(c, b);
    lemma_field_mul_neg(c, b);
    assert(field_mul(c, neg_b) == field_neg(bc));

    // Step 4: add(ac, neg(bc)) = sub(ac, bc)
    // ac and bc are already < p (field elements)
    assert(ac < p) by {
        lemma_mod_bound((a * c) as int, p as int);
    };
    assert(bc < p) by {
        lemma_mod_bound((b * c) as int, p as int);
    };
    lemma_field_sub_eq_add_neg(ac, bc);
    assert(field_add(ac, field_neg(bc)) == field_sub(ac, bc));

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
        field_inv(field_mul(a, b)) == field_mul(field_inv(a), field_inv(b)),
{
    let p = p();
    p_gt_2();

    let ab = field_mul(a, b);
    let inv_a = field_inv(a);
    let inv_b = field_inv(b);
    let inv_a_inv_b = field_mul(inv_a, inv_b);

    // Handle zero cases: if a % p == 0 or b % p == 0, both sides are 0
    // since inv(0) == 0 by convention
    if a % p == 0 || b % p == 0 {
        // LHS: ab = 0, so inv(ab) = inv(0) = 0
        assert(field_inv(ab) == 0) by {
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
    assert(field_inv(ab) == inv_a_inv_b) by {
        field_inv_unique(ab, inv_a_inv_b);
    };
}

/// Lemma: a²/b² = (a/b)² (mod p)
///
/// Where a/b means a · inv(b)
///
/// ## Mathematical Proof
/// ```text
/// a²/b² = a² · inv(b²)
///       = a² · inv(b)²           [by lemma_inv_of_product(b,b)]
///       = (a · inv(b))²          [since (xy)² = x²y²]
///       = (a/b)²
/// ```
pub proof fn lemma_quotient_of_squares(a: nat, b: nat)
    ensures
        field_mul(field_square(a), field_inv(field_square(b))) == field_square(
            field_mul(a, field_inv(b)),
        ),
{
    p_gt_2();  // Needed for field operations

    let a2 = field_square(a);
    let b2 = field_square(b);
    let inv_b = field_inv(b);
    let inv_b2 = field_inv(b2);
    let a_div_b = field_mul(a, inv_b);

    // Step 1: inv(b²) = inv(b)²  (special case of inv(a·b) = inv(a)·inv(b))
    assert(inv_b2 == field_square(inv_b)) by {
        lemma_inv_of_product(b, b);
    };

    // Step 2: a² · inv(b)² = (a · inv(b))² (product-of-squares property)
    assert(field_mul(a2, field_square(inv_b)) == field_square(a_div_b)) by {
        lemma_product_of_squares_eq_square_of_product(a, inv_b);
    };

    // Chain: a² · inv(b²) = a² · inv(b)² = (a · inv(b))²
    assert(field_mul(a2, inv_b2) == field_mul(a2, field_square(inv_b)));
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
        field_mul(field_square(x), field_square(y)) == field_square(field_mul(x, y)),
{
    let p = p();
    p_gt_2();

    let x2 = field_square(x);  // (x * x) % p
    let y2 = field_square(y);  // (y * y) % p
    let xy = field_mul(x, y);  // (x * y) % p
    let xy2 = field_square(xy);  // ((x * y) % p * (x * y) % p) % p

    // Goal: (x² * y²) % p = ((xy) * (xy)) % p
    assert(field_mul(x2, y2) == xy2) by {
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
        field_inv(field_inv(x)) == x % p(),
{
    let p = p();
    p_gt_2();  // Needed for field operations

    let inv_x = field_inv(x);
    let x_mod = x % p;

    // Handle zero case: if x % p == 0, then inv(x) = 0 and inv(inv(x)) = inv(0) = 0 = x % p
    if x % p == 0 {
        assert(field_inv(inv_x) == x_mod) by {
            // inv(x) = 0 when x % p == 0
            assert(inv_x == 0);
            // inv(0) = 0 since 0 % p == 0
            assert(field_inv(0) == 0) by {
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
    assert(field_inv(inv_x) == x_mod) by {
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
        field_mul(a, b) == c % p(),
    ensures
        a % p() == field_mul(c, field_inv(b)),
{
    let p = p();
    p_gt_2();  // Needed for field operations

    let inv_b = field_inv(b);
    let ab_mod = field_mul(a, b);

    // Establish inv_b properties: inv_b < p and (b % p) * inv_b % p == 1
    assert(inv_b < p && ((b % p) * inv_b) % p == 1) by {
        field_inv_property(b);
    };

    // Step 1: field_mul(a, b) = (a * b) % p = c % p
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
    assert((ab_mod * inv_b) % p == field_mul(c, inv_b)) by {
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
        field_mul(field_mul(a, b), c) == field_mul(a, field_mul(b, c)),
{
    let p = p();
    p_gt_2();

    let ab = field_mul(a, b);
    let bc = field_mul(b, c);

    // LHS = ((a*b) % p * c) % p
    // RHS = (a * (b*c) % p) % p

    // By mod absorption, both equal (a * b * c) % p
    assert(field_mul(ab, c) == field_mul(a, bc)) by {
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
        field_mul(a, b) == field_mul(b, a),
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
        field_mul(a, field_inv(field_mul(a, b))) == field_inv(b),
{
    let p = p();
    p_gt_2();

    let ab = field_mul(a, b);
    let inv_a = field_inv(a);
    let inv_b = field_inv(b);
    let inv_ab = field_inv(ab);

    // Handle zero case: if b % p == 0, then inv(b) = 0 and ab = 0
    // LHS = a · inv(ab) = a · 0 = 0 = inv(b) = RHS
    if b % p == 0 {
        // LHS = a · inv(ab) = 0
        assert(field_mul(a, inv_ab) == 0) by {
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
    let inv_a_times_inv_b = field_mul(inv_a, inv_b);
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

    let a_times_inv_ab = field_mul(a, inv_ab);

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
        field_mul(field_neg(1), a) == field_neg(a),
{
    let p = p();
    p_gt_2();

    let neg_one = field_neg(1);
    let neg_a = field_neg(a);
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
        assert(((p - 1) * a_mod_p) == 0) by {
            lemma_mul_basics_2((p - 1) as int);
        }
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
            // field_neg(a) = (p - (a % p)) % p = (p - a_mod_p) % p = remainder
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
        field_mul(field_neg(a), field_inv(field_mul(a, b))) == field_mul(
            field_neg(1),
            field_inv(b),
        ),
{
    let p = p();
    p_gt_2();  // Needed for field operations

    let neg_a = field_neg(a);
    let neg_one = field_neg(1);
    let ab = field_mul(a, b);
    let inv_ab = field_inv(ab);
    let inv_b = field_inv(b);
    let a_times_inv_ab = field_mul(a, inv_ab);

    // Handle zero case: if b % p == 0, then inv(b) = 0 and ab = 0
    // LHS = (-a) · inv(ab) = (-a) · 0 = 0 = (-1) · 0 = (-1) · inv(b) = RHS
    if b % p == 0 {
        // LHS = (-a) · inv(ab) = 0
        assert(field_mul(neg_a, inv_ab) == 0) by {
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
        assert(field_mul(neg_one, inv_b) == 0) by {
            assert(inv_b == 0);
            assert(inv_b % p == 0) by {
                lemma_small_mod(0, p);
            };
        };
        return ;
    }
    // Non-zero case: proceed with original proof
    // Step 1: (-a) = (-1) · a

    assert(field_mul(neg_one, a) == neg_a) by {
        lemma_neg_one_times_is_neg(a);
    };

    // Step 2: a · inv(a·b) = inv(b)
    assert(a_times_inv_ab == inv_b) by {
        lemma_a_times_inv_ab_is_inv_b(a, b);
    };

    // Step 3: ((-1) · a) · inv(a·b) = (-1) · (a · inv(a·b)) [associativity]
    assert(field_mul(field_mul(neg_one, a), inv_ab) == field_mul(neg_one, field_mul(a, inv_ab)))
        by {
        lemma_field_mul_assoc(neg_one, a, inv_ab);
    };

    // Chain: (-a) · inv(a·b) = (-1) · inv(b)
    assert(field_mul(neg_a, inv_ab) == field_mul(neg_one, inv_b));
}

/// Lemma: (-1) · (-a) = a  (double negation in field)
///
/// Proof: (-1) · (-a) = field_neg(-a) = --a = a % p = a (since a < p).
/// Uses lemma_neg_one_times_is_neg and lemma_field_neg_neg.
pub proof fn lemma_double_negation(a: nat)
    requires
        a < p(),
        a != 0,
    ensures
        field_mul(field_neg(1), field_neg(a)) == a,
{
    p_gt_2();
    // (-1) * (-a) = field_neg(-a) = --a
    lemma_neg_one_times_is_neg(field_neg(a));
    // --a = a % p
    lemma_field_neg_neg(a);
    // a % p = a (since a < p)
    lemma_small_mod(a, p());
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
        field_mul(field_mul(a, c), field_inv(field_mul(b, c))) == field_mul(a, field_inv(b)),
{
    let p = p();
    p_gt_2();

    let ac = field_mul(a, c);
    let bc = field_mul(b, c);
    let inv_b = field_inv(b);
    let inv_c = field_inv(c);
    let inv_bc = field_inv(bc);

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
    assert(inv_bc == field_mul(inv_b, inv_c)) by {
        lemma_inv_of_product(b, c);
    };

    // Step 2: c · inv(c) = 1
    assert(field_mul(c, inv_c) == 1) by {
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

    let inv_b_inv_c = field_mul(inv_b, inv_c);

    // (a·c) · inv(b·c) = (a·c) · (inv(b) · inv(c))
    assert(field_mul(ac, inv_bc) == field_mul(ac, inv_b_inv_c));

    // Now show (a·c) · (inv(b) · inv(c)) = a · inv(b)
    assert(field_mul(ac, inv_b_inv_c) == field_mul(a, inv_b)) by {
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
        field_mul(a, b) != 0,
{
    let p = p();
    p_gt_2();

    let ab = field_mul(a, b);

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
/// field_sub(x, x) = (((x % p) + p) - (x % p)) % p = p % p = 0
pub proof fn lemma_field_sub_self(x: nat)
    ensures
        field_sub(x, x) == 0,
{
    let p = p();
    p_gt_2();
    let x_mod = x % p;

    // field_sub(x, x) = (((x % p) + p) - (x % p)) % p
    assert(field_sub(x, x) == (((x_mod + p) - x_mod) as nat) % p);
    // (x_mod + p) - x_mod == p by commutativity: (a + b) - a == (b + a) - a == b
    assert((x_mod + p) - x_mod == p) by {
        assert(x_mod + p == p + x_mod);  // commutativity
        assert((p + x_mod) - x_mod == p);  // cancellation
    }
    assert(p % p == 0) by {
        vstd::arithmetic::div_mod::lemma_mod_self_0(p as int);
    }
}

// =============================================================================
// FOIL (First, Outer, Inner, Last) expansion lemmas for binomial products over the field.
// =============================================================================
/// FOIL: (a+b)(c+d) = (ac + ad) + (bc + bd)
pub proof fn lemma_foil_add(a: nat, b: nat, c: nat, d: nat)
    ensures
        field_mul(field_add(a, b), field_add(c, d)) == field_add(
            field_add(field_mul(a, c), field_mul(a, d)),
            field_add(field_mul(b, c), field_mul(b, d)),
        ),
{
    let ab = field_add(a, b);
    let cd = field_add(c, d);

    // (a+b)*(c+d) = (a+b)*c + (a+b)*d by distribution
    assert(field_mul(ab, cd) == field_add(field_mul(ab, c), field_mul(ab, d))) by {
        lemma_field_mul_distributes_over_add(ab, c, d);
    }

    // (a+b)*c = a*c + b*c  by comm then distrib
    assert(field_mul(ab, c) == field_add(field_mul(a, c), field_mul(b, c))) by {
        lemma_field_mul_comm(ab, c);
        lemma_field_mul_distributes_over_add(c, a, b);
        lemma_field_mul_comm(c, a);
        lemma_field_mul_comm(c, b);
    }

    // (a+b)*d = a*d + b*d  by comm then distrib
    assert(field_mul(ab, d) == field_add(field_mul(a, d), field_mul(b, d))) by {
        lemma_field_mul_comm(ab, d);
        lemma_field_mul_distributes_over_add(d, a, b);
        lemma_field_mul_comm(d, a);
        lemma_field_mul_comm(d, b);
    }

    // Now: (a+b)(c+d) = (ac + bc) + (ad + bd)
    // We need: (ac + ad) + (bc + bd)
    // These are equal by associativity and commutativity of field addition
    // (ac + bc) + (ad + bd) = ac + (bc + ad) + bd = ac + (ad + bc) + bd = (ac + ad) + (bc + bd)
    let ac = field_mul(a, c);
    let ad = field_mul(a, d);
    let bc = field_mul(b, c);
    let bd = field_mul(b, d);

    // We have: result = (ac + bc) + (ad + bd)
    // We want: result = (ac + ad) + (bc + bd)
    // Both equal ac + ad + bc + bd in the field; prove via modular arithmetic
    assert(field_add(field_add(ac, bc), field_add(ad, bd)) == field_add(
        field_add(ac, ad),
        field_add(bc, bd),
    )) by {
        let p = p();
        p_gt_2();
        lemma_add_mod_noop((ac + bc) as int, (ad + bd) as int, p as int);
        lemma_add_mod_noop(ac as int, bc as int, p as int);
        lemma_add_mod_noop(ad as int, bd as int, p as int);
        lemma_add_mod_noop((ac + ad) as int, (bc + bd) as int, p as int);
        lemma_add_mod_noop(ac as int, ad as int, p as int);
        lemma_add_mod_noop(bc as int, bd as int, p as int);
        // Both reduce to (ac + bc + ad + bd) % p = (ac + ad + bc + bd) % p
        // which holds since integer addition is commutative
        assert((ac + bc + ad + bd) == (ac + ad + bc + bd));
    }
}

/// FOIL for subtraction: (a-b)(c-d) = (ac + bd) - (ad + bc)
/// More precisely: (a-b)(c-d) = ac - ad - bc + bd = (ac+bd) - (ad+bc)
pub proof fn lemma_foil_sub(a: nat, b: nat, c: nat, d: nat)
    ensures
        field_mul(field_sub(a, b), field_sub(c, d)) == field_sub(
            field_add(field_mul(a, c), field_mul(b, d)),
            field_add(field_mul(a, d), field_mul(b, c)),
        ),
{
    let a_minus_b = field_sub(a, b);
    let c_minus_d = field_sub(c, d);
    let ac = field_mul(a, c);
    let ad = field_mul(a, d);
    let bc = field_mul(b, c);
    let bd = field_mul(b, d);

    // (a-b)(c-d) = (a-b)*c - (a-b)*d
    // Use comm: (a-b)*(c-d) = (c-d)*(a-b), then sub_right(c,d,a_minus_b)
    assert(field_mul(a_minus_b, c_minus_d) == field_sub(
        field_mul(a_minus_b, c),
        field_mul(a_minus_b, d),
    )) by {
        lemma_field_mul_comm(a_minus_b, c_minus_d);
        // (c-d)*(a-b) = c*(a-b) - d*(a-b)
        lemma_field_mul_distributes_over_sub_right(c, d, a_minus_b);
        // c*(a-b) = (a-b)*c and d*(a-b) = (a-b)*d
        lemma_field_mul_comm(c, a_minus_b);
        lemma_field_mul_comm(d, a_minus_b);
    }

    // (a-b)*c = a*c - b*c
    assert(field_mul(a_minus_b, c) == field_sub(ac, bc)) by {
        lemma_field_mul_distributes_over_sub_right(a, b, c);
    }

    // (a-b)*d = a*d - b*d
    assert(field_mul(a_minus_b, d) == field_sub(ad, bd)) by {
        lemma_field_mul_distributes_over_sub_right(a, b, d);
    }

    // (ac - bc) - (ad - bd) = (ac + bd) - (ad + bc)
    // Both sides ≡ ac - bc - ad + bd (mod p).
    // We prove this by showing both sides equal the same nat value.
    let lhs = field_sub(field_sub(ac, bc), field_sub(ad, bd));
    let rhs = field_sub(field_add(ac, bd), field_add(ad, bc));

    // Show LHS = (ac - bc - ad + bd) mod p (as int then cast to nat)
    assert(lhs as int == ((ac as int - bc as int) - (ad as int - bd as int)) % (p() as int)) by {
        let p = p();
        let p_int = p as int;
        p_gt_2();
        lemma_small_mod(ac, p);
        lemma_small_mod(bc, p);
        lemma_small_mod(ad, p);
        lemma_small_mod(bd, p);
        // field_sub(ac, bc) = (ac + p - bc) % p
        // = (ac - bc + p) % p = (ac - bc) % p
        lemma_mod_add_multiples_vanish(ac as int - bc as int, p_int);
        lemma_mod_add_multiples_vanish(ad as int - bd as int, p_int);
        // Now sub the results
        let s1 = field_sub(ac, bc);
        let s2 = field_sub(ad, bd);
        // s1 = (ac - bc) % p as nat, s2 = (ad - bd) % p as nat
        // field_sub(s1, s2) = (s1%p + p - s2%p) % p
        // Since s1 < p and s2 < p, s1%p=s1 and s2%p=s2
        lemma_small_mod(s1, p);
        lemma_small_mod(s2, p);
        // = (s1 + p - s2) % p = (s1 - s2 + p) % p = (s1 - s2) % p
        lemma_mod_add_multiples_vanish(s1 as int - s2 as int, p_int);
        // = ((ac-bc)%p - (ad-bd)%p) % p = (ac-bc-ad+bd) % p
        lemma_sub_mod_noop(ac as int - bc as int, ad as int - bd as int, p_int);
    }

    // Show RHS = (ac + bd - ad - bc) mod p
    assert(rhs as int == ((ac as int + bd as int) - (ad as int + bc as int)) % (p() as int)) by {
        let p = p();
        let p_int = p as int;
        p_gt_2();
        lemma_small_mod(ac, p);
        lemma_small_mod(bc, p);
        lemma_small_mod(ad, p);
        lemma_small_mod(bd, p);
        let a1 = field_add(ac, bd);
        let a2 = field_add(ad, bc);
        lemma_small_mod(a1, p);
        lemma_small_mod(a2, p);
        lemma_mod_add_multiples_vanish(a1 as int - a2 as int, p_int);
        lemma_add_mod_noop(ac as int, bd as int, p_int);
        lemma_add_mod_noop(ad as int, bc as int, p_int);
        lemma_sub_mod_noop(ac as int + bd as int, ad as int + bc as int, p_int);
    }

    // The integer expressions are equal
    assert((ac as int - bc as int) - (ad as int - bd as int) == (ac as int + bd as int) - (ad as int
        + bc as int));

    // Therefore LHS == RHS
    assert(lhs == rhs);
}

// =============================================================================
// PP/MM decomposition lemmas
// =============================================================================
/// Helper: FOIL sum reordering.
/// (ac+ad)+(bc+bd) == (ac+bd)+(ad+bc) — rearranging the four-term sum.
proof fn lemma_foil_sum_reorder(ac: nat, ad: nat, bc: nat, bd: nat)
    ensures
        field_add(field_add(ac, ad), field_add(bc, bd)) == field_add(
            field_add(ac, bd),
            field_add(ad, bc),
        ),
{
    let p = p();
    assert(field_add(field_add(ac, ad), field_add(bc, bd)) == field_add(
        field_add(ac, bd),
        field_add(ad, bc),
    )) by {
        p_gt_2();
        lemma_add_mod_noop((ac + ad) as int, (bc + bd) as int, p as int);
        lemma_add_mod_noop(ac as int, ad as int, p as int);
        lemma_add_mod_noop(bc as int, bd as int, p as int);
        lemma_add_mod_noop((ac + bd) as int, (ad + bc) as int, p as int);
        lemma_add_mod_noop(ac as int, bd as int, p as int);
        lemma_add_mod_noop(ad as int, bc as int, p as int);
        assert((ac + ad + bc + bd) == (ac + bd + ad + bc));
    };
}

/// Shared decomposition for PP/MM identities.
/// Decomposes PP = (a+b)(c+d) and MM = (a-b)(c-d) into:
///   PP == big_a + big_b  and  MM == big_a - big_b
/// where big_a = ac + bd and big_b = ad + bc.
proof fn lemma_pp_mm_decompose(a: nat, b: nat, c: nat, d: nat)
    ensures
        ({
            let ac = field_mul(a, c);
            let ad = field_mul(a, d);
            let bc = field_mul(b, c);
            let bd = field_mul(b, d);
            let big_a = field_add(ac, bd);
            let big_b = field_add(ad, bc);
            let pp = field_mul(field_add(a, b), field_add(c, d));
            let mm = field_mul(field_sub(a, b), field_sub(c, d));
            pp == field_add(big_a, big_b) && mm == field_sub(big_a, big_b)
        }),
{
    let ac = field_mul(a, c);
    let ad = field_mul(a, d);
    let bc = field_mul(b, c);
    let bd = field_mul(b, d);

    lemma_foil_add(a, b, c, d);
    lemma_foil_sub(a, b, c, d);
    lemma_foil_sum_reorder(ac, ad, bc, bd);
}

/// PP - MM = 2·(y1·x2 + x1·y2) when PP = (y1+x1)(y2+x2) and MM = (y1-x1)(y2-x2)
/// More precisely, using field elements a = y1, b = x1, c = y2, d = x2:
///   (a+b)(c+d) - (a-b)(c-d) = 2·(a·d + b·c)
pub proof fn lemma_pp_minus_mm(a: nat, b: nat, c: nat, d: nat)
    ensures
        field_sub(
            field_mul(field_add(a, b), field_add(c, d)),
            field_mul(field_sub(a, b), field_sub(c, d)),
        ) == field_mul(2, field_add(field_mul(a, d), field_mul(b, c))),
{
    lemma_pp_mm_decompose(a, b, c, d);
    let big_a = field_add(field_mul(a, c), field_mul(b, d));
    let big_b = field_add(field_mul(a, d), field_mul(b, c));

    // Apply: (A+B) - (A-B) = 2B
    lemma_field_add_sub_recover_double(big_a, big_b);
}

/// PP + MM = 2·(y1·y2 + x1·x2)
pub proof fn lemma_pp_plus_mm(a: nat, b: nat, c: nat, d: nat)
    ensures
        field_add(
            field_mul(field_add(a, b), field_add(c, d)),
            field_mul(field_sub(a, b), field_sub(c, d)),
        ) == field_mul(2, field_add(field_mul(a, c), field_mul(b, d))),
{
    lemma_pp_mm_decompose(a, b, c, d);
    let big_a = field_add(field_mul(a, c), field_mul(b, d));
    let big_b = field_add(field_mul(a, d), field_mul(b, c));

    // Apply: (A+B) + (A-B) = 2A
    lemma_field_add_add_recover_double(big_a, big_b);
}

// =============================================================================
// Algebraic helper lemmas for projective ↔ affine factoring
// =============================================================================
/// Helper: (a/b) * b = a (mod p) when b is non-zero in the field.
/// Formally: mul(mul(a, inv(b)), b) == a % p().
pub proof fn lemma_div_mul_cancel(a: nat, b: nat)
    requires
        b % p() != 0,
    ensures
        field_mul(field_mul(a, field_inv(b)), b) == a % p(),
{
    let inv_b = field_inv(b);
    assert(field_mul(field_mul(a, inv_b), b) == a % p()) by {
        lemma_field_mul_assoc(a, inv_b, b);
        // mul(a, mul(inv(b), b)) = mul(a, 1) = a % p
        lemma_inv_mul_cancel(b);
        lemma_field_mul_one_right(a);
    };
}

/// Helper: mul(a*b, c*d) = mul(a*c, b*d) — four-factor rearrangement.
/// Rearranges (ab)(cd) to (ac)(bd) using associativity and commutativity.
pub proof fn lemma_four_factor_rearrange(a: nat, b: nat, c: nat, d: nat)
    ensures
        field_mul(field_mul(a, b), field_mul(c, d)) == field_mul(field_mul(a, c), field_mul(b, d)),
{
    let ab = field_mul(a, b);
    let cd = field_mul(c, d);
    let ac = field_mul(a, c);
    let bd = field_mul(b, d);

    assert(field_mul(ab, cd) == field_mul(ac, bd)) by {
        // (ab)(cd) = a(b(cd)) = a((bc)d) = a((cb)d) = a(c(bd)) = (ac)(bd)
        lemma_field_mul_assoc(a, b, cd);
        lemma_field_mul_assoc(b, c, d);
        lemma_field_mul_comm(b, c);
        lemma_field_mul_assoc(c, b, d);
        lemma_field_mul_assoc(a, c, bd);
    };
}

/// Helper: a*c + b*c = (a+b)*c — reverse distributivity for addition.
pub proof fn lemma_reverse_distribute_add(a: nat, b: nat, c: nat)
    ensures
        field_add(field_mul(a, c), field_mul(b, c)) == field_mul(field_add(a, b), c),
{
    assert(field_add(field_mul(a, c), field_mul(b, c)) == field_mul(field_add(a, b), c)) by {
        lemma_field_mul_comm(field_add(a, b), c);
        lemma_field_mul_distributes_over_add(c, a, b);
        lemma_field_mul_comm(c, a);
        lemma_field_mul_comm(c, b);
    };
}

/// Helper: a*c - b*c = (a-b)*c — reverse distributivity for subtraction.
pub proof fn lemma_reverse_distribute_sub(a: nat, b: nat, c: nat)
    ensures
        field_sub(field_mul(a, c), field_mul(b, c)) == field_mul(field_sub(a, b), c),
{
    assert(field_sub(field_mul(a, c), field_mul(b, c)) == field_mul(field_sub(a, b), c)) by {
        lemma_field_mul_comm(field_sub(a, b), c);
        lemma_field_mul_distributes_over_sub_right(a, b, c);
    };
}

/// Helper: Field left cancellation. If mul(a, b) == mul(a, c) and a ≠ 0, then b ≡ c (mod p).
pub proof fn lemma_field_mul_left_cancel(a: nat, b: nat, c: nat)
    requires
        a % p() != 0,
        field_mul(a, b) == field_mul(a, c),
    ensures
        b % p() == c % p(),
{
    let inv_a = field_inv(a);
    assert(b % p() == c % p()) by {
        // Multiply both sides by inv(a):
        // mul(inv(a), mul(a, b)) = mul(inv(a), mul(a, c))
        // mul(mul(inv(a), a), b) = mul(mul(inv(a), a), c)   [by assoc]
        // mul(1, b) = mul(1, c)                              [by inv_mul_cancel]
        // b % p = c % p                                      [by mul_one_left]
        lemma_field_mul_assoc(inv_a, a, b);
        lemma_field_mul_assoc(inv_a, a, c);
        lemma_field_mul_comm(inv_a, a);
        lemma_inv_mul_cancel(a);
        lemma_field_mul_one_left(b);
        lemma_field_mul_one_left(c);
    };
}

/// Helper: a + a = mul(2, a) — addition with self equals doubling.
pub proof fn lemma_add_self_eq_double(a: nat)
    ensures
        field_add(a, a) == field_mul(2, a),
{
    p_gt_2();
    let pp = p();
    // add(a, a) = (a + a) % p and mul(2, a) = (2 * a) % p
    // Since a + a == 2 * a as integers, these are equal.
    assert((a + a) as int == (2 * a) as int);
}

/// Double negation in field arithmetic: neg(neg(a)) = a % p.
pub proof fn lemma_neg_neg(a: nat)
    ensures
        field_neg(field_neg(a)) == a % p(),
{
    let p = p();
    p_gt_2();
    let a_mod = a % p;
    let neg_a = field_neg(a);

    assert(a_mod < p) by {
        lemma_mod_bound(a as int, p as int);
    };

    if a_mod == 0 {
        // neg(a) = (p - 0) % p = 0
        assert(neg_a == 0) by {
            lemma_mod_self_0(p as int);
        };
        // neg(0) = (p - 0) % p = 0 = a % p
        assert(field_neg(neg_a) == 0) by {
            lemma_mod_self_0(p as int);
        };
    } else {
        // neg(a) = (p - a_mod) % p = p - a_mod  (since 0 < p - a_mod < p)
        assert(neg_a == (p - a_mod) as nat) by {
            lemma_small_mod((p - a_mod) as nat, p);
        };
        // neg_a < p, so neg_a % p = neg_a
        assert(neg_a % p == neg_a) by {
            lemma_small_mod(neg_a, p);
        };
        // neg(neg_a) = (p - neg_a) % p = a_mod % p = a_mod
        assert((p - neg_a) as nat == a_mod);
        assert(field_neg(neg_a) == a_mod) by {
            lemma_small_mod(a_mod, p);
        };
    }
}

/// Helper: field_sub(c, field_neg(d)) == field_add(c, d).
///
/// Subtracting a negation is the same as adding: c - (-d) = c + d.
pub proof fn lemma_sub_neg_eq_add(c: nat, d: nat)
    ensures
        field_sub(c, field_neg(d)) == field_add(c, d),
{
    let neg_d = field_neg(d);
    let p = p();
    assert(field_sub(c, neg_d) == field_add(c, d)) by {
        lemma_field_sub_eq_add_neg(c, neg_d);
        lemma_neg_neg(d);
        p_gt_2();
        lemma_add_mod_noop(c as int, (d % p) as int, p as int);
        lemma_add_mod_noop(c as int, d as int, p as int);
        lemma_mod_twice(d as int, p as int);
    };
}

/// Shared setup for PM/MP identities: sub(c,d) = add(c, neg(d)) and sub(c, neg(d)) = add(c,d).
proof fn lemma_pm_mp_neg_setup(c: nat, d: nat)
    ensures
        field_sub(c, d) == field_add(c, field_neg(d)),
        field_sub(c, field_neg(d)) == field_add(c, d),
{
    lemma_field_sub_eq_add_neg(c, d);
    lemma_sub_neg_eq_add(c, d);
}

/// PM - MP = 2*(bc - ad) where PM = (a+b)(c-d) and MP = (a-b)(c+d).
/// This is the mixed-FOIL identity for the cross terms in subtraction.
/// Proven by substituting neg(d) into lemma_pp_minus_mm.
pub proof fn lemma_pm_minus_mp(a: nat, b: nat, c: nat, d: nat)
    ensures
        field_sub(
            field_mul(field_add(a, b), field_sub(c, d)),
            field_mul(field_sub(a, b), field_add(c, d)),
        ) == field_mul(2, field_sub(field_mul(b, c), field_mul(a, d))),
{
    let neg_d = field_neg(d);
    let ad = field_mul(a, d);
    let bc = field_mul(b, c);

    lemma_pm_mp_neg_setup(c, d);

    // Apply pp_minus_mm with neg(d): sub(PM, MP) == mul(2, add(mul(a,neg_d), bc))
    assert(field_sub(
        field_mul(field_add(a, b), field_add(c, neg_d)),
        field_mul(field_sub(a, b), field_sub(c, neg_d)),
    ) == field_mul(2, field_add(field_mul(a, neg_d), bc))) by {
        lemma_pp_minus_mm(a, b, c, neg_d);
    };

    // mul(a, neg(d)) = neg(ad)
    assert(field_mul(a, neg_d) == field_neg(ad)) by {
        lemma_field_mul_neg(a, d);
    };
    // add(neg(ad), bc) = sub(bc, ad) by commutativity + sub definition
    assert(field_add(field_neg(ad), bc) == field_sub(bc, ad)) by {
        lemma_field_sub_eq_add_neg(bc, ad);
        assert((field_neg(ad) + bc) == (bc + field_neg(ad)));
    };
}

/// PM + MP = 2*(ac - bd) where PM = (a+b)(c-d) and MP = (a-b)(c+d).
/// This is the mixed-FOIL identity for the diagonal terms in subtraction.
/// Proven by substituting neg(d) into lemma_pp_plus_mm.
pub proof fn lemma_pm_plus_mp(a: nat, b: nat, c: nat, d: nat)
    ensures
        field_add(
            field_mul(field_add(a, b), field_sub(c, d)),
            field_mul(field_sub(a, b), field_add(c, d)),
        ) == field_mul(2, field_sub(field_mul(a, c), field_mul(b, d))),
{
    let neg_d = field_neg(d);
    let ac = field_mul(a, c);
    let bd = field_mul(b, d);

    lemma_pm_mp_neg_setup(c, d);

    // Apply pp_plus_mm with neg(d): add(PM, MP) == mul(2, add(ac, mul(b, neg_d)))
    assert(field_add(
        field_mul(field_add(a, b), field_add(c, neg_d)),
        field_mul(field_sub(a, b), field_sub(c, neg_d)),
    ) == field_mul(2, field_add(ac, field_mul(b, neg_d)))) by {
        lemma_pp_plus_mm(a, b, c, neg_d);
    };

    // mul(b, neg(d)) = neg(bd)
    assert(field_mul(b, neg_d) == field_neg(bd)) by {
        lemma_field_mul_neg(b, d);
    };
    // add(ac, neg(bd)) = sub(ac, bd)
    assert(field_add(ac, field_neg(bd)) == field_sub(ac, bd)) by {
        lemma_field_sub_eq_add_neg(ac, bd);
    };
}

// =============================================================================
// Field negation helpers
// =============================================================================
/// Double negation: field_neg(field_neg(a)) == a % p()
///
/// Unlike `lemma_double_negation` (which proves (-1)·(-a) = a for a < p, a ≠ 0),
/// this proves the iterated-negation identity --a = a % p for arbitrary nat a,
/// including a = 0 and a >= p.
pub proof fn lemma_field_neg_neg(a: nat)
    ensures
        field_neg(field_neg(a)) == a % p(),
{
    let pn = p();
    p_gt_2();
    let a_mod = a % pn;
    lemma_mod_bound(a as int, pn as int);
    // field_neg(a) = (p - a%p) % p
    if a_mod == 0 {
        // field_neg(0) = (p - 0) % p = 0
        lemma_mod_self_0(pn as int);
        assert(field_neg(a) == 0) by {
            lemma_small_mod(0, pn);
        };
        // field_neg(0) = 0, field_neg(field_neg(0)) = 0 = a % p
        assert(field_neg(0nat) == 0) by {
            lemma_mod_self_0(pn as int);
            lemma_small_mod(0, pn);
        };
    } else {
        // a_mod > 0, so neg_a = p - a_mod < p
        let neg_a: nat = (pn - a_mod) as nat;
        assert(neg_a < pn);
        assert(neg_a > 0) by {
            // a_mod < p, so p - a_mod > 0
        };
        lemma_small_mod(neg_a, pn);
        assert(field_neg(a) == neg_a);
        // field_neg(neg_a) = (p - neg_a) % p = (p - (p - a_mod)) % p = a_mod % p = a_mod
        assert((pn - neg_a) as nat == a_mod) by (nonlinear_arith)
            requires
                neg_a == (pn - a_mod) as nat,
                a_mod < pn,
                a_mod > 0,
        ;
        lemma_small_mod(neg_a, pn);
        lemma_small_mod(a_mod, pn);
    }
}

/// Negation preserves nonzero: a % p != 0 ==> field_neg(a) != 0
pub proof fn lemma_field_neg_nonzero(a: nat)
    requires
        a % p() != 0,
    ensures
        field_neg(a) != 0,
{
    let pn = p();
    p_gt_2();
    let a_mod = a % pn;
    lemma_mod_bound(a as int, pn as int);
    // field_neg(a) = (p - a_mod) % p
    // Since 0 < a_mod < p: 0 < p - a_mod < p
    assert(a_mod > 0);
    assert(a_mod < pn);
    let neg_a: nat = (pn - a_mod) as nat;
    assert(neg_a > 0);
    assert(neg_a < pn);
    lemma_small_mod(neg_a, pn);
    assert(field_neg(a) == neg_a);
}

/// Negation distributes over left factor: field_mul(field_neg(a), b) == field_neg(field_mul(a, b))
///
/// This is the left-factor variant of `lemma_field_mul_neg` (which handles the right factor).
pub proof fn lemma_field_neg_mul_left(a: nat, b: nat)
    ensures
        field_mul(field_neg(a), b) == field_neg(field_mul(a, b)),
{
    // field_mul(field_neg(a), b) = field_mul(b, field_neg(a))  [comm]
    //                            = field_neg(field_mul(b, a))  [mul_neg]
    //                            = field_neg(field_mul(a, b))  [comm]
    lemma_field_mul_comm(field_neg(a), b);
    lemma_field_mul_neg(b, a);
    lemma_field_mul_comm(b, a);
}

/// field_square(pow(x, k) % p) == pow(x, 2*k) % p
///
/// Proof: field_square(y) = y^2 % p for y = x^k % p.
/// (x^k % p)^2 % p = x^(2k) % p by mod absorption and pow_multiplies.
pub proof fn lemma_field_square_of_pow_mod(x: int, k: nat)
    requires
        x >= 0,
    ensures
        pow(x, k) >= 0,
        pow(x, 2 * k) >= 0,
        field_square((pow(x, k) as nat) % p()) == (pow(x, 2 * k) as nat) % p(),
{
    let pn = p();
    p_gt_2();
    let xk = pow(x, k);
    lemma_pow_nonnegative(x, k);
    let y = (xk as nat) % pn;

    // field_square(y) = (y * y) % p
    // y = xk % p
    // (y * y) % p = (xk * xk) % p  [mod absorption]
    assert(field_square(y) == (xk * xk) as nat % pn) by {
        lemma_mul_mod_noop((xk as nat) as int, (xk as nat) as int, pn as int);
    };

    // xk * xk = xk^2 = x^(2k)
    assert(pow(xk, 2) == pow(x, 2 * k)) by {
        lemma_pow_multiplies(x, k, 2);
    };

    // pow(xk, 2) == xk * xk
    lemma_pow_2_is_mul(xk);
}

// =============================================================================
// Helper: v * field_square(u*v3) = u * (u*v7) when v7 = v3^2 * v
// =============================================================================
/// Key cancellation: field_mul(v, field_square(field_mul(u, v3))) = field_mul(u, w)
/// where v3 = field_mul(field_square(v), v) and w = field_mul(u, field_mul(field_square(v3), v))
///
/// Math: v * (u*v^3)^2 = v * u^2 * v^6 = u * u * v^7 = u * (u*v^7) = u * w
pub proof fn lemma_v_times_sq_uv3_eq_u_times_w(u_val: nat, v_val: nat)
    ensures
        ({
            let v3 = field_mul(field_square(v_val), v_val);
            let v7 = field_mul(field_square(v3), v_val);
            let w = field_mul(u_val, v7);
            let uv3 = field_mul(u_val, v3);
            field_mul(v_val, field_square(uv3)) == field_mul(u_val, w)
        }),
{
    let pn = p();
    p_gt_2();
    let v3 = field_mul(field_square(v_val), v_val);
    let v7 = field_mul(field_square(v3), v_val);
    let w = field_mul(u_val, v7);
    let uv3 = field_mul(u_val, v3);

    // Step 1: field_square(uv3) = field_mul(field_square(u_val), field_square(v3))
    lemma_product_of_squares_eq_square_of_product(u_val, v3);
    let u2 = field_square(u_val);
    let v3_sq = field_square(v3);
    assert(field_square(uv3) == field_mul(u2, v3_sq));

    // Step 2: v_val * field_mul(u2, v3_sq) = field_mul(field_mul(v_val, v3_sq), u2) by rearrangement
    assert(field_mul(v_val, field_mul(u2, v3_sq)) == field_mul(field_mul(v_val, v3_sq), u2)) by {
        // v * (u2 * v3_sq) = v * (v3_sq * u2) by comm
        lemma_field_mul_comm(u2, v3_sq);
        // = (v * v3_sq) * u2 by assoc
        lemma_field_mul_assoc(v_val, v3_sq, u2);
    };

    // Step 3: field_mul(v_val, v3_sq) = v7
    // v7 = field_mul(field_square(v3), v_val) = field_mul(v3_sq, v_val)
    // field_mul(v_val, v3_sq) = field_mul(v3_sq, v_val) = v7  by comm
    assert(field_mul(v_val, v3_sq) == v7) by {
        lemma_field_mul_comm(v_val, v3_sq);
    };

    // Step 4: field_mul(v7, u2) = field_mul(v7, field_mul(u_val, u_val))
    // u2 = field_square(u_val) = field_mul(u_val, u_val)
    // So field_mul(v7, u2) = field_mul(v7, field_mul(u_val, u_val))
    //    = field_mul(field_mul(v7, u_val), u_val) by assoc
    //    = field_mul(field_mul(u_val, v7), u_val) by comm on inner
    //    = field_mul(w, u_val) = field_mul(u_val, w) by comm
    assert(field_mul(v7, u2) == field_mul(u_val, w)) by {
        lemma_field_mul_assoc(v7, u_val, u_val);
        lemma_field_mul_comm(v7, u_val);
        lemma_field_mul_comm(field_mul(u_val, v7), u_val);
    };

    // Chain: v * sq(uv3) = v * mul(u2, v3_sq) = mul(mul(v, v3_sq), u2) = mul(v7, u2) = mul(u, w)
}

/// Connect field_mul(v, field_square(r)) to field_canonical(r * r * v) and vice versa.
/// This is needed because is_sqrt_ratio uses field_canonical(r*r*v) directly.
pub proof fn lemma_field_mul_square_canonical(r: nat, v: nat)
    ensures
        field_mul(v, field_square(r)) == field_canonical(r * r * v),
        field_mul(field_square(r), v) == field_canonical(r * r * v),
{
    let pn = p();
    p_gt_2();
    // field_square(r) = (r * r) % p
    // field_mul(v, field_square(r)) = (v * field_square(r)) % p = (v * ((r*r)%p)) % p
    // By lemma_mul_mod_noop_right: = (v * (r * r)) % p
    lemma_mul_mod_noop_right(v as int, (r * r) as int, pn as int);
    assert(v * (r * r) == r * r * v) by {
        lemma_mul_is_commutative(v as int, (r * r) as int);
    };
    // field_mul(field_square(r), v) = (field_square(r) * v) % p = (((r*r)%p) * v) % p
    lemma_mul_mod_noop_left((r * r) as int, v as int, pn as int);
    assert((r * r) * v == r * r * v) by {
        lemma_mul_is_associative(r as int, r as int, v as int);
    };
}

// =============================================================================
// Factoring / distribution helpers with common factor on the right
// =============================================================================
/// Helper: a·z + b·z = z·(a + b) (reverse distribute addition over common factor).
pub proof fn lemma_factor_result_component_add(a: nat, b: nat, z: nat)
    ensures
        field_add(field_mul(a, z), field_mul(b, z)) == field_mul(z, field_add(a, b)),
{
    lemma_reverse_distribute_add(a, b, z);
    lemma_field_mul_comm(field_add(a, b), z);
}

/// Helper: a·z - b·z = z·(a - b) (reverse distribute subtraction over common factor).
pub proof fn lemma_factor_result_component_sub(a: nat, b: nat, z: nat)
    ensures
        field_sub(field_mul(a, z), field_mul(b, z)) == field_mul(z, field_sub(a, b)),
{
    lemma_reverse_distribute_sub(a, b, z);
    lemma_field_mul_comm(field_sub(a, b), z);
}

// =============================================================================
// Scalar reassociation helpers
// =============================================================================
/// Helper: 2·(z·num) = z·(2·num), i.e. reassociate the scalar 2 past z.
pub proof fn lemma_reassociate_2_z_num(z: nat, num: nat)
    ensures
        field_mul(2, field_mul(z, num)) == field_mul(z, field_mul(2, num)),
{
    lemma_field_mul_assoc(2, z, num);
    lemma_field_mul_comm(2nat, z);
    lemma_field_mul_assoc(z, 2, num);
}

/// Helper: 2 + 2t = 2·(1+t) in the field.
pub proof fn lemma_two_times_one_plus_t(t: nat)
    ensures
        field_add(2nat, field_mul(2, t)) == field_mul(2, field_add(1, t)),
{
    p_gt_2();
    lemma_field_mul_distributes_over_add(2, 1, t);
    lemma_field_mul_one_right(2nat);
    lemma_small_mod(2nat, p());
}

/// Helper: 2 - 2t = 2·(1-t) in the field.
pub proof fn lemma_two_times_one_minus_t(t: nat)
    ensures
        field_sub(2nat, field_mul(2, t)) == field_mul(2, field_sub(1, t)),
{
    p_gt_2();
    lemma_field_mul_comm(2nat, field_sub(1, t));
    lemma_field_mul_distributes_over_sub_right(1, t, 2);
    lemma_field_mul_one_left(2nat);
    lemma_small_mod(2nat, p());
    lemma_field_mul_comm(t, 2nat);
}

// =============================================================================
// Nonzero helpers
// =============================================================================
/// Helper: If v % p() != 0 then v != 0.
pub proof fn lemma_nonzero_from_mod(v: nat)
    requires
        v % p() != 0,
    ensures
        v != 0,
{
    if v == 0 {
        p_gt_2();
        lemma_small_mod(0nat, p());
        assert((0nat % p()) == 0);
        assert(v % p() == 0);
        assert(false);
    }
}

} // verus!
