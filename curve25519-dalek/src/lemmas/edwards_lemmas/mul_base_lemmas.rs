//! Specs and lemmas for `mul_base` (Pippenger scalar multiplication)
//!
//! This module contains specs and proofs for the radix-16 decomposition used in the
//! Pippenger algorithm (`mul_base`) for efficient scalar multiplication.
//!
//! ## Algorithm Overview
//!
//! The algorithm splits a 256-bit scalar into 64 signed radix-16 digits (each in [-8, 8])
//! and represents scalar `s` as:
//!     `s = sum_{i=0..63} d_i * 16^i`
//!
//! The Pippenger algorithm optimizes evaluation by separating even and odd indexed digits:
//!     - Even digits: `d_0, d_2, d_4, ...` contribute `sum_{j} d_{2j} * 256^j`
//!     - Odd digits:  `d_1, d_3, d_5, ...` contribute `16 * sum_{j} d_{2j+1} * 256^j`
//!
//! This allows computing two separate sums and combining them with a single doubling.
//!
//! ## Key Specs
//!
//! - `odd_sum_up_to`: Partial sum of odd-indexed digit contributions
//! - `even_sum_up_to`: Partial sum of even-indexed digit contributions
//! - `pippenger_partial`: State during Pippenger loop (16 * odd_sum + partial even_sum);
//!   `pippenger_partial(digits, 64, B)` is the full sum equal to [scalar] * B
//!
//! ## Key Lemmas
//!
//! - `lemma_pippenger_sum_correct`: Proves `pippenger_partial(digits, 64, P) == [reconstruct(digits)] P`
//! - `lemma_even_sum_up_to_correct`: Proves even digit accumulation equals scalar multiplication
//! - `lemma_odd_sum_up_to_correct`: Proves odd digit accumulation equals scalar multiplication
//! - `lemma_select_is_signed_scalar_mul`: Proves table lookup correctness for signed digits
#![allow(unused_imports)]
use crate::backend::serial::curve_models::AffineNielsPoint;
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::common_lemmas::pow_lemmas::{lemma_pow2_even, pow2_MUL_div};
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::{
    is_valid_radix_16, is_valid_radix_2w, radix_16_all_bounded, radix_16_digit_bounded,
    reconstruct_radix_16, reconstruct_radix_2w,
};
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_pos, pow2};
use vstd::calc;
use vstd::prelude::*;

verus! {

// =============================================================================
// Spec Functions: Scalar contribution from even/odd radix-16 digits
// =============================================================================
/// Computes the scalar contribution of even-indexed radix-16 digits.
///
/// Given a sequence of 64 signed digits `d_0, d_1, ..., d_63`, this function computes:
///     `sum_{j=0..n-1} d_{2j} * 256^j`
///
/// The factor 256 arises because adjacent even indices (d_0, d_2, d_4, ...) differ
/// by 16^2 = 256 in their contribution to the original scalar.
///
/// # Arguments
/// - `digits`: Sequence of radix-16 digits
/// - `n`: Number of even-odd pairs to sum (typically 32 for 64 digits)
///
/// # Returns
/// The signed integer scalar contribution from even-indexed digits
pub open spec fn radix16_even_scalar(digits: Seq<i8>, n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        let nm1 = (n - 1) as nat;
        (digits[0] as int) + (pow256(1) as int) * radix16_even_scalar(digits.skip(2), nm1)
    }
}

/// Computes the scalar contribution of odd-indexed radix-16 digits.
///
/// Given a sequence of 64 signed digits `d_0, d_1, ..., d_63`, this function computes:
///     `sum_{j=0..n-1} d_{2j+1} * 256^j`
///
/// The factor 256 arises because adjacent odd indices (d_1, d_3, d_5, ...) differ
/// by 16^2 = 256 in their contribution to the original scalar.
///
/// # Arguments
/// - `digits`: Sequence of radix-16 digits
/// - `n`: Number of even-odd pairs to sum (typically 32 for 64 digits)
///
/// # Returns
/// The signed integer scalar contribution from odd-indexed digits
pub open spec fn radix16_odd_scalar(digits: Seq<i8>, n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        let nm1 = (n - 1) as nat;
        (digits[1] as int) + (pow256(1) as int) * radix16_odd_scalar(digits.skip(2), nm1)
    }
}

// =============================================================================
// Spec Functions: Partial sum specs for Pippenger mul_base algorithm
// =============================================================================
/// Partial sum of odd-indexed radix-16 digits: sum over odd i < upper_i of a[i] * 256^(i/2) * B
///
/// This matches the structure of Loop 1 in mul_base which processes odd indices.
/// For odd index i, table[i/2] contains 256^(i/2) * B multiples.
#[verifier::opaque]
pub open spec fn odd_sum_up_to(digits: Seq<i8>, upper_i: int, B: (nat, nat)) -> (nat, nat)
    decreases upper_i,
{
    if upper_i <= 0 {
        math_edwards_identity()
    } else {
        let i = upper_i - 1;
        if i % 2 == 1 {
            // Odd index - add term a[i] * 256^(i/2) * B
            let prev = odd_sum_up_to(digits, i, B);
            let base = edwards_scalar_mul(B, pow256((i / 2) as nat));
            let term = edwards_scalar_mul_signed(base, digits[i] as int);
            edwards_add(prev.0, prev.1, term.0, term.1)
        } else {
            // Even index - skip
            odd_sum_up_to(digits, i, B)
        }
    }
}

/// Partial sum of even-indexed radix-16 digits: sum over even i < upper_i of a[i] * 256^(i/2) * B
///
/// This matches the structure of Loop 2 in mul_base which processes even indices.
#[verifier::opaque]
pub open spec fn even_sum_up_to(digits: Seq<i8>, upper_i: int, B: (nat, nat)) -> (nat, nat)
    decreases upper_i,
{
    if upper_i <= 0 {
        math_edwards_identity()
    } else {
        let i = upper_i - 1;
        if i % 2 == 0 {
            // Even index - add term a[i] * 256^(i/2) * B
            let prev = even_sum_up_to(digits, i, B);
            let base = edwards_scalar_mul(B, pow256((i / 2) as nat));
            let term = edwards_scalar_mul_signed(base, digits[i] as int);
            edwards_add(prev.0, prev.1, term.0, term.1)
        } else {
            // Odd index - skip
            even_sum_up_to(digits, i, B)
        }
    }
}

/// Partial state during loop 2: 16 * odd_sum + even_sum_up_to(digits, even_upper_i, B)
///
/// After loop 1 and mul_by_pow_2(4), the point equals 16 * odd_sum.
/// Loop 2 then adds even-indexed terms one at a time.
#[verifier::opaque]
pub open spec fn pippenger_partial(digits: Seq<i8>, even_upper_i: int, B: (nat, nat)) -> (
    nat,
    nat,
) {
    let odd_sum = odd_sum_up_to(digits, 64, B);
    let scaled = edwards_scalar_mul(odd_sum, 16);
    let even_sum = even_sum_up_to(digits, even_upper_i, B);
    edwards_add(scaled.0, scaled.1, even_sum.0, even_sum.1)
}

// =============================================================================
// Lemmas: One-step unfoldings (avoid rlimit in loop proofs)
// =============================================================================
pub proof fn lemma_even_sum_up_to_step_even(digits: Seq<i8>, i: int, B: (nat, nat))
    requires
        0 <= i,
        i % 2 == 0,
    ensures
        even_sum_up_to(digits, i + 1, B) == ({
            let prev = even_sum_up_to(digits, i, B);
            let base = edwards_scalar_mul(B, pow256((i / 2) as nat));
            let term = edwards_scalar_mul_signed(base, digits[i] as int);
            edwards_add(prev.0, prev.1, term.0, term.1)
        }),
{
    reveal_with_fuel(even_sum_up_to, 2);
}

pub proof fn lemma_even_sum_up_to_step_odd(digits: Seq<i8>, i: int, B: (nat, nat))
    requires
        0 <= i,
        i % 2 == 1,
    ensures
        even_sum_up_to(digits, i + 1, B) == even_sum_up_to(digits, i, B),
{
    reveal_with_fuel(even_sum_up_to, 2);
}

pub proof fn lemma_pippenger_partial_step_even(digits: Seq<i8>, i: int, B: (nat, nat))
    requires
        0 <= i,
        i % 2 == 0,
    ensures
        ({
            let pi = pippenger_partial(digits, i, B);
            let base = edwards_scalar_mul(B, pow256((i / 2) as nat));
            let term = edwards_scalar_mul_signed(base, digits[i] as int);
            edwards_add(pi.0, pi.1, term.0, term.1)
        }) == pippenger_partial(digits, i + 1, B),
{
    reveal(pippenger_partial);
    let odd_sum = odd_sum_up_to(digits, 64, B);
    let scaled = edwards_scalar_mul(odd_sum, 16);

    let even_i = even_sum_up_to(digits, i, B);
    lemma_even_sum_up_to_step_even(digits, i, B);
    let even_ip1 = even_sum_up_to(digits, i + 1, B);

    let base = edwards_scalar_mul(B, pow256((i / 2) as nat));
    let term = edwards_scalar_mul_signed(base, digits[i] as int);

    // pippenger_partial(digits, i, B) == scaled + even_i
    let pi = pippenger_partial(digits, i, B);
    assert(pi == edwards_add(scaled.0, scaled.1, even_i.0, even_i.1));

    // even_ip1 == even_i + term
    assert(even_ip1 == {
        let prev = even_sum_up_to(digits, i, B);
        edwards_add(prev.0, prev.1, term.0, term.1)
    });
    assert(even_ip1 == edwards_add(even_i.0, even_i.1, term.0, term.1));

    // (scaled + even_i) + term == scaled + (even_i + term)
    axiom_edwards_add_associative(scaled.0, scaled.1, even_i.0, even_i.1, term.0, term.1);
    assert(edwards_add(pi.0, pi.1, term.0, term.1) == edwards_add(
        scaled.0,
        scaled.1,
        even_ip1.0,
        even_ip1.1,
    ));
    assert(edwards_add(scaled.0, scaled.1, even_ip1.0, even_ip1.1) == pippenger_partial(
        digits,
        i + 1,
        B,
    ));
}

pub proof fn lemma_pippenger_partial_step_odd(digits: Seq<i8>, i: int, B: (nat, nat))
    requires
        0 <= i,
        i % 2 == 1,
    ensures
        pippenger_partial(digits, i + 1, B) == pippenger_partial(digits, i, B),
{
    reveal(pippenger_partial);
    let odd_sum = odd_sum_up_to(digits, 64, B);
    let scaled = edwards_scalar_mul(odd_sum, 16);
    lemma_even_sum_up_to_step_odd(digits, i, B);
    assert(pippenger_partial(digits, i, B) == {
        let even_sum = even_sum_up_to(digits, i, B);
        edwards_add(scaled.0, scaled.1, even_sum.0, even_sum.1)
    });
    assert(pippenger_partial(digits, i + 1, B) == {
        let even_sum = even_sum_up_to(digits, i + 1, B);
        edwards_add(scaled.0, scaled.1, even_sum.0, even_sum.1)
    });
}

// =============================================================================
// Lemmas: Signed scalar multiplication composition
// =============================================================================
/// Lemma: Signed scalar multiplication distributes over basepoint scaling.
///
/// Shows that `[a]([k]P) = [a*k]P` for signed `a` and unsigned `k`.
///
/// This is essential for proving that scalar multiplication by a sum of
/// weighted digits equals the sum of individual digit contributions.
pub proof fn lemma_edwards_scalar_mul_signed_of_scalar_mul(P: (nat, nat), k: nat, a: int)
    requires
        k > 0,
    ensures
        edwards_scalar_mul_signed(edwards_scalar_mul(P, k), a) == edwards_scalar_mul_signed(
            P,
            a * (k as int),
        ),
{
    reveal(edwards_scalar_mul_signed);
    if a >= 0 {
        // Reduce to the nat-nat composition lemma.
        let an = a as nat;

        assert(edwards_scalar_mul_signed(edwards_scalar_mul(P, k), a) == edwards_scalar_mul(
            edwards_scalar_mul(P, k),
            an,
        ));
        assert(edwards_scalar_mul_signed(P, a * (k as int)) == edwards_scalar_mul(
            P,
            (a * (k as int)) as nat,
        ));

        // Show k*an == (a*k) as nat.
        assert((a * (k as int)) as nat == an * k);
        assert(an * k == k * an) by {
            lemma_mul_is_commutative(an as int, k as int);
        }

        assert(edwards_scalar_mul(edwards_scalar_mul(P, k), an) == edwards_scalar_mul(P, k * an))
            by {
            lemma_edwards_scalar_mul_composition(P, k, an);
        }
        assert(edwards_scalar_mul(P, (a * (k as int)) as nat) == edwards_scalar_mul(P, k * an));
    } else {
        // a < 0: expand via definition and use nat composition on (-a).
        let ap = (-a) as nat;

        assert(edwards_scalar_mul_signed(edwards_scalar_mul(P, k), a) == {
            let (x, y) = edwards_scalar_mul(edwards_scalar_mul(P, k), ap);
            (math_field_neg(x), y)
        });

        // Rewrite the inner scalar multiplication using nat composition.
        assert(edwards_scalar_mul(edwards_scalar_mul(P, k), ap) == edwards_scalar_mul(P, k * ap))
            by {
            lemma_edwards_scalar_mul_composition(P, k, ap);
        }

        // For a < 0 and k > 0, a*k < 0, so signed scalar mul uses the negation branch.
        assert(k as int > 0);
        assert(-a > 0);
        assert((-a) * (k as int) > 0) by {
            lemma_mul_strictly_positive(-a, k as int);
        }
        assert(-(a * (k as int)) > 0) by {
            lemma_mul_unary_negation(a, k as int);
        }
        assert(a * (k as int) < 0);

        // Expand RHS definition for negative scalar.
        assert(edwards_scalar_mul_signed(P, a * (k as int)) == {
            let (x, y) = edwards_scalar_mul(P, (-(a * (k as int))) as nat);
            (math_field_neg(x), y)
        });

        // Show that -(a*k) as nat equals k * (-a) as nat.
        assert((-(a * (k as int))) as nat == k * ap) by {
            // (-a) * k == -(a * k) by integer multiplication properties
            lemma_mul_unary_negation(a, k as int);
            assert(-(a * (k as int)) == (-a) * (k as int));
            assert(-a == ap as int);
            assert((-(a * (k as int))) == (ap * k) as int);
            lemma_mul_is_commutative(ap as int, k as int);
        }

        // Conclude both sides are the same negation of the same positive scalar multiplication.
        assert(edwards_scalar_mul(P, (-(a * (k as int))) as nat) == edwards_scalar_mul(P, k * ap));
    }
}

// =============================================================================
// Lemmas: Even and odd sum correctness
// =============================================================================
/// Lemma: `even_sum_up_to` computes `[radix16_even_scalar] * B`.
///
/// Proves by induction that summing even-indexed digit contributions in the
/// Pippenger algorithm produces the correct scalar multiplication result.
pub proof fn lemma_even_sum_up_to_correct(digits: Seq<i8>, B: (nat, nat), n: nat)
    requires
        digits.len() >= 2 * n,
    ensures
        even_sum_up_to(digits, (2 * n) as int, B) == edwards_scalar_mul_signed(
            B,
            radix16_even_scalar(digits, n),
        ),
    decreases n,
{
    if n == 0 {
        reveal(even_sum_up_to);
        reveal(edwards_scalar_mul_signed);
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(radix16_even_scalar(digits, 0) == 0);
        assert(even_sum_up_to(digits, 0, B) == math_edwards_identity());
    } else {
        let nm1 = (n - 1) as nat;
        lemma_even_sum_up_to_correct(digits, B, nm1);

        // Unfold the spec once to skip the odd index (2n-1), then once to add the even index (2n-2).
        let upper = (2 * n) as int;
        let u1 = upper - 1;  // 2n-1 (odd)
        let u2 = upper - 2;  // 2n-2 (even)

        assert(u1 % 2 == 1) by (compute);
        assert(u2 % 2 == 0) by (compute);
        assert((u2 / 2) as nat == nm1) by (compute);

        reveal(even_sum_up_to);
        assert(even_sum_up_to(digits, upper, B) == even_sum_up_to(digits, u1, B));

        reveal(even_sum_up_to);
        let prev = even_sum_up_to(digits, u2, B);
        let base = edwards_scalar_mul(B, pow256(nm1));
        let term = edwards_scalar_mul_signed(base, digits[u2] as int);
        assert(even_sum_up_to(digits, u1, B) == edwards_add(prev.0, prev.1, term.0, term.1));

        // Rewrite prev using the IH (note u2 == 2*(n-1)).
        assert(u2 == (2 * nm1) as int) by (compute);
        assert(prev == even_sum_up_to(digits, (2 * nm1) as int, B));
        assert(prev == edwards_scalar_mul_signed(B, radix16_even_scalar(digits, nm1)));

        // Rewrite term to a signed scalar multiplication on B.
        assert(pow256(nm1) > 0) by {
            reveal(pow256);
            lemma_pow2_pos(8 * nm1);
        }
        lemma_edwards_scalar_mul_signed_of_scalar_mul(B, pow256(nm1), digits[u2] as int);
        assert(term == edwards_scalar_mul_signed(B, (digits[u2] as int) * (pow256(nm1) as int)));

        // Combine via signed additivity.
        axiom_edwards_scalar_mul_signed_additive(
            B,
            radix16_even_scalar(digits, nm1),
            (digits[u2] as int) * (pow256(nm1) as int),
        );
        assert(edwards_add(prev.0, prev.1, term.0, term.1) == edwards_scalar_mul_signed(
            B,
            radix16_even_scalar(digits, nm1) + (digits[u2] as int) * (pow256(nm1) as int),
        ));

        // Relate the scalar update to the low-end recursive definition.
        // radix16_even_scalar(digits, n) = radix16_even_scalar(digits, n-1) + digits[2n-2]*256^(n-1)
        assert(radix16_even_scalar(digits, n) == radix16_even_scalar(digits, nm1) + (
        digits[u2] as int) * (pow256(nm1) as int)) by {
            // Prove the step lemma for radix16_even_scalar by induction on n.
            lemma_radix16_even_scalar_step(digits, n);
        }
    }
}

/// Lemma: `odd_sum_up_to` computes `[radix16_odd_scalar] * B`.
///
/// Proves by induction that summing odd-indexed digit contributions in the
/// Pippenger algorithm produces the correct scalar multiplication result.
pub proof fn lemma_odd_sum_up_to_correct(digits: Seq<i8>, B: (nat, nat), n: nat)
    requires
        digits.len() >= 2 * n,
    ensures
        odd_sum_up_to(digits, (2 * n) as int, B) == edwards_scalar_mul_signed(
            B,
            radix16_odd_scalar(digits, n),
        ),
    decreases n,
{
    if n == 0 {
        reveal(odd_sum_up_to);
        reveal(edwards_scalar_mul_signed);
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(radix16_odd_scalar(digits, 0) == 0);
        assert(odd_sum_up_to(digits, 0, B) == math_edwards_identity());
    } else {
        let nm1 = (n - 1) as nat;
        lemma_odd_sum_up_to_correct(digits, B, nm1);

        let upper = (2 * n) as int;
        let idx = upper - 1;  // 2n-1 (odd)
        let prev_u = upper - 2;  // 2n-2

        assert(idx % 2 == 1) by (compute);
        assert((idx / 2) as nat == nm1) by (compute);

        reveal(odd_sum_up_to);
        let prev_full = odd_sum_up_to(digits, idx, B);
        let base = edwards_scalar_mul(B, pow256(nm1));
        let term = edwards_scalar_mul_signed(base, digits[idx] as int);
        assert(odd_sum_up_to(digits, upper, B) == edwards_add(
            prev_full.0,
            prev_full.1,
            term.0,
            term.1,
        ));

        // For idx = 2n-1, the preceding index prev_u = idx-1 is even, so odd_sum_up_to skips it:
        reveal(odd_sum_up_to);
        assert(prev_full == odd_sum_up_to(digits, prev_u, B));

        // Now rewrite prev_u to the n-1 prefix (2*(n-1)).
        assert(prev_u == (2 * nm1) as int) by (compute);
        let prev = odd_sum_up_to(digits, (2 * nm1) as int, B);
        assert(prev_full == prev);
        assert(prev == edwards_scalar_mul_signed(B, radix16_odd_scalar(digits, nm1)));

        assert(pow256(nm1) > 0) by {
            reveal(pow256);
            lemma_pow2_pos(8 * nm1);
        }
        lemma_edwards_scalar_mul_signed_of_scalar_mul(B, pow256(nm1), digits[idx] as int);
        assert(term == edwards_scalar_mul_signed(B, (digits[idx] as int) * (pow256(nm1) as int)));

        axiom_edwards_scalar_mul_signed_additive(
            B,
            radix16_odd_scalar(digits, nm1),
            (digits[idx] as int) * (pow256(nm1) as int),
        );
        assert(edwards_add(prev_full.0, prev_full.1, term.0, term.1) == edwards_scalar_mul_signed(
            B,
            radix16_odd_scalar(digits, nm1) + (digits[idx] as int) * (pow256(nm1) as int),
        ));

        assert(radix16_odd_scalar(digits, n) == radix16_odd_scalar(digits, nm1) + (
        digits[idx] as int) * (pow256(nm1) as int)) by {
            lemma_radix16_odd_scalar_step(digits, n);
        }
    }
}

// =============================================================================
// Lemmas: Radix-16 scalar step (inductive structure)
// =============================================================================
/// Step lemma for `radix16_even_scalar`: relates n pairs to (n-1) pairs.
///
/// Shows that adding one more even-odd pair to the sum adds the new even
/// digit with weight 256^(n-1):
///     `E(n) = E(n-1) + d_{2(n-1)} * 256^{n-1}`
pub proof fn lemma_radix16_even_scalar_step(digits: Seq<i8>, n: nat)
    requires
        n > 0,
        digits.len() >= 2 * n,
    ensures
        radix16_even_scalar(digits, n) == radix16_even_scalar(digits, (n - 1) as nat) + (digits[(2
            * ((n - 1) as nat)) as int] as int) * (pow256((n - 1) as nat) as int),
    decreases n,
{
    if n == 1 {
        reveal(radix16_even_scalar);
        assert(radix16_even_scalar(digits, 0) == 0);
        assert(pow256(0) == 1) by {
            reveal(pow256);
            lemma2_to64();
        }
        // radix16_even_scalar(digits, 1) = digits[0] and pow256(0) = 1.
        assert(radix16_even_scalar(digits, 1) == (digits[0] as int) + (pow256(1) as int)
            * radix16_even_scalar(digits.skip(2), 0));
        assert(radix16_even_scalar(digits.skip(2), 0) == 0);
        vstd::arithmetic::mul::lemma_mul_basics_2(pow256(1) as int);
        assert((pow256(1) as int) * radix16_even_scalar(digits.skip(2), 0) == 0);
        assert(radix16_even_scalar(digits, 1) == digits[0] as int);
        vstd::arithmetic::mul::lemma_mul_basics_3(digits[0] as int);
        assert(radix16_even_scalar(digits, 0) + (digits[0] as int) * (pow256(0) as int)
            == digits[0] as int);
    } else {
        let nm1 = (n - 1) as nat;
        let nm2 = (nm1 - 1) as nat;
        lemma_radix16_even_scalar_step(digits.skip(2), nm1);

        // Pull out the IH term from the suffix.
        let suf = digits.skip(2);
        assert(suf.len() >= 2 * nm1) by {
            assert(digits.len() >= 2 * n);
        }

        // Map the suffix index back to the original digits: suf[2*nm2] = digits[2*nm1].
        let suf_idx = (2 * nm2) as int;
        assert(suf_idx + 2 < digits.len());
        assert(suf[suf_idx] == digits[suf_idx + 2]);
        assert(suf_idx + 2 == (2 * nm1) as int) by (compute);
        assert(suf[suf_idx] == digits[(2 * nm1) as int]);

        // pow256(nm1) = pow256(1) * pow256(nm2)
        assert((pow256(1) as int) * (pow256(nm2) as int) == (pow256(nm1) as int)) by {
            reveal(pow256);
            assert(8 * nm1 == 8 * nm2 + 8) by (compute);
            vstd::arithmetic::power2::lemma_pow2_adds(8 * nm2, 8);
            // pow2(8*nm2 + 8) = pow2(8*nm2) * pow2(8)
            lemma_mul_is_commutative(pow2(8 * nm2) as int, pow2(8) as int);
        }

        // Expand E(n) and substitute the IH on the suffix, then regroup.
        reveal(radix16_even_scalar);
        calc! {
            (==)
            radix16_even_scalar(digits, n); (==) {}
            (digits[0] as int) + (pow256(1) as int) * radix16_even_scalar(suf, nm1); (==) {
                assert(radix16_even_scalar(suf, nm1) == radix16_even_scalar(suf, nm2) + (
                suf[suf_idx] as int) * (pow256(nm2) as int));
                lemma_mul_is_distributive_add(
                    (pow256(1) as int),
                    radix16_even_scalar(suf, nm2),
                    (suf[suf_idx] as int) * (pow256(nm2) as int),
                );
            }
            (digits[0] as int) + (pow256(1) as int) * radix16_even_scalar(suf, nm2) + (pow256(
                1,
            ) as int) * ((suf[suf_idx] as int) * (pow256(nm2) as int)); (==) {
                // (pow256(1) * (d * pow256(nm2))) == d * pow256(nm1)
                let d = suf[suf_idx] as int;
                let p = pow256(nm2) as int;
                let b = pow256(1) as int;
                assert(b * (d * p) == (b * d) * p) by {
                    lemma_mul_is_associative(b, d, p);
                }
                assert(b * d == d * b) by {
                    lemma_mul_is_commutative(b, d);
                }
                assert((d * b) * p == d * (b * p)) by {
                    lemma_mul_is_associative(d, b, p);
                }
                assert(b * (d * p) == d * (b * p));
                assert((pow256(1) as int) * (pow256(nm2) as int) == (pow256(nm1) as int));
                assert(suf[suf_idx] == digits[(2 * nm1) as int]);
            }
            (digits[0] as int) + (pow256(1) as int) * radix16_even_scalar(suf, nm2) + (digits[(2
                * nm1) as int] as int) * (pow256(nm1) as int); (==) {
                // radix16_even_scalar(digits, nm1) = digits[0] + pow256(1) * radix16_even_scalar(suf, nm2)
                assert(radix16_even_scalar(digits, nm1) == (digits[0] as int) + (pow256(1) as int)
                    * radix16_even_scalar(suf, nm2));
            }
            radix16_even_scalar(digits, nm1) + (digits[(2 * nm1) as int] as int) * (pow256(
                nm1,
            ) as int);
        }
    }
}

/// Step lemma for `radix16_odd_scalar`: relates n pairs to (n-1) pairs.
///
/// Shows that adding one more even-odd pair to the sum adds the new odd
/// digit with weight 256^(n-1):
///     `O(n) = O(n-1) + d_{2(n-1)+1} * 256^{n-1}`
pub proof fn lemma_radix16_odd_scalar_step(digits: Seq<i8>, n: nat)
    requires
        n > 0,
        digits.len() >= 2 * n,
    ensures
        radix16_odd_scalar(digits, n) == radix16_odd_scalar(digits, (n - 1) as nat) + (digits[(2 * (
        (n - 1) as nat) + 1) as int] as int) * (pow256((n - 1) as nat) as int),
    decreases n,
{
    if n == 1 {
        reveal(radix16_odd_scalar);
        assert(radix16_odd_scalar(digits, 0) == 0);
        assert(pow256(0) == 1) by {
            reveal(pow256);
            lemma2_to64();
        }
        assert(radix16_odd_scalar(digits, 1) == (digits[1] as int) + (pow256(1) as int)
            * radix16_odd_scalar(digits.skip(2), 0));
        assert(radix16_odd_scalar(digits.skip(2), 0) == 0);
        vstd::arithmetic::mul::lemma_mul_basics_2(pow256(1) as int);
        assert((pow256(1) as int) * radix16_odd_scalar(digits.skip(2), 0) == 0);
        assert(radix16_odd_scalar(digits, 1) == digits[1] as int);
        vstd::arithmetic::mul::lemma_mul_basics_3(digits[1] as int);
        assert(radix16_odd_scalar(digits, 0) + (digits[1] as int) * (pow256(0) as int)
            == digits[1] as int);
    } else {
        let nm1 = (n - 1) as nat;
        let nm2 = (nm1 - 1) as nat;
        lemma_radix16_odd_scalar_step(digits.skip(2), nm1);

        let suf = digits.skip(2);
        assert(suf.len() >= 2 * nm1);

        let suf_idx = (2 * nm2 + 1) as int;
        assert(suf_idx + 2 < digits.len());
        assert(suf[suf_idx] == digits[suf_idx + 2]);
        assert(suf_idx + 2 == (2 * nm1 + 1) as int) by (compute);
        assert(suf[suf_idx] == digits[(2 * nm1 + 1) as int]);

        assert((pow256(1) as int) * (pow256(nm2) as int) == (pow256(nm1) as int)) by {
            reveal(pow256);
            assert(8 * nm1 == 8 * nm2 + 8) by (compute);
            vstd::arithmetic::power2::lemma_pow2_adds(8 * nm2, 8);
            lemma_mul_is_commutative(pow2(8 * nm2) as int, pow2(8) as int);
        }

        reveal(radix16_odd_scalar);
        calc! {
            (==)
            radix16_odd_scalar(digits, n); (==) {}
            (digits[1] as int) + (pow256(1) as int) * radix16_odd_scalar(suf, nm1); (==) {
                assert(radix16_odd_scalar(suf, nm1) == radix16_odd_scalar(suf, nm2) + (
                suf[suf_idx] as int) * (pow256(nm2) as int));
                lemma_mul_is_distributive_add(
                    (pow256(1) as int),
                    radix16_odd_scalar(suf, nm2),
                    (suf[suf_idx] as int) * (pow256(nm2) as int),
                );
            }
            (digits[1] as int) + (pow256(1) as int) * radix16_odd_scalar(suf, nm2) + (pow256(
                1,
            ) as int) * ((suf[suf_idx] as int) * (pow256(nm2) as int)); (==) {
                let d = suf[suf_idx] as int;
                let p = pow256(nm2) as int;
                let b = pow256(1) as int;
                assert(b * (d * p) == (b * d) * p) by {
                    lemma_mul_is_associative(b, d, p);
                }
                assert(b * d == d * b) by {
                    lemma_mul_is_commutative(b, d);
                }
                assert((d * b) * p == d * (b * p)) by {
                    lemma_mul_is_associative(d, b, p);
                }
                assert(b * (d * p) == d * (b * p));
                assert((pow256(1) as int) * (pow256(nm2) as int) == (pow256(nm1) as int));
                assert(suf[suf_idx] == digits[(2 * nm1 + 1) as int]);
            }
            (digits[1] as int) + (pow256(1) as int) * radix16_odd_scalar(suf, nm2) + (digits[(2
                * nm1 + 1) as int] as int) * (pow256(nm1) as int); (==) {
                assert(radix16_odd_scalar(digits, nm1) == (digits[1] as int) + (pow256(1) as int)
                    * radix16_odd_scalar(suf, nm2));
            }
            radix16_odd_scalar(digits, nm1) + (digits[(2 * nm1 + 1) as int] as int) * (pow256(
                nm1,
            ) as int);
        }
    }
}

// =============================================================================
// Lemmas: Radix-16 reconstruction relates to even/odd split
// =============================================================================
/// Lemma: The radix-16 reconstruction equals the even/odd split.
///
/// Proves that:
///     `reconstruct_radix_16(digits) = E(n) + 16 * O(n)`
///
/// where E(n) is the even scalar contribution and O(n) is the odd scalar contribution.
/// This is the key identity that allows the Pippenger algorithm to split the computation.
pub proof fn lemma_reconstruct_radix16_even_odd(digits: Seq<i8>, n: nat)
    requires
        digits.len() >= 2 * n,
    ensures
        reconstruct_radix_16(digits.take((2 * n) as int)) == radix16_even_scalar(digits, n) + 16
            * radix16_odd_scalar(digits, n),
    decreases n,
{
    if n == 0 {
        reveal(reconstruct_radix_16);
        reveal(reconstruct_radix_2w);
        assert(digits.take(0).len() == 0);
    } else {
        let nm1 = (n - 1) as nat;
        lemma_reconstruct_radix16_even_odd(digits.skip(2), nm1);

        let pref = digits.take((2 * n) as int);
        assert(pref.len() == 2 * n);
        assert(pref.len() >= 2);

        // Unroll reconstruct by two digits: a0 + 16*a1 + 256*reconstruct(rest).
        reveal(reconstruct_radix_16);
        reveal(reconstruct_radix_2w);
        let r1 = reconstruct_radix_2w(pref.skip(1), 4);
        assert(reconstruct_radix_16(pref) == (pref[0] as int) + pow2(4) * r1);
        assert(pref.skip(1).len() > 0);
        assert(r1 == (pref.skip(1)[0] as int) + pow2(4) * reconstruct_radix_2w(
            pref.skip(1).skip(1),
            4,
        )) by {
            reveal(reconstruct_radix_2w);
        }
        assert(pref.skip(1).skip(1) =~= pref.skip(2));
        assert(reconstruct_radix_2w(pref.skip(1).skip(1), 4) == reconstruct_radix_2w(
            pref.skip(2),
            4,
        ));
        assert(pref.skip(1)[0] == pref[1]);

        assert(pow2(4) == 16) by {
            lemma2_to64();
        }
        assert(pow2(8) == 256) by {
            lemma2_to64();
        }
        vstd::arithmetic::power2::lemma_pow2_adds(4, 4);

        // Relate the remainder prefix: pref.skip(2) == digits.skip(2).take(2*(n-1)).
        let rest = digits.skip(2).take((2 * nm1) as int);
        assert(pref.skip(2) =~= rest);

        // Use IH on the remainder.
        assert(reconstruct_radix_16(rest) == radix16_even_scalar(digits.skip(2), nm1) + 16
            * radix16_odd_scalar(digits.skip(2), nm1));
        assert(reconstruct_radix_16(pref.skip(2)) == reconstruct_radix_16(rest));

        // Now finish by rewriting both sides to `a0 + 16*a1 + 256*(...)`.
        reveal(radix16_even_scalar);
        reveal(radix16_odd_scalar);
        calc! {
            (==)
            reconstruct_radix_16(pref); (==) {}
            (pref[0] as int) + pow2(4) * r1; (==) {
                assert(r1 == (pref[1] as int) + pow2(4) * reconstruct_radix_2w(pref.skip(2), 4));
            }
            (pref[0] as int) + pow2(4) * ((pref[1] as int) + pow2(4) * reconstruct_radix_2w(
                pref.skip(2),
                4,
            )); (==) {
                lemma_mul_is_distributive_add(
                    pow2(4) as int,
                    pref[1] as int,
                    (pow2(4) as int) * (reconstruct_radix_2w(pref.skip(2), 4) as int),
                );
            }
            (pref[0] as int) + (pow2(4) as int) * (pref[1] as int) + (pow2(4) as int) * ((pow2(
                4,
            ) as int) * (reconstruct_radix_2w(pref.skip(2), 4) as int)); (==) {
                lemma_mul_is_associative(
                    pow2(4) as int,
                    pow2(4) as int,
                    reconstruct_radix_2w(pref.skip(2), 4) as int,
                );
                assert((pow2(4) as int) * (pow2(4) as int) == (pow2(8) as int));
            }
            (pref[0] as int) + 16 * (pref[1] as int) + (pow2(8) as int) * (reconstruct_radix_16(
                pref.skip(2),
            ) as int); (==) {
                assert(pow2(8) == pow256(1)) by {
                    reveal(pow256);
                }
                assert(pref[0] == digits[0]);
                assert(pref[1] == digits[1]);
                assert(reconstruct_radix_16(pref.skip(2)) == radix16_even_scalar(
                    digits.skip(2),
                    nm1,
                ) + 16 * radix16_odd_scalar(digits.skip(2), nm1));
            }
            (digits[0] as int) + 16 * (digits[1] as int) + (pow256(1) as int) * ((
            radix16_even_scalar(digits.skip(2), nm1) + 16 * radix16_odd_scalar(
                digits.skip(2),
                nm1,
            )) as int); (==) {
                lemma_mul_is_distributive_add(
                    (pow256(1) as int),
                    radix16_even_scalar(digits.skip(2), nm1),
                    16 * radix16_odd_scalar(digits.skip(2), nm1),
                );
            }
            (digits[0] as int) + 16 * (digits[1] as int) + (pow256(1) as int) * radix16_even_scalar(
                digits.skip(2),
                nm1,
            ) + (pow256(1) as int) * (16 * radix16_odd_scalar(digits.skip(2), nm1)); (==) {
                assert(radix16_even_scalar(digits, n) == (digits[0] as int) + (pow256(1) as int)
                    * radix16_even_scalar(digits.skip(2), nm1));
                assert(radix16_odd_scalar(digits, n) == (digits[1] as int) + (pow256(1) as int)
                    * radix16_odd_scalar(digits.skip(2), nm1));
                lemma_mul_is_associative(
                    (pow256(1) as int),
                    16,
                    radix16_odd_scalar(digits.skip(2), nm1),
                );
            }
            radix16_even_scalar(digits, n) + 16 * radix16_odd_scalar(digits, n);
        }
    }
}

// =============================================================================
// Main correctness lemmas for Pippenger sum
// =============================================================================
/// Main lemma: Pippenger sum equals signed scalar multiplication by the reconstructed scalar.
///
/// This is the core correctness theorem for the Pippenger algorithm. It proves:
///     `pippenger_partial(digits, 64, P) == [reconstruct_radix_16(digits)] P`
///
/// The proof combines:
/// 1. Even digit sum correctness (`lemma_even_sum_up_to_correct`)
/// 2. Odd digit sum correctness (`lemma_odd_sum_up_to_correct`)
/// 3. Reconstruction equals even + 16*odd (`lemma_reconstruct_radix16_even_odd`)
/// 4. Signed additivity axiom to combine the sums
pub proof fn lemma_pippenger_sum_correct_signed(digits: Seq<i8>, basepoint: (nat, nat))
    requires
        digits.len() == 64,
    ensures
        pippenger_partial(digits, 64, basepoint) == edwards_scalar_mul_signed(
            basepoint,
            reconstruct_radix_16(digits),
        ),
{
    // Split into odd/even parts, prove each part is a signed scalar multiplication of basepoint,
    // then combine using the signed scalar-mul axioms.
    let n = 32nat;
    assert(digits.len() >= 2 * n);

    // Unfold pippenger_partial and rewrite via the proved equalities.
    reveal(pippenger_partial);

    let odd_sum = odd_sum_up_to(digits, 64, basepoint);
    let even_sum = even_sum_up_to(digits, 64, basepoint);

    assert(odd_sum == edwards_scalar_mul_signed(basepoint, radix16_odd_scalar(digits, n))) by {
        lemma_odd_sum_up_to_correct(digits, basepoint, n);
    }
    assert(even_sum == edwards_scalar_mul_signed(basepoint, radix16_even_scalar(digits, n))) by {
        lemma_even_sum_up_to_correct(digits, basepoint, n);
    }

    // Scale the odd sum by 16, then add the even sum.
    let scaled = edwards_scalar_mul(odd_sum, 16);
    assert(scaled == edwards_scalar_mul_signed(basepoint, radix16_odd_scalar(digits, n) * 16)) by {
        lemma_edwards_scalar_mul_signed_composition(basepoint, radix16_odd_scalar(digits, n), 16);
    }

    assert(edwards_add(scaled.0, scaled.1, even_sum.0, even_sum.1) == edwards_scalar_mul_signed(
        basepoint,
        radix16_odd_scalar(digits, n) * 16 + radix16_even_scalar(digits, n),
    )) by {
        axiom_edwards_scalar_mul_signed_additive(
            basepoint,
            radix16_odd_scalar(digits, n) * 16,
            radix16_even_scalar(digits, n),
        );
    }

    // Use the arithmetic lemma to rewrite the scalar as the radix-16 reconstruction.
    assert(digits.take(64) =~= digits);
    assert(reconstruct_radix_16(digits.take(64)) == radix16_even_scalar(digits, n) + 16
        * radix16_odd_scalar(digits, n)) by {
        lemma_reconstruct_radix16_even_odd(digits, n);
    }
    assert(reconstruct_radix_16(digits) == radix16_even_scalar(digits, n) + 16 * radix16_odd_scalar(
        digits,
        n,
    ));
    assert(radix16_odd_scalar(digits, n) * 16 + radix16_even_scalar(digits, n)
        == radix16_even_scalar(digits, n) + 16 * radix16_odd_scalar(digits, n)) by {
        lemma_mul_is_commutative(radix16_odd_scalar(digits, n), 16);
    }

    // Close: pippenger_partial(digits, 64, basepoint) is edwards_add(scaled, even_sum).
    assert(pippenger_partial(digits, 64, basepoint) == edwards_add(
        scaled.0,
        scaled.1,
        even_sum.0,
        even_sum.1,
    ));
    assert(edwards_scalar_mul_signed(
        basepoint,
        radix16_odd_scalar(digits, n) * 16 + radix16_even_scalar(digits, n),
    ) == edwards_scalar_mul_signed(basepoint, reconstruct_radix_16(digits)));
}

/// Convenience lemma: Pippenger sum equals unsigned scalar multiplication when scalar is nonnegative.
///
/// When the reconstructed scalar is known to be a natural number (nonnegative),
/// this simplifies to the unsigned scalar multiplication.
pub proof fn lemma_pippenger_sum_correct(digits: Seq<i8>, basepoint: (nat, nat), scalar_nat: nat)
    requires
        digits.len() == 64,
        reconstruct_radix_16(digits) == scalar_nat as int,
    ensures
        pippenger_partial(digits, 64, basepoint) == edwards_scalar_mul(basepoint, scalar_nat),
{
    lemma_pippenger_sum_correct_signed(digits, basepoint);
    assert(edwards_scalar_mul_signed(basepoint, reconstruct_radix_16(digits))
        == edwards_scalar_mul_signed(basepoint, scalar_nat as int));
    assert(edwards_scalar_mul_signed(basepoint, scalar_nat as int) == edwards_scalar_mul(
        basepoint,
        scalar_nat,
    )) by {
        // scalar_nat is nonnegative, so signed and unsigned scalar multiplication coincide.
        reveal(edwards_scalar_mul_signed);
    }
}

// =============================================================================
// Coordinate bounds lemmas for AffineNiels point operations
// =============================================================================
/// Helper lemma: odd_sum_up_to always returns reduced coordinates.
/// By induction: base case is identity (0,1), recursive case uses edwards_add which is always reduced.
pub proof fn lemma_odd_sum_up_to_canonical(digits: Seq<i8>, upper_i: int, B: (nat, nat))
    requires
        B.0 < p(),
        B.1 < p(),
    ensures
        odd_sum_up_to(digits, upper_i, B).0 < p(),
        odd_sum_up_to(digits, upper_i, B).1 < p(),
    decreases upper_i,
{
    reveal(odd_sum_up_to);
    p_gt_2();
    if upper_i <= 0 {
        // Base case: identity (0, 1), both < p
    } else {
        let i = upper_i - 1;
        if i % 2 == 1 {
            // Recursive case with addition
            lemma_odd_sum_up_to_canonical(digits, i, B);
            let prev = odd_sum_up_to(digits, i, B);
            let base = edwards_scalar_mul(B, pow256((i / 2) as nat));
            lemma_edwards_scalar_mul_canonical(B, pow256((i / 2) as nat));
            let term = edwards_scalar_mul_signed(base, digits[i] as int);
            lemma_edwards_scalar_mul_signed_canonical(base, digits[i] as int);
            lemma_edwards_add_canonical(prev.0, prev.1, term.0, term.1);
        } else {
            // Even index - skip, just recurse
            lemma_odd_sum_up_to_canonical(digits, i, B);
        }
    }
}

// =============================================================================
// Lemma: Table lookup correctness (select function)
// =============================================================================
/// Lemma: The result of select(x) on a valid table equals [x]*basepoint in affine coords.
///
/// The `select` function performs constant-time lookup from a precomputed table
/// of basepoint multiples. For a digit x in [-8, 8]:
/// - x > 0: `table[x-1]` decodes to `[x]*P` (positive multiple from table)
/// - x == 0: identity decodes to `[0]*P = O` (identity element)
/// - x < 0: `negate(table[-x-1])` decodes to `[-x]*P` negated = `[x]*P`
pub proof fn lemma_select_is_signed_scalar_mul(
    table: [AffineNielsPoint; 8],
    x: i8,
    result: AffineNielsPoint,
    basepoint: (nat, nat),
)
    requires
        -8 <= x <= 8,
        crate::specs::window_specs::is_valid_lookup_table_affine_coords(table, basepoint, 8),
        // select's postconditions (what we know about result):
        (x > 0 ==> result == table[(x - 1) as int]),
        (x == 0 ==> result == identity_affine_niels()),
        (x < 0 ==> result == negate_affine_niels(table[((-x) - 1) as int])),
    ensures
        affine_niels_point_as_affine_edwards(result) == edwards_scalar_mul_signed(
            basepoint,
            x as int,
        ),
{
    reveal(edwards_scalar_mul_signed);

    if x > 0 {
        // result == table[(x-1) as int]
        // From the table spec: affine_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(basepoint, j+1)
        // With j = x-1: edwards_scalar_mul(basepoint, x)
        // Since x > 0, edwards_scalar_mul_signed(basepoint, x) == edwards_scalar_mul(basepoint, x)
        let j = (x - 1) as int;
        assert(0 <= j < 8);
        assert(affine_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (j + 1) as nat,
        ));
        assert((j + 1) as nat == x as nat);
    } else if x == 0 {
        // result == identity_affine_niels()
        // edwards_scalar_mul_signed(basepoint, 0) == edwards_scalar_mul(basepoint, 0) == identity
        lemma_identity_affine_niels_is_identity();
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(edwards_scalar_mul(basepoint, 0) == math_edwards_identity());
    } else {
        // x < 0: result == negate_affine_niels(table[((-x) - 1) as int])
        // table[(-x)-1] decodes to edwards_scalar_mul(basepoint, -x)
        // negate_affine_niels gives edwards_neg of that
        // edwards_scalar_mul_signed(basepoint, x) for x < 0 is edwards_neg(edwards_scalar_mul(basepoint, -x))
        let j = ((-x) - 1) as int;
        assert(0 <= j < 8);
        assert(affine_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (j + 1) as nat,
        ));
        assert((j + 1) as nat == (-x) as nat);

        lemma_negate_affine_niels_is_edwards_neg(table[j]);
        assert(affine_niels_point_as_affine_edwards(negate_affine_niels(table[j])) == edwards_neg(
            edwards_scalar_mul(basepoint, (-x) as nat),
        ));
    }
}

// =============================================================================
// Lemma: Basepoint table select gives signed scalar multiplication
// =============================================================================
/// Lemma: For a valid basepoint table, selecting digit a[i] gives [a[i]] * (256^(i/2) * B).
///
/// This lemma combines table validity with `lemma_select_is_signed_scalar_mul` to prove
/// that the selected point corresponds to signed scalar multiplication by the digit.
/// Used in both loop 1 and loop 2 of mul_base.
#[cfg(feature = "precomputed-tables")]
pub proof fn lemma_basepoint_table_select(
    table: crate::edwards::EdwardsBasepointTable,
    a: Seq<i8>,
    i: int,
    selected: AffineNielsPoint,
    B: (nat, nat),
)
    requires
        is_valid_edwards_basepoint_table(table, B),
        B == spec_ed25519_basepoint(),
        0 <= i < 64,
        -8 <= a[i] <= 8,
        // select postconditions (from LookupTable::select):
        (a[i] > 0 ==> selected == table.0[(i / 2) as int].0[(a[i] - 1) as int]),
        (a[i] == 0 ==> selected == identity_affine_niels()),
        (a[i] < 0 ==> selected == negate_affine_niels(
            table.0[(i / 2) as int].0[((-a[i]) - 1) as int],
        )),
    ensures
        affine_niels_point_as_affine_edwards(selected) == edwards_scalar_mul_signed(
            edwards_scalar_mul(B, pow256((i / 2) as nat)),
            a[i] as int,
        ),
{
    let table_idx = i / 2;
    let table_base = edwards_scalar_mul(B, pow256(table_idx as nat));

    // From is_valid_edwards_basepoint_table, extract validity for this table index
    assert(0 <= table_idx < 32);
    assert(crate::specs::window_specs::is_valid_lookup_table_affine_coords(
        table.0[table_idx].0,
        table_base,
        8,
    )) by {
        reveal(is_valid_edwards_basepoint_table);
    }

    // Apply lemma_select_is_signed_scalar_mul
    lemma_select_is_signed_scalar_mul(table.0[table_idx].0, a[i], selected, table_base);
}

// =============================================================================
// Lemma: Valid radix-16 implies bounded digits
// =============================================================================
/// Lemma: is_valid_radix_16 implies radix_16_all_bounded
///
/// is_valid_radix_16 gives tighter bounds (-8 <= d < 8 for non-last, -8 <= d <= 8 for last)
/// but radix_16_all_bounded (-8 <= d <= 8 for all) is still implied.
pub proof fn lemma_valid_radix_16_implies_all_bounded(digits: [i8; 64])
    requires
        is_valid_radix_16(&digits),
    ensures
        radix_16_all_bounded(&digits),
{
    // Expand the definitions:
    //
    // - is_valid_radix_16(digits) = is_valid_radix_2w(digits, 4, 64)
    // - is_valid_radix_2w gives, for each i in [0, 64):
    //     -8 <= digits[i] and (digits[i] < 8) for i < 63, while (digits[63] <= 8)
    // This implies the simpler predicate radix_16_all_bounded(digits):
    //     forall i in [0, 64): -8 <= digits[i] <= 8
    // `is_valid_radix_16(digits)` is `is_valid_radix_2w(digits, 4, 64)`.
    assert(is_valid_radix_2w(&digits, 4, 64));

    // Prove the pointwise bound `-8 <= digits[i] <= 8` for all i in [0, 64).
    assert forall|i: int| 0 <= i < 64 implies radix_16_digit_bounded(#[trigger] digits[i]) by {
        // From `is_valid_radix_2w(digits, 4, 64)` we get:
        // - for i < 63: -8 <= digits[i] < 8
        // - for i = 63: -8 <= digits[i] <= 8
        //
        // because bound = pow2(w-1) = pow2(3) = 8.
        assert(pow2(3) == 8) by {
            vstd::arithmetic::power2::lemma2_to64();
        }
        if i < 63 {
            assert(-8 <= digits[i] && digits[i] < 8);
            // Strengthen `< 8` to `<= 8`.
            assert(digits[i] <= 8);
        } else {
            assert(i == 63);
            assert(-8 <= digits[i] && digits[i] <= 8);
        }
    }

    assert(radix_16_all_bounded(&digits));
}

} // verus!
