//! Helper lemmas for proving Montgomery exponentiation chains
//!
//! These are the Montgomery-arithmetic analogues of the field-level
//! `pow_chain_lemmas.rs`. In Montgomery arithmetic, each operation
//! introduces an extra factor of R^{-1}, so we track an exponent invariant:
//!
//!   (v * pow(R, e - 1)) % L == pow(self_val, e) % L
//!
//! for each intermediate variable v with logical exponent e.
#![allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::specs::primality_specs::*;
use crate::specs::scalar52_specs::*;

verus! {

/// Montgomery multiplication adds exponents.
///
/// If `a` has logical exponent `ea` and `b` has logical exponent `eb`
/// (meaning `(a * R^(ea-1)) % L == self^ea % L` etc.), and
/// `montgomery_mul(a, b)` satisfies `result * R ≡ a * b (mod L)`,
/// then `result` has logical exponent `ea + eb`.
pub proof fn lemma_montgomery_mul_exponent_add(
    self_val: nat,
    a: nat,
    b: nat,
    result: nat,
    ea: nat,
    eb: nat,
    R: nat,
    L: nat,
)
    requires
        L > 0,
        R > 0,
        ea > 0,
        eb > 0,
        // Montgomery mul postcondition: result * R ≡ a * b (mod L)
        (result * R) % L == (a * b) % L,
        // Exponent invariant for a: (a * R^(ea-1)) % L == self^ea % L
        (a * pow(R as int, (ea - 1) as nat) as nat) % L == (pow(self_val as int, ea) as nat) % L,
        // Exponent invariant for b: (b * R^(eb-1)) % L == self^eb % L
        (b * pow(R as int, (eb - 1) as nat) as nat) % L == (pow(self_val as int, eb) as nat) % L,
    ensures
// Exponent invariant for result with ea + eb

        (result * pow(R as int, (ea + eb - 1) as nat) as nat) % L == (pow(
            self_val as int,
            (ea + eb) as nat,
        ) as nat) % L,
{
    let R_int = R as int;
    let L_int = L as int;
    let s_int = self_val as int;
    let ea_1 = (ea - 1) as nat;
    let eb_1 = (eb - 1) as nat;
    let eab_1 = (ea + eb - 1) as nat;

    assert(pow(R_int, ea_1) >= 0 && pow(R_int, eb_1) >= 0 && pow(R_int, eab_1) >= 0 && pow(
        s_int,
        ea,
    ) >= 0 && pow(s_int, eb) >= 0 && pow(s_int, ea + eb) >= 0) by {
        lemma_pow_nonnegative(R_int, ea_1);
        lemma_pow_nonnegative(R_int, eb_1);
        lemma_pow_nonnegative(R_int, eab_1);
        lemma_pow_nonnegative(s_int, ea);
        lemma_pow_nonnegative(s_int, eb);
        lemma_pow_nonnegative(s_int, ea + eb);
    }

    assert(eab_1 == 1 + ea_1 + eb_1) by (nonlinear_arith)
        requires
            ea > 0,
            eb > 0,
            ea_1 == ea - 1,
            eb_1 == eb - 1,
            eab_1 == ea + eb - 1,
    ;

    assert(pow(R_int, eab_1) == R_int * (pow(R_int, ea_1) * pow(R_int, eb_1))) by {
        lemma_pow_adds(R_int, 1nat, (ea_1 + eb_1) as nat);
        lemma_pow1(R_int);
        lemma_pow_adds(R_int, ea_1, eb_1);
        assert(pow(R_int, eab_1) == pow(R_int, 1 + (ea_1 + eb_1)));
        assert(pow(R_int, 1 + (ea_1 + eb_1)) == pow(R_int, 1nat) * pow(
            R_int,
            (ea_1 + eb_1) as nat,
        ));
        assert(pow(R_int, 1nat) == R_int);
        assert(pow(R_int, (ea_1 + eb_1) as nat) == pow(R_int, ea_1) * pow(R_int, eb_1));
    }

    let R_ea1: int = pow(R_int, ea_1);
    let R_eb1: int = pow(R_int, eb_1);

    // result * R^(ea+eb-1) = (result * R) * R^(ea-1) * R^(eb-1)
    assert(result as int * pow(R_int, eab_1) == (result * R) as int * (R_ea1 * R_eb1)) by {
        lemma_mul_is_associative(result as int, R_int, R_ea1 * R_eb1);
    }

    // (result * R) ≡ (a * b) (mod L)
    // So (result * R) * (R_ea1 * R_eb1) ≡ (a * b) * (R_ea1 * R_eb1) (mod L)
    assert(((result * R) as int * (R_ea1 * R_eb1)) % L_int == ((a * b) as int * (R_ea1 * R_eb1))
        % L_int) by {
        lemma_mul_mod_noop((result * R) as int, (R_ea1 * R_eb1), L_int);
        lemma_mul_mod_noop((a * b) as int, (R_ea1 * R_eb1), L_int);
    }

    // (a * b) * (R_ea1 * R_eb1) = (a * R_ea1) * (b * R_eb1)
    assert((a * b) as int * (R_ea1 * R_eb1) == (a as int * R_ea1) * (b as int * R_eb1))
        by (nonlinear_arith)
        requires
            R_ea1 >= 0,
            R_eb1 >= 0,
    ;

    // (a * R_ea1) % L == self^ea % L and (b * R_eb1) % L == self^eb % L
    // So (a * R_ea1) * (b * R_eb1) ≡ self^ea * self^eb (mod L)
    assert(((a as int * R_ea1) * (b as int * R_eb1)) % L_int == (pow(s_int, ea) * pow(s_int, eb))
        % L_int) by {
        lemma_mul_mod_noop((a as int * R_ea1), (b as int * R_eb1), L_int);
        lemma_mul_mod_noop(pow(s_int, ea), pow(s_int, eb), L_int);
    }

    assert(pow(s_int, ea) * pow(s_int, eb) == pow(s_int, ea + eb)) by {
        lemma_pow_adds(s_int, ea, eb);
    }

    // Chain everything together
    assert(((result as int * pow(R_int, eab_1)) % L_int) == (pow(s_int, ea + eb) % L_int));
}

/// Montgomery squaring doubles the exponent.
///
/// Special case of `lemma_montgomery_mul_exponent_add` with a == b, ea == eb.
pub proof fn lemma_montgomery_square_exponent_double(
    self_val: nat,
    a: nat,
    result: nat,
    e: nat,
    R: nat,
    L: nat,
)
    requires
        L > 0,
        R > 0,
        e > 0,
        // Montgomery square postcondition: result * R ≡ a * a (mod L)
        (result * R) % L == (a * a) % L,
        // Exponent invariant for a
        (a * pow(R as int, (e - 1) as nat) as nat) % L == (pow(self_val as int, e) as nat) % L,
    ensures
        (result * pow(R as int, (2 * e - 1) as nat) as nat) % L == (pow(
            self_val as int,
            (2 * e) as nat,
        ) as nat) % L,
{
    assert(2 * e == e + e);
    lemma_montgomery_mul_exponent_add(self_val, a, a, result, e, e, R, L);
}

/// square_multiply composes the exponent as 2^n * ey + ex.
///
/// Given `square_multiply`'s postcondition:
///   (y_new * R^(2^n)) % L == (y_old^(2^n) * x) % L
/// and the exponent invariant for y_old (exp ey) and x (exp ex),
/// prove the invariant holds for y_new with exp 2^n * ey + ex.
pub proof fn lemma_square_multiply_exponent_compose(
    self_val: nat,
    y_old: nat,
    x_val: nat,
    y_new: nat,
    ey: nat,
    ex: nat,
    n: nat,
    R: nat,
    L: nat,
)
    requires
        L > 0,
        R > 0,
        ey > 0,
        ex > 0,
        // square_multiply postcondition
        (y_new * pow(R as int, pow2(n)) as nat) % L == (pow(y_old as int, pow2(n)) * x_val) % (
        L as int),
        // Exponent invariant for y_old
        (y_old * pow(R as int, (ey - 1) as nat) as nat) % L == (pow(self_val as int, ey) as nat)
            % L,
        // Exponent invariant for x
        (x_val * pow(R as int, (ex - 1) as nat) as nat) % L == (pow(self_val as int, ex) as nat)
            % L,
    ensures
        ({
            let new_exp: nat = (pow2(n) * ey + ex) as nat;
            (y_new * pow(R as int, (new_exp - 1) as nat) as nat) % L == (pow(
                self_val as int,
                new_exp,
            ) as nat) % L
        }),
{
    let R_int = R as int;
    let L_int = L as int;
    let s_int = self_val as int;
    let p2n: nat = pow2(n);

    assert(p2n >= 1) by {
        lemma_pow2_pos(n);
    }

    let new_exp: nat = (p2n * ey + ex) as nat;
    let new_exp_1: nat = (new_exp - 1) as nat;
    let ey_1: nat = (ey - 1) as nat;
    let ex_1: nat = (ex - 1) as nat;

    assert(pow(R_int, p2n) >= 0 && pow(R_int, new_exp_1) >= 0 && pow(R_int, ey_1) >= 0 && pow(
        R_int,
        ex_1,
    ) >= 0 && pow(s_int, ey) >= 0 && pow(s_int, ex) >= 0 && pow(s_int, new_exp) >= 0 && pow(
        y_old as int,
        p2n,
    ) >= 0) by {
        lemma_pow_nonnegative(R_int, p2n);
        lemma_pow_nonnegative(R_int, new_exp_1);
        lemma_pow_nonnegative(R_int, ey_1);
        lemma_pow_nonnegative(R_int, ex_1);
        lemma_pow_nonnegative(s_int, ey);
        lemma_pow_nonnegative(s_int, ex);
        lemma_pow_nonnegative(s_int, new_exp);
        lemma_pow_nonnegative(y_old as int, p2n);
    }

    assert(new_exp_1 == p2n + p2n * ey_1 + ex_1) by (nonlinear_arith)
        requires
            p2n >= 1,
            ey >= 1,
            ex >= 1,
            new_exp == p2n * ey + ex,
            new_exp_1 == new_exp - 1,
            ey_1 == ey - 1,
            ex_1 == ex - 1,
    ;

    let R_p2n: int = pow(R_int, p2n);
    let R_p2n_ey1: int = pow(R_int, (p2n * ey_1) as nat);
    let R_ex1: int = pow(R_int, ex_1);

    // R^(new_exp-1) = R^(p2n) * R^(p2n * ey_1) * R^(ex_1)
    assert(pow(R_int, new_exp_1) == R_p2n * (R_p2n_ey1 * R_ex1) && R_p2n_ey1 >= 0) by {
        lemma_pow_adds(R_int, p2n, (p2n * ey_1 + ex_1) as nat);
        lemma_pow_adds(R_int, (p2n * ey_1) as nat, ex_1);
        lemma_pow_nonnegative(R_int, (p2n * ey_1) as nat);
        lemma_pow_nonnegative(R_int, (p2n * ey_1 + ex_1) as nat);
    }

    // y_new * R^(new_exp-1) = (y_new * R^p2n) * R^(p2n*ey_1) * R^(ex_1)
    assert(y_new as int * pow(R_int, new_exp_1) == (y_new as int * R_p2n) * (R_p2n_ey1 * R_ex1))
        by {
        lemma_mul_is_associative(y_new as int, R_p2n, R_p2n_ey1 * R_ex1);
    }

    // From square_multiply postcondition: y_new * R^p2n ≡ y_old^p2n * x (mod L)
    assert(((y_new as int * R_p2n) * (R_p2n_ey1 * R_ex1)) % L_int == ((pow(y_old as int, p2n)
        * x_val as int) * (R_p2n_ey1 * R_ex1)) % L_int) by {
        lemma_mul_mod_noop((y_new as int * R_p2n), (R_p2n_ey1 * R_ex1), L_int);
        lemma_mul_mod_noop((pow(y_old as int, p2n) * x_val as int), (R_p2n_ey1 * R_ex1), L_int);
    }

    // (y_old^p2n * x) * (R^(p2n*ey_1) * R^(ex_1))
    // = (y_old^p2n * R^(p2n*ey_1)) * (x * R^(ex_1))
    assert((pow(y_old as int, p2n) * x_val as int) * (R_p2n_ey1 * R_ex1) == (pow(y_old as int, p2n)
        * R_p2n_ey1) * (x_val as int * R_ex1)) by (nonlinear_arith)
        requires
            R_p2n_ey1 >= 0,
            R_ex1 >= 0,
            pow(y_old as int, p2n) >= 0,
    ;

    let R_ey1: int = pow(R_int, ey_1);

    // R^(p2n*ey_1) = (R^ey_1)^p2n by pow_multiplies
    assert(R_p2n_ey1 == pow(R_ey1, p2n) && R_ey1 >= 0) by {
        lemma_pow_multiplies(R_int, ey_1, p2n);
        lemma_pow_nonnegative(R_int, ey_1);
    }

    // y_old^p2n * (R^ey_1)^p2n = (y_old * R^ey_1)^p2n
    assert(pow(y_old as int, p2n) * pow(R_ey1, p2n) == pow(y_old as int * R_ey1, p2n)) by {
        lemma_pow_distributes(y_old as int, R_ey1, p2n);
    }

    // (self^ey)^p2n = self^(ey * p2n) = self^(p2n * ey)
    assert(pow(s_int, ey * p2n) == pow(s_int, p2n * ey) && pow(s_int, p2n * ey) >= 0) by {
        lemma_pow_multiplies(s_int, ey, p2n);
        lemma_pow_nonnegative(s_int, p2n * ey);
    }

    // self^(p2n*ey) * self^ex = self^(p2n*ey + ex) = self^new_exp
    assert(pow(s_int, (p2n * ey) as nat) * pow(s_int, ex) == pow(s_int, new_exp)) by {
        lemma_pow_adds(s_int, (p2n * ey) as nat, ex);
    }
    assert(p2n * ey + ex == new_exp);

    // Now chain everything explicitly through intermediate assertions.

    // Step A: rewrite y_new * R^(new_exp-1)
    let lhs = y_new as int * pow(R_int, new_exp_1);
    let mid1 = (y_new as int * R_p2n) * (R_p2n_ey1 * R_ex1);
    assert(lhs == mid1);

    // Step B: apply square_multiply postcondition
    let y_old_p2n_x = pow(y_old as int, p2n) * x_val as int;
    let mid2 = y_old_p2n_x * (R_p2n_ey1 * R_ex1);
    assert(lhs % L_int == mid2 % L_int);

    // Step C: regroup to (y_old^p2n * R^(p2n*ey_1)) * (x * R^(ex_1))
    let part1 = pow(y_old as int, p2n) * R_p2n_ey1;
    let part2 = x_val as int * R_ex1;
    assert(mid2 == part1 * part2);

    // Step D: y_old^p2n * R^(p2n*ey_1) = (y_old * R^ey_1)^p2n
    let y_R_ey1 = y_old as int * R_ey1;
    assert(part1 == pow(y_R_ey1, p2n));

    // Step E: (y_old * R^ey_1)^p2n ≡ (self^ey)^p2n (mod L)
    let s_ey = pow(s_int, ey);
    assert(pow(y_R_ey1, p2n) % L_int == pow(s_ey, p2n) % L_int) by {
        lemma_pow_mod_congruent(y_old as int * R_ey1, pow(s_int, ey), p2n, L_int);
        lemma_pow_nonnegative(y_R_ey1, p2n);
        lemma_pow_nonnegative(s_ey, p2n);
    }

    // Step F: (self^ey)^p2n = self^(ey * p2n) = self^(p2n * ey)
    assert(pow(s_ey, p2n) == pow(s_int, ey * p2n)) by {
        lemma_pow_multiplies(s_int, ey, p2n);
    }
    assert(ey * p2n == p2n * ey) by (nonlinear_arith);

    // Step G: combine part1 ≡ self^(p2n*ey) (mod L) and part2 ≡ self^ex (mod L)
    assert(part1 % L_int == pow(s_int, p2n * ey) % L_int);
    assert(part2 % L_int == pow(s_int, ex) % L_int);

    assert((part1 * part2) % L_int == (pow(s_int, p2n * ey) * pow(s_int, ex)) % L_int) by {
        lemma_mul_mod_noop(part1, part2, L_int);
        lemma_mul_mod_noop(pow(s_int, p2n * ey), pow(s_int, ex), L_int);
    }

    // Step H: self^(p2n*ey) * self^ex == self^new_exp
    assert(pow(s_int, p2n * ey) * pow(s_int, ex) == pow(s_int, new_exp));

    // Final chain: lhs % L == mid2 % L == (part1 * part2) % L == self^new_exp % L
    assert(lhs % L_int == pow(s_int, new_exp) % L_int);
}

/// Final algebraic step: given the exponent invariant at exp = L-2,
/// plus Fermat's Little Theorem, derive y * self ≡ R^2 (mod L).
///
/// The proof:
///   (y * R^(L-3)) % L == self^(L-2) % L       [exponent invariant]
///   self^(L-1) % L == 1                        [Fermat on self]
///   R^(L-1) % L == 1                           [Fermat on R]
///
///   y * self * R^(L-3) ≡ self^(L-2) * self = self^(L-1) ≡ 1  (mod L)
///   R^(L-3) * R^2 = R^(L-1) ≡ 1                              (mod L)
///   So y * self ≡ R^2  (mod L)
pub proof fn lemma_exponent_chain_implies_montgomery_inverse(
    self_val: nat,
    y_val: nat,
    R: nat,
    L: nat,
)
    requires
        L > 3,
        R > 0,
        self_val > 0,
        self_val < L,
        is_prime(L),
        R % L != 0,
        // Exponent invariant at exp = L - 2
        (y_val * pow(R as int, (L - 3) as nat) as nat) % L == (pow(
            self_val as int,
            (L - 2) as nat,
        ) as nat) % L,
    ensures
        (y_val * self_val) % L == (R * R) % L,
{
    let L_int = L as int;
    let R_int = R as int;
    let s_int = self_val as int;

    // Establish Fermat prerequisites
    assert(self_val % L != 0) by {
        lemma_small_mod(self_val, L);
    }

    assert((pow(s_int, (L - 1) as nat) as nat) % L == 1) by {
        lemma_fermat_little_theorem(self_val, L);
    }

    assert((pow(R_int, (L - 1) as nat) as nat) % L == 1) by {
        lemma_fermat_little_theorem(R, L);
    }

    // self^(L-2) * self = self^(L-1)
    assert(pow(s_int, (L - 2) as nat) * s_int == pow(s_int, (L - 1) as nat) && pow(
        s_int,
        (L - 2) as nat,
    ) >= 0 && pow(s_int, (L - 1) as nat) >= 0) by {
        lemma_pow_adds(s_int, (L - 2) as nat, 1nat);
        lemma_pow1(s_int);
        lemma_pow_nonnegative(s_int, (L - 2) as nat);
        lemma_pow_nonnegative(s_int, (L - 1) as nat);
    }

    let Lm3: nat = (L - 3) as nat;
    let Lm1: nat = (L - 1) as nat;
    assert(Lm3 + 2 == Lm1);

    // R^(L-3) * R^2 = R^(L-1)
    assert(pow(R_int, Lm3) * pow(R_int, 2nat) == pow(R_int, Lm1) && pow(R_int, Lm3) >= 0 && pow(
        R_int,
        Lm1,
    ) >= 0 && pow(R_int, 2nat) >= 0) by {
        lemma_pow_adds(R_int, Lm3, 2nat);
        lemma_pow_nonnegative(R_int, (L - 3) as nat);
        lemma_pow_nonnegative(R_int, (L - 1) as nat);
        lemma_pow_nonnegative(R_int, 2nat);
    }

    let R_L3: int = pow(R_int, (L - 3) as nat);
    let R_2: int = pow(R_int, 2nat);
    let s_L2: int = pow(s_int, (L - 2) as nat);

    // R^2 = R * R
    assert(R_2 == R_int * R_int) by {
        lemma_pow1(R_int);
        lemma_pow_adds(R_int, 1nat, 1nat);
    }

    // From the exponent invariant, multiplying both sides by self_val:
    // (y * R^(L-3) * self) % L == (self^(L-2) * self) % L == self^(L-1) % L == 1
    assert(((y_val as int * R_L3) * s_int) % L_int == 1) by {
        // y * R^(L-3) ≡ self^(L-2) (mod L)
        // So (y * R^(L-3)) * self ≡ self^(L-2) * self (mod L)
        lemma_mul_mod_noop((y_val as int * R_L3), s_int, L_int);
        lemma_mul_mod_noop(s_L2, s_int, L_int);
        // self^(L-2) * self == self^(L-1)
        assert(s_L2 * s_int == pow(s_int, (L - 1) as nat));
    }

    // (y * self * R^(L-3)) % L == 1
    assert((y_val as int * s_int * R_L3) % L_int == 1) by {
        lemma_mul_is_associative(y_val as int, R_L3, s_int);
        lemma_mul_is_commutative(R_L3, s_int);
        lemma_mul_is_associative(y_val as int, s_int, R_L3);
    }

    // (R^(L-3) * R^2) % L == 1  (from Fermat on R)
    assert((R_L3 * R_2) % L_int == 1) by {
        assert(R_L3 * R_2 == pow(R_int, (L - 1) as nat));
    }

    // Now: y*self * R^(L-3) ≡ 1 and R^(L-3) * R^2 ≡ 1 (mod L)
    // Multiply both: (y*self * R^(L-3)) * R^2 ≡ R^2 (mod L)
    // And: y*self * (R^(L-3) * R^2) ≡ y*self (mod L)
    // So: y*self ≡ R^2 (mod L)

    // (y*self) * (R^(L-3) * R^2) ≡ (y*self) * 1 ≡ y*self (mod L)
    // Also (y*self) * (R^(L-3) * R^2) = (y*self*R^(L-3)) * R^2 ≡ 1 * R^2 ≡ R^2 (mod L)
    let ys = y_val as int * s_int;
    let ys_RL3 = ys * R_L3;

    assert(ys * (R_L3 * R_2) == ys_RL3 * R_2) by {
        lemma_mul_is_associative(ys, R_L3, R_2);
    }
    assert(ys_RL3 % L_int == 1);

    // (ys_RL3 * R_2) % L == R_2 % L
    assert((ys * (R_L3 * R_2)) % L_int == R_2 % L_int) by {
        lemma_mul_mod_noop(ys_RL3, R_2, L_int);
        assert(1 * (R_2 % L_int) == R_2 % L_int) by {
            lemma_mul_basics(R_2 % L_int);
        }
        vstd::arithmetic::div_mod::lemma_mod_twice(R_2, L_int);
    }

    let RL3_R2 = R_L3 * R_2;
    assert(RL3_R2 % L_int == 1) by {
        assert(R_L3 * R_2 == pow(R_int, Lm1));
    }

    // (ys * RL3_R2) % L == ys % L
    assert((ys * (R_L3 * R_2)) % L_int == ys % L_int) by {
        lemma_mul_mod_noop(ys, RL3_R2, L_int);
        assert((ys % L_int) * 1 == ys % L_int) by {
            lemma_mul_basics(ys % L_int);
        }
        vstd::arithmetic::div_mod::lemma_mod_twice(ys, L_int);
    }

    // Both equal (ys * (R_L3 * R_2)) % L, so R_2 % L == ys % L
    assert(ys % L_int == R_2 % L_int);

    // Convert to nat-level assertion
    assert((y_val * self_val) % L == (R * R) % L);
}

/// Spec function computing the exponent produced by the montgomery_invert addition chain.
///
/// Each step corresponds to a `square_multiply(&mut y, n, &x)` call where
/// `2^n` is written as a literal multiplier. This avoids the opaque `pow2`
/// so the result can be evaluated by `compute_only`.
pub open spec fn montgomery_invert_chain_exponent() -> nat {
    let e: nat = 16nat;
    let e: nat = 85070591730234615865843651857942052864nat * e + 5;  // 2^126, _101
    let e: nat = 16nat * e + 3;  // 2^4,  _11
    let e: nat = 32nat * e + 15;  // 2^5,  _1111
    let e: nat = 32nat * e + 15;  // 2^5,  _1111
    let e: nat = 16nat * e + 9;  // 2^4,  _1001
    let e: nat = 4nat * e + 3;  // 2^2,  _11
    let e: nat = 32nat * e + 15;  // 2^5,  _1111
    let e: nat = 16nat * e + 5;  // 2^4,  _101
    let e: nat = 64nat * e + 5;  // 2^6,  _101
    let e: nat = 8nat * e + 7;  // 2^3,  _111
    let e: nat = 32nat * e + 15;  // 2^5,  _1111
    let e: nat = 32nat * e + 7;  // 2^5,  _111
    let e: nat = 16nat * e + 3;  // 2^4,  _11
    let e: nat = 32nat * e + 11;  // 2^5,  _1011
    let e: nat = 64nat * e + 11;  // 2^6,  _1011
    let e: nat = 1024nat * e + 9;  // 2^10, _1001
    let e: nat = 16nat * e + 3;  // 2^4,  _11
    let e: nat = 32nat * e + 3;  // 2^5,  _11
    let e: nat = 32nat * e + 3;  // 2^5,  _11
    let e: nat = 32nat * e + 9;  // 2^5,  _1001
    let e: nat = 16nat * e + 7;  // 2^4,  _111
    let e: nat = 64nat * e + 15;  // 2^6,  _1111
    let e: nat = 32nat * e + 11;  // 2^5,  _1011
    let e: nat = 8nat * e + 5;  // 2^3,  _101
    let e: nat = 64nat * e + 15;  // 2^6,  _1111
    let e: nat = 8nat * e + 5;  // 2^3,  _101
    let e: nat = 8nat * e + 3;  // 2^3,  _11
    e
}

/// Proves that the addition chain exponent equals group_order() - 2.
pub proof fn lemma_chain_exp_is_l_minus_2()
    ensures
        montgomery_invert_chain_exponent() == group_order() - 2,
{
    assert(montgomery_invert_chain_exponent()
        == 7237005577332262213973186563042994240857116359379907606001950938285454250987nat)
        by (compute_only);
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_adds(64, 64);
    lemma_pow2_adds(128, 64);
    lemma_pow2_adds(192, 60);
}

/// Establishes concrete values for every pow2(n) used in the addition chain,
/// bridging between symbolic `pow2` and the literal multipliers in the spec function.
pub proof fn lemma_pow2_chain_multipliers()
    ensures
        pow2(2) == 4,
        pow2(3) == 8,
        pow2(4) == 16,
        pow2(5) == 32,
        pow2(6) == 64,
        pow2(10) == 1024,
        pow2(126) == 85070591730234615865843651857942052864nat,
{
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_adds(64, 62);
}

} // verus!
