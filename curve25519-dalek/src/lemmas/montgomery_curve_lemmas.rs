//! Lemmas and axioms for Montgomery curve operations.
//!
//! Provides axioms and lemmas for verifying the Montgomery ladder.
//!
//! ## Reference
//!
//! The xDBL and xADD formulas are from:
//! > Craig Costello & Benjamin Smith (2017).
//! > *Montgomery curves and their arithmetic*.
//! > <https://eprint.iacr.org/2017/212.pdf>
//!
//! ## Contents
//!
//! - **Group Axioms**: associativity, identity, inverse for Montgomery curve addition
//! - **xDBL Axiom** (Equation 10): doubling `[2]P` in projective coordinates `(U:W)`
//! - **xADD Axiom** (Equation 9): differential addition `P + Q` given `P - Q`
//! - **Scalar Multiplication Lemmas**: distribution `[m+n]P = [m]P + [n]P`, doubling `[2n]P = [n]P + [n]P`
//! - **Projective Representation Lemmas**: connecting projective `(U:W)` to affine `u = U/W`
#![allow(unused)]
use crate::constants::{APLUS2_OVER_FOUR, MONTGOMERY_A};
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::montgomery_specs::*;
use crate::specs::primality_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

// =============================================================================
// GROUP AXIOMS: properties of the Montgomery curve group structure.
// =============================================================================
/// Axiom: Montgomery addition is associative
/// (P + Q) + R = P + (Q + R)
pub proof fn axiom_montgomery_add_associative(
    P: MontgomeryAffine,
    Q: MontgomeryAffine,
    R: MontgomeryAffine,
)
    ensures
        montgomery_add(montgomery_add(P, Q), R) == montgomery_add(P, montgomery_add(Q, R)),
{
    admit();
}

/// Axiom: Left identity element
/// ∞ + P = P
pub proof fn axiom_montgomery_add_identity_left(P: MontgomeryAffine)
    ensures
        montgomery_add(MontgomeryAffine::Infinity, P) == P,
{
    admit();
}

/// Axiom: Infinity is the identity element (right identity)
/// P + ∞ = P
pub proof fn axiom_montgomery_add_identity(P: MontgomeryAffine)
    ensures
        montgomery_add(P, MontgomeryAffine::Infinity) == P,
{
    admit();
}

/// Axiom: every point has an inverse
/// P + (-P) = ∞
pub proof fn axiom_montgomery_add_inverse(P: MontgomeryAffine)
    ensures
        montgomery_add(P, montgomery_neg(P)) == MontgomeryAffine::Infinity,
{
    admit();
}

// =============================================================================
// X-ONLY PROJECTIVE FORMULAS AND AXIOMS
// Costello–Smith 2017: https://eprint.iacr.org/2017/212.pdf (Equations 9–10)
// =============================================================================
//
// The Montgomery ladder operates on x-coordinates only, using projective (U:W)
// representation where the affine x-coordinate is u = U/W.
//
// Montgomery curve: By² = x(x² + Ax + 1)
// - Affine point: (u, v) where u is x-coord, v is y-coord; plus point at infinity ∞
// - Projective x-only: (U:W) represents affine u = U/W; infinity when W = 0
//
// Notation: uppercase U, W = projective coords; lowercase u = affine coord (u = U/W).
//
// Each formula is modeled as a `spec fn` (the algebraic computation) paired with
// an `axiom` (asserting the computation equals the mathematical operation).
//
// -----------------------------------------------------------------------------
// xDBL (Equation 10): Doubling P → [2]P
// -----------------------------------------------------------------------------
//
// Input:  (U : W) representing point P
// Output: (U' : W') representing [2]P
//
// Precondition: (U:W) validly represents P (for ∞, requires W = 0 and U ≠ 0).
//
// Formulas:
//   U' = (U + W)² · (U - W)²
//   W' = ((U + W)² - (U - W)²) · ((U - W)² + ((A+2)/4) · ((U + W)² - (U - W)²))
//
pub(crate) open spec fn spec_xdbl_projective(U: nat, W: nat) -> (nat, nat) {
    let t0 = math_field_add(U, W);  // t0 = U + W
    let t1 = math_field_sub(U, W);  // t1 = U - W
    let t4 = math_field_square(t0);  // t4 = (U + W)²
    let t5 = math_field_square(t1);  // t5 = (U - W)²
    let t6 = math_field_sub(t4, t5);  // t6 = (U + W)² - (U - W)² = 4·U·W
    let a24 = spec_field_element(&APLUS2_OVER_FOUR);  // a24 = (A+2)/4
    let t13 = math_field_mul(a24, t6);  // t13 = ((A+2)/4) · 4·U·W
    let t15 = math_field_add(t13, t5);  // t15 = (U - W)² + ((A+2)/4) · 4·U·W
    let U2 = math_field_mul(t4, t5);  // U' = (U + W)² · (U - W)²
    let W2 = math_field_mul(t6, t15);  // W' = 4·U·W · ((U - W)² + ((A+2)/4) · 4·U·W)
    (U2, W2)
}

/// **xDBL Axiom**: `spec_xdbl_projective` correctly computes [2]P.
///
/// If `(U:W)` represents affine point `P`, then `xDBL(U,W)` represents `[2]P`.
pub(crate) proof fn axiom_xdbl_projective_correct(P: MontgomeryAffine, U: nat, W: nat)
    requires
// (U:W) represents P: for finite points u = U/W; for ∞ we have W = 0, U ≠ 0

        projective_represents_montgomery_or_infinity_nat(U, W, P),
    ensures
        ({
            let (U2, W2) = spec_xdbl_projective(U, W);
            projective_represents_montgomery_or_infinity_nat(U2, W2, montgomery_add(P, P))
        }),
{
    admit();
}

/// **Lemma**: xDBL gives W'=0 when U=0 or W=0.
///
/// When U=0 or W=0, we have (U+W)² = (U-W)², so t6 = 0 and W' = t6 * ... = 0.
pub(crate) proof fn lemma_xdbl_degenerate_gives_w_zero(U: nat, W: nat)
    requires
        U == 0 || W == 0,
    ensures
        ({
            let (_, W2) = spec_xdbl_projective(U, W);
            W2 == 0
        }),
{
    let t0 = math_field_add(U, W);
    let t1 = math_field_sub(U, W);
    let t4 = math_field_square(t0);
    let t5 = math_field_square(t1);
    let t6 = math_field_sub(t4, t5);

    p_gt_2();

    // Show t4 == t5
    if U == 0 {
        // t0 = (0 + W) % p = W % p
        assert(t0 == W % p());
        // t1 = math_field_sub(0, W) = (((0 % p) + p) - (W % p)) % p = (p - (W % p)) % p = math_field_neg(W)
        assert(t1 == math_field_neg(W)) by {
            lemma_small_mod(0, p());
            assert(0nat % p() == 0);
        }
        // (-W)² = (W % p)²
        assert(t5 == math_field_square(W % p())) by {
            lemma_neg_square_eq(W);
        }
        // t4 = (W % p)²
        assert(t4 == math_field_square(W % p())) by {
            lemma_square_mod_noop(W);
        }
        assert(t4 == t5);
    } else {
        // W == 0 case: t0 = U % p, t1 = U % p
        assert(W == 0);
        assert(t0 == U % p());
        // math_field_sub(U, 0) = (((U % p) + p) - 0) % p = ((U % p) + p) % p = U % p
        assert(t1 == U % p()) by {
            lemma_small_mod(0nat, p());
            // t1 = ((U % p) + p) % p
            // lemma_mod_add_multiples_vanish: (x + p) % p == x % p
            lemma_mod_add_multiples_vanish((U % p()) as int, p() as int);
            // (U % p) % p == U % p
            lemma_mod_twice(U as int, p() as int);
        }
        assert(t0 == t1);
        assert(t4 == t5);
    }

    assert(t6 == 0) by {
        lemma_field_sub_self(t4);
    }

    // W2 = t6 * t15 = 0 * anything = 0
    assert(spec_xdbl_projective(U, W).1 == 0) by {
        let t15 = math_field_add(math_field_mul(spec_field_element(&APLUS2_OVER_FOUR), t6), t5);
        lemma_field_mul_zero_left(0, t15);
    }
}

// -----------------------------------------------------------------------------
// xADD (Equation 9): Differential addition P + Q given P - Q
// -----------------------------------------------------------------------------
//
// Input:  (U_P : W_P) representing P
//         (U_Q : W_Q) representing Q
//         u(P-Q)      affine x-coordinate of P - Q
// Output: (U' : W') representing P + Q
//
// Preconditions: P ≠ Q and u(P-Q) ≠ 0.
//
// Formulas (with P - Q in affine form, i.e., W(P-Q) = 1):
//   U' = [(U_P + W_P)(U_Q - W_Q) + (U_P - W_P)(U_Q + W_Q)]²
//   W' = u(P-Q) · [(U_P + W_P)(U_Q - W_Q) - (U_P - W_P)(U_Q + W_Q)]²
//
pub(crate) open spec fn spec_xadd_projective(
    U_P: nat,
    W_P: nat,
    U_Q: nat,
    W_Q: nat,
    affine_PmQ: nat,  // u(P-Q) in affine coordinates
) -> (nat, nat) {
    let t0 = math_field_add(U_P, W_P);  // t0 = U_P + W_P
    let t1 = math_field_sub(U_P, W_P);  // t1 = U_P - W_P
    let t2 = math_field_add(U_Q, W_Q);  // t2 = U_Q + W_Q
    let t3 = math_field_sub(U_Q, W_Q);  // t3 = U_Q - W_Q
    let t7 = math_field_mul(t0, t3);  // t7 = (U_P + W_P)(U_Q - W_Q)
    let t8 = math_field_mul(t1, t2);  // t8 = (U_P - W_P)(U_Q + W_Q)
    let t9 = math_field_add(t7, t8);  // t7 + t8
    let t10 = math_field_sub(t7, t8);  // t7 - t8
    let U_PpQ = math_field_square(t9);  // U' = (t7 + t8)²
    let W_PpQ = math_field_mul(affine_PmQ, math_field_square(t10));  // W' = u(P-Q) · (t7 - t8)²
    (U_PpQ, W_PpQ)
}

/// **xADD Axiom**: `spec_xadd_projective` correctly computes P + Q.
///
/// Requires P ≠ Q and u(P - Q) ≠ 0.
pub(crate) proof fn axiom_xadd_projective_correct(
    P: MontgomeryAffine,
    Q: MontgomeryAffine,
    U_P: nat,
    W_P: nat,
    U_Q: nat,
    W_Q: nat,
    affine_PmQ: nat,
)
    requires
// (U_P:W_P) represents P; (U_Q:W_Q) represents Q

        projective_represents_montgomery_or_infinity_nat(U_P, W_P, P),
        projective_represents_montgomery_or_infinity_nat(U_Q, W_Q, Q),
        P != Q,
        affine_PmQ != 0,
        // u-coordinate is symmetric: u(P-Q) = u(Q-P) since u is invariant under negation
        affine_PmQ == spec_u_coordinate(montgomery_sub(P, Q)) || affine_PmQ == spec_u_coordinate(
            montgomery_sub(Q, P),
        ),
    ensures
        ({
            let (U_PpQ, W_PpQ) = spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ);
            projective_represents_montgomery_or_infinity_nat(U_PpQ, W_PpQ, montgomery_add(P, Q))
        }),
{
    admit();
}

/// Combined xDBLADD step for the Montgomery ladder.
///
/// Returns `(U_dbl, W_dbl, U_add, W_add)` where:
/// - `(U_dbl:W_dbl)` is `xDBL(U_P, W_P)` — the doubled point `[2]P`
/// - `(U_add:W_add)` is `xADD(U_P, W_P, U_Q, W_Q, affine_PmQ)` — the sum `P + Q`
pub(crate) open spec fn spec_xdbladd_projective(
    U_P: nat,
    W_P: nat,
    U_Q: nat,
    W_Q: nat,
    affine_PmQ: nat,
) -> (nat, nat, nat, nat) {
    let (U2, W2) = spec_xdbl_projective(U_P, W_P);
    let (U3, W3) = spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ);
    (U2, W2, U3, W3)
}

// =============================================================================
// SCALAR MULTIPLICATION LEMMAS
// =============================================================================
/// Lemma: If an affine point has reduced u-coordinate (< p), then any projective representation
/// of its u-coordinate yields the same value via `spec_projective_u_coordinate`.
pub proof fn lemma_projective_represents_implies_u_coordinate(
    P_proj: crate::montgomery::ProjectivePoint,
    P_aff: MontgomeryAffine,
)
    requires
        projective_represents_montgomery_or_infinity(P_proj, P_aff),
    ensures
        spec_projective_u_coordinate(P_proj) == (spec_u_coordinate(P_aff) % p()),
{
    match P_aff {
        MontgomeryAffine::Infinity => {
            // Representation gives W == 0, and both u-coordinate conventions map ∞ to 0.
            assert(spec_field_element(&P_proj.W) == 0);
            assert(spec_projective_u_coordinate(P_proj) == 0);
            assert(spec_u_coordinate(P_aff) == 0);
            assert(spec_u_coordinate(P_aff) % p() == 0) by {
                p_gt_2();
                lemma_small_mod(0, p());
            }
        },
        MontgomeryAffine::Finite { u, v: _ } => {
            let U = spec_field_element(&P_proj.U);
            let W = spec_field_element(&P_proj.W);
            assert(W != 0);
            assert(U == math_field_mul(u, W));
            assert(W % p() != 0) by {
                let W_raw = spec_field_element_as_nat(&P_proj.W);
                assert(W == W_raw % p());
                assert(W_raw % p() < p()) by {
                    p_gt_2();
                    lemma_mod_division_less_than_divisor(W_raw as int, p() as int);
                }
                assert(W % p() == W) by {
                    lemma_small_mod(W, p());
                }
            }

            // spec_projective_u_coordinate = U / W = (u*W) / W = u
            assert(spec_projective_u_coordinate(P_proj) == math_field_mul(U, math_field_inv(W)));
            assert(spec_projective_u_coordinate(P_proj) == math_field_mul(
                math_field_mul(u, W),
                math_field_inv(W),
            ));

            assert(spec_projective_u_coordinate(P_proj) == math_field_mul(
                u,
                math_field_mul(W, math_field_inv(W)),
            )) by {
                lemma_field_mul_assoc(u, W, math_field_inv(W));
            }

            assert(math_field_mul(W, math_field_inv(W)) == 1) by {
                lemma_inv_mul_cancel(W);
                lemma_field_mul_comm(math_field_inv(W), W);
            }

            assert(math_field_mul(u, 1) == u % p()) by {
                lemma_field_mul_one_right(u);
            }
            assert(spec_projective_u_coordinate(P_proj) == u % p());
        },
    }
}

// -----------------------------------------------------------------------------
// Basic scalar multiplication lemmas
// -----------------------------------------------------------------------------
/// Lemma: scalar multiplication by 1 gives P
pub proof fn lemma_montgomery_scalar_mul_one(P: MontgomeryAffine)
    ensures
        montgomery_scalar_mul(P, 1) == P,
{
    // [1]P = P + [0]P = P + Infinity = P
    assert(montgomery_scalar_mul(P, 0) == MontgomeryAffine::Infinity);
    assert(montgomery_scalar_mul(P, 1) == montgomery_add(P, montgomery_scalar_mul(P, 0)));
    assert(montgomery_add(P, MontgomeryAffine::Infinity) == P);
}

/// Lemma: unfolding scalar multiplication by n+1
///
/// [n+1]P = P + [n]P (by definition)
///
/// Note: Kept as explicit lemma; inlining causes rlimit issues in the ladder loop.
pub proof fn lemma_montgomery_scalar_mul_succ(P: MontgomeryAffine, n: nat)
    ensures
        montgomery_scalar_mul(P, n + 1) == montgomery_add(P, montgomery_scalar_mul(P, n)),
{
    // Follows directly from the recursive definition
}

/// Lemma: scalar multiplication distributes over addition of scalars
/// [m + n]P = [m]P + [n]P
///
/// This is a fundamental property that follows from associativity and identity.
/// Proof by induction on m.
///
/// Used by: `differential_add_and_double` proof (to connect [k]P + [k+1]P = [2k+1]P)
pub proof fn lemma_montgomery_scalar_mul_add(P: MontgomeryAffine, m: nat, n: nat)
    ensures
        montgomery_scalar_mul(P, m + n) == montgomery_add(
            montgomery_scalar_mul(P, m),
            montgomery_scalar_mul(P, n),
        ),
    decreases m,
{
    if m == 0 {
        // Base case: [0 + n]P = [n]P = ∞ + [n]P = [0]P + [n]P
        assert(montgomery_scalar_mul(P, 0) == MontgomeryAffine::Infinity);
        axiom_montgomery_add_identity_left(montgomery_scalar_mul(P, n));
    } else {
        let m_minus_1 = (m - 1) as nat;

        lemma_montgomery_scalar_mul_add(P, m_minus_1, n);

        // [m+n]P = P + [m+n-1]P = P + [m-1+n]P
        assert(m + n >= 1);
        assert(m + n - 1 == m_minus_1 + n) by {
            assert(m >= 1);
            assert(m_minus_1 == m - 1);
        }
        assert(montgomery_scalar_mul(P, m + n) == montgomery_add(
            P,
            montgomery_scalar_mul(P, m_minus_1 + n),
        ));

        // Expand IH on [m-1+n]P.
        assert(montgomery_scalar_mul(P, m_minus_1 + n) == montgomery_add(
            montgomery_scalar_mul(P, m_minus_1),
            montgomery_scalar_mul(P, n),
        ));

        axiom_montgomery_add_associative(
            P,
            montgomery_scalar_mul(P, m_minus_1),
            montgomery_scalar_mul(P, n),
        );
        assert(montgomery_add(
            P,
            montgomery_add(montgomery_scalar_mul(P, m_minus_1), montgomery_scalar_mul(P, n)),
        ) == montgomery_add(
            montgomery_add(P, montgomery_scalar_mul(P, m_minus_1)),
            montgomery_scalar_mul(P, n),
        ));

        // By definition: [m]P = P + [m-1]P.
        assert(montgomery_scalar_mul(P, m) == montgomery_add(
            P,
            montgomery_scalar_mul(P, m_minus_1),
        ));

        assert(montgomery_scalar_mul(P, m + n) == montgomery_add(
            montgomery_scalar_mul(P, m),
            montgomery_scalar_mul(P, n),
        ));
    }
}

/// Lemma: [2n]P = [n]P + [n]P (doubling a scalar multiple)
///
/// Used by: `differential_add_and_double` proof (to show xDBL output is [2k]B)
pub proof fn lemma_montgomery_scalar_mul_double(P: MontgomeryAffine, n: nat)
    ensures
        montgomery_scalar_mul(P, 2 * n) == montgomery_add(
            montgomery_scalar_mul(P, n),
            montgomery_scalar_mul(P, n),
        ),
{
    // [2n]P = [n + n]P = [n]P + [n]P (by lemma_montgomery_scalar_mul_add)
    lemma_montgomery_scalar_mul_add(P, n, n);
}

// =============================================================================
// DEGENERATE BASEPOINT (u=0) LEMMAS
// =============================================================================
//
// These lemmas handle the edge case where the basepoint u-coordinate is 0.
// The point (0,0) is the unique 2-torsion point on Curve25519's Montgomery form:
// it satisfies (0,0) + (0,0) = ∞.
//
// For the Montgomery ladder, if u(P-Q) = 0, all scalar multiples have u = 0.
// This is used in `mul_bits_be` to handle this degenerate case.
//
// Used by: `lemma_u_coordinate_scalar_mul_canonical_lift_zero` which is called
// from `mul_bits_be` for the u=0 edge case.
/// Lemma: the unique square root of 0 is 0.
pub proof fn lemma_math_sqrt_zero()
    ensures
        math_sqrt(0) == 0,
{
    // Witness: 0 is a square root of 0 mod p
    assert(exists|y: nat| y < p() && #[trigger] ((y * y) % p()) == (0nat % p())) by {
        let y: nat = 0;
        p_gt_2();
        assert(y < p() && (y * y) % p() == 0nat % p());
    };

    reveal(math_sqrt);
    let y = math_sqrt(0);
    // From math_sqrt definition: y < p and y^2 ≡ 0 (mod p)
    assert(y < p() && (y * y) % p() == 0);

    // If y^2 ≡ 0 (mod p) and p is prime, then y ≡ 0 (mod p).
    // Since y < p, we have y = 0.
    assert(y == 0) by {
        axiom_p_is_prime();
        lemma_euclid_prime(y, y, p());
        lemma_small_mod(y, p());
    }
}

/// Lemma: canonical_sqrt(0) = 0.
pub proof fn lemma_canonical_sqrt_zero()
    ensures
        canonical_sqrt(0) == 0,
{
    lemma_math_sqrt_zero();
    let s1 = math_sqrt(0);
    assert(s1 == 0);

    // math_field_neg(0) == 0
    assert(math_field_neg(0) == 0) by {
        p_gt_2();
        assert(math_field_neg(0) == (p() - (0nat % p())) as nat % p());
        lemma_mod_self_0(p() as int);
    }

    // s1 is even (0 % 2 == 0), so canonical_sqrt returns s1.
    assert(canonical_sqrt(0) == s1);
}

/// Lemma: canonical_montgomery_lift(0) is the (0,0) 2-torsion point.
pub proof fn lemma_canonical_montgomery_lift_zero()
    ensures
        canonical_montgomery_lift(0) == (MontgomeryAffine::Finite { u: 0, v: 0 }),
{
    lemma_canonical_sqrt_zero();
    assert(montgomery_rhs(0) == 0) by {
        let A = spec_field_element(&MONTGOMERY_A);
        let u2 = math_field_mul(0, 0);
        let u3 = math_field_mul(u2, 0);
        let Au2 = math_field_mul(A, u2);
        assert(montgomery_rhs(0) == math_field_add(math_field_add(u3, Au2), 0));
        p_gt_2();
        lemma_small_mod(0, p());
        assert(0nat % p() == 0nat);
        assert(u2 == 0) by {
            lemma_field_mul_zero_left(0, 0);
        }
        assert(u3 == 0) by {
            lemma_field_mul_zero_left(u2, 0);
        }
        assert(Au2 == 0) by {
            lemma_field_mul_zero_right(A, u2);
        }
        assert(math_field_add(math_field_add(0, 0), 0) == 0) by {
            p_gt_2();
            assert(math_field_add(0, 0) == (0nat + 0nat) % p());
            assert(math_field_add(0, 0) == 0);
            assert(math_field_add(0, 0) + 0 == 0);
            assert(math_field_add(math_field_add(0, 0), 0) == (0nat + 0nat) % p());
            assert(math_field_add(math_field_add(0, 0), 0) == 0);
        }
        assert(montgomery_rhs(0) == 0);
    }
    assert(canonical_montgomery_lift(0) == MontgomeryAffine::Finite {
        u: 0nat % p(),
        v: canonical_sqrt(montgomery_rhs(0)),
    });
    assert(0nat % p() == 0nat) by {
        p_gt_2();
        lemma_mod_self_0(p() as int);
    }
    assert(canonical_sqrt(montgomery_rhs(0)) == 0);
}

/// Lemma: the (0,0) point doubles to infinity under montgomery_add.
pub proof fn lemma_montgomery_add_zero_point_doubles_to_infinity()
    ensures
        ({
            let P = canonical_montgomery_lift(0);
            montgomery_add(P, P) == MontgomeryAffine::Infinity
        }),
{
    let P = canonical_montgomery_lift(0);
    assert(P == MontgomeryAffine::Finite { u: 0, v: 0 }) by {
        lemma_canonical_montgomery_lift_zero();
    }
    // Unfold montgomery_add on (0,0)+(0,0): it matches the P = -Q case.
    assert(montgomery_add(P, P) == MontgomeryAffine::Infinity);
}

/// Lemma: scalar multiplication of the (0,0) 2-torsion point stays in {∞, P}.
pub proof fn lemma_montgomery_scalar_mul_zero_point_closed(n: nat)
    ensures
        ({
            let P = canonical_montgomery_lift(0);
            let R = montgomery_scalar_mul(P, n);
            R == MontgomeryAffine::Infinity || R == P
        }),
    decreases n,
{
    let P = canonical_montgomery_lift(0);
    if n == 0 {
        assert(montgomery_scalar_mul(P, 0) == MontgomeryAffine::Infinity);
    } else {
        lemma_montgomery_scalar_mul_zero_point_closed((n - 1) as nat);
        let R_prev = montgomery_scalar_mul(P, (n - 1) as nat);
        assert(R_prev == MontgomeryAffine::Infinity || R_prev == P);
        // Unfold scalar multiplication: [n]P = P + [n-1]P
        assert(montgomery_scalar_mul(P, n) == montgomery_add(P, R_prev));
        if R_prev == MontgomeryAffine::Infinity {
            // P + ∞ = P (by definition of montgomery_add)
            assert(montgomery_add(P, MontgomeryAffine::Infinity) == P);
            assert(montgomery_scalar_mul(P, n) == P);
        } else {
            // R_prev == P, so P + P = ∞
            assert(montgomery_scalar_mul(P, n) == MontgomeryAffine::Infinity) by {
                lemma_montgomery_add_zero_point_doubles_to_infinity();
            }
        }
    }
}

/// Lemma: u-coordinate of any scalar multiple of canonical_montgomery_lift(0) is 0.
pub proof fn lemma_u_coordinate_scalar_mul_canonical_lift_zero(n: nat)
    ensures
        ({
            let P = canonical_montgomery_lift(0);
            spec_u_coordinate(montgomery_scalar_mul(P, n)) == 0
        }),
{
    lemma_montgomery_scalar_mul_zero_point_closed(n);
    lemma_canonical_montgomery_lift_zero();
    let P = canonical_montgomery_lift(0);
    let R = montgomery_scalar_mul(P, n);
    if R == MontgomeryAffine::Infinity {
        assert(spec_u_coordinate(MontgomeryAffine::Infinity) == 0);
    } else {
        assert(R == P);
        assert(P == MontgomeryAffine::Finite { u: 0, v: 0 });
        assert(spec_u_coordinate(MontgomeryAffine::Finite { u: 0, v: 0 }) == 0);
    }
}

/// Lemma: u-coordinate of any scalar multiple of a canonical lift is reduced (< p).
///
/// This follows from:
/// 1. canonical_montgomery_lift produces points with u < p (uses u % p())
/// 2. montgomery_add uses field operations which preserve u < p
/// 3. By induction, all scalar multiples have u < p
///
/// This lemma is used to show that `(spec_u_coordinate(...) % p()) == spec_u_coordinate(...)`,
/// which allows us to drop the redundant `% p()` when converting from projective representation
/// to u-coordinate equality.
pub proof fn lemma_canonical_scalar_mul_u_coord_reduced(u0: nat, n: nat)
    requires
        u0 != 0,
    ensures
        ({
            let P = canonical_montgomery_lift(u0);
            let R = montgomery_scalar_mul(P, n);
            spec_u_coordinate(R) < p()
        }),
    decreases n,
{
    let P = canonical_montgomery_lift(u0);
    let R = montgomery_scalar_mul(P, n);
    p_gt_2();

    if n == 0 {
        // montgomery_scalar_mul(P, 0) = Infinity
        // spec_u_coordinate(Infinity) = 0 < p()
        assert(R == MontgomeryAffine::Infinity);
        assert(spec_u_coordinate(R) == 0);
    } else {
        // montgomery_scalar_mul(P, n) = montgomery_add(P, montgomery_scalar_mul(P, n-1))
        let R_prev = montgomery_scalar_mul(P, (n - 1) as nat);
        lemma_canonical_scalar_mul_u_coord_reduced(u0, (n - 1) as nat);
        assert(spec_u_coordinate(R_prev) < p());

        // Now R = montgomery_add(P, R_prev)
        // montgomery_add returns either Infinity (u-coord 0) or Finite with u computed
        // via math_field_* operations which always return values < p()
        lemma_montgomery_add_u_coord_reduced(P, R_prev, u0);
    }
}

/// Helper lemma: montgomery_add preserves the property that u-coordinates are < p()
proof fn lemma_montgomery_add_u_coord_reduced(P: MontgomeryAffine, Q: MontgomeryAffine, u0: nat)
    requires
        u0 != 0,
        P == canonical_montgomery_lift(u0),
        spec_u_coordinate(Q) < p(),
    ensures
        spec_u_coordinate(montgomery_add(P, Q)) < p(),
{
    p_gt_2();
    let R = montgomery_add(P, Q);

    // P = canonical_montgomery_lift(u0) means P = Finite{u: u0 % p(), v: ...}
    // So spec_u_coordinate(P) = u0 % p() < p()
    assert(spec_u_coordinate(P) < p()) by {
        // canonical_montgomery_lift creates Finite{u: u % p(), v: ...}
        lemma_mod_division_less_than_divisor(u0 as int, p() as int);
    }

    match R {
        MontgomeryAffine::Infinity => {
            assert(spec_u_coordinate(R) == 0);
        },
        MontgomeryAffine::Finite { u, v } => {
            // u is computed via math_field_sub which returns a value < p()
            // The montgomery_add formula computes u3 = math_field_sub(math_field_sub(...), ...)
            // All math_field_* operations return values % p() which are < p()
            assert(u < p()) by {
                // math_field_sub(a, b) = (((a % p()) + p()) - (b % p())) % p() < p()
                lemma_mod_division_less_than_divisor(u as int, p() as int);
            }
        },
    }
}

} // verus!
