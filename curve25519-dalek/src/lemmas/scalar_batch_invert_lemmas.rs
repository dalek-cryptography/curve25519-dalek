//! Proof lemmas for batch_invert function
//!
//! These lemmas prove the correctness of the batch inversion algorithm
//! which computes multiplicative inverses for a slice of scalars using
//! Montgomery multiplication.
#[allow(unused_imports)]
use crate::scalar::Scalar;
#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar52_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ============================================================================
// Helper specs for batch_invert
// ============================================================================
/// Partial product of scalars from 0 to n-1 (mod group_order)
/// This computes: ∏_{j=0}^{n-1} scalars[j] (mod L)
pub open spec fn partial_product(scalars: Seq<Scalar>, n: int) -> nat
    recommends
        0 <= n <= scalars.len(),
    decreases n,
{
    if n <= 0 {
        1nat
    } else {
        (partial_product(scalars, n - 1) * bytes32_to_nat(&scalars[n - 1].bytes)) % group_order()
    }
}

/// Partial product in Montgomery form (multiplied by R)
/// This represents what acc holds in the first loop: R * ∏_{j=0}^{i-1} inputs[j] (mod L)
pub open spec fn partial_product_montgomery(scalars: Seq<Scalar>, n: int) -> nat
    recommends
        0 <= n <= scalars.len(),
{
    (montgomery_radix() * partial_product(scalars, n)) % group_order()
}

// ============================================================================
// Proof lemmas for batch_invert
// ============================================================================
/// Lemma: partial_product equals product_of_scalars when n equals length
pub proof fn lemma_partial_product_full(scalars: Seq<Scalar>)
    ensures
        partial_product(scalars, scalars.len() as int) == product_of_scalars(scalars),
    decreases scalars.len(),
{
    if scalars.len() == 0 {
        // Base case: both are 1
    } else {
        let n = scalars.len() as int;
        let prefix = scalars.subrange(0, n - 1);

        // Inductive step: partial_product(scalars, n-1) == product_of_scalars(prefix)
        lemma_partial_product_full(prefix);

        // Now show partial_product(scalars, n) == product_of_scalars(scalars)
        assert(partial_product(scalars, n) == (partial_product(scalars, n - 1) * bytes32_to_nat(
            &scalars[n - 1].bytes,
        )) % group_order());
        assert(product_of_scalars(scalars) == (product_of_scalars(prefix) * bytes32_to_nat(
            &scalars[n - 1].bytes,
        )) % group_order());

        // Need: partial_product(scalars, n-1) == partial_product(prefix, n-1)
        // This follows because scalars and prefix agree on indices 0..n-1
        lemma_partial_product_prefix_eq(scalars, prefix, n - 1);
    }
}

/// Lemma: partial_product only depends on prefix elements
pub proof fn lemma_partial_product_prefix_eq(scalars1: Seq<Scalar>, scalars2: Seq<Scalar>, n: int)
    requires
        0 <= n <= scalars1.len(),
        0 <= n <= scalars2.len(),
        forall|j: int| 0 <= j < n ==> scalars1[j] == scalars2[j],
    ensures
        partial_product(scalars1, n) == partial_product(scalars2, n),
    decreases n,
{
    if n <= 0 {
        // Base case
    } else {
        lemma_partial_product_prefix_eq(scalars1, scalars2, n - 1);
    }
}

/// Helper lemma: if a ≡ c (mod L) and b ≡ d (mod L), then a*b ≡ c*d (mod L)
pub proof fn lemma_mul_congruence(a: nat, b: nat, c: nat, d: nat, L: nat)
    requires
        L > 0,
        a % L == c % L,
        b % L == d % L,
    ensures
        (a * b) % L == (c * d) % L,
{
    lemma_mul_mod_noop_general(a as int, b as int, L as int);
    lemma_mul_mod_noop_general(c as int, d as int, L as int);
}

/// Lemma: Montgomery multiplication preserves the partial product invariant
///
/// If acc_before holds R * partial_product(scalars, i) (mod L),
/// and tmp holds scalars[i] * R (mod L),
/// and acc_after = montgomery_mul(acc_before, tmp),
/// then acc_after holds R * partial_product(scalars, i+1) (mod L).
pub proof fn lemma_montgomery_mul_partial_product(
    acc_before: nat,
    tmp: nat,
    acc_after: nat,
    scalars: Seq<Scalar>,
    i: int,
)
    requires
        0 <= i < scalars.len(),
        acc_before % group_order() == (montgomery_radix() * partial_product(scalars, i))
            % group_order(),
        tmp % group_order() == (bytes32_to_nat(&scalars[i].bytes) * montgomery_radix())
            % group_order(),
        (acc_after * montgomery_radix()) % group_order() == (acc_before * tmp) % group_order(),
    ensures
        acc_after % group_order() == (montgomery_radix() * partial_product(scalars, i + 1))
            % group_order(),
{
    use crate::lemmas::scalar_lemmas::lemma_cancel_mul_pow2_mod;
    let (L, R, pp_i, s_i) = (
        group_order(),
        montgomery_radix(),
        partial_product(scalars, i),
        bytes32_to_nat(&scalars[i].bytes),
    );
    lemma_mul_congruence(acc_before, tmp, R * pp_i, s_i * R, L);
    assert((R * pp_i) * (s_i * R) == (R * pp_i * s_i) * R) by (nonlinear_arith);
    lemma_cancel_mul_pow2_mod(acc_after, R * pp_i * s_i, R);
    lemma_mul_mod_noop_right(R as int, (pp_i * s_i) as int, L as int);
    assert(R * pp_i * s_i == R * (pp_i * s_i)) by (nonlinear_arith);
}

/// Lemma: In the backward loop, the acc invariant is maintained
///
/// If acc_before * partial_product(scalars, i+1) ≡ 1 (mod L),
/// and we compute acc_after = montgomery_mul(acc_before, input_val),
/// then acc_after * partial_product(scalars, i) ≡ 1 (mod L).
pub proof fn lemma_backward_loop_acc_invariant(
    acc_before: nat,
    input_val: nat,
    acc_after: nat,
    scalars: Seq<Scalar>,
    i: int,
)
    requires
        0 <= i < scalars.len(),
        (acc_before * partial_product(scalars, i + 1)) % group_order() == 1nat,
        input_val % group_order() == (bytes32_to_nat(&scalars[i].bytes) * montgomery_radix())
            % group_order(),
        (acc_after * montgomery_radix()) % group_order() == (acc_before * input_val)
            % group_order(),
    ensures
        (acc_after * partial_product(scalars, i)) % group_order() == 1nat,
{
    use crate::lemmas::scalar_lemmas::lemma_cancel_mul_pow2_mod;
    let (L, R, pp_i, s_i) = (
        group_order(),
        montgomery_radix(),
        partial_product(scalars, i),
        bytes32_to_nat(&scalars[i].bytes),
    );
    lemma_mul_congruence(acc_before, input_val, acc_before, s_i * R, L);
    assert((acc_before * s_i) * R == acc_before * (s_i * R)) by (nonlinear_arith);
    lemma_cancel_mul_pow2_mod(acc_after, acc_before * s_i, R);
    lemma_mul_congruence(acc_after, pp_i, acc_before * s_i, pp_i, L);
    assert((acc_before * s_i) * pp_i == acc_before * (pp_i * s_i)) by (nonlinear_arith);
    lemma_mul_mod_noop_right(acc_before as int, (pp_i * s_i) as int, L as int);
}

/// Lemma: After inverting the accumulated product, we have the inverse of the product
///
/// This connects the inversion step to the final postcondition.
pub proof fn lemma_invert_chain(acc_before: nat, acc_after: nat, final_acc: nat, product: nat)
    requires
        acc_before % group_order() == (montgomery_radix() * product) % group_order(),
        (acc_after * acc_before) % group_order() == (montgomery_radix() * montgomery_radix())
            % group_order(),
        (final_acc * montgomery_radix()) % group_order() == acc_after % group_order(),
        final_acc < group_order(),
    ensures
        (final_acc * product) % group_order() == 1nat % group_order(),
{
    use crate::lemmas::scalar_lemmas::lemma_cancel_mul_pow2_mod;
    let (L, R) = (group_order(), montgomery_radix());
    lemma_mul_congruence(final_acc * R, acc_before, acc_after, acc_before, L);
    lemma_mul_congruence(final_acc * R, acc_before, final_acc * R, R * product, L);
    assert((final_acc * R) * (R * product) == ((final_acc * product) * R) * R) by (nonlinear_arith);
    assert(R * R == 1 * R * R) by (nonlinear_arith);
    lemma_cancel_mul_pow2_mod((final_acc * product) * R, R, R);
    lemma_cancel_mul_pow2_mod(final_acc * product, 1, R);
}

/// Lemma: In the backward loop, the computed result is the inverse of the input scalar
///
/// This is the key lemma that proves each inputs[i] becomes the inverse of original_inputs[i].
pub proof fn lemma_backward_loop_is_inverse(
    acc_before: nat,
    scratch_val: nat,
    result_m: nat,
    result: nat,
    scalars: Seq<Scalar>,
    i: int,
)
    requires
        0 <= i < scalars.len(),
        (acc_before * partial_product(scalars, i + 1)) % group_order() == 1nat,
        scratch_val % group_order() == (montgomery_radix() * partial_product(scalars, i))
            % group_order(),
        (result_m * montgomery_radix()) % group_order() == (acc_before * scratch_val)
            % group_order(),
        result_m < pow2(256),
        result == result_m,
    ensures
        (result * bytes32_to_nat(&scalars[i].bytes)) % group_order() == 1nat,
{
    use crate::lemmas::scalar_lemmas::lemma_cancel_mul_pow2_mod;
    let (L, R, pp_i, s_i) = (
        group_order(),
        montgomery_radix(),
        partial_product(scalars, i),
        bytes32_to_nat(&scalars[i].bytes),
    );
    lemma_mul_congruence(acc_before, scratch_val, acc_before, R * pp_i, L);
    assert(acc_before * (R * pp_i) == (acc_before * pp_i) * R) by (nonlinear_arith);
    lemma_cancel_mul_pow2_mod(result_m, acc_before * pp_i, R);
    lemma_mul_congruence(result_m, s_i, acc_before * pp_i, s_i, L);
    assert((acc_before * pp_i) * s_i == acc_before * (pp_i * s_i)) by (nonlinear_arith);
    lemma_mul_mod_noop_right(acc_before as int, (pp_i * s_i) as int, L as int);
}

} // verus!
