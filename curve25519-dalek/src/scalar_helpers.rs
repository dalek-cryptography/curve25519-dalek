//! Helper functions for scalar operations in MODIFIED CODE
use crate::scalar::Scalar;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::specs::scalar52_specs::*;

#[allow(unused_imports)]
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;

verus! {

// ============================================================================
// Core lemmas for Scalar::ZERO and Scalar::ONE
// ============================================================================
/// Lemma: bytes32_to_nat of all-zero bytes equals 0
pub proof fn lemma_bytes32_to_nat_zero()
    ensures
        bytes32_to_nat(&Scalar::ZERO.bytes) == 0,
{
    // 0 * x == 0 for all terms
    assert forall|i: nat| i < 32 implies (0nat) * #[trigger] pow2(i * 8) == 0 by {
        lemma_mul_basics(pow2(i * 8) as int);
    }
}

/// Lemma: bytes32_to_nat of ONE's bytes equals 1
pub proof fn lemma_bytes32_to_nat_one()
    ensures
        bytes32_to_nat(&Scalar::ONE.bytes) == 1,
{
    let bytes = Scalar::ONE.bytes;
    assert(bytes[0] == 1);
    // pow2(0) == 1
    lemma2_to64();
    // 0 * x == 0 for remaining terms
    assert forall|i: nat| 1 <= i < 32 implies (0nat) * #[trigger] pow2(i * 8) == 0 by {
        lemma_mul_basics(pow2(i * 8) as int);
    }
}

/// Combined lemma for ZERO: value is 0, less than L, canonical, and congruent to 0
pub proof fn lemma_scalar_zero_properties()
    ensures
        scalar_to_nat(&Scalar::ZERO) == 0,
        scalar_to_nat(&Scalar::ZERO) < group_order(),
        is_canonical_scalar(&Scalar::ZERO),
        scalar_congruent_nat(&Scalar::ZERO, 0),
{
    lemma_bytes32_to_nat_zero();
    lemma_small_mod(0nat, group_order());
    // bytes[31] == 0 <= 127 for all-zero bytes
    assert(Scalar::ZERO.bytes[31] <= 127);
}

/// Combined lemma for ONE: value is 1, less than L, and congruent to 1
pub proof fn lemma_scalar_one_properties()
    ensures
        scalar_to_nat(&Scalar::ONE) == 1,
        scalar_to_nat(&Scalar::ONE) < group_order(),
        scalar_congruent_nat(&Scalar::ONE, 1),
        is_canonical_scalar(&Scalar::ONE),
{
    lemma_bytes32_to_nat_one();
    lemma_small_mod(1nat, group_order());
}

// ============================================================================
// Main helper functions
// ============================================================================
impl Scalar {
    /// Compute the product of all scalars in a slice.
    ///
    /// # Returns
    ///
    /// The product of all scalars modulo the group order.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// let scalars = [
    ///     Scalar::from(2u64),
    ///     Scalar::from(3u64),
    ///     Scalar::from(5u64),
    /// ];
    ///
    /// let product = Scalar::product_of_slice(&scalars);
    /// assert_eq!(product, Scalar::from(30u64));
    /// ```
    #[allow(clippy::needless_range_loop, clippy::op_ref)]
    pub fn product_of_slice(scalars: &[Scalar]) -> (result: Scalar)
        requires
            forall|i: int| #![auto] 0 <= i < scalars@.len() ==> is_canonical_scalar(&scalars@[i]),
        ensures
            scalar_to_nat(&result) < group_order(),
            is_canonical_scalar(&result),
            scalar_congruent_nat(&result, product_of_scalars(scalars@)),
    {
        let n = scalars.len();
        let mut acc = Scalar::ONE;

        proof {
            lemma_scalar_one_properties();
            assert(scalars@.subrange(0, 0) =~= Seq::<Scalar>::empty());
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                forall|j: int|
                    #![auto]
                    0 <= j < scalars@.len() ==> is_canonical_scalar(&scalars@[j]),
                scalar_to_nat(&acc) < group_order(),
                is_canonical_scalar(&acc),
                scalar_congruent_nat(&acc, product_of_scalars(scalars@.subrange(0, i as int))),
        {
            let _old_acc = acc;

            proof {
                // Inline: product extends by one element
                let sub = scalars@.subrange(0, (i + 1) as int);
                assert(sub.subrange(0, i as int) =~= scalars@.subrange(0, i as int));
            }

            acc = &acc * &scalars[i];

            proof {
                let L = group_order();
                let acc_val = bytes32_to_nat(&acc.bytes);
                let old_acc_val = bytes32_to_nat(&_old_acc.bytes);
                let scalar_val = bytes32_to_nat(&scalars[i as int].bytes);
                let prod_prev = product_of_scalars(scalars@.subrange(0, i as int));

                lemma_mul_mod_noop_general(old_acc_val as int, scalar_val as int, L as int);
                lemma_mul_mod_noop_general(prod_prev as int, scalar_val as int, L as int);
                lemma_mod_twice(prod_prev as int * scalar_val as int, L as int);
            }
        }

        proof {
            assert(scalars@.subrange(0, n as int) =~= scalars@);
        }

        acc
    }

    /// Compute the sum of all scalars in a slice.
    ///
    /// # Returns
    ///
    /// The sum of all scalars modulo the group order.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// let scalars = [
    ///     Scalar::from(2u64),
    ///     Scalar::from(3u64),
    ///     Scalar::from(5u64),
    /// ];
    ///
    /// let sum = Scalar::sum_of_slice(&scalars);
    /// assert_eq!(sum, Scalar::from(10u64));
    /// ```
    #[allow(clippy::needless_range_loop, clippy::op_ref)]
    pub fn sum_of_slice(scalars: &[Scalar]) -> (result: Scalar)
        requires
            forall|i: int| #![auto] 0 <= i < scalars@.len() ==> is_canonical_scalar(&scalars@[i]),
        ensures
            scalar_to_nat(&result) < group_order(),
            is_canonical_scalar(&result),
            scalar_congruent_nat(&result, sum_of_scalars(scalars@)),
    {
        let n = scalars.len();
        let mut acc = Scalar::ZERO;

        proof {
            lemma_scalar_zero_properties();
            assert(scalars@.subrange(0, 0) =~= Seq::<Scalar>::empty());
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                forall|j: int|
                    #![auto]
                    0 <= j < scalars@.len() ==> is_canonical_scalar(&scalars@[j]),
                scalar_to_nat(&acc) < group_order(),
                is_canonical_scalar(&acc),
                scalar_congruent_nat(&acc, sum_of_scalars(scalars@.subrange(0, i as int))),
        {
            let _old_acc = acc;

            proof {
                // Inline: sum extends by one element
                let sub = scalars@.subrange(0, (i + 1) as int);
                assert(sub.subrange(0, i as int) =~= scalars@.subrange(0, i as int));
            }

            acc = &acc + &scalars[i];

            proof {
                let L = group_order();
                let acc_val = bytes32_to_nat(&acc.bytes);
                let old_acc_val = bytes32_to_nat(&_old_acc.bytes);
                let scalar_val = bytes32_to_nat(&scalars[i as int].bytes);
                let sum_prev = sum_of_scalars(scalars@.subrange(0, i as int));

                lemma_mod_bound(old_acc_val as int + scalar_val as int, L as int);
                lemma_add_mod_noop(old_acc_val as int, scalar_val as int, L as int);
                lemma_add_mod_noop(sum_prev as int, scalar_val as int, L as int);
                lemma_mod_twice(sum_prev as int + scalar_val as int, L as int);
            }
        }

        proof {
            assert(scalars@.subrange(0, n as int) =~= scalars@);
        }

        acc
    }
}

} // verus!
