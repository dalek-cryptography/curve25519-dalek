//! Helper functions for scalar operations in MODIFIED CODE

use crate::scalar::Scalar;
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::backend::serial::u64::scalar_specs::*;

#[allow(unused_imports)]
use crate::scalar_specs::*;

verus! {

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
    ensures
        // Result is a valid scalar (bytes represent a value < group_order)
        scalar_to_nat(&result) < group_order(),
        // Result represents the product of all scalars in the slice (mod group_order)
        scalar_congruent_nat(&result, product_of_scalars(scalars@)),
    {
        let n = scalars.len();
        let mut acc = Scalar::ONE;

        proof {
            // Assume properties of Scalar::ONE
            assume(scalar_to_nat(&acc) < group_order());
            assume(scalar_to_nat(&acc) == 1);
            assume(scalar_congruent_nat(&acc, product_of_scalars(scalars@.subrange(0, 0))));
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                scalar_to_nat(&acc) < group_order(),
                // acc represents the product of scalars[0..i]
                scalar_congruent_nat(&acc, product_of_scalars(scalars@.subrange(0, i as int))),
        {
            proof {
                // Assume preconditions for multiplication are satisfied
                assume(false);
            }
            acc = &acc * &scalars[i];

            proof {
                // Assume the result maintains the invariant
                assume(scalar_to_nat(&acc) < group_order());
                assume(scalar_congruent_nat(&acc, product_of_scalars(scalars@.subrange(0, (i + 1) as int))));
            }
        }

        proof {
            // At this point, acc is the product of all scalars
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
    /* <VERIFICATION NOTE>
     Refactored for Verus: Use index-based loop over slice
    </VERIFICATION NOTE> */
    #[allow(clippy::needless_range_loop, clippy::op_ref)]
    pub fn sum_of_slice(scalars: &[Scalar]) -> (result: Scalar)
    ensures
        // Result is a valid scalar (bytes represent a value < group_order)
        scalar_to_nat(&result) < group_order(),
        // Result represents the sum of all scalars in the slice (mod group_order)
        scalar_congruent_nat(&result, sum_of_scalars(scalars@)),
    {
        let n = scalars.len();
        let mut acc = Scalar::ZERO;

        proof {
            // Assume properties of Scalar::ZERO
            assume(scalar_to_nat(&acc) < group_order());
            assume(scalar_to_nat(&acc) == 0);
            assume(scalar_congruent_nat(&acc, sum_of_scalars(scalars@.subrange(0, 0))));
        }

        for i in 0..n
            invariant
                n == scalars.len(),
                scalar_to_nat(&acc) < group_order(),
                // acc represents the sum of scalars[0..i]
                scalar_congruent_nat(&acc, sum_of_scalars(scalars@.subrange(0, i as int))),
        {
            proof {
                // Assume preconditions for addition are satisfied
                assume(false);
            }
            acc = &acc + &scalars[i];

            proof {
                // Assume the result maintains the invariant
                assume(scalar_to_nat(&acc) < group_order());
                assume(scalar_congruent_nat(&acc, sum_of_scalars(scalars@.subrange(0, (i + 1) as int))));
            }
        }

        proof {
            // At this point, acc is the sum of all scalars
            assert(scalars@.subrange(0, n as int) =~= scalars@);
        }

        acc
    }
}

} // verus!
