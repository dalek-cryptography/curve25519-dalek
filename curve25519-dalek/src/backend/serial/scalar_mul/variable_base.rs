#![allow(non_snake_case)]

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::window::LookupTable;

#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::{
    edwards_point_as_affine, edwards_scalar_mul, is_valid_completed_point,
    is_valid_projective_niels_point, is_well_formed_edwards_point,
};
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs::{fe51_limbs_bounded, sum_of_limbs_bounded};
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::{radix_16_all_bounded, radix_16_digit_bounded, scalar_as_nat};
#[cfg(verus_keep_ghost)]
use crate::specs::window_specs::lookup_table_projective_limbs_bounded;

use vstd::prelude::*;

verus! {

/// Perform constant-time, variable-base scalar multiplication.
/// Computes scalar * point on the Ed25519 curve.
// VERIFICATION NOTE: PROOF BYPASS - assumes used for intermediate preconditions
#[rustfmt::skip]  // keep alignment of explanatory comments
pub(crate) fn mul(point: &EdwardsPoint, scalar: &Scalar) -> (result: EdwardsPoint)
    requires
// as_radix_16 requires scalar.bytes[31] <= 127 (MSB clear, i.e. scalar < 2^255)

        scalar.bytes[31] <= 127,
        // Input point must be well-formed (valid coordinates with proper limb bounds)
        is_well_formed_edwards_point(*point),
    ensures
// Result is a well-formed Edwards point

        is_well_formed_edwards_point(result),
        // Functional correctness: result represents scalar * point
        edwards_point_as_affine(result) == edwards_scalar_mul(
            edwards_point_as_affine(*point),
            scalar_as_nat(scalar),
        ),
{
    // Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]
    let lookup_table = LookupTable::<ProjectiveNielsPoint>::from(point);
    // Setting s = scalar, compute
    //
    //    s = s_0 + s_1*16^1 + ... + s_63*16^63,
    //
    // with `-8 ≤ s_i < 8` for `0 ≤ i < 63` and `-8 ≤ s_63 ≤ 8`.
    // This decomposition requires s < 2^255, which is guaranteed by Scalar invariant #1.
    let scalar_digits = scalar.as_radix_16();
    // Compute s*P as
    //
    //    s*P = P*(s_0 +   s_1*16^1 +   s_2*16^2 + ... +   s_63*16^63)
    //    s*P =  P*s_0 + P*s_1*16^1 + P*s_2*16^2 + ... + P*s_63*16^63
    //    s*P = P*s_0 + 16*(P*s_1 + 16*(P*s_2 + 16*( ... + P*s_63)...))
    //
    // We sum right-to-left.

    // Unwrap first loop iteration to save computing 16*identity
    let mut tmp2;
    let mut tmp3 = EdwardsPoint::identity();
    proof {
        // From identity() postcondition
        assert(is_well_formed_edwards_point(tmp3));
        // From as_radix_16 postcondition: radix_16_all_bounded ensures all digits in [-8, 8]
        assert(radix_16_all_bounded(&scalar_digits));
        assert(radix_16_digit_bounded(scalar_digits[63]));  // instantiate for index 63
    }
    /* ORIGINAL CODE:
    let mut tmp1 = &tmp3 + &lookup_table.select(scalar_digits[63]);
    */
    // REFACTORED: Extract select to bind result for proof block
    let selected = lookup_table.select(scalar_digits[63]);
    proof {
        // Validity: select returns a valid ProjectiveNielsPoint (from select postcondition)
        assert(is_valid_projective_niels_point(selected));
    }
    let mut tmp1 = &tmp3 + &selected;

    // Now tmp1 = s_63*P in P1xP1 coords
    /* ORIGINAL CODE:
    for i in (0..63).rev() {
    */
    // REFACTORED: Verus doesn't support .rev() on ranges, so iterate forward and compute reverse index
    for j in 0usize..63
        invariant
    // scalar_digits bounds remain valid throughout the loop

            radix_16_all_bounded(&scalar_digits),
            // lookup_table has bounded limbs (from from() postcondition)
            lookup_table_projective_limbs_bounded(lookup_table.0),
            // tmp1 is always a valid completed point (from Add postcondition)
            is_valid_completed_point(tmp1),
            // tmp1 limb bounds (from Add postcondition, preserved through loop)
            fe51_limbs_bounded(&tmp1.X, 54),
            fe51_limbs_bounded(&tmp1.Y, 54),
            fe51_limbs_bounded(&tmp1.Z, 54),
            fe51_limbs_bounded(&tmp1.T, 54),
    {
        let i = 62 - j;  // i goes from 62 down to 0
        tmp2 = tmp1.as_projective();  // tmp2 =    (prev) in P2 coords
        tmp1 = tmp2.double();  // tmp1 =  2*(prev) in P1xP1 coords
        tmp2 = tmp1.as_projective();  // tmp2 =  2*(prev) in P2 coords
        tmp1 = tmp2.double();  // tmp1 =  4*(prev) in P1xP1 coords
        tmp2 = tmp1.as_projective();  // tmp2 =  4*(prev) in P2 coords
        tmp1 = tmp2.double();  // tmp1 =  8*(prev) in P1xP1 coords
        tmp2 = tmp1.as_projective();  // tmp2 =  8*(prev) in P2 coords
        tmp1 = tmp2.double();  // tmp1 = 16*(prev) in P1xP1 coords
        tmp3 = tmp1.as_extended();  // tmp3 = 16*(prev) in P3 coords
        /* ORIGINAL CODE:
        tmp1 = &tmp3 + &lookup_table.select(scalar_digits[i]);
        */
        // REFACTORED: Extract select to bind result for proof block
        let selected = lookup_table.select(scalar_digits[i]);
        proof {
            // Validity: select returns a valid ProjectiveNielsPoint (from select postcondition)
            assert(is_valid_projective_niels_point(selected));
        }
        tmp1 = &tmp3 + &selected;
        // Now tmp1 = s_i*P + 16*(prev) in P1xP1 coords
    }
    proof {
        // From loop invariant
        assert(is_valid_completed_point(tmp1));
        // From Add<ProjectiveNielsPoint> postconditions (now includes limb bounds)
        assert(fe51_limbs_bounded(&tmp1.X, 54));
        assert(fe51_limbs_bounded(&tmp1.Y, 54));
        assert(fe51_limbs_bounded(&tmp1.Z, 54));
        assert(fe51_limbs_bounded(&tmp1.T, 54));
    }
    let result = tmp1.as_extended();
    proof {
        // postconditions
        assume(edwards_point_as_affine(result) == edwards_scalar_mul(
            edwards_point_as_affine(*point),
            scalar_as_nat(scalar),
        ));
    }
    result
}

} // verus!
