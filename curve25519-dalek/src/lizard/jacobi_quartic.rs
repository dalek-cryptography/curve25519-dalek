//! Helper functions for use with Lizard
#![allow(non_snake_case)]

use subtle::Choice;
use subtle::ConstantTimeEq;

use super::lizard_constants;
use crate::constants;

use crate::field::FieldElement;

#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::{
    choice_not, choice_or, conditional_assign_generic, conditional_negate_field_element,
    negate_field_element,
};

use vstd::prelude::*;

#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::lizard_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;

verus! {

/// Represents a point (s,t) on the the Jacobi quartic associated
/// to the Edwards curve.
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct JacobiPoint {
    pub S: FieldElement,
    pub T: FieldElement,
}

impl JacobiPoint {
    /// Elligator2 is defined in two steps: first a field element is converted
    /// to a point (s,t) on the Jacobi quartic associated to the Edwards curve.
    /// Then this point is mapped to a point on the Edwards curve.
    /// This function computes a field element that is mapped to a given (s,t)
    /// with Elligator2 if it exists.
    pub(crate) fn elligator_inv(&self) -> (result: (Choice, FieldElement))
        requires
            fe51_limbs_bounded(&self.S, 54),
            fe51_limbs_bounded(&self.T, 54),
        ensures
            fe51_limbs_bounded(&result.1, 54),
            // Correctness: when a preimage exists, Elligator forward maps it to
            // the Edwards point corresponding to this Jacobi quartic point
            crate::backend::serial::u64::subtle_assumes::choice_is_true(result.0) == true
                ==> spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&result.1))
                == jacobi_to_edwards_affine(
                fe51_as_canonical_nat(&self.S),
                fe51_as_canonical_nat(&self.T),
            ),
    {
        proof {
            admit();  // PROOF BYPASS: algebraic Elligator roundtrip + limb bound tracking
        }
        let mut out = FieldElement::ZERO;

        // Special case: s = 0.  If s is zero, either t = 1 or t = -1.
        // If t=1, then sqrt(i*d) is the preimage.  Otherwise it's 0.
        let s_is_zero = self.S.is_zero();
        let t_equals_one = self.T.ct_eq(&FieldElement::ONE);
        /* ORIGINAL CODE: out.conditional_assign(&lizard_constants::SQRT_ID, t_equals_one); */
        conditional_assign_generic(&mut out, &lizard_constants::SQRT_ID, t_equals_one);
        let mut ret = s_is_zero;
        let mut done = s_is_zero;

        // a := (t+1) (d+1)/(d-1)
        let a = &(&self.T + &FieldElement::ONE) * &lizard_constants::DP1_OVER_DM1;
        let a2 = a.square();

        // y := 1/sqrt(i (s^4 - a^2)).
        let s2 = self.S.square();
        let s4 = s2.square();
        let invSqY = &(&s4 - &a2) * &constants::SQRT_M1;

        // There is no preimage if the square root of i*(s^4-a^2) does not exist.
        let (sq, y) = invSqY.invsqrt();
        /* ORIGINAL CODE: ret |= sq; done |= !sq; */
        ret = choice_or(ret, sq);
        done = choice_or(done, choice_not(sq));

        // x := (a + sign(s)*s^2) y
        let mut pms2 = s2;
        /* ORIGINAL CODE: pms2.conditional_negate(self.S.is_negative()); */
        conditional_negate_field_element(&mut pms2, self.S.is_negative());
        let mut x = &(&a + &pms2) * &y;
        let x_is_negative = x.is_negative();
        /* ORIGINAL CODE: x.conditional_negate(x_is_negative); */
        conditional_negate_field_element(&mut x, x_is_negative);
        /* ORIGINAL CODE: out.conditional_assign(&x, !done); */
        conditional_assign_generic(&mut out, &x, choice_not(done));

        (ret, out)
    }

    /// Compute the dual of this Jacobi quartic point: (-S, -T).
    pub(crate) fn dual(&self) -> (result: JacobiPoint)
        requires
            fe51_limbs_bounded(&self.S, 54),
            fe51_limbs_bounded(&self.T, 54),
        ensures
            fe51_limbs_bounded(&result.S, 52),
            fe51_limbs_bounded(&result.T, 52),
            fe51_as_canonical_nat(&result.S) == field_neg(fe51_as_canonical_nat(&self.S)),
            fe51_as_canonical_nat(&result.T) == field_neg(fe51_as_canonical_nat(&self.T)),
    {
        /* ORIGINAL CODE: JacobiPoint { S: -(&self.S), T: -(&self.T) } */
        // Using negate_field_element wrapper to avoid Verus internal error
        JacobiPoint { S: negate_field_element(&self.S), T: negate_field_element(&self.T) }
    }
}

} // verus!
