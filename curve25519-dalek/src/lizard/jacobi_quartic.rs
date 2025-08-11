//! Helper functions for use with Lizard

#![allow(non_snake_case)]

use subtle::Choice;
use subtle::ConditionallyNegatable;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

use super::lizard_constants;
use crate::constants;

use crate::field::FieldElement;

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
    pub(crate) fn elligator_inv(&self) -> (Choice, FieldElement) {
        let mut out = FieldElement::ZERO;

        // Special case: s = 0.  If s is zero, either t = 1 or t = -1.
        // If t=1, then sqrt(i*d) is the preimage.  Otherwise it's 0.
        let s_is_zero = self.S.is_zero();
        let t_equals_one = self.T.ct_eq(&FieldElement::ONE);
        out.conditional_assign(&lizard_constants::SQRT_ID, t_equals_one);
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
        ret |= sq;
        done |= !sq;

        // x := (a + sign(s)*s^2) y
        let mut pms2 = s2;
        pms2.conditional_negate(self.S.is_negative());
        let mut x = &(&a + &pms2) * &y;
        let x_is_negative = x.is_negative();
        x.conditional_negate(x_is_negative);
        out.conditional_assign(&x, !done);

        (ret, out)
    }

    pub(crate) fn dual(&self) -> JacobiPoint {
        JacobiPoint {
            S: -(&self.S),
            T: -(&self.T),
        }
    }
}
