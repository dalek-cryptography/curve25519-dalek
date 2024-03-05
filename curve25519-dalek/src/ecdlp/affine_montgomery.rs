use crate::{constants::MONTGOMERY_A, field::FieldElement, EdwardsPoint};

#[derive(Clone, Copy, Debug)]
pub(crate) struct AffineMontgomeryPoint {
    pub u: FieldElement,
    pub v: FieldElement,
}

impl AffineMontgomeryPoint {
    pub fn is_identity_not_ct(&self) -> bool {
        self.u == FieldElement::ZERO && self.v == FieldElement::ZERO
    }

    pub fn identity() -> Self {
        AffineMontgomeryPoint {
            u: FieldElement::ZERO,
            v: FieldElement::ZERO,
        }
    }

    pub fn from_bytes(u: &[u8; 32], v: &[u8; 32]) -> Self {
        Self {
            u: FieldElement::from_bytes(u),
            v: FieldElement::from_bytes(v),
        }
    }

    /// Add two `AffineMontgomeryPoint` together.
    pub fn addition_not_ct(&self, p2: &Self) -> AffineMontgomeryPoint {
        let p1 = self;
        if p1.is_identity_not_ct() {
            // p2 + P_inf = p2
            *p2
        } else if p2.is_identity_not_ct() {
            // p1 + P_inf = p1
            *p1
        } else if p1.u == p2.u && p1.v == -&p2.v {
            // p1 = -p2 = (u1, -v1), meaning p1 + p2 = P_inf
            Self::identity()
        } else {
            let lambda = if p1.u == p2.u {
                // doubling case

                // (3*u1^2 + 2*A*u1 + 1) / (2*v1)
                // todo this is ugly
                let u1_sq = p1.u.square();
                let u1_sq_3 = &(&u1_sq + &u1_sq) + &u1_sq;
                let u1_ta = &MONTGOMERY_A * &p1.u;
                let u1_ta_2 = &u1_ta + &u1_ta;
                let den = &p1.v + &p1.v;
                let num = &(&u1_sq_3 + &u1_ta_2) + &FieldElement::ONE;

                &num * &den.invert()
            } else {
                // (v1 - v2) / (u1 - u2)
                &(&p1.v - &p2.v) * &(&p1.u - &p2.u).invert()
            };

            // u3 = lambda^2 - A - u1 - u2
            // v3 = lambda * (u1 - u3) - v1
            let new_u = &(&lambda.square() - &MONTGOMERY_A) - &(&p1.u + &p2.u);
            let new_v = &(&lambda * &(&p1.u - &new_u)) - &p1.v;

            AffineMontgomeryPoint { u: new_u, v: new_v }
        }
    }
}

// FIXME(upstream): FieldElement::from_bytes should probably be const
// see test for correctness of this const
fn edwards_to_montgomery_alpha() -> FieldElement {
    // Constant comes from https://ristretto.group/details/isogenies.html (birational mapping from E2 = E_(a2,d2) to M_(B,A))
    // alpha = sqrt((A + 2) / (B * a_2)) with B = 1 and a_2 = -1.
    FieldElement::from_bytes(&[
        6, 126, 69, 255, 170, 4, 110, 204, 130, 26, 125, 75, 209, 211, 161, 197, 126, 79, 252, 3,
        220, 8, 123, 210, 187, 6, 160, 96, 244, 237, 38, 15,
    ])
}

impl From<&'_ EdwardsPoint> for AffineMontgomeryPoint {
    #[allow(non_snake_case)]
    fn from(eddy: &EdwardsPoint) -> Self {
        let ALPHA = edwards_to_montgomery_alpha();

        // u = (1+y)/(1-y) = (Z+Y)/(Z-Y),
        // v = (1+y)/(x(1-y)) * alpha = (Z+Y)/(X-T) * alpha.
        let Z_plus_Y = &eddy.Z + &eddy.Y;
        let Z_minus_Y = &eddy.Z - &eddy.Y;
        let X_minus_T = &eddy.X - &eddy.T;
        AffineMontgomeryPoint {
            u: &Z_plus_Y * &Z_minus_Y.invert(),
            v: &(&Z_plus_Y * &X_minus_T.invert()) * &ALPHA,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_const_alpha() {
        // Constant comes from https://ristretto.group/details/isogenies.html (birational mapping from E2 = E_(a2,d2) to M_(B,A))
        // alpha = sqrt((A + 2) / (B * a_2)) with B = 1 and a_2 = -1.
        let two = &FieldElement::ONE + &FieldElement::ONE;
        let (is_sq, v) =
            FieldElement::sqrt_ratio_i(&(&MONTGOMERY_A + &two), &FieldElement::MINUS_ONE);
        assert!(bool::from(is_sq));

        assert_eq!(edwards_to_montgomery_alpha().as_bytes(), v.as_bytes());
    }
}
