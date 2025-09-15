//! Constants for use in Lizard
//!
//! Could be moved into backend/serial/u??/constants.rs

#[cfg(curve25519_dalek_bits = "64")]
pub(crate) use super::u64_constants::*;

#[cfg(curve25519_dalek_bits = "32")]
pub(crate) use super::u32_constants::*;

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {

    use super::*;
    use crate::constants;
    use crate::field::FieldElement;

    #[test]
    fn test_lizard_constants() {
        let (_, sqrt_id) = FieldElement::sqrt_ratio_i(
            &(&constants::SQRT_M1 * &constants::EDWARDS_D),
            &FieldElement::ONE,
        );
        assert_eq!(sqrt_id, SQRT_ID);

        assert_eq!(
            &(&constants::EDWARDS_D + &FieldElement::ONE)
                * &(&constants::EDWARDS_D - &FieldElement::ONE).invert(),
            DP1_OVER_DM1
        );

        assert_eq!(
            MDOUBLE_INVSQRT_A_MINUS_D,
            -&(&constants::INVSQRT_A_MINUS_D + &constants::INVSQRT_A_MINUS_D)
        );

        assert_eq!(
            MIDOUBLE_INVSQRT_A_MINUS_D,
            &MDOUBLE_INVSQRT_A_MINUS_D * &constants::SQRT_M1
        );

        let (_, invsqrt_one_plus_d) = (&constants::EDWARDS_D + &FieldElement::ONE).invsqrt();
        assert_eq!(-&invsqrt_one_plus_d, MINVSQRT_ONE_PLUS_D);
    }
}
