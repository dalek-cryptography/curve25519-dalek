//! Constants for use in Lizard
//!
//! Could be moved into backend/serial/u??/constants.rs

#[cfg(feature = "u64_backend")]
pub(crate) use lizard::u64_constants::*;

#[cfg(feature = "u32_backend")]
pub(crate) use lizard::u32_constants::*;


// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(all(test, feature = "stage2_build"))]
mod test {

    use super::*;
    use constants;
    use field::FieldElement;

    #[test]
    fn test_lizard_constants() {
        let (_, sqrt_id) =  FieldElement::sqrt_ratio_i(
            &(&constants::SQRT_M1 * &constants::EDWARDS_D),
            &FieldElement::one()
        );
        assert_eq!(sqrt_id, SQRT_ID);

        assert_eq!(
            &(&constants::EDWARDS_D + &FieldElement::one())
            * &(&constants::EDWARDS_D - &FieldElement::one()).invert(),
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

        let (_, invsqrt_one_plus_d) = (
            &constants::EDWARDS_D + &FieldElement::one()).invsqrt();
        assert_eq!(
            -&invsqrt_one_plus_d,
            MINVSQRT_ONE_PLUS_D
        );
    }
}
