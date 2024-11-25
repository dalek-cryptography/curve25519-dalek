//
// This file is part of curve25519-dalek fork by Arcium.
//! Module for common traits.

use core::ops::ShrAssign;

use elliptic_curve::array::Array;
use elliptic_curve::bigint::ArrayEncoding;
use elliptic_curve::bigint::U256;
use elliptic_curve::consts::U32;
use elliptic_curve::ops::Invert;
use elliptic_curve::ops::MulByGenerator;
use elliptic_curve::scalar::FromUintUnchecked;
use elliptic_curve::scalar::IsHigh;
use elliptic_curve::Curve;
use elliptic_curve::Field;
use elliptic_curve::FieldBytes;
use elliptic_curve::FieldBytesEncoding;
use elliptic_curve::PrimeField;
use elliptic_curve::ScalarPrimitive;
use subtle::Choice;
use subtle::CtOption;

use crate::constants::BASEPOINT_ORDER_PRIVATE;
use crate::EdwardsPoint;
use crate::RistrettoPoint;
use crate::Scalar;

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
/// Empty struct for the curve
pub struct Dalek {}

impl Curve for Dalek {
    type FieldBytesSize = U32;
    type Uint = U256;
    const ORDER: Self::Uint = U256::from_le_slice(BASEPOINT_ORDER_PRIVATE.as_bytes());
}

// Impls for EdwardsPoint
impl MulByGenerator for EdwardsPoint {
    fn mul_by_generator(scalar: &Self::Scalar) -> Self {
        <Self as group::Group>::generator() * scalar
    }
}

// Impls for EdwardsPoint
impl MulByGenerator for RistrettoPoint {
    fn mul_by_generator(scalar: &Self::Scalar) -> Self {
        <Self as group::Group>::generator() * scalar
    }
}

// Impls for Scalar
impl AsRef<Scalar> for Scalar {
    fn as_ref(&self) -> &Scalar {
        self
    }
}

impl From<ScalarPrimitive<Dalek>> for Scalar {
    fn from(value: ScalarPrimitive<Dalek>) -> Self {
        Scalar::from_bytes_mod_order(value.to_uint().to_le_bytes())
    }
}

impl From<U256> for Scalar {
    fn from(value: U256) -> Self {
        Scalar::from_bytes_mod_order(value.to_le_bytes())
    }
}

impl FromUintUnchecked for Scalar {
    type Uint = U256;
    fn from_uint_unchecked(uint: Self::Uint) -> Self {
        Scalar {
            bytes: uint.to_le_bytes(),
        }
    }
}

impl Into<FieldBytes<Dalek>> for Scalar {
    fn into(self) -> FieldBytes<Dalek> {
        U256::encode_field_bytes(&U256::from_le_slice(&self.bytes))
    }
}

impl Into<ScalarPrimitive<Dalek>> for Scalar {
    fn into(self) -> ScalarPrimitive<Dalek> {
        ScalarPrimitive::new(U256::from_le_slice(&self.bytes)).unwrap()
    }
}

impl Into<U256> for Scalar {
    fn into(self) -> U256 {
        U256::from_le_slice(&self.bytes)
    }
}

impl Into<U256> for &mut Scalar {
    fn into(self) -> U256 {
        U256::from_le_slice(&self.bytes)
    }
}

impl Invert for Scalar {
    type Output = CtOption<Self>;
    fn invert(&self) -> Self::Output {
        Field::invert(self)
    }
}

impl IsHigh for Scalar {
    fn is_high(&self) -> Choice {
        let res = self >= &<Scalar as PrimeField>::TWO_INV;
        Choice::from(res as u8)
    }
}

impl PartialOrd for Scalar {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Scalar {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        for (s, o) in self.bits_le().rev().zip(other.bits_le().rev()) {
            match (s, o) {
                (true, false) => return core::cmp::Ordering::Greater,
                (false, true) => return core::cmp::Ordering::Less,
                _ => (),
            };
        }
        core::cmp::Ordering::Equal
    }
}

impl ShrAssign<usize> for Scalar {
    fn shr_assign(&mut self, rhs: usize) {
        let temp = Into::<U256>::into(self.clone())
            .shr_vartime(rhs as u32)
            .to_le_bytes();
        *self = Scalar::from_bytes_mod_order(temp);
    }
}

impl elliptic_curve::ops::Reduce<U256> for Scalar {
    type Bytes = Array<u8, U32>;
    fn reduce(n: U256) -> Self {
        Self::from_bytes_mod_order(n.to_le_bytes())
    }
    fn reduce_bytes(bytes: &Self::Bytes) -> Self {
        Self::from_bytes_mod_order(bytes.0)
    }
}

impl FieldBytesEncoding<Dalek> for U256 {
    fn decode_field_bytes(field_bytes: &FieldBytes<Dalek>) -> Self {
        U256::from_le_byte_array(*field_bytes)
    }
    fn encode_field_bytes(&self) -> FieldBytes<Dalek> {
        self.to_le_byte_array()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encodable_curve::Dalek;
    use crate::Scalar;
    use elliptic_curve::bigint::U256;
    use elliptic_curve::scalar::IsHigh;
    use elliptic_curve::Curve;
    use subtle::Choice;

    #[test]
    fn test_partial_ord() {
        assert!(Scalar::ZERO <= Scalar::ONE);
    }

    fn another_is_high(s: Scalar) -> Choice {
        let s_as_uint: U256 = s.into();
        let res = (Dalek::ORDER - s_as_uint) < s_as_uint;
        Choice::from(res as u8)
    }
    #[test]
    fn test_is_high() {
        let mut csprng = rand_core::OsRng;
        for _i in 0..10 {
            let s = Scalar::random(&mut csprng);
            let res1 = s.is_high().unwrap_u8();
            let res2 = another_is_high(s).unwrap_u8();
            assert_eq!(res1, res2);
        }
    }

    #[test]
    fn test_encoding() {
        let one = Scalar::ONE;
        let t: U256 = one.into();
        assert_eq!(one, <Scalar as FromUintUnchecked>::from_uint_unchecked(t));
        assert_eq!(one, Scalar::from(t));
    }

    #[test]
    fn test_field_encoding() {
        let one = U256::from_le_slice(&Scalar::ONE.to_bytes());
        let t: FieldBytes<Dalek> = FieldBytesEncoding::encode_field_bytes(&one);
        let one_bis: U256 = FieldBytesEncoding::decode_field_bytes(&t);
        assert_eq!(one, one_bis);
    }

    #[test]
    fn test_scalar_encoding_decoding() {
        let mut rng = rand::thread_rng();
        let s = Scalar::random(&mut rng);
        let s_256: U256 = s.into();
        let s_again2: Scalar = s_256.into();

        let s_array: Array<u8, U32> = s.into();
        let field_bytes = U256::decode_field_bytes(&s_array);
        let s_again: Scalar = field_bytes.into();

        let s_field_bytes = s_256.encode_field_bytes();
        let s_uint = U256::decode_field_bytes(&s_field_bytes);
        let s_again3 = <Scalar as FromUintUnchecked>::from_uint_unchecked(s_uint);

        assert_eq!(s, s_again);
        assert_eq!(s, s_again2);
        assert_eq!(s, s_again3);
    }
}
