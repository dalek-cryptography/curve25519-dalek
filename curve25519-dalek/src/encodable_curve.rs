use core::ops::Not;
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
use elliptic_curve::ScalarPrimitive;
use subtle::Choice;
use subtle::CtOption;

use crate::constants::BASEPOINT_ORDER_PRIVATE;
use crate::EdwardsPoint;
use crate::Scalar;

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct Dalek {}

impl Curve for Dalek {
    type FieldBytesSize = U32;
    type Uint = U256;
    const ORDER: Self::Uint = U256::from_le_slice(BASEPOINT_ORDER_PRIVATE.as_bytes());
}

impl MulByGenerator for EdwardsPoint {}

// Impls for Scalar

impl AsRef<Scalar> for Scalar {
    fn as_ref(&self) -> &Scalar {
        self
    }
}

// NOTE: ScalarPrimitive is big endian. Dalek uses little endian
impl From<ScalarPrimitive<Dalek>> for Scalar {
    fn from(value: ScalarPrimitive<Dalek>) -> Self {
        Scalar::from_bytes_mod_order(value.to_uint().to_le_bytes())
    }
}

impl FromUintUnchecked for Scalar {
    // CHECK! Is the 4 correct?
    type Uint = elliptic_curve::bigint::Uint<4>;
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
    //FIXME: Can we do better?
    fn is_high(&self) -> Choice {
        let t = self.double().is_canonical();
        Choice::not(t)
    }
}

impl PartialOrd for Scalar {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        for (s, o) in self.bits_le().rev().zip(other.bits_le().rev()) {
            match (s, o) {
                (true, false) => return Some(core::cmp::Ordering::Greater),
                (false, true) => return Some(core::cmp::Ordering::Less),
                _ => (),
            };
        }
        return Some(core::cmp::Ordering::Equal);
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
        U256::from_be_byte_array(*field_bytes)
    }

    fn encode_field_bytes(&self) -> FieldBytes<Dalek> {
        self.to_be_byte_array()
    }
}
