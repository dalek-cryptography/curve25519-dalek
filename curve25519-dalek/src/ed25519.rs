use elliptic_curve::{bigint::U256, consts::U32, Curve, CurveArithmetic, FieldBytesEncoding};

use crate::{constants::BASEPOINT_ORDER_PRIVATE, edwards::CompressedEdwardsY, EdwardsPoint, Scalar};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct Ed25519;

impl Curve for Ed25519 {
    type FieldBytesSize = U32;

    type Uint = U256;

    const ORDER: Self::Uint = U256::from_le_slice(&BASEPOINT_ORDER_PRIVATE.bytes);
}

impl CurveArithmetic for Ed25519 {
    type AffinePoint = CompressedEdwardsY;

    type ProjectivePoint = EdwardsPoint;

    type Scalar = Scalar;
}

impl FieldBytesEncoding<Ed25519> for U256 {}
