use elliptic_curve::{bigint::U256, consts::U32, Curve, CurveArithmetic, FieldBytesEncoding};

use crate::{constants::BASEPOINT_ORDER_PRIVATE, edwards::affine::AffinePoint, EdwardsPoint, Scalar};

/// QUESTION: I don't know where to put this singleton. Maybe in the crate's root?
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct Ed25519;

impl Curve for Ed25519 {
    type FieldBytesSize = U32;

    type Uint = U256;

    const ORDER: Self::Uint = U256::from_le_slice(&BASEPOINT_ORDER_PRIVATE.bytes);
}

impl CurveArithmetic for Ed25519 {
    type AffinePoint = AffinePoint;

    type ProjectivePoint = EdwardsPoint;

    type Scalar = Scalar;
}

impl FieldBytesEncoding<Ed25519> for U256 {}
