use super::{CompressedEdwardsY, EdwardsPoint};
use crate::traits::Identity;
use crate::{field::FieldElement, Scalar};
use core::ops::Mul;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

#[cfg(feature = "zeroize")]
use zeroize::DefaultIsZeroes;

/// Affine Edwards point on untwisted curve.
#[derive(Copy, Clone, Debug)]
pub struct AffinePoint {
    pub(super) x: FieldElement,
    pub(super) y: FieldElement,
}

impl ConstantTimeEq for AffinePoint {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.x.ct_eq(&other.x) & self.y.ct_eq(&other.y)
    }
}

impl ConditionallySelectable for AffinePoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            x: FieldElement::conditional_select(&a.x, &b.x, choice),
            y: FieldElement::conditional_select(&a.y, &b.y, choice),
        }
    }
}

impl Default for AffinePoint {
    fn default() -> AffinePoint {
        AffinePoint::identity()
    }
}

impl Identity for AffinePoint {
    fn identity() -> AffinePoint {
        AffinePoint {
            x: FieldElement::ZERO,
            y: FieldElement::ONE,
        }
    }
}

impl PartialEq for AffinePoint {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Eq for AffinePoint {}

#[cfg(feature = "zeroize")]
impl DefaultIsZeroes for AffinePoint {}

impl AffinePoint {
    /// Convert to extended coordinates.
    pub fn to_edwards(self) -> EdwardsPoint {
        EdwardsPoint {
            X: self.x,
            Y: self.y,
            Z: FieldElement::ONE,
            T: &self.x * &self.y,
        }
    }

    /// Compress affine Edwards coordinates into `CompressedEdwardsY` format.
    #[inline]
    pub fn compress(self) -> CompressedEdwardsY {
        let mut s = self.y.to_bytes();
        s[31] ^= self.x.is_negative().unwrap_u8() << 7;
        CompressedEdwardsY(s)
    }
}

impl Mul<AffinePoint> for Scalar {
    type Output = EdwardsPoint;

    #[inline]
    fn mul(self, rhs: AffinePoint) -> EdwardsPoint {
        self * &rhs
    }
}

impl Mul<&AffinePoint> for Scalar {
    type Output = EdwardsPoint;

    #[inline]
    fn mul(self, rhs: &AffinePoint) -> EdwardsPoint {
        rhs.to_edwards() * self
    }
}

#[cfg(test)]
mod tests {
    use super::{AffinePoint, EdwardsPoint, Identity};
    use crate::constants;

    #[test]
    fn identity_conversion() {
        assert_eq!(
            AffinePoint::identity().to_edwards(),
            EdwardsPoint::identity()
        );
    }

    #[test]
    fn generator_round_trip() {
        let basepoint = constants::ED25519_BASEPOINT_POINT;
        assert_eq!(basepoint.to_affine().to_edwards(), basepoint);
    }
}
