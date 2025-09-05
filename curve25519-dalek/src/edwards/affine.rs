use super::{CompressedEdwardsY, EdwardsPoint};
use crate::traits::Identity;
use crate::{Scalar, field::FieldElement};
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
    /// Create an `AffinePoint` from its coordinates.
    ///
    /// Returns `None` if the point is off-curve.
    ///
    /// This function runs in variable time.
    #[cfg(feature = "hazmat")]
    pub const fn from_coordinates(x: FieldElement, y: FieldElement) -> Option<Self> {
        let x_sq = x.const_mul(&x);
        let y_sq = y.const_mul(&y);

        let mut lhs = crate::constants::MINUS_ONE.const_mul(&x_sq);
        lhs.const_add_assign(&y_sq);

        let mut rhs = FieldElement::ONE;
        rhs.const_add_assign(&crate::constants::EDWARDS_D.const_mul(&x_sq.const_mul(&y_sq)));

        let lhs: [u8; 32] = lhs.to_bytes();
        let rhs: [u8; 32] = rhs.to_bytes();

        let mut i = 0;
        while i < 32 {
            if lhs[i] != rhs[i] {
                return None;
            }
            i += 1;
        }
        Some(Self { x, y })
    }

    /// Convert to extended coordinates.
    pub const fn to_edwards(self) -> EdwardsPoint {
        EdwardsPoint {
            X: self.x,
            Y: self.y,
            Z: FieldElement::ONE,
            T: self.x.const_mul(&self.y),
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
