//! Hazardous materials with no semver guarantees.

use core::{
    fmt::Debug,
    iter::{Product, Sum},
    marker::PhantomData,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use typenum::{U0, Unsigned};

use ff::{Field, FromUniformBytes, PrimeField};

use crate::field::FieldElement as Underlying;

pub mod lazy_field;
mod lazy_field25519;
pub(crate) use lazy_field25519::UnderlyingCapacity;

/// An opaque view of the field element backend.
/*
  The `Underlying` struct is exposed via the `LazyField` trait. As the underlying field
  implementations don't have safe arithmetic, we don't want to expose their arithmetic, but we must
  expose _them_. We solve this by wrapping them into the following struct.
*/
#[derive(Clone, Copy)]
pub struct OpaqueFieldElement(Underlying);

/// A `FieldElement` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// The `FieldElement` type is an alias for one of the platform-specific
/// implementations. Its size and internals are not guaranteed to have
/// any specific properties and are not covered by semver.
///
/// Usage is recommended to be done via `LazyFieldWithCapacity<U3>` which is
/// comprehensive to all backends.
#[derive(Copy)]
pub struct FieldElement<U: Unsigned = U0>(pub(crate) OpaqueFieldElement, pub(crate) PhantomData<U>);
unsafe impl<U: Unsigned> Send for FieldElement<U> {}
unsafe impl<U: Unsigned> Sync for FieldElement<U> {}

impl<U: Unsigned> FieldElement<U> {
    pub(crate) const fn from(underlying: Underlying) -> Self {
        Self(OpaqueFieldElement(underlying), PhantomData)
    }

    /// Create a `FieldElement` within a `const` context.
    pub const fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let underlying = Underlying::from_bytes(bytes);
        let canonical_bytes: [u8; 32] = underlying.to_bytes();
        let mut i = 0;
        while i < 32 {
            if canonical_bytes[i] != bytes[i] {
                return None;
            }
            i += 1;
        }
        Some(Self::from(underlying))
    }
}

impl<U: Unsigned> ConstantTimeEq for FieldElement<U> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.0.ct_eq(&other.0.0)
    }
}
impl<U: Unsigned> PartialEq for FieldElement<U> {
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}
impl<U: Unsigned> Eq for FieldElement<U> {}

impl<U: Unsigned> Clone for FieldElement<U> {
    fn clone(&self) -> Self {
        *self
    }
}

impl Default for FieldElement {
    fn default() -> Self {
        Self::from(Underlying::ZERO)
    }
}

impl<U: Unsigned> Debug for FieldElement<U> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.0.fmt(f)
    }
}

impl<U: Unsigned> ConditionallySelectable for FieldElement<U> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self::from(<_>::conditional_select(&a.0.0, &b.0.0, choice))
    }
}

impl Add<&FieldElement> for FieldElement {
    type Output = Self;
    fn add(self, other: &Self) -> Self {
        let unreduced = &self.0.0 + &other.0.0;
        // Force a reduction
        Self::from(Underlying::from_bytes(&unreduced.to_bytes()))
    }
}
#[allow(clippy::op_ref)]
impl Add for FieldElement {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        self + &other
    }
}
impl AddAssign for FieldElement {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}
impl AddAssign<&FieldElement> for FieldElement {
    fn add_assign(&mut self, other: &Self) {
        *self = *self + other;
    }
}

impl Sub<&FieldElement> for FieldElement {
    type Output = Self;
    fn sub(self, other: &Self) -> Self {
        Self::from(&self.0.0 - &other.0.0)
    }
}
#[allow(clippy::op_ref)]
impl Sub for FieldElement {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        self - &other
    }
}
impl SubAssign for FieldElement {
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}
impl SubAssign<&FieldElement> for FieldElement {
    fn sub_assign(&mut self, other: &Self) {
        *self = *self - other;
    }
}

impl Neg for FieldElement {
    type Output = Self;
    fn neg(mut self) -> Self {
        // `negate` modifies in-place
        let () = self.0.0.negate();
        Self::from(self.0.0)
    }
}

impl Mul<&FieldElement> for FieldElement {
    type Output = Self;
    fn mul(self, other: &Self) -> Self {
        Self::from(&self.0.0 * &other.0.0)
    }
}
#[allow(clippy::op_ref)]
impl Mul for FieldElement {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        self * &other
    }
}
impl MulAssign for FieldElement {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}
impl MulAssign<&FieldElement> for FieldElement {
    fn mul_assign(&mut self, other: &Self) {
        *self = *self * other;
    }
}

impl Sum for FieldElement {
    fn sum<I: Iterator<Item = FieldElement>>(iter: I) -> Self {
        let mut res = FieldElement::ZERO;
        for item in iter {
            res += item;
        }
        res
    }
}
impl<'a> Sum<&'a FieldElement> for FieldElement {
    fn sum<I: Iterator<Item = &'a FieldElement>>(iter: I) -> Self {
        iter.copied().sum()
    }
}

impl Product<FieldElement> for FieldElement {
    fn product<I: Iterator<Item = FieldElement>>(iter: I) -> Self {
        let mut res = FieldElement::ONE;
        for item in iter {
            res *= item;
        }
        res
    }
}
impl<'a> Product<&'a FieldElement> for FieldElement {
    fn product<I: Iterator<Item = &'a FieldElement>>(iter: I) -> Self {
        iter.copied().product()
    }
}

impl Field for FieldElement {
    const ZERO: Self = Self::from(Underlying::ZERO);
    const ONE: Self = Self::from(Underlying::ONE);

    fn try_from_rng<R: rand_core::TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        let mut bytes = [0; 64];
        rng.try_fill_bytes(&mut bytes)?;
        Ok(Self::from(Underlying::from_bytes_wide(&bytes)))
    }

    fn square(&self) -> Self {
        *self * self
    }

    fn double(&self) -> Self {
        *self + self
    }

    fn invert(&self) -> CtOption<Self> {
        CtOption::new(Self::from(self.0.0.invert()), !self.is_zero())
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        let res = Underlying::sqrt_ratio_i(&num.0.0, &div.0.0);
        (res.0, Self::from(res.1))
    }
}

impl PrimeField for FieldElement {
    type Repr = [u8; 32];

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let res = Self::from(Underlying::from_bytes(&repr));
        CtOption::new(res, repr.ct_eq(&res.0.0.to_bytes()))
    }

    fn from_repr_vartime(repr: Self::Repr) -> Option<Self> {
        Self::from_repr(repr).into()
    }

    fn to_repr(&self) -> Self::Repr {
        self.0.0.to_bytes()
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.0.0.to_bytes()[0] & 1)
    }

    const MODULUS: &'static str =
        "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed";
    const NUM_BITS: u32 = 255;
    const CAPACITY: u32 = 254;

    const TWO_INV: Self = Self::from(Underlying::from_bytes(&[
        247, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 63,
    ]));
    const MULTIPLICATIVE_GENERATOR: Self = Self::from(Underlying::from_bytes(&[
        2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0,
    ]));
    const S: u32 = 2;
    const ROOT_OF_UNITY: Self = Self::from(Underlying::from_bytes(&[
        176, 160, 14, 74, 39, 27, 238, 196, 120, 228, 47, 173, 6, 24, 67, 47, 167, 215, 251, 61,
        153, 0, 77, 43, 11, 223, 193, 79, 128, 36, 131, 43,
    ]));
    const ROOT_OF_UNITY_INV: Self = Self::from(Underlying::from_bytes(&[
        61, 95, 241, 181, 216, 228, 17, 59, 135, 27, 208, 82, 249, 231, 188, 208, 88, 40, 4, 194,
        102, 255, 178, 212, 244, 32, 62, 176, 127, 219, 124, 84,
    ]));
    const DELTA: Self = Self::from(Underlying::from_bytes(&[
        16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0,
    ]));
}

#[cfg(feature = "group-bits")]
impl ff::PrimeFieldBits for FieldElement {
    type ReprBits = [u8; 32];

    fn to_le_bits(&self) -> ff::FieldBits<Self::ReprBits> {
        self.to_repr().into()
    }

    fn char_le_bits() -> ff::FieldBits<Self::ReprBits> {
        [
            237, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 127,
        ]
        .into()
    }
}

impl From<u64> for FieldElement {
    fn from(a: u64) -> Self {
        // Portable method to convert a u64 to a FieldElement,
        // regardless of the internal representation
        let mut bytes = [0; 32];
        bytes[..8].copy_from_slice(&a.to_le_bytes());
        Self::from(Underlying::from_bytes(&bytes))
    }
}

impl FromUniformBytes<64> for FieldElement {
    fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        Self::from(Underlying::from_bytes_wide(bytes))
    }
}

#[cfg(feature = "zeroize")]
impl<U: Unsigned> zeroize::Zeroize for FieldElement<U> {
    fn zeroize(&mut self) {
        self.0.0.zeroize();
    }
}
