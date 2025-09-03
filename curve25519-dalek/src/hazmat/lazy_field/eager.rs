//! A safe exposure of the various `FieldElement` backends, with a unified API.

use core::{
    fmt::Debug,
    iter::{Product, Sum},
    marker::PhantomData,
    ops::*,
};

use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use typenum::{B1, U0, U256, Unsigned, type_operators::IsLessOrEqual};

use rand_core::{RngCore, TryRngCore};

use ff::Field;

use super::*;

/// A wrapper for any field so it may satisfy the `LazyField` traits.
///
/// This allows developers to entirely use the `LazyField` traits, as all existing `Field`
/// implementations may be used with them via this compatibility shim.
#[derive(Copy, Clone, Default)]
pub struct EagerField<U: Unsigned, F: Field>(pub F, pub PhantomData<U>);

// Avoids `U: Send + Sync + Unsigned`
unsafe impl<U: Unsigned, F: Field> Send for EagerField<U, F> {}
unsafe impl<U: Unsigned, F: Field> Sync for EagerField<U, F> {}

impl<U: Unsigned, F: Field> Debug for EagerField<U, F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("EagerField")
            .field("0", &self.0)
            .field("1", &self.1)
            .finish()
    }
}

impl<F: Field> EagerField<U0, F> {
    const fn from(field: F) -> Self {
        Self(field, PhantomData)
    }
}

impl<F: Field> ConditionallySelectable for EagerField<U0, F> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self::from(<_>::conditional_select(&a.0, &b.0, choice))
    }
}
impl<U: Unsigned, F: Field> ConstantTimeEq for EagerField<U, F> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}
impl<U: Unsigned, F: Field> PartialEq for EagerField<U, F> {
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}
impl<U: Unsigned, F: Field> Eq for EagerField<U, F> {}
impl<F: Field> Neg for EagerField<U0, F> {
    type Output = Self;
    fn neg(self) -> Self {
        Self::from(self.0.neg())
    }
}
impl<F: Field> Add for EagerField<U0, F> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self::from(self.0.add(other.0))
    }
}
impl<F: Field> Sub for EagerField<U0, F> {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self::from(self.0.sub(other.0))
    }
}
impl<F: Field> Mul for EagerField<U0, F> {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        Self::from(self.0.mul(other.0))
    }
}
impl<F: Field> Sum for EagerField<U0, F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self::from(F::sum(iter.map(|item| item.0)))
    }
}
impl<F: Field> Product for EagerField<U0, F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        Self::from(F::product(iter.map(|item| item.0)))
    }
}
impl<'a, F: Field> Add<&'a Self> for EagerField<U0, F> {
    type Output = Self;
    fn add(self, other: &'a Self) -> Self {
        Self::from(self.0.add(&other.0))
    }
}
impl<'a, F: Field> Sub<&'a Self> for EagerField<U0, F> {
    type Output = Self;
    fn sub(self, other: &'a Self) -> Self {
        Self::from(self.0.sub(&other.0))
    }
}
impl<'a, F: Field> Mul<&'a Self> for EagerField<U0, F> {
    type Output = Self;
    fn mul(self, other: &'a Self) -> Self {
        Self::from(self.0.mul(&other.0))
    }
}
impl<'a, F: Field> Sum<&'a Self> for EagerField<U0, F> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        Self::from(F::sum(iter.map(|item| &item.0)))
    }
}
impl<'a, F: Field> Product<&'a Self> for EagerField<U0, F> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        Self::from(F::product(iter.map(|item| &item.0)))
    }
}
impl<F: Field> AddAssign for EagerField<U0, F> {
    fn add_assign(&mut self, other: Self) {
        self.0.add_assign(other.0);
    }
}
impl<F: Field> SubAssign for EagerField<U0, F> {
    fn sub_assign(&mut self, other: Self) {
        self.0.sub_assign(other.0);
    }
}
impl<F: Field> MulAssign for EagerField<U0, F> {
    fn mul_assign(&mut self, other: Self) {
        self.0.mul_assign(other.0);
    }
}
impl<'a, F: Field> AddAssign<&'a Self> for EagerField<U0, F> {
    fn add_assign(&mut self, other: &'a Self) {
        self.0.add_assign(&other.0);
    }
}
impl<'a, F: Field> SubAssign<&'a Self> for EagerField<U0, F> {
    fn sub_assign(&mut self, other: &'a Self) {
        self.0.sub_assign(&other.0);
    }
}
impl<'a, F: Field> MulAssign<&'a Self> for EagerField<U0, F> {
    fn mul_assign(&mut self, other: &'a Self) {
        self.0.mul_assign(&other.0);
    }
}
impl<F: Field> Field for EagerField<U0, F> {
    const ZERO: Self = Self::from(F::ZERO);
    const ONE: Self = Self::from(F::ONE);
    fn try_from_rng<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        F::try_from_rng(rng).map(Self::from)
    }
    fn square(&self) -> Self {
        Self::from(self.0.square())
    }
    fn double(&self) -> Self {
        Self::from(self.0.double())
    }
    fn invert(&self) -> CtOption<Self> {
        self.0.invert().map(Self::from)
    }
    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        let (choice, root) = F::sqrt_ratio(&num.0, &div.0);
        (choice, Self::from(root))
    }
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        Self::from(F::random(rng))
    }
    fn is_zero(&self) -> Choice {
        self.0.is_zero()
    }
    fn is_zero_vartime(&self) -> bool {
        self.0.is_zero_vartime()
    }
    fn cube(&self) -> Self {
        Self::from(self.0.cube())
    }
    fn sqrt_alt(&self) -> (Choice, Self) {
        let (choice, root) = self.0.sqrt_alt();
        (choice, Self::from(root))
    }
    fn sqrt(&self) -> CtOption<Self> {
        self.0.sqrt().map(Self::from)
    }
    fn pow<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        Self::from(self.0.pow(exp))
    }
    fn pow_vartime<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        Self::from(self.0.pow_vartime(exp))
    }
}

impl<U: Unsigned, F: Field> Reducible for EagerField<U, F> {
    type Output = EagerField<U0, F>;
    fn reduce(&self) -> Self::Output {
        Self::Output::from(self.0)
    }
}

impl<CapacityUsed: Unsigned + IsLessOrEqual<U256, Output = B1>, F: Field> LazyField<CapacityUsed>
    for EagerField<CapacityUsed, F>
{
    // `U::MAX` does not exist. This should be well-defined/fully implemented and excessive
    type Capacity = U256;
    type Underlying = F;

    fn as_underlying(&self) -> &Self::Underlying {
        &self.0
    }

    fn add<
        V: Unsigned + Add<CapacityUsed, Output: Unsigned + IsLessOrEqual<Self::Capacity, Output = B1>>,
        T: LazyField<V, Underlying = Self::Underlying>,
    >(
        self,
        other: &T,
    ) -> impl LazyField<<V as Add<CapacityUsed>>::Output, Capacity = Self::Capacity> {
        EagerField::<<V as Add<CapacityUsed>>::Output, F>(
            self.0 + other.as_underlying(),
            PhantomData,
        )
    }

    fn mul<V: Unsigned, T: LazyField<V, Underlying = Self::Underlying>>(
        self,
        other: &T,
    ) -> <Self as Reducible>::Output {
        EagerField::from(self.0 * other.as_underlying())
    }
}

#[cfg(feature = "zeroize")]
impl<U: Unsigned, F: zeroize::Zeroize + Field> zeroize::Zeroize for EagerField<U, F> {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}
