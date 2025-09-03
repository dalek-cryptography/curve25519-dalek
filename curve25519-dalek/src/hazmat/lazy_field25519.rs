use core::ops::Add;

use typenum::{U0, Unsigned, type_operators::IsLessOrEqual};

use super::{FieldElement, OpaqueFieldElement, lazy_field::*};
use crate::field::FieldElement as Underlying;

type ReducibleOutput = FieldElement<U0>;
impl<U: Unsigned> Reducible for FieldElement<U>
where
    FieldElement<U>: LazyField<U>,
{
    /// The reduced element.
    type Output = ReducibleOutput;
    /// Reduce to a reduced element.
    fn reduce(&self) -> Self::Output {
        let res = ReducibleOutput::from(Underlying::from_bytes(&self.0.0.to_bytes()));
        // For God knows what reason, Rust doesn't realize this is the same type
        unsafe { *((&res as *const _) as *const _) }
    }
}

/// Sealed trait for the capacity of the `FieldElement` backend.
// Rust believe this is in a public API, as it... technically is? so it must be `pub`.
pub trait UnderlyingCapacity {
    type Capacity: Unsigned;
}

impl<CapacityUsed: Unsigned> LazyField<CapacityUsed> for FieldElement<CapacityUsed> {
    type Capacity = <Underlying as UnderlyingCapacity>::Capacity;
    type Underlying = OpaqueFieldElement;

    fn as_underlying(&self) -> &Self::Underlying {
        &self.0
    }

    fn add<
        V: Unsigned
            + Add<
                CapacityUsed,
                Output: Unsigned + IsLessOrEqual<<Underlying as UnderlyingCapacity>::Capacity>,
            >,
        T: LazyField<V, Underlying = Self::Underlying>,
    >(
        self,
        other: &T,
    ) -> impl Reducible<Output = <Self as Reducible>::Output>
    + LazyField<
        <V as Add<CapacityUsed>>::Output,
        Capacity = Self::Capacity,
        Underlying = Self::Underlying,
    > {
        FieldElement::<<V as Add<CapacityUsed>>::Output>::from(&self.0.0 + &other.as_underlying().0)
    }

    fn mul<V: Unsigned, T: LazyField<V, Underlying = Self::Underlying>>(
        self,
        other: &T,
    ) -> <Self as Reducible>::Output {
        let unreduced = &self.0.0 * &other.as_underlying().0;
        FieldElement::from(Underlying::from_bytes(&unreduced.to_bytes()))
    }
}

#[cfg(test)]
mod tests {
    use rand_core::{OsRng, TryRngCore};
    use typenum::U3;

    use crate::hazmat::lazy_field::{EagerField, LazyField, LazyFieldWithCapacity, Reducible};

    #[test]
    fn three_add_and_then_mul() {
        use crate::hazmat::FieldElement;
        use core::marker::PhantomData;
        use ff::Field;

        let mut rng = OsRng.unwrap_err();

        let a = FieldElement::random(&mut rng);
        let b = FieldElement::random(&mut rng);
        let c = FieldElement::random(&mut rng);
        let d = FieldElement::random(&mut rng);
        let e = FieldElement::random(&mut rng);
        let f = FieldElement::random(&mut rng);
        let expected = (a + b + c) * (d + e + f);

        assert_eq!(a.add(&b).add(&c).mul(&d.add(&e).add(&f)), expected);

        assert_eq!(
            EagerField(a, PhantomData::<typenum::U0>)
                .add(&EagerField(b, PhantomData::<typenum::U0>))
                .add(&EagerField(c, PhantomData::<typenum::U0>))
                .mul(
                    &EagerField(d, PhantomData::<typenum::U0>)
                        .add(&EagerField(e, PhantomData::<typenum::U0>))
                        .add(&EagerField(f, PhantomData::<typenum::U0>))
                )
                .0,
            expected
        );
    }
}
