use core::ops::Add;

use typenum::{U1, Unsigned, type_operators::IsLessOrEqual};

use super::{FieldElement, OpaqueFieldElement, lazy_field::*};
use crate::field::FieldElement as Underlying;

type ReducibleOutput = FieldElement<U1>;
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
    ) -> impl LazyField<
        <V as Add<CapacityUsed>>::Output,
        Capacity = Self::Capacity,
        Underlying = Self::Underlying,
        Output = <Self as Reducible>::Output,
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
    use crate::hazmat::lazy_field::{EagerField, LazyField, LazyFieldWithCapacity, Reducible};
    use typenum::{B1, U2, type_operators::IsLessOrEqual};

    fn add_pair_then_mul<F: LazyFieldWithCapacity<U2>>(
        a: F,
        b: F,
        c: F,
        d: F,
    ) -> <F as Reducible>::Output
    where
        U2: IsLessOrEqual<F::Capacity, Output = B1>,
    {
        let ab = a.add(&b);
        let cd = c.add(&d);
        ab.mul(&cd)
    }

    #[test]
    fn lazy_add_then_mul() {
        use crate::hazmat::FieldElement;
        use core::marker::PhantomData;
        use ff::Field;
        use rand_core::{OsRng, TryRngCore};

        let mut rng = OsRng.unwrap_err();

        for _ in 0..10_000 {
            let a = FieldElement::random(&mut rng);
            let b = FieldElement::random(&mut rng);
            let c = FieldElement::random(&mut rng);
            let d = FieldElement::random(&mut rng);
            let expected = (a + b) * (c + d);

            assert_eq!(LazyField::add(a, &b).mul(&LazyField::add(c, &d)), expected);
            assert_eq!(add_pair_then_mul(a, b, c, d), expected);

            let a = EagerField(a, PhantomData::<typenum::U1>);
            let b = EagerField(b, PhantomData::<typenum::U1>);
            let c = EagerField(c, PhantomData::<typenum::U1>);
            let d = EagerField(d, PhantomData::<typenum::U1>);

            assert_eq!(
                LazyField::add(a, &b).mul(&LazyField::add(c, &d)).0,
                expected
            );
            assert_eq!(add_pair_then_mul(a, b, c, d).0, expected);
        }
    }
}
