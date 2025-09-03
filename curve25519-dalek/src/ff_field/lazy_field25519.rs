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
    ) -> impl LazyField<<V as Add<CapacityUsed>>::Output, Capacity = Self::Capacity> {
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
