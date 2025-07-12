use core::ops::Add;

use typenum::{U0, Unsigned, type_operators::IsLessOrEqual};

use crate::{FieldElement, field::FieldElement as Underlying, lazy_field::*};

type ReducibleOutput = FieldElement<U0>;
impl<U: Unsigned> Reducible for FieldElement<U>
where
    FieldElement<U>: LazyField<U>,
{
    /// The reduced element.
    type Output = ReducibleOutput;
    /// Reduce to a reduced element.
    fn reduce(&self) -> Self::Output {
        let res = ReducibleOutput::from(Underlying::from_bytes(&self.0.to_bytes()));
        // For God knows what reason, Rust doesn't realize this is the same type
        unsafe { *((&res as *const _) as *const _) }
    }
}

/// Sealed trait for the capacity of the `FieldElement` backend.
pub trait UnderlyingCapacity {
    type Capacity: Unsigned;
}

impl<CapacityUsed: Unsigned> LazyField<CapacityUsed> for FieldElement<CapacityUsed> {
    type Capacity = <Underlying as UnderlyingCapacity>::Capacity;
    type Underlying = Underlying;

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
        FieldElement::<<V as Add<CapacityUsed>>::Output>::from(&self.0 + other.as_underlying())
    }

    fn mul<V: Unsigned, T: LazyField<V, Underlying = Self::Underlying>>(
        self,
        other: &T,
    ) -> <Self as Reducible>::Output {
        let unreduced = &self.0 * other.as_underlying();
        FieldElement::from(Underlying::from_bytes(&unreduced.to_bytes()))
    }
}
