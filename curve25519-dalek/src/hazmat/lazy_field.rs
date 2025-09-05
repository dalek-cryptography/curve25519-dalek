//! Traits for working with fields which only perform reduction as needed.

use core::{fmt::Debug, ops::Add};

use typenum::{B1, U1, Unsigned, type_operators::IsLessOrEqual};

use ff::Field;

mod eager;
pub use eager::*;

/// An element which can be reduced.
pub trait Reducible {
    /// The reduced element.
    type Output: Field + LazyField<U1>;
    /// Reduce to a reduced element.
    fn reduce(&self) -> Self::Output;
}

/// An element of a field which is only reduced as instructed.
///
/// By only reducing as instructed, when necessary, unnecessary reductions can be optimized out.
/// In order to ensure a safe API, `typenum` is used to track the number of operations performed
/// and ensure arithmetic remains well-defined.
/*
  There's a oddity here where `CapacityUsed` is not bound to be less than `Capacity`. Such elements
  aren't obtainable nor usable via the `add` function however, so it shouldn't be an issue?
  Attempting to introduce that bound overloads the Rust type system.
*/
pub trait LazyField<CapacityUsed: Unsigned>:
    Sized + Eq + Copy + Clone + Send + Sync + Debug + 'static + Reducible
{
    /// The amount of operations which can be performed while operations remain well-defined.
    type Capacity: Unsigned;
    /// The non-generic type underlying this which presumably lacks inherent capacity checks.
    type Underlying;

    /// A reference to the underlying type.
    ///
    /// The underlying type is allowed to have undefined semantics and MUST NOT be used directly.
    fn as_underlying(&self) -> &Self::Underlying;

    // The type corresponding to a certain usage of capacity.
    // type ForCapacityUsed<TheoreticalCapacityUsed: Unsigned>: LazyField<TheoreticalCapacityUsed, >

    /// Add two lazy elements where the result remains within the capacity.
    fn add<
        V: Unsigned + Add<CapacityUsed, Output: Unsigned + IsLessOrEqual<Self::Capacity, Output = B1>>,
        T: LazyField<V, Underlying = Self::Underlying>,
    >(
        self,
        other: &T,
    ) -> impl LazyField<
        <V as Add<CapacityUsed>>::Output,
        Capacity = Self::Capacity,
        Underlying = Self::Underlying,
        Output = <Self as Reducible>::Output,
    >;

    /// Multiply two lazy elements.
    ///
    /// This will always return a reduced field element.
    fn mul<V: Unsigned, T: LazyField<V, Underlying = Self::Underlying>>(
        self,
        other: &T,
    ) -> <Self as Reducible>::Output;
}

/// A lazy field with _at least_ the specified amount of capacity.
///
/// When working generically with fields, the amount of capacity will differ. This method sets a
/// minimum bound on the capacity, allowing taking advantage of the bound regardless of the field.
///
/// `LazyFieldWithCapacity<U1>` is _recommended_ due to the widespread popularity of 255-bit
/// fields.
pub trait LazyFieldWithCapacity<U: Unsigned + IsLessOrEqual<Self::Capacity, Output = B1>>:
    LazyField<U1>
{
}
impl<U: Unsigned + IsLessOrEqual<Self::Capacity, Output = B1>, F: LazyField<U1>>
    LazyFieldWithCapacity<U> for F
{
}
