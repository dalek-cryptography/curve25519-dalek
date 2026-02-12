//! Tell Verus what Choice and CtOption do
use subtle::{Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::backend::serial::u64::field::FieldElement51;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs::{fe51_as_canonical_nat, fe51_limbs_bounded, field_neg};

use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExChoice(Choice);

/*** External trait specification for subtle::ConstantTimeEq ***/

#[verifier::external_trait_specification]
pub trait ExConstantTimeEq {
    type ExternalTraitSpecificationFor: ConstantTimeEq;

    // Note: Implementations should define their own preconditions via a companion spec trait
    // For EdwardsPoint, see ConstantTimeEqSpecImpl in edwards.rs
    fn ct_eq(&self, other: &Self) -> Choice;
}

/*** External type specification for subtle::CtOption ***/

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[allow(dead_code)]
pub struct ExCtOption<T>(CtOption<T>);

/// Spec-level view of Choice as a boolean
/// true = Choice(1), false = Choice(0)
pub uninterp spec fn choice_is_true(c: Choice) -> bool;

pub assume_specification[ Choice::from ](u: u8) -> (c: Choice)
    ensures
        (u == 1) == choice_is_true(c),
;

pub assume_specification[ Choice::unwrap_u8 ](c: &Choice) -> (u: u8)
    ensures
        choice_is_true(*c) ==> u == 1u8,
        !choice_is_true(*c) ==> u == 0u8,
;

// VERIFICATION NOTE: For other external functions, we use wrapper functions because:
// - Generic functions don't work well with assume_specification
// - Trait implementations on arrays have issues with assume_specification
/// Wrapper for conditional_select on u64
#[verifier::external_body]
pub fn select(a: &u64, b: &u64, c: Choice) -> (res: u64)
    ensures
        !choice_is_true(c) ==> res == *a,
        choice_is_true(c) ==> res == *b,
{
    u64::conditional_select(a, b, c)
}

/// Wrapper for conditional_select on u8
#[verifier::external_body]
pub fn select_u8(a: &u8, b: &u8, c: Choice) -> (res: u8)
    ensures
        !choice_is_true(c) ==> res == *a,
        choice_is_true(c) ==> res == *b,
{
    u8::conditional_select(a, b, c)
}

/// Wrapper for ct_eq on byte arrays
#[verifier::external_body]
pub fn ct_eq_bytes32(a: &[u8; 32], b: &[u8; 32]) -> (c: Choice)
    ensures
        choice_is_true(c) == (*a == *b),
{
    a.ct_eq(b)
}

/// Wrapper for ct_eq on limb arrays (5 u64s for FieldElement51)
#[verifier::external_body]
pub fn ct_eq_limbs5(a: &[u64; 5], b: &[u64; 5]) -> (c: Choice)
    ensures
        choice_is_true(c) == (*a == *b),
{
    a.ct_eq(b)
}

/// Wrapper for ct_eq on u8
#[verifier::external_body]
pub fn ct_eq_u8(a: &u8, b: &u8) -> (c: Choice)
    ensures
        choice_is_true(c) == (*a == *b),
{
    a.ct_eq(b)
}

/// Wrapper for ct_eq on u16
#[verifier::external_body]
pub fn ct_eq_u16(a: &u16, b: &u16) -> (c: Choice)
    ensures
        choice_is_true(c) == (*a == *b),
{
    a.ct_eq(b)
}

/// Wrapper for Choice::into (converts Choice to bool)
#[verifier::external_body]
pub fn choice_into(c: Choice) -> (b: bool)
    ensures
        b == choice_is_true(c),
{
    c.into()
}

/// Wrapper for bitwise AND on Choice
#[verifier::external_body]
pub fn choice_and(a: Choice, b: Choice) -> (c: Choice)
    ensures
        choice_is_true(c) == (choice_is_true(a) && choice_is_true(b)),
{
    use core::ops::BitAnd;
    a.bitand(b)
}

/// Wrapper for bitwise NOT on Choice
#[verifier::external_body]
pub fn choice_not(a: Choice) -> (c: Choice)
    ensures
        choice_is_true(c) == !choice_is_true(a),
{
    use core::ops::Not;
    a.not()
}

/// Wrapper for bitwise OR on Choice
#[verifier::external_body]
pub fn choice_or(a: Choice, b: Choice) -> (c: Choice)
    ensures
        choice_is_true(c) == (choice_is_true(a) || choice_is_true(b)),
{
    use core::ops::BitOr;
    a.bitor(b)
}

/*** CtOption specifications ***/

/// Spec-level view of CtOption::is_some
pub uninterp spec fn ct_option_has_value<T>(opt: CtOption<T>) -> bool;

/// Spec-level view of CtOption::unwrap - what value it contains
pub uninterp spec fn ct_option_value<T>(opt: CtOption<T>) -> T;

/// Wrapper function for CtOption::new
#[verifier::external_body]
pub fn ct_option_new<T>(value: T, choice: Choice) -> (result: CtOption<T>)
    ensures
        ct_option_has_value(result) == choice_is_true(choice),
        ct_option_value(result) == value,
{
    CtOption::new(value, choice)
}

/// Wrapper function for CtOption::is_some
#[verifier::external_body]
pub fn ct_option_is_some<T>(opt: &CtOption<T>) -> (c: Choice)
    ensures
        choice_is_true(c) == ct_option_has_value(*opt),
{
    opt.is_some()
}

/// Wrapper function for CtOption::is_none
#[verifier::external_body]
pub fn ct_option_is_none<T>(opt: &CtOption<T>) -> (c: Choice)
    ensures
        choice_is_true(c) == !ct_option_has_value(*opt),
{
    opt.is_none()
}

/// Wrapper function for CtOption::unwrap
#[verifier::external_body]
pub fn ct_option_unwrap<T>(opt: CtOption<T>) -> (val: T)
    requires
        ct_option_has_value(opt),
    ensures
        val == ct_option_value(opt),
{
    opt.unwrap()
}

/*** ConditionallySelectable specifications for u64 ***/

// Specification for u64::conditional_swap
pub assume_specification[ <u64 as ConditionallySelectable>::conditional_swap ](
    a: &mut u64,
    b: &mut u64,
    choice: Choice,
)
    ensures
        !choice_is_true(choice) ==> (*a == *old(a) && *b == *old(b)),
        choice_is_true(choice) ==> (*a == *old(b) && *b == *old(a)),
;

// Specification for u64::conditional_assign
pub assume_specification[ <u64 as ConditionallySelectable>::conditional_assign ](
    a: &mut u64,
    b: &u64,
    choice: Choice,
)
    ensures
        !choice_is_true(choice) ==> *a == *old(a),
        choice_is_true(choice) ==> *a == *b,
;

/// Wrapper for conditional_select on u64
#[verifier::external_body]
pub fn conditional_select_u64(a: &u64, b: &u64, choice: Choice) -> (res: u64)
    ensures
        !choice_is_true(choice) ==> res == *a,
        choice_is_true(choice) ==> res == *b,
{
    select(a, b, choice)
}

/// Wrapper for conditional_swap on u64
#[verifier::external_body]
pub fn conditional_swap_u64(a: &mut u64, b: &mut u64, choice: Choice)
    ensures
        !choice_is_true(choice) ==> (*a == *old(a) && *b == *old(b)),
        choice_is_true(choice) ==> (*a == *old(b) && *b == *old(a)),
{
    u64::conditional_swap(a, b, choice)
}

/// Wrapper for conditional_assign on u64
#[verifier::external_body]
pub fn conditional_assign_u64(a: &mut u64, b: &u64, choice: Choice)
    ensures
        !choice_is_true(choice) ==> *a == *old(a),
        choice_is_true(choice) ==> *a == *b,
{
    a.conditional_assign(b, choice)
}

/// Generic wrapper for conditional_negate on types implementing ConditionallyNegatable
/// Used for: ProjectiveNielsPoint, AffineNielsPoint in window.rs
/// For FieldElement51 with proper specs, we use conditional_negate_field_element instead.
#[verifier::external_body]
pub fn conditional_negate_generic<T>(a: &mut T, choice: Choice) where
    T: subtle::ConditionallyNegatable,
 {
    a.conditional_negate(choice);
}

/// Specialized wrapper for conditional_negate on FieldElement51 with proper specs.
/// Use this when you need verified limb bounds and functional correctness guarantees.
///
/// # How reduction happens
///
/// The `subtle` crate provides a blanket impl of `ConditionallyNegatable` for any type
/// implementing `ConditionallySelectable` + `Neg`. When called, it invokes our local impls:
///
/// ```text
/// subtle::conditional_negate()  // blanket impl
///     ├─► Neg::neg()            // field.rs - calls negate()
///     │       └─► reduce()      // field.rs - performs modular reduction
///     └─► conditional_assign()  // field.rs - selects original or negated
/// ```
///
/// Verus note: we keep this as an `external_body` wrapper because the underlying
/// `subtle::ConditionallyNegatable::conditional_negate` is defined in an external crate.
/// We attach a precise functional contract here without verifying the external implementation.
///
/// Bounds note:
/// - If `choice` is true, this performs a field negation, which calls `reduce()` and yields a 52-bit bound.
/// - If `choice` is false, this is a no-op, so we can only preserve whatever limb bounds `old(a)` had.
#[verifier::external_body]
pub fn conditional_negate_field_element(a: &mut FieldElement51, choice: Choice)
    requires
        fe51_limbs_bounded(
            old(a),
            54,
        ),  // Allow the standard 54-bit bound used by most field ops

    ensures
        fe51_limbs_bounded(a, 54),
        choice_is_true(choice) ==> fe51_limbs_bounded(a, 52),
        !choice_is_true(choice) ==> *a == *old(a),
        fe51_as_canonical_nat(a) == if choice_is_true(choice) {
            field_neg(fe51_as_canonical_nat(old(a)))
        } else {
            fe51_as_canonical_nat(old(a))
        },
{
    a.conditional_negate(choice);
}

/// Generic wrapper for ConditionallySelectable::conditional_assign()
#[verifier::external_body]
pub fn conditional_assign_generic<T>(a: &mut T, b: &T, choice: Choice) where
    T: subtle::ConditionallySelectable,
 {
    a.conditional_assign(b, choice)
}

/*** ConditionallySelectable specification for FieldElement51 ***/

/// Wrapper for conditional_select on FieldElement51
#[verifier::external_body]
pub fn conditional_select_field_element(
    a: &FieldElement51,
    b: &FieldElement51,
    choice: Choice,
) -> (result: FieldElement51)
    ensures
        !choice_is_true(choice) ==> result == *a,
        choice_is_true(choice) ==> result == *b,
{
    FieldElement51::conditional_select(a, b, choice)
}

/*** ConditionallySelectable specification for ProjectivePoint ***/

/// Wrapper for conditional_swap on Montgomery ProjectivePoint
/// This is needed because assume_specification doesn't work on provided trait methods
#[verifier::external_body]
pub fn conditional_swap_montgomery_projective(
    a: &mut crate::montgomery::ProjectivePoint,
    b: &mut crate::montgomery::ProjectivePoint,
    choice: Choice,
)
    ensures
// If choice is false, points remain unchanged

        !choice_is_true(choice) ==> {
            &&& a.U == old(a).U
            &&& a.W == old(a).W
            &&& b.U == old(b).U
            &&& b.W == old(b).W
        },
        // If choice is true, points are swapped
        choice_is_true(choice) ==> {
            &&& a.U == old(b).U
            &&& a.W == old(b).W
            &&& b.U == old(a).U
            &&& b.W == old(a).W
        },
{
    crate::montgomery::ProjectivePoint::conditional_swap(a, b, choice)
}

} // verus!
