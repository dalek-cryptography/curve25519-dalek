//! Tell Verus what Choice and CtOption do
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExChoice(Choice);

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

#[verifier::external_body]
/// See https://docs.rs/subtle/latest/subtle/trait.ConditionallySelectable.html#tymethod.conditional_select
pub fn select(a: &u64, b: &u64, c: Choice) -> (res: u64)
    ensures
        !choice_is_true(c) ==> res == a,
        choice_is_true(c) ==> res == b,
{
    u64::conditional_select(a, b, c)
}

// Helper for conditional_select on u8
#[verifier::external_body]
pub fn select_u8(a: &u8, b: &u8, c: Choice) -> (res: u8)
    ensures
        !choice_is_true(c) ==> res == a,
        choice_is_true(c) ==> res == b,
{
    u8::conditional_select(a, b, c)
}

// Assume specification for ct_eq on byte arrays
#[verifier::external_body]
pub fn ct_eq_bytes32(a: &[u8; 32], b: &[u8; 32]) -> (c: Choice)
    ensures
        choice_is_true(c) == (a == b),
{
    a.ct_eq(b)
}

// Assume specification for ct_eq on limb arrays (5 u64s for FieldElement51)
#[verifier::external_body]
pub fn ct_eq_limbs5(a: &[u64; 5], b: &[u64; 5]) -> (c: Choice)
    ensures
        choice_is_true(c) == (a == b),
{
    a.ct_eq(b)
}

// Helper for ct_eq on u8
#[verifier::external_body]
pub fn ct_eq_u8(a: &u8, b: &u8) -> (c: Choice)
    ensures
        choice_is_true(c) == (a == b),
{
    a.ct_eq(b)
}

// Helper for Choice::into (converts Choice to bool)
#[verifier::external_body]
pub fn choice_into(c: Choice) -> (b: bool)
    ensures
        b == choice_is_true(c),
{
    c.into()
}

// Helper for bitwise AND on Choice
#[verifier::external_body]
pub fn choice_and(a: Choice, b: Choice) -> (c: Choice)
    ensures
        choice_is_true(c) == (choice_is_true(a) && choice_is_true(b)),
{
    use core::ops::BitAnd;
    a.bitand(b)
}

// Wrapper for bitwise NOT on Choice
#[verifier::external_body]
pub fn choice_not(a: Choice) -> (c: Choice)
    ensures
        choice_is_true(c) == !choice_is_true(a),
{
    use core::ops::Not;
    a.not()
}

// Wrapper for bitwise OR on Choice
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
pub fn ct_option_new<T>(value: T, choice: Choice) -> CtOption<T> {
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

/*** ConditionallySelectable wrappers for u64 arrays ***/

/// Wrapper for conditional_select on u64 - already exists as `select` above
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

/// Wrapper for conditional_negate on FieldElement
#[verifier::external_body]
pub fn conditional_negate_field<T>(a: &mut T, choice: Choice) where
    T: subtle::ConditionallyNegatable,
 {
    a.conditional_negate(choice);
}

/// Wrapper for FieldElement negation to avoid Verus internal error
#[verifier::external_body]
pub fn negate_field<T>(a: &T) -> (result: T) where for <'a>&'a T: core::ops::Neg<Output = T> {
    -a
}

} // verus!
