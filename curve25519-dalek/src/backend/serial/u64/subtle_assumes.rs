//! Tell Verus what Choice does
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExChoice(Choice);

/// Spec-level view of Choice as a boolean
/// true = Choice(1), false = Choice(0)
pub uninterp spec fn choice_is_true(c: Choice) -> bool;

pub assume_specification [Choice::from](u: u8) -> (c: Choice)
    ensures (u == 1) == choice_is_true(c);

#[verifier::external_body]
/// See https://docs.rs/subtle/latest/subtle/trait.ConditionallySelectable.html#tymethod.conditional_select
pub fn select(a: &u64, b: &u64, c: Choice) -> (res: u64)
    ensures !choice_is_true(c) ==> res == a,
            choice_is_true(c) ==> res == b
{
    u64::conditional_select(a, b, c)
}

// Helper for conditional_select on u8
#[verifier::external_body]
pub fn select_u8(a: &u8, b: &u8, c: Choice) -> (res: u8)
    ensures !choice_is_true(c) ==> res == a,
            choice_is_true(c) ==> res == b
{
    u8::conditional_select(a, b, c)
}

// Assume specification for ct_eq on byte arrays
#[verifier::external_body]
pub fn ct_eq_bytes32(a: &[u8; 32], b: &[u8; 32]) -> (c: Choice)
    ensures choice_is_true(c) == (a == b)
{
    a.ct_eq(b)
}

// Helper for ct_eq on u8
#[verifier::external_body]
pub fn ct_eq_u8(a: &u8, b: &u8) -> (c: Choice)
    ensures choice_is_true(c) == (a == b)
{
    a.ct_eq(b)
}

// Helper for Choice::into (converts Choice to bool)
#[verifier::external_body]
pub fn choice_into(c: Choice) -> (b: bool)
    ensures b == choice_is_true(c)
{
    c.into()
}

// Helper for bitwise AND on Choice
#[verifier::external_body]
pub fn choice_and(a: Choice, b: Choice) -> (c: Choice)
    ensures choice_is_true(c) == (choice_is_true(a) && choice_is_true(b))
{
    use core::ops::BitAnd;
    a.bitand(b)
}

} // verus!
