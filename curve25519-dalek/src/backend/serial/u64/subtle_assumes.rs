//! Tell Verus what Choice does
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use vstd::prelude::*;

verus! {

#[allow(dead_code)]
pub enum RevealedChoice {
    Choice0,
    Choice1,
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExChoice(Choice);

pub uninterp spec fn reveal_choice(c: Choice) -> RevealedChoice;

pub assume_specification [Choice::from](u: u8) -> (c: Choice)
    ensures u == 0 ==> reveal_choice(c) == RevealedChoice::Choice0,
            u == 1 ==> reveal_choice(c) == RevealedChoice::Choice1;

#[verifier::external_body]
/// See https://docs.rs/subtle/latest/subtle/trait.ConditionallySelectable.html#tymethod.conditional_select
pub fn select(a: &u64, b: &u64, c: Choice) -> (res: u64)
    ensures reveal_choice(c) == RevealedChoice::Choice0 ==> res == a,
            reveal_choice(c) == RevealedChoice::Choice1 ==> res == b
{
    u64::conditional_select(a, b, c)
}

// Helper for conditional_select on u8
#[verifier::external_body]
pub fn select_u8(a: &u8, b: &u8, c: Choice) -> (res: u8)
    ensures reveal_choice(c) == RevealedChoice::Choice0 ==> res == a,
            reveal_choice(c) == RevealedChoice::Choice1 ==> res == b
{
    u8::conditional_select(a, b, c)
}

// Assume specification for ct_eq on byte arrays
#[verifier::external_body]
pub fn ct_eq_bytes32(a: &[u8; 32], b: &[u8; 32]) -> (c: Choice)
    ensures a == b ==> reveal_choice(c) == RevealedChoice::Choice1,
            a != b ==> reveal_choice(c) == RevealedChoice::Choice0
{
    a.ct_eq(b)
}

// Helper for ct_eq on u8
#[verifier::external_body]
pub fn ct_eq_u8(a: &u8, b: &u8) -> (c: Choice)
    ensures a == b ==> reveal_choice(c) == RevealedChoice::Choice1,
            a != b ==> reveal_choice(c) == RevealedChoice::Choice0
{
    a.ct_eq(b)
}

// Helper for Choice::into (converts Choice to bool)
#[verifier::external_body]
pub fn choice_into(c: Choice) -> (b: bool)
    ensures reveal_choice(c) == RevealedChoice::Choice1 ==> b == true,
            reveal_choice(c) == RevealedChoice::Choice0 ==> b == false
{
    c.into()
}

// Helper for bitwise AND on Choice
#[verifier::external_body]
pub fn choice_and(a: Choice, b: Choice) -> (c: Choice)
    ensures (reveal_choice(a) == RevealedChoice::Choice1 && reveal_choice(b) == RevealedChoice::Choice1)
                ==> reveal_choice(c) == RevealedChoice::Choice1,
            (reveal_choice(a) == RevealedChoice::Choice0 || reveal_choice(b) == RevealedChoice::Choice0)
                ==> reveal_choice(c) == RevealedChoice::Choice0
{
    use core::ops::BitAnd;
    a.bitand(b)
}

} // verus!
