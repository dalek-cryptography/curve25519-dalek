//! Tell Verus what Choice does
use subtle::{Choice, ConditionallySelectable};

use vstd::prelude::*;

verus! {

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
pub fn select(a: &u64, b: &u64, c: Choice) -> (res: u64)
    ensures reveal_choice(c) == RevealedChoice::Choice0 ==> res == a,
            reveal_choice(c) == RevealedChoice::Choice1 ==> res == b
{
    u64::conditional_select(a, b, c)
}

} // verus!
