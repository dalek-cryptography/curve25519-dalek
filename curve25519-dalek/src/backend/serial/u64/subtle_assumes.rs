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
pub fn select(x: &u64, y: &u64, c: Choice) -> (res: u64)
    ensures reveal_choice(c) == RevealedChoice::Choice1 ==> res == x,
            reveal_choice(c) == RevealedChoice::Choice0 ==> res == y
{
    u64::conditional_select(x, y, c)
}

} // verus!
