//! Tell Verus what Choice does
use subtle::{Choice, ConditionallySelectable};

use vstd::prelude::*;

verus! {


#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExChoice(Choice);

pub uninterp spec fn boolify(c: Choice) -> bool;

pub assume_specification [Choice::from](u: u8) -> (c: Choice)
    ensures u == 0 ==> boolify(c) == false,
            u == 1 ==> boolify(c) == true;

#[verifier::external_body]
pub fn select(x: &u64, y: &u64, c: Choice) -> (res: u64)
    ensures boolify(c) ==> res == x,
            ! boolify(c) ==> res == y
{
    u64::conditional_select(x, y, c)
}

} // verus!
