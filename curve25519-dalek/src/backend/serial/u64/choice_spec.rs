use core::fmt::Debug;
use core::ops::{Index, IndexMut};
use subtle::{Choice, ConditionallySelectable};

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::constants;

#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;

verus! {

// Tell Verus what Choice does

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
