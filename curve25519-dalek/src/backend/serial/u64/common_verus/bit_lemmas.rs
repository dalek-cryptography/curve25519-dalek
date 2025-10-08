#![allow(unused)]
use vstd::prelude::*;

verus! {

pub proof fn bitwise_or_r_zero_is_id(a: u64)
    ensures
        a | 0 == a
{
    assert( a | 0 == a) by (bit_vector);
}

pub proof fn bitwise_or_l_zero_is_id(a: u64)
    ensures
        0 | a == a
{
    assert( 0 | a == a) by (bit_vector);
}

fn main() {}

}
