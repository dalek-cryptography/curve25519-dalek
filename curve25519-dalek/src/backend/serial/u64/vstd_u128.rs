#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

// Placeholder until u128 lemma gets into vstd;
verus! {

pub broadcast proof fn lemma_u128_low_bits_mask_is_mod(x: u128, n: nat)
    requires
        n < u128::BITS,
    ensures
        #[trigger] (x & (low_bits_mask(n) as u128)) == x % (pow2(n) as u128),
{
    // Body-copy doesn't work.
    assume(false);
}

}
