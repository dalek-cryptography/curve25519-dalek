#![allow(unused)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

use super::field_core::*;
use super::pow2_51_lemmas::*;

use super::super::common_verus::mul_lemmas::*;

verus! {

// Auxiliary lemma for reordering terms in the pow2k proof
pub proof fn lemma_reorder_mul(a: int, b: int)
    ensures
        2 * (a * (19 * b)) == 19 * (2 * (a * b))
{
    // 2*( a * (19 * b)) = (2 * a) * (19 * b)
    lemma_mul_is_associative(2, a, 19 * b);
    // (2 * a) * (19 * b) = (19 * b) * (2 * a) = 19 * (b * (2 * a))
    lemma_mul_is_associative(19, b, 2 * a);
    // (b * (2 * a)) = (b * (a * 2)) = 2 * (a * b)
    lemma_mul_is_associative(b, a, 2);
}


pub proof fn term_product_bounds(a: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        forall |i: int| 0 <= i < 5 ==> a[i] < bound
    ensures
        // c0
        (a[0] as u128) * (a[0] as u128) < bound * bound,
        (a[1] as u128) * ((19 * a[4]) as u128) < 19 * (bound * bound),
        (a[2] as u128) * ((19 * a[3]) as u128) < 19 * (bound * bound),
        // c1
        (a[3] as u128) * ((19 * a[3]) as u128) < 19 * (bound * bound),
        (a[0] as u128) * (a[1] as u128) < (bound * bound),
        (a[2] as u128) * ((19 * a[4]) as u128) < 19 * (bound * bound),
        // c2
        (a[1] as u128) * (a[1] as u128) < (bound * bound),
        (a[0] as u128) * (a[2] as u128) < (bound * bound),
        (a[4] as u128) * ((19 * a[3]) as u128) < 19 * (bound * bound),
        // c3
        (a[4] as u128) * ((19 * a[4]) as u128) < 19 * (bound * bound),
        (a[0] as u128) * (a[3] as u128) < (bound * bound),
        (a[1] as u128) * (a[2] as u128) < (bound * bound),
        // c4
        (a[2] as u128) * (a[2] as u128) < (bound * bound),
        (a[0] as u128) * (a[4] as u128) < (bound * bound),
        (a[1] as u128) * (a[3] as u128) < (bound * bound)
{
    let bound19 = (19 * bound) as u64;

    let a3_19 = (19 * a[3]) as u64;
    let a4_19 = (19 * a[4]) as u64;

    assert(bound * (19 * bound) == 19 * (bound * bound)) by {
        lemma_mul_is_associative(19, bound as int, bound as int);
    }

    // c0
    lemma_m(a[0], a[0], bound, bound);
    lemma_m(a[1], a4_19, bound, bound19);
    lemma_m(a[2], a3_19, bound, bound19);

    // c1
    lemma_m(a[3], a3_19, bound, bound19);
    lemma_m(a[0],  a[1], bound, bound);
    lemma_m(a[2], a4_19, bound, bound19);

    // c2
    lemma_m(a[1],  a[1], bound, bound);
    lemma_m(a[0],  a[2], bound, bound);
    lemma_m(a[4], a3_19, bound, bound19);

    // c3
    lemma_m(a[4], a4_19, bound, bound19);
    lemma_m(a[0],  a[3], bound, bound);
    lemma_m(a[1],  a[2], bound, bound);

    // c4
    lemma_m(a[2],  a[2], bound, bound);
    lemma_m(a[0],  a[4], bound, bound);
    lemma_m(a[1],  a[3], bound, bound);
}

pub open spec fn c0_0_val(a: [u64; 5]) -> u128 {
    (a[0] *  a[0] + 2*( a[1] * (19 * a[4]) + a[2] * (19 * a[3]))) as u128
}
pub open spec fn c1_0_val(a: [u64; 5]) -> u128 {
    (a[3] *  (19 * a[3]) + 2 *( a[0] * a[1] + a[2] * (19 * a[4]))) as u128
}
pub open spec fn c2_0_val(a: [u64;5]) -> u128{
    (a[1] *  a[1] + 2*( a[0] *  a[2] + a[4] * (19 * a[3]))) as u128
}
pub open spec fn c3_0_val(a: [u64;5]) -> u128{
    (a[4] * (19 * a[4]) + 2*( a[0] *  a[3] + a[1] * a[2])) as u128
}
pub open spec fn c4_0_val(a: [u64;5]) -> u128{
    (a[2] *  a[2] + 2*( a[0] *  a[4] + a[1] *  a[3])) as u128
}

pub proof fn c_i_0_bounded(a: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        forall |i: int| 0 <= i < 5 ==> a[i] < bound
    ensures
        c0_0_val(a) < 77 * (bound * bound),
        c1_0_val(a) < 59 * (bound * bound),
        c2_0_val(a) < 41 * (bound * bound),
        c3_0_val(a) < 23 * (bound * bound),
        c4_0_val(a) <  5 * (bound * bound)
{
    term_product_bounds(a, bound);
}

pub open spec fn c0_val(a: [u64; 5]) -> u128 {
    c0_0_val(a)
}
pub open spec fn c1_val(a: [u64; 5]) -> u128 {
    (c1_0_val(a) + ((c0_val(a) >> 51) as u64) as u128) as u128
}
pub open spec fn c2_val(a: [u64;5]) -> u128{
    (c2_0_val(a) + ((c1_val(a) >> 51) as u64) as u128) as u128
}
pub open spec fn c3_val(a: [u64;5]) -> u128{
    (c3_0_val(a) + ((c2_val(a) >> 51) as u64) as u128) as u128
}
pub open spec fn c4_val(a: [u64;5]) -> u128{
    (c4_0_val(a) + ((c3_val(a) >> 51) as u64) as u128) as u128
}

pub proof fn c_i_shift_bounded(a: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        77 * (bound * bound) + u64::MAX <= ((u64::MAX as u128) << 51),
        forall |i: int| 0 <= i < 5 ==> a[i] < bound
    ensures
        (c0_val(a) >> 51) <= (u64::MAX as u128),
        (c1_val(a) >> 51) <= (u64::MAX as u128),
        (c2_val(a) >> 51) <= (u64::MAX as u128),
        (c3_val(a) >> 51) <= (u64::MAX as u128),
        (c4_val(a) >> 51) <= (u64::MAX as u128)

{
    c_i_0_bounded(a, bound);

    lemma_shr_51_fits_u64(c0_val(a));
    lemma_shr_51_fits_u64(c1_val(a));
    lemma_shr_51_fits_u64(c2_val(a));
    lemma_shr_51_fits_u64(c3_val(a));
    lemma_shr_51_fits_u64(c4_val(a));
}

pub open spec fn carry_val(a: [u64; 5]) -> u64 {
    (c4_val(a) >> 51) as u64
}

pub open spec fn a0_0_val(a: [u64; 5]) -> u64 {
    (c0_val(a) as u64) & mask51
}
pub open spec fn a1_0_val(a: [u64; 5]) -> u64 {
    (c1_val(a) as u64) & mask51
}
pub open spec fn a2_0_val(a: [u64; 5]) -> u64 {
    (c2_val(a) as u64) & mask51
}
pub open spec fn a3_0_val(a: [u64; 5]) -> u64 {
    (c3_val(a) as u64) & mask51
}
pub open spec fn a4_0_val(a: [u64; 5]) -> u64 {
    (c4_val(a) as u64) & mask51
}

fn main() {}

}
