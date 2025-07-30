#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::common_verus::*;

// Lemmas and spec functions only used in field_verus.rs
// A lemma should be in this file instead of `common_verus` if:
//  - It references some constant prominent in `field_verus` (e.g. 51 for bit operations, 2^255 -19)
//  - It defines or reasons about a spec function relevant only to `field_verus`
verus! {

// p = 2^255 - 19
pub open spec fn p() -> nat {
    (pow2(255) - 19) as nat
}

// Proof that 2^255 > 19
pub proof fn pow255_gt_19()
    ensures
        pow2(255) > 19
{
    lemma2_to64(); // 2^5
    lemma_pow2_strictly_increases(5, 255);
}

// Specialization for b = 51
pub proof fn lemma_two_factoring_51(k : nat, ai: u64)
    ensures
        pow2(k + 51) * ai == pow2(k) * (pow2(51) * ai)
{
    lemma_two_factoring(k, 51, ai);
}

// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
pub open spec fn as_nat(limbs: [u64; 5]) -> nat {
    (limbs[0] as nat) +
    pow2(51) * (limbs[1] as nat) +
    pow2(102) * (limbs[2] as nat) +
    pow2(153) * (limbs[3] as nat) +
    pow2(204) * (limbs[4] as nat)
}

// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
pub open spec fn as_nat_32_u8(limbs: [u8; 32]) -> nat {
    // Verus error: `core::iter::range::impl&%15::fold` is not supported
    // we write them out manually
    (limbs[0] as nat) +
    pow2( 1 * 8) * (limbs[ 1] as nat) +
    pow2( 2 * 8) * (limbs[ 2] as nat) +
    pow2( 3 * 8) * (limbs[ 3] as nat) +
    pow2( 4 * 8) * (limbs[ 4] as nat) +
    pow2( 5 * 8) * (limbs[ 5] as nat) +
    pow2( 6 * 8) * (limbs[ 6] as nat) +
    pow2( 7 * 8) * (limbs[ 7] as nat) +
    pow2( 8 * 8) * (limbs[ 8] as nat) +
    pow2( 9 * 8) * (limbs[ 9] as nat) +
    pow2(10 * 8) * (limbs[10] as nat) +
    pow2(11 * 8) * (limbs[11] as nat) +
    pow2(12 * 8) * (limbs[12] as nat) +
    pow2(13 * 8) * (limbs[13] as nat) +
    pow2(14 * 8) * (limbs[14] as nat) +
    pow2(15 * 8) * (limbs[15] as nat) +
    pow2(16 * 8) * (limbs[16] as nat) +
    pow2(17 * 8) * (limbs[17] as nat) +
    pow2(18 * 8) * (limbs[18] as nat) +
    pow2(19 * 8) * (limbs[19] as nat) +
    pow2(20 * 8) * (limbs[20] as nat) +
    pow2(21 * 8) * (limbs[21] as nat) +
    pow2(22 * 8) * (limbs[22] as nat) +
    pow2(23 * 8) * (limbs[23] as nat) +
    pow2(24 * 8) * (limbs[24] as nat) +
    pow2(25 * 8) * (limbs[25] as nat) +
    pow2(26 * 8) * (limbs[26] as nat) +
    pow2(27 * 8) * (limbs[27] as nat) +
    pow2(28 * 8) * (limbs[28] as nat) +
    pow2(29 * 8) * (limbs[29] as nat) +
    pow2(30 * 8) * (limbs[30] as nat) +
    pow2(31 * 8) * (limbs[31] as nat)
}

// Lemma: If a > b pointwise, then as_nat(a - b) = as_nat(a) - as_nat(b)
pub proof fn lemma_as_nat_sub(a: [u64;5], b: [u64;5])
    requires
        forall |i:int| 0 <= i < 5 ==> b[i] < a[i]
    ensures
        as_nat([
            (a[0] - b[0]) as u64,
            (a[1] - b[1]) as u64,
            (a[2] - b[2]) as u64,
            (a[3] - b[3]) as u64,
            (a[4] - b[4]) as u64
        ]) == as_nat(a) - as_nat(b)
{
    let c: [u64;5] = [
        (a[0] - b[0]) as u64,
        (a[1] - b[1]) as u64,
        (a[2] - b[2]) as u64,
        (a[3] - b[3]) as u64,
        (a[4] - b[4]) as u64
    ];
    // distribute pow2
    assert( as_nat(c) ==
        (a[0] - b[0]) +
        pow2(51) * a[1] - pow2(51) * b[1] +
        pow2(102) * a[2] - pow2(102) * b[2] +
        pow2(153) * a[3] - pow2(153) * b[3] +
        pow2(204) * a[4] - pow2(204) * b[4]
    ) by {
        broadcast use lemma_mul_is_distributive_sub;
    }
}

pub proof fn lemma_add_then_shift(a: u64, b: u64)
    requires
        a < (1u64 << 52),
        b < (1u64 << 52)
    ensures
        (a + b) < (1u64 << 53),
        ((a + b) as u64 >> 51) < 4
{
    lemma2_to64_rest();
    assert((a + b) < 1u64 << 53) by {
        assert((1u64 << 52) + (1u64 << 52) == 1u64 << 53) by (compute);
    }
    assert(1u64 << 53 == (1u64 << 51) * 4) by (bit_vector);
    // 0 < b  /\ a < b * c => a/b < c
    lemma_multiply_divide_lt((a + b) as int, (1u64 << 51) as int, 4int);
    shift_is_pow2(51);
    shift_is_pow2(53);
    assert((a + b) as u64 >> 51 == (a + b) as u64 / (pow2(51) as u64)) by {
        lemma_u64_shr_is_div((a + b) as u64, 51);
    }
    assert(pow2(53) / pow2(51) == 4) by {
        lemma_pow2_subtracts(51, 53);
    }
}

// >> preserves [<=]. Unfortunately, these operations are u128 and
// we need lemma_u128_shr_is_div.
pub proof fn lemma_shr_51_le(a: u128, b: u128)
    requires
        a <= b
    ensures
        (a >> 51) <= (b >> 51)
{
    lemma_pow2_pos(51);
    lemma2_to64_rest(); // pow2(51) value
    lemma_u128_shr_is_div(a, 51);
    lemma_u128_shr_is_div(b, 51);
    lemma_div_is_ordered(a as int, b as int, 51);
}

// Corollary of above, using the identity (a << x) >> x == a for u64::MAX
pub proof fn lemma_shr_51_fits_u64(a: u128)
    requires
        a <= (u64::MAX as u128) << 51
    ensures
        (a >> 51) <= (u64::MAX as u128)

{
    assert(((u64::MAX as u128) << 51) >> 51 == (u64::MAX as u128)) by (compute);
    lemma_shr_51_le(a, (u64::MAX as u128) << 51);
}

// dummy, so we can call `verus`
fn main() {}

}
