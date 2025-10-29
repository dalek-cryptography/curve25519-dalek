#![allow(unused)]
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

// p = 2^255 - 19
pub open spec fn p() -> nat {
    (pow2(255) - 19) as nat
}

// Proof that 2^255 > 19
pub proof fn pow255_gt_19()
    ensures
        pow2(255) > 19,
{
    lemma2_to64();  // 2^5
    lemma_pow2_strictly_increases(5, 255);
}

pub open spec const mask51: u64 = 2251799813685247u64;

// Basic properties of mask51:
// - It's the value of low_bits_mask (spec function defined in vstd and used in its lemmas)
// - it's less than 2^51
pub proof fn l51_bit_mask_lt()
    ensures
        mask51 == low_bits_mask(51),
        mask51 < (1u64 << 51) as nat,
{
    lemma2_to64_rest();
    assert(mask51 < (1u64 << 51) as nat) by (compute);
}

// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
pub open spec fn as_nat(limbs: [u64; 5]) -> nat {
    (limbs[0] as nat) + pow2(51) * (limbs[1] as nat) + pow2(102) * (limbs[2] as nat) + pow2(153) * (
    limbs[3] as nat) + pow2(204) * (limbs[4] as nat)
}

// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
pub open spec fn as_nat_32_u8(limbs: &[u8; 32]) -> nat {
    // Verus error: `core::iter::range::impl&%15::fold` is not supported
    // we write them out manually
    //
    // Note: We use byte-first order (limbs[i] * pow2(i*8)) to match
    // the natural structure of limb contribution functions in limbs_to_bytes_lemmas.rs
    (limbs[0] as nat) + (limbs[1] as nat) * pow2(1 * 8) + (limbs[2] as nat) * pow2(2 * 8) + (
    limbs[3] as nat) * pow2(3 * 8) + (limbs[4] as nat) * pow2(4 * 8) + (limbs[5] as nat) * pow2(
        5 * 8,
    ) + (limbs[6] as nat) * pow2(6 * 8) + (limbs[7] as nat) * pow2(7 * 8) + (limbs[8] as nat)
        * pow2(8 * 8) + (limbs[9] as nat) * pow2(9 * 8) + (limbs[10] as nat) * pow2(10 * 8) + (
    limbs[11] as nat) * pow2(11 * 8) + (limbs[12] as nat) * pow2(12 * 8) + (limbs[13] as nat)
        * pow2(13 * 8) + (limbs[14] as nat) * pow2(14 * 8) + (limbs[15] as nat) * pow2(15 * 8) + (
    limbs[16] as nat) * pow2(16 * 8) + (limbs[17] as nat) * pow2(17 * 8) + (limbs[18] as nat)
        * pow2(18 * 8) + (limbs[19] as nat) * pow2(19 * 8) + (limbs[20] as nat) * pow2(20 * 8) + (
    limbs[21] as nat) * pow2(21 * 8) + (limbs[22] as nat) * pow2(22 * 8) + (limbs[23] as nat)
        * pow2(23 * 8) + (limbs[24] as nat) * pow2(24 * 8) + (limbs[25] as nat) * pow2(25 * 8) + (
    limbs[26] as nat) * pow2(26 * 8) + (limbs[27] as nat) * pow2(27 * 8) + (limbs[28] as nat)
        * pow2(28 * 8) + (limbs[29] as nat) * pow2(29 * 8) + (limbs[30] as nat) * pow2(30 * 8) + (
    limbs[31] as nat) * pow2(31 * 8)
}

pub open spec fn as_nat_32_u8_rec(limbs: &[u8; 32], index: nat) -> nat
    decreases 32 - index,
{
    if index >= 32 {
        0
    } else {
        (limbs[index as int] as nat) * pow2(index * 8) + as_nat_32_u8_rec(limbs, index + 1)
    }
}

pub open spec fn load8_at_spec(input: &[u8], i: usize) -> nat {
    (pow2(0 * 8) * input[i + 0] + pow2(1 * 8) * input[i + 1] + pow2(2 * 8) * input[i + 2] + pow2(
        3 * 8,
    ) * input[i + 3] + pow2(4 * 8) * input[i + 4] + pow2(5 * 8) * input[i + 5] + pow2(6 * 8)
        * input[i + 6] + pow2(7 * 8) * input[i + 7]) as nat
}

pub open spec fn spec_reduce(limbs: [u64; 5]) -> (r: [u64; 5]) {
    let r = [
        ((limbs[0] & mask51) + (limbs[4] >> 51) * 19) as u64,
        ((limbs[1] & mask51) + (limbs[0] >> 51)) as u64,
        ((limbs[2] & mask51) + (limbs[1] >> 51)) as u64,
        ((limbs[3] & mask51) + (limbs[2] >> 51)) as u64,
        ((limbs[4] & mask51) + (limbs[3] >> 51)) as u64,
    ];
    r
}

pub open spec const sixteen_p_vec: [u64; 5] = [
    36028797018963664u64,  // 16 * (2^51 - 19)
    36028797018963952u64,  // 16 * (2^51 -  1)
    36028797018963952u64,  // 16 * (2^51 -  1)
    36028797018963952u64,  // 16 * (2^51 -  1)
    36028797018963952u64  // 16 * (2^51 -  1)
    ,
];

pub open spec fn pre_reduce_limbs(limbs: [u64; 5]) -> [u64; 5] {
    let r = [
        (sixteen_p_vec[0] - limbs[0]) as u64,
        (sixteen_p_vec[1] - limbs[1]) as u64,
        (sixteen_p_vec[2] - limbs[2]) as u64,
        (sixteen_p_vec[3] - limbs[3]) as u64,
        (sixteen_p_vec[4] - limbs[4]) as u64,
    ];
    r
}

pub open spec fn spec_negate(limbs: [u64; 5]) -> [u64; 5] {
    let r = spec_reduce(pre_reduce_limbs(limbs));
    r
}

pub open spec fn compute_q_arr(limbs: [u64; 5]) -> [u64; 5] {
    let q0 = ((limbs[0] + 19) as u64 >> 51) as u64;
    let q1 = ((limbs[1] + q0) as u64 >> 51) as u64;
    let q2 = ((limbs[2] + q1) as u64 >> 51) as u64;
    let q3 = ((limbs[3] + q2) as u64 >> 51) as u64;
    let q4 = ((limbs[4] + q3) as u64 >> 51) as u64;
    [q0, q1, q2, q3, q4]
}

/// Spec function to compute q value from limbs
pub open spec fn compute_q_spec(limbs: [u64; 5]) -> u64 {
    compute_q_arr(limbs)[4]
}

pub open spec fn compute_unmasked_limbs(input_limbs: [u64; 5], q: u64) -> [u64; 5] {
    let l0 = (input_limbs[0] + 19 * q) as u64;
    let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
    let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
    let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
    let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
    [l0, l1, l2, l3, l4]
}

/// Spec function to compute the reduction result
pub open spec fn reduce_with_q_spec(input_limbs: [u64; 5], q: u64) -> [u64; 5] {
    let l = compute_unmasked_limbs(input_limbs, q);
    let l0 = l[0];
    let l1 = l[1];
    let l2 = l[2];
    let l3 = l[3];
    let l4 = l[4];
    let l0_masked = (l0 & mask51) as u64;
    let l1_masked = (l1 & mask51) as u64;
    let l2_masked = (l2 & mask51) as u64;
    let l3_masked = (l3 & mask51) as u64;
    let l4_masked = (l4 & mask51) as u64;
    [l0_masked, l1_masked, l2_masked, l3_masked, l4_masked]
}

pub open spec fn bit_arrange(limbs: [u64; 5]) -> [u8; 32] {
    let s = [
        limbs[0] as u8,
        (limbs[0] >> 8) as u8,
        (limbs[0] >> 16) as u8,
        (limbs[0] >> 24) as u8,
        (limbs[0] >> 32) as u8,
        (limbs[0] >> 40) as u8,
        ((limbs[0] >> 48) | (limbs[1] << 3)) as u8,
        (limbs[1] >> 5) as u8,
        (limbs[1] >> 13) as u8,
        (limbs[1] >> 21) as u8,
        (limbs[1] >> 29) as u8,
        (limbs[1] >> 37) as u8,
        ((limbs[1] >> 45) | (limbs[2] << 6)) as u8,
        (limbs[2] >> 2) as u8,
        (limbs[2] >> 10) as u8,
        (limbs[2] >> 18) as u8,
        (limbs[2] >> 26) as u8,
        (limbs[2] >> 34) as u8,
        (limbs[2] >> 42) as u8,
        ((limbs[2] >> 50) | (limbs[3] << 1)) as u8,
        (limbs[3] >> 7) as u8,
        (limbs[3] >> 15) as u8,
        (limbs[3] >> 23) as u8,
        (limbs[3] >> 31) as u8,
        (limbs[3] >> 39) as u8,
        ((limbs[3] >> 47) | (limbs[4] << 4)) as u8,
        (limbs[4] >> 4) as u8,
        (limbs[4] >> 12) as u8,
        (limbs[4] >> 20) as u8,
        (limbs[4] >> 28) as u8,
        (limbs[4] >> 36) as u8,
        (limbs[4] >> 44) as u8,
    ];

    s
}

pub open spec fn spec_as_bytes(limbs: [u64; 5]) -> [u8; 32] {
    let reduced_limbs = spec_reduce(limbs);
    let q = compute_q_spec(reduced_limbs);
    bit_arrange(reduce_with_q_spec(reduced_limbs, q))
}

} // verus!
