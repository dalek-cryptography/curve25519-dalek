#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {


// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
// This also appears in `curve25519-dalek/src/backend/serial/u64/field_lemmas.rs`, to be combined.
pub open spec fn as_nat_32_u8(limbs: [u8; 32]) -> nat {
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


}
