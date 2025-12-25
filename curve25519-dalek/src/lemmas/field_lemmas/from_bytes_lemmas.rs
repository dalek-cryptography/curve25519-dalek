#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::load8_lemmas::*;

use super::super::common_lemmas::bit_lemmas::*;
use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mask_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::core_specs::*;
use crate::specs::field_specs_u64::*;

verus! {

pub proof fn lemma_assemble_mod_div(a: nat, d: nat, b: nat)
    ensures
        (a % pow2(d)) * pow2(b) + pow2(b + d) * (a / pow2(d)) == a * pow2(b),
{
    let pb = pow2(b);
    let pd = pow2(d);
    let pbd = pow2(b + d);

    assert(pbd == pb * pd) by {
        lemma_pow2_adds(b, d);
    }

    let amod = a % pd;
    let adiv = a / pd;

    assert(pbd * adiv == (pd * adiv) * pb) by {
        lemma_mul_is_associative(pb as int, pd as int, adiv as int);
        lemma_mul_is_commutative(pb as int, (pd * adiv) as int);
    }

    assert(amod * pb + (pd * adiv) * pb == (amod + pd * adiv) * pb) by {
        lemma_mul_is_distributive_add_other_way(pb as int, amod as int, (pd * adiv) as int);
    }

    assert(amod + pd * adiv == a) by {
        assert(pd > 0) by {
            lemma_pow2_pos(d);
        }
        lemma_fundamental_div_mod(a as int, pd as int);
    }

}

pub proof fn lemma_assemble_pow_a_pow(a: nat, j: nat, k: nat, l: nat)
    requires
        k * 8 > l,
    ensures
        pow2(j * 8 + l) * (a * pow2((k * 8 - l) as nat)) == a * pow2((j + k) * 8),
{
    let d = (k * 8 - l) as nat;
    let dd = j * 8 + l;
    let pjl = pow2(j * 8 + l);

    assert(pjl * (a * pow2(d)) == (a * pow2(d)) * pjl) by {
        lemma_mul_is_commutative(pjl as int, a * pow2(d) as int);
    }

    assert((a * pow2(d)) * pjl == a * pow2(d + dd)) by {
        lemma_mul_is_associative(a as int, pow2(d) as int, pjl as int);
        lemma_pow2_adds(d, dd);
    }

    assert(d + dd == (j + k) * 8) by {
        assert((j + k) * 8 == j * 8 + k * 8) by {
            lemma_mul_is_distributive_add_other_way(8, d as int, dd as int);
        }
    }
}

pub proof fn lemma_from_bytes32_to_nat_01(bytes: &[u8; 32])
    ensures
        (spec_load8_at(bytes, 0) as u64 & mask51) + pow2(51) * ((spec_load8_at(bytes, 6) as u64
            >> 3) & mask51) == (bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (bytes[2]
            * pow2(2 * 8)) + (bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5] * pow2(
            5 * 8,
        )) + (bytes[6] * pow2(6 * 8)) + (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(8 * 8)) + (
        bytes[9] * pow2(9 * 8)) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + ((
        bytes[12] as nat % pow2(6)) * pow2((12 * 8) as nat)),
{
    assert((spec_load8_at(bytes, 0) as u64) & mask51 == (bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(
        1 * 8,
    )) + (bytes[2] * pow2(2 * 8)) + (bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5]
        * pow2(5 * 8)) + ((bytes[6] as nat % pow2(3)) * pow2(6 * 8))) by {
        lemma_load8_at_limb0(bytes);
    }

    assert(((spec_load8_at(bytes, 6) as u64) >> 3) & mask51 == (bytes[6] as nat / pow2(3)) + (
    bytes[7] * pow2((1 * 8 - 3) as nat)) + (bytes[8] * pow2((2 * 8 - 3) as nat)) + (bytes[9] * pow2(
        (3 * 8 - 3) as nat,
    )) + (bytes[10] * pow2((4 * 8 - 3) as nat)) + (bytes[11] * pow2((5 * 8 - 3) as nat)) + ((
    bytes[12] as nat % pow2(6)) * pow2((6 * 8 - 3) as nat))) by {
        lemma_load8_at_limb1(bytes);
    }

    assert(pow2(51) * ((spec_load8_at(bytes, 6) as u64 >> 3) & mask51) == pow2(51) * (
    bytes[6] as nat / pow2(3)) + pow2(51) * (bytes[7] * pow2((1 * 8 - 3) as nat)) + pow2(51) * (
    bytes[8] * pow2((2 * 8 - 3) as nat)) + pow2(51) * (bytes[9] * pow2((3 * 8 - 3) as nat)) + pow2(
        51,
    ) * (bytes[10] * pow2((4 * 8 - 3) as nat)) + pow2(51) * (bytes[11] * pow2((5 * 8 - 3) as nat))
        + pow2(51) * ((bytes[12] as nat % pow2(6)) * pow2((6 * 8 - 3) as nat))) by {
        lemma_mul_distributive_7_terms(
            pow2(51) as int,
            (bytes[6] as nat / pow2(3)) as int,
            (bytes[7] * pow2((1 * 8 - 3) as nat)) as int,
            (bytes[8] * pow2((2 * 8 - 3) as nat)) as int,
            (bytes[9] * pow2((3 * 8 - 3) as nat)) as int,
            (bytes[10] * pow2((4 * 8 - 3) as nat)) as int,
            (bytes[11] * pow2((5 * 8 - 3) as nat)) as int,
            ((bytes[12] as nat % pow2(6)) * pow2((6 * 8 - 3) as nat)) as int,
        );
    }

    assert(((bytes[6] as nat % pow2(3)) * pow2(6 * 8)) + pow2(51) * (bytes[6] as nat / pow2(3))
        == bytes[6] * pow2(6 * 8)) by {
        lemma_assemble_mod_div(bytes[6] as nat, 3, 6 * 8);
    }

    assert(pow2(51) * (bytes[7] * pow2((1 * 8 - 3) as nat)) + pow2(51) * (bytes[8] * pow2(
        (2 * 8 - 3) as nat,
    )) + pow2(51) * (bytes[9] * pow2((3 * 8 - 3) as nat)) + pow2(51) * (bytes[10] * pow2(
        (4 * 8 - 3) as nat,
    )) + pow2(51) * (bytes[11] * pow2((5 * 8 - 3) as nat)) + pow2(51) * ((bytes[12] as nat % pow2(
        6,
    )) * pow2((6 * 8 - 3) as nat)) == (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(8 * 8)) + (
    bytes[9] * pow2(9 * 8)) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + ((
    bytes[12] as nat % pow2(6)) * pow2((12 * 8) as nat))) by {
        lemma_assemble_pow_a_pow(bytes[7] as nat, 6, 1, 3);
        lemma_assemble_pow_a_pow(bytes[8] as nat, 6, 2, 3);
        lemma_assemble_pow_a_pow(bytes[9] as nat, 6, 3, 3);
        lemma_assemble_pow_a_pow(bytes[10] as nat, 6, 4, 3);
        lemma_assemble_pow_a_pow(bytes[11] as nat, 6, 5, 3);
        lemma_assemble_pow_a_pow(bytes[12] as nat % pow2(6), 6, 6, 3);
    }
}

pub proof fn lemma_from_bytes32_to_nat_012(bytes: &[u8; 32])
    ensures
        (spec_load8_at(bytes, 0) as u64 & mask51) + pow2(51) * ((spec_load8_at(bytes, 6) as u64
            >> 3) & mask51) + pow2(102) * ((spec_load8_at(bytes, 12) as u64 >> 6) & mask51) == (
        bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (bytes[2] * pow2(2 * 8)) + (bytes[3]
            * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5] * pow2(5 * 8)) + (bytes[6] * pow2(
            6 * 8,
        )) + (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(8 * 8)) + (bytes[9] * pow2(9 * 8)) + (
        bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + (bytes[12] * pow2(12 * 8)) + (
        bytes[13] * pow2(13 * 8)) + (bytes[14] * pow2(14 * 8)) + (bytes[15] * pow2(15 * 8)) + (
        bytes[16] * pow2(16 * 8)) + (bytes[17] * pow2(17 * 8)) + (bytes[18] * pow2(18 * 8)) + ((
        bytes[19] as nat % pow2(1)) * pow2((19 * 8) as nat)),
{
    assert((spec_load8_at(bytes, 0) as u64 & mask51) + pow2(51) * ((spec_load8_at(bytes, 6) as u64
        >> 3) & mask51) == (bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (bytes[2] * pow2(
        2 * 8,
    )) + (bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5] * pow2(5 * 8)) + (bytes[6]
        * pow2(6 * 8)) + (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(8 * 8)) + (bytes[9] * pow2(
        9 * 8,
    )) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + ((bytes[12] as nat % pow2(6))
        * pow2((12 * 8) as nat))) by {
        lemma_from_bytes32_to_nat_01(bytes);
    }

    assert(((spec_load8_at(bytes, 12) as u64) >> 6) & mask51 == (bytes[12] as nat / pow2(6)) + (
    bytes[13] * pow2((1 * 8 - 6) as nat)) + (bytes[14] * pow2((2 * 8 - 6) as nat)) + (bytes[15]
        * pow2((3 * 8 - 6) as nat)) + (bytes[16] * pow2((4 * 8 - 6) as nat)) + (bytes[17] * pow2(
        (5 * 8 - 6) as nat,
    )) + (bytes[18] * pow2((6 * 8 - 6) as nat)) + ((bytes[19] as nat % pow2(1)) * pow2(
        (7 * 8 - 6) as nat,
    ))) by {
        lemma_load8_at_limb2(bytes);
    }

    assert(pow2(102) * ((spec_load8_at(bytes, 12) as u64 >> 6) & mask51) == pow2(102) * (
    bytes[12] as nat / pow2(6)) + pow2(102) * (bytes[13] * pow2((1 * 8 - 6) as nat)) + pow2(102) * (
    bytes[14] * pow2((2 * 8 - 6) as nat)) + pow2(102) * (bytes[15] * pow2((3 * 8 - 6) as nat))
        + pow2(102) * (bytes[16] * pow2((4 * 8 - 6) as nat)) + pow2(102) * (bytes[17] * pow2(
        (5 * 8 - 6) as nat,
    )) + pow2(102) * (bytes[18] * pow2((6 * 8 - 6) as nat)) + pow2(102) * ((bytes[19] as nat % pow2(
        1,
    )) * pow2((7 * 8 - 6) as nat))) by {
        lemma_mul_distributive_8_terms(
            pow2(102) as int,
            (bytes[12] as nat / pow2(6)) as int,
            (bytes[13] * pow2((1 * 8 - 6) as nat)) as int,
            (bytes[14] * pow2((2 * 8 - 6) as nat)) as int,
            (bytes[15] * pow2((3 * 8 - 6) as nat)) as int,
            (bytes[16] * pow2((4 * 8 - 6) as nat)) as int,
            (bytes[17] * pow2((5 * 8 - 6) as nat)) as int,
            (bytes[18] * pow2((6 * 8 - 6) as nat)) as int,
            ((bytes[19] as nat % pow2(1)) * pow2((7 * 8 - 6) as nat)) as int,
        );
    }

    assert(((bytes[12] as nat % pow2(6)) * pow2((12 * 8) as nat)) + pow2(102) * (bytes[12] as nat
        / pow2(6)) == bytes[12] * pow2(12 * 8)) by {
        lemma_assemble_mod_div(bytes[12] as nat, 6, 12 * 8);
    }

    assert(pow2(102) * (bytes[13] * pow2((1 * 8 - 6) as nat)) + pow2(102) * (bytes[14] * pow2(
        (2 * 8 - 6) as nat,
    )) + pow2(102) * (bytes[15] * pow2((3 * 8 - 6) as nat)) + pow2(102) * (bytes[16] * pow2(
        (4 * 8 - 6) as nat,
    )) + pow2(102) * (bytes[17] * pow2((5 * 8 - 6) as nat)) + pow2(102) * (bytes[18] * pow2(
        (6 * 8 - 6) as nat,
    )) + pow2(102) * ((bytes[19] as nat % pow2(1)) * pow2((7 * 8 - 6) as nat)) == (bytes[13] * pow2(
        13 * 8,
    )) + (bytes[14] * pow2(14 * 8)) + (bytes[15] * pow2(15 * 8)) + (bytes[16] * pow2(16 * 8)) + (
    bytes[17] * pow2(17 * 8)) + (bytes[18] * pow2(18 * 8)) + ((bytes[19] as nat % pow2(1)) * pow2(
        (19 * 8) as nat,
    ))) by {
        lemma_assemble_pow_a_pow(bytes[13] as nat, 12, 1, 6);
        lemma_assemble_pow_a_pow(bytes[14] as nat, 12, 2, 6);
        lemma_assemble_pow_a_pow(bytes[15] as nat, 12, 3, 6);
        lemma_assemble_pow_a_pow(bytes[16] as nat, 12, 4, 6);
        lemma_assemble_pow_a_pow(bytes[17] as nat, 12, 5, 6);
        lemma_assemble_pow_a_pow(bytes[18] as nat, 12, 6, 6);
        lemma_assemble_pow_a_pow(bytes[19] as nat % pow2(1), 12, 7, 6);
    }
}

pub proof fn lemma_from_bytes32_to_nat_0123(bytes: &[u8; 32])
    ensures
        (spec_load8_at(bytes, 0) as u64 & mask51) + pow2(51) * ((spec_load8_at(bytes, 6) as u64
            >> 3) & mask51) + pow2(102) * ((spec_load8_at(bytes, 12) as u64 >> 6) & mask51) + pow2(
            153,
        ) * ((spec_load8_at(bytes, 19) as u64 >> 1) & mask51) == (bytes[0] * pow2(0 * 8)) + (
        bytes[1] * pow2(1 * 8)) + (bytes[2] * pow2(2 * 8)) + (bytes[3] * pow2(3 * 8)) + (bytes[4]
            * pow2(4 * 8)) + (bytes[5] * pow2(5 * 8)) + (bytes[6] * pow2(6 * 8)) + (bytes[7] * pow2(
            7 * 8,
        )) + (bytes[8] * pow2(8 * 8)) + (bytes[9] * pow2(9 * 8)) + (bytes[10] * pow2(10 * 8)) + (
        bytes[11] * pow2(11 * 8)) + (bytes[12] * pow2(12 * 8)) + (bytes[13] * pow2(13 * 8)) + (
        bytes[14] * pow2(14 * 8)) + (bytes[15] * pow2(15 * 8)) + (bytes[16] * pow2(16 * 8)) + (
        bytes[17] * pow2(17 * 8)) + (bytes[18] * pow2(18 * 8)) + (bytes[19] * pow2(19 * 8)) + (
        bytes[20] * pow2(20 * 8)) + (bytes[21] * pow2(21 * 8)) + (bytes[22] * pow2(22 * 8)) + (
        bytes[23] * pow2(23 * 8)) + (bytes[24] * pow2(24 * 8)) + ((bytes[25] as nat % pow2(4))
            * pow2((25 * 8) as nat)),
{
    assert((spec_load8_at(bytes, 0) as u64 & mask51) + pow2(51) * ((spec_load8_at(bytes, 6) as u64
        >> 3) & mask51) + pow2(102) * ((spec_load8_at(bytes, 12) as u64 >> 6) & mask51) == (bytes[0]
        * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (bytes[2] * pow2(2 * 8)) + (bytes[3] * pow2(
        3 * 8,
    )) + (bytes[4] * pow2(4 * 8)) + (bytes[5] * pow2(5 * 8)) + (bytes[6] * pow2(6 * 8)) + (bytes[7]
        * pow2(7 * 8)) + (bytes[8] * pow2(8 * 8)) + (bytes[9] * pow2(9 * 8)) + (bytes[10] * pow2(
        10 * 8,
    )) + (bytes[11] * pow2(11 * 8)) + (bytes[12] * pow2(12 * 8)) + (bytes[13] * pow2(13 * 8)) + (
    bytes[14] * pow2(14 * 8)) + (bytes[15] * pow2(15 * 8)) + (bytes[16] * pow2(16 * 8)) + (bytes[17]
        * pow2(17 * 8)) + (bytes[18] * pow2(18 * 8)) + ((bytes[19] as nat % pow2(1)) * pow2(
        (19 * 8) as nat,
    ))) by {
        lemma_from_bytes32_to_nat_012(bytes);
    }

    assert(((spec_load8_at(bytes, 19) as u64) >> 1) & mask51 == (bytes[19] as nat / pow2(1)) + (
    bytes[20] * pow2((1 * 8 - 1) as nat)) + (bytes[21] * pow2((2 * 8 - 1) as nat)) + (bytes[22]
        * pow2((3 * 8 - 1) as nat)) + (bytes[23] * pow2((4 * 8 - 1) as nat)) + (bytes[24] * pow2(
        (5 * 8 - 1) as nat,
    )) + ((bytes[25] as nat % pow2(4)) * pow2((6 * 8 - 1) as nat))) by {
        lemma_load8_at_limb3(bytes);
    }

    assert(pow2(153) * (((spec_load8_at(bytes, 19) as u64) >> 1) & mask51) == pow2(153) * (
    bytes[19] as nat / pow2(1)) + pow2(153) * (bytes[20] * pow2((1 * 8 - 1) as nat)) + pow2(153) * (
    bytes[21] * pow2((2 * 8 - 1) as nat)) + pow2(153) * (bytes[22] * pow2((3 * 8 - 1) as nat))
        + pow2(153) * (bytes[23] * pow2((4 * 8 - 1) as nat)) + pow2(153) * (bytes[24] * pow2(
        (5 * 8 - 1) as nat,
    )) + pow2(153) * ((bytes[25] as nat % pow2(4)) * pow2((6 * 8 - 1) as nat))) by {
        lemma_mul_distributive_7_terms(
            pow2(153) as int,
            (bytes[19] as nat / pow2(1)) as int,
            (bytes[20] * pow2((1 * 8 - 1) as nat)) as int,
            (bytes[21] * pow2((2 * 8 - 1) as nat)) as int,
            (bytes[22] * pow2((3 * 8 - 1) as nat)) as int,
            (bytes[23] * pow2((4 * 8 - 1) as nat)) as int,
            (bytes[24] * pow2((5 * 8 - 1) as nat)) as int,
            ((bytes[25] as nat % pow2(4)) * pow2((6 * 8 - 1) as nat)) as int,
        );
    }

    assert(((bytes[19] as nat % pow2(1)) * pow2((19 * 8) as nat)) + pow2(153) * (bytes[19] as nat
        / pow2(1)) == bytes[19] * pow2(19 * 8)) by {
        lemma_assemble_mod_div(bytes[19] as nat, 1, 19 * 8)
    }

    assert(pow2(153) * (bytes[20] * pow2((1 * 8 - 1) as nat)) + pow2(153) * (bytes[21] * pow2(
        (2 * 8 - 1) as nat,
    )) + pow2(153) * (bytes[22] * pow2((3 * 8 - 1) as nat)) + pow2(153) * (bytes[23] * pow2(
        (4 * 8 - 1) as nat,
    )) + pow2(153) * (bytes[24] * pow2((5 * 8 - 1) as nat)) + pow2(153) * ((bytes[25] as nat % pow2(
        4,
    )) * pow2((6 * 8 - 1) as nat)) == (bytes[20] * pow2(20 * 8)) + (bytes[21] * pow2(21 * 8)) + (
    bytes[22] * pow2(22 * 8)) + (bytes[23] * pow2(23 * 8)) + (bytes[24] * pow2(24 * 8)) + ((
    bytes[25] as nat % pow2(4)) * pow2((25 * 8) as nat))) by {
        lemma_assemble_pow_a_pow(bytes[20] as nat, 19, 1, 1);
        lemma_assemble_pow_a_pow(bytes[21] as nat, 19, 2, 1);
        lemma_assemble_pow_a_pow(bytes[22] as nat, 19, 3, 1);
        lemma_assemble_pow_a_pow(bytes[23] as nat, 19, 4, 1);
        lemma_assemble_pow_a_pow(bytes[24] as nat, 19, 5, 1);
        lemma_assemble_pow_a_pow(bytes[25] as nat % pow2(4), 19, 6, 1);
    }
}

pub proof fn lemma_from_bytes32_to_nat_01234(bytes: &[u8; 32])
    ensures
        (spec_load8_at(bytes, 0) as u64 & mask51) + pow2(51) * ((spec_load8_at(bytes, 6) as u64
            >> 3) & mask51) + pow2(102) * ((spec_load8_at(bytes, 12) as u64 >> 6) & mask51) + pow2(
            153,
        ) * ((spec_load8_at(bytes, 19) as u64 >> 1) & mask51) + pow2(204) * ((spec_load8_at(
            bytes,
            24,
        ) as u64 >> 12) & mask51) == (bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (bytes[2]
            * pow2(2 * 8)) + (bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5] * pow2(
            5 * 8,
        )) + (bytes[6] * pow2(6 * 8)) + (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(8 * 8)) + (
        bytes[9] * pow2(9 * 8)) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + (
        bytes[12] * pow2(12 * 8)) + (bytes[13] * pow2(13 * 8)) + (bytes[14] * pow2(14 * 8)) + (
        bytes[15] * pow2(15 * 8)) + (bytes[16] * pow2(16 * 8)) + (bytes[17] * pow2(17 * 8)) + (
        bytes[18] * pow2(18 * 8)) + (bytes[19] * pow2(19 * 8)) + (bytes[20] * pow2(20 * 8)) + (
        bytes[21] * pow2(21 * 8)) + (bytes[22] * pow2(22 * 8)) + (bytes[23] * pow2(23 * 8)) + (
        bytes[24] * pow2(24 * 8)) + (bytes[25] * pow2(25 * 8)) + (bytes[26] * pow2(26 * 8)) + (
        bytes[27] * pow2(27 * 8)) + (bytes[28] * pow2(28 * 8)) + (bytes[29] * pow2(29 * 8)) + (
        bytes[30] * pow2(30 * 8)) + ((bytes[31] as nat % pow2(7)) * pow2((31 * 8) as nat)),
{
    assert((spec_load8_at(bytes, 0) as u64 & mask51) + pow2(51) * ((spec_load8_at(bytes, 6) as u64
        >> 3) & mask51) + pow2(102) * ((spec_load8_at(bytes, 12) as u64 >> 6) & mask51) + pow2(153)
        * ((spec_load8_at(bytes, 19) as u64 >> 1) & mask51) == (bytes[0] * pow2(0 * 8)) + (bytes[1]
        * pow2(1 * 8)) + (bytes[2] * pow2(2 * 8)) + (bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(
        4 * 8,
    )) + (bytes[5] * pow2(5 * 8)) + (bytes[6] * pow2(6 * 8)) + (bytes[7] * pow2(7 * 8)) + (bytes[8]
        * pow2(8 * 8)) + (bytes[9] * pow2(9 * 8)) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(
        11 * 8,
    )) + (bytes[12] * pow2(12 * 8)) + (bytes[13] * pow2(13 * 8)) + (bytes[14] * pow2(14 * 8)) + (
    bytes[15] * pow2(15 * 8)) + (bytes[16] * pow2(16 * 8)) + (bytes[17] * pow2(17 * 8)) + (bytes[18]
        * pow2(18 * 8)) + (bytes[19] * pow2(19 * 8)) + (bytes[20] * pow2(20 * 8)) + (bytes[21]
        * pow2(21 * 8)) + (bytes[22] * pow2(22 * 8)) + (bytes[23] * pow2(23 * 8)) + (bytes[24]
        * pow2(24 * 8)) + ((bytes[25] as nat % pow2(4)) * pow2((25 * 8) as nat))) by {
        lemma_from_bytes32_to_nat_0123(bytes);
    }

    assert(((spec_load8_at(bytes, 24) as u64) >> 12) & mask51 == (bytes[25] as nat / pow2(4)) + (
    bytes[26] * pow2((2 * 8 - 12) as nat)) + (bytes[27] * pow2((3 * 8 - 12) as nat)) + (bytes[28]
        * pow2((4 * 8 - 12) as nat)) + (bytes[29] * pow2((5 * 8 - 12) as nat)) + (bytes[30] * pow2(
        (6 * 8 - 12) as nat,
    )) + ((bytes[31] as nat % pow2(7)) * pow2((7 * 8 - 12) as nat))) by {
        lemma_load8_at_limb4(bytes);
    }

    assert(pow2(204) * (((spec_load8_at(bytes, 24) as u64) >> 12) & mask51) == pow2(204) * (
    bytes[25] as nat / pow2(4)) + pow2(204) * (bytes[26] * pow2((2 * 8 - 12) as nat)) + pow2(204)
        * (bytes[27] * pow2((3 * 8 - 12) as nat)) + pow2(204) * (bytes[28] * pow2(
        (4 * 8 - 12) as nat,
    )) + pow2(204) * (bytes[29] * pow2((5 * 8 - 12) as nat)) + pow2(204) * (bytes[30] * pow2(
        (6 * 8 - 12) as nat,
    )) + pow2(204) * ((bytes[31] as nat % pow2(7)) * pow2((7 * 8 - 12) as nat))) by {
        lemma_mul_distributive_7_terms(
            pow2(204) as int,
            (bytes[25] as nat / pow2(4)) as int,
            (bytes[26] * pow2((2 * 8 - 12) as nat)) as int,
            (bytes[27] * pow2((3 * 8 - 12) as nat)) as int,
            (bytes[28] * pow2((4 * 8 - 12) as nat)) as int,
            (bytes[29] * pow2((5 * 8 - 12) as nat)) as int,
            (bytes[30] * pow2((6 * 8 - 12) as nat)) as int,
            ((bytes[31] as nat % pow2(7)) * pow2((7 * 8 - 12) as nat)) as int,
        );
    }

    assert(((bytes[25] as nat % pow2(4)) * pow2((25 * 8) as nat)) + pow2(204) * (bytes[25] as nat
        / pow2(4)) == bytes[25] * pow2(25 * 8)) by {
        lemma_assemble_mod_div(bytes[25] as nat, 4, 25 * 8)
    }

    assert(pow2(204) * (bytes[26] * pow2((2 * 8 - 12) as nat)) + pow2(204) * (bytes[27] * pow2(
        (3 * 8 - 12) as nat,
    )) + pow2(204) * (bytes[28] * pow2((4 * 8 - 12) as nat)) + pow2(204) * (bytes[29] * pow2(
        (5 * 8 - 12) as nat,
    )) + pow2(204) * (bytes[30] * pow2((6 * 8 - 12) as nat)) + pow2(204) * ((bytes[31] as nat
        % pow2(7)) * pow2((7 * 8 - 12) as nat)) == (bytes[26] * pow2(26 * 8)) + (bytes[27] * pow2(
        27 * 8,
    )) + (bytes[28] * pow2(28 * 8)) + (bytes[29] * pow2(29 * 8)) + (bytes[30] * pow2(30 * 8)) + ((
    bytes[31] as nat % pow2(7)) * pow2((31 * 8) as nat))) by {
        lemma_assemble_pow_a_pow(bytes[26] as nat, 24, 2, 12);
        lemma_assemble_pow_a_pow(bytes[27] as nat, 24, 3, 12);
        lemma_assemble_pow_a_pow(bytes[28] as nat, 24, 4, 12);
        lemma_assemble_pow_a_pow(bytes[29] as nat, 24, 5, 12);
        lemma_assemble_pow_a_pow(bytes[30] as nat, 24, 6, 12);
        lemma_assemble_pow_a_pow(bytes[31] as nat % pow2(7), 24, 7, 12);
    }
}

pub proof fn lemma_from_bytes32_to_nat(bytes: &[u8; 32])
    ensures
        u64_5_as_nat(
            [
                spec_load8_at(bytes, 0) as u64 & mask51,
                (spec_load8_at(bytes, 6) as u64 >> 3) & mask51,
                (spec_load8_at(bytes, 12) as u64 >> 6) & mask51,
                (spec_load8_at(bytes, 19) as u64 >> 1) & mask51,
                (spec_load8_at(bytes, 24) as u64 >> 12) & mask51,
            ],
        ) == (bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (bytes[2] * pow2(2 * 8)) + (
        bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5] * pow2(5 * 8)) + (bytes[6]
            * pow2(6 * 8)) + (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(8 * 8)) + (bytes[9] * pow2(
            9 * 8,
        )) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + (bytes[12] * pow2(12 * 8))
            + (bytes[13] * pow2(13 * 8)) + (bytes[14] * pow2(14 * 8)) + (bytes[15] * pow2(15 * 8))
            + (bytes[16] * pow2(16 * 8)) + (bytes[17] * pow2(17 * 8)) + (bytes[18] * pow2(18 * 8))
            + (bytes[19] * pow2(19 * 8)) + (bytes[20] * pow2(20 * 8)) + (bytes[21] * pow2(21 * 8))
            + (bytes[22] * pow2(22 * 8)) + (bytes[23] * pow2(23 * 8)) + (bytes[24] * pow2(24 * 8))
            + (bytes[25] * pow2(25 * 8)) + (bytes[26] * pow2(26 * 8)) + (bytes[27] * pow2(27 * 8))
            + (bytes[28] * pow2(28 * 8)) + (bytes[29] * pow2(29 * 8)) + (bytes[30] * pow2(30 * 8))
            + ((bytes[31] as nat % pow2(7)) * pow2((31 * 8) as nat)),
{
    lemma_from_bytes32_to_nat_01234(bytes);
}

pub proof fn lemma_as_nat_32_mod_255(bytes: &[u8; 32])
    ensures
        bytes32_to_nat(bytes) % pow2(255) == (bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (
        bytes[2] * pow2(2 * 8)) + (bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5]
            * pow2(5 * 8)) + (bytes[6] * pow2(6 * 8)) + (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(
            8 * 8,
        )) + (bytes[9] * pow2(9 * 8)) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + (
        bytes[12] * pow2(12 * 8)) + (bytes[13] * pow2(13 * 8)) + (bytes[14] * pow2(14 * 8)) + (
        bytes[15] * pow2(15 * 8)) + (bytes[16] * pow2(16 * 8)) + (bytes[17] * pow2(17 * 8)) + (
        bytes[18] * pow2(18 * 8)) + (bytes[19] * pow2(19 * 8)) + (bytes[20] * pow2(20 * 8)) + (
        bytes[21] * pow2(21 * 8)) + (bytes[22] * pow2(22 * 8)) + (bytes[23] * pow2(23 * 8)) + (
        bytes[24] * pow2(24 * 8)) + (bytes[25] * pow2(25 * 8)) + (bytes[26] * pow2(26 * 8)) + (
        bytes[27] * pow2(27 * 8)) + (bytes[28] * pow2(28 * 8)) + (bytes[29] * pow2(29 * 8)) + (
        bytes[30] * pow2(30 * 8)) + ((bytes[31] as nat % pow2(7)) * pow2(31 * 8)),
{
    assert(bytes32_to_nat(bytes) == (bytes[0] * pow2(0 * 8)) + (bytes[1] * pow2(1 * 8)) + (bytes[2]
        * pow2(2 * 8)) + (bytes[3] * pow2(3 * 8)) + (bytes[4] * pow2(4 * 8)) + (bytes[5] * pow2(
        5 * 8,
    )) + (bytes[6] * pow2(6 * 8)) + (bytes[7] * pow2(7 * 8)) + (bytes[8] * pow2(8 * 8)) + (bytes[9]
        * pow2(9 * 8)) + (bytes[10] * pow2(10 * 8)) + (bytes[11] * pow2(11 * 8)) + (bytes[12]
        * pow2(12 * 8)) + (bytes[13] * pow2(13 * 8)) + (bytes[14] * pow2(14 * 8)) + (bytes[15]
        * pow2(15 * 8)) + (bytes[16] * pow2(16 * 8)) + (bytes[17] * pow2(17 * 8)) + (bytes[18]
        * pow2(18 * 8)) + (bytes[19] * pow2(19 * 8)) + (bytes[20] * pow2(20 * 8)) + (bytes[21]
        * pow2(21 * 8)) + (bytes[22] * pow2(22 * 8)) + (bytes[23] * pow2(23 * 8)) + (bytes[24]
        * pow2(24 * 8)) + (bytes[25] * pow2(25 * 8)) + (bytes[26] * pow2(26 * 8)) + (bytes[27]
        * pow2(27 * 8)) + (bytes[28] * pow2(28 * 8)) + (bytes[29] * pow2(29 * 8)) + (bytes[30]
        * pow2(30 * 8)) + (bytes[31] * pow2(31 * 8)) == pow2_sum_u8(bytes, 0, 8, 30) + (bytes[31]
        * pow2(31 * 8))) by {
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(bytes[0] == bytes[0] * pow2(0)) by {
            lemma_mul_basics_3(bytes[0] as int);
        }
        reveal_with_fuel(pow2_sum_u8, 31);
    }
    assert(bytes32_to_nat(bytes) % pow2(255) == (pow2_sum_u8(bytes, 0, 8, 30) + bytes[31] * pow2(
        31 * 8,
    )) as nat % pow2(255));

    assert((pow2_sum_u8(bytes, 0, 8, 30) + bytes[31] * pow2(31 * 8)) as nat % pow2(255)
        == pow2_sum_u8(bytes, 0, 8, 30) + (bytes[31] * pow2(31 * 8)) as nat % pow2(255)) by {
        assert(pow2_sum_u8(bytes, 0, 8, 30) < pow2(31 * 8)) by {
            assert forall|i: nat| 0 <= i <= 30 implies bytes[i as int] < pow2(8) by {
                lemma_u8_lt_pow2_8(bytes[i as int]);
            }
            lemma_pow2_sum_u8_bounds(bytes, 0, 8, 30);
        }
        assert((pow2_sum_u8(bytes, 0, 8, 30) + bytes[31] * pow2(31 * 8)) as nat % pow2(255)
            == pow2_sum_u8(bytes, 0, 8, 30) % pow2(255) + (bytes[31] * pow2(31 * 8)) as nat % pow2(
            255,
        )) by {
            lemma_binary_sum_mod_decomposition(
                pow2_sum_u8(bytes, 0, 8, 30),
                bytes[31] as nat,
                31 * 8,
                255,
            );
        }

        assert(pow2_sum_u8(bytes, 0, 8, 30) % pow2(255) == pow2_sum_u8(bytes, 0, 8, 30)) by {
            assert(pow2(31 * 8) < pow2(255)) by {
                lemma_pow2_strictly_increases(31 * 8, 255);
            }
            lemma_small_mod(pow2_sum_u8(bytes, 0, 8, 30), pow2(255));
        }
    }

    assert((bytes[31] as nat * pow2(31 * 8)) % pow2(255) == ((bytes[31] as nat % pow2(7)) * pow2(
        31 * 8,
    ))) by {
        lemma_pow2_mul_mod(bytes[31] as nat, 31 * 8, 255);
    }
}

} // verus!
