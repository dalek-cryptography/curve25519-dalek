#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_verus::bit_lemmas::*;
use super::super::common_verus::div_mod_lemmas::*;
use super::super::common_verus::mask_lemmas::*;
use super::super::common_verus::mul_lemmas::*;
use super::super::common_verus::pow_lemmas::*;
use super::super::common_verus::shift_lemmas::*;

use super::field_core::*;
use super::load8_lemmas::*;

verus! {

pub proof fn assemble_mod_div(a: nat, d: nat, b: nat)
    ensures
        (a % pow2(d)) * pow2(b) + pow2(b + d) * (a / pow2(d))
        ==
        a * pow2(b)
{
    let pb = pow2(b);
    let pd = pow2(d);
    let pbd = pow2(b + d);

    assert(pbd == pb *  pd) by {
        lemma_pow2_adds(b, d);
    }

    let amod = a % pd;
    let adiv = a / pd;

    assert( pbd * adiv == (pd * adiv) * pb) by {
        lemma_mul_is_associative(pb as int, pd as int, adiv as int);
        lemma_mul_is_commutative(pb as int, (pd * adiv) as int);
    }

    assert( amod * pb + (pd * adiv) * pb == (amod + pd * adiv) * pb) by {
        lemma_mul_is_distributive_add_other_way(pb as int, amod as int, (pd * adiv) as int);
    }

    assert(amod + pd * adiv == a) by {
        assert(pd > 0) by {
            lemma_pow2_pos(d);
        }
        lemma_fundamental_div_mod(a as int, pd as int);
    }

}

pub proof fn assemble_pow_a_pow(a: nat, j: nat, k: nat, l: nat)
    requires
        k * 8 > l
    ensures
        pow2(j * 8 + l) * (a * pow2((k * 8 - l) as nat))
        ==
        a * pow2((j + k) * 8)
{
    let d = (k * 8 - l) as nat;
    let dd = j * 8 + l;
    let pjl = pow2(j * 8 + l);

    assert(
        pjl * (a * pow2(d)) == (a * pow2(d)) * pjl
    ) by {
        lemma_mul_is_commutative(pjl as int, a * pow2(d) as int);
    }

    assert(
        (a * pow2(d)) * pjl == a * pow2(d + dd)
    ) by {
        lemma_mul_is_associative(a as int, pow2(d) as int, pjl as int);
        lemma_pow2_adds(d, dd);
    }

    assert( d + dd == (j + k) * 8) by {
        assert((j + k) * 8 == j * 8 + k * 8) by {
            lemma_mul_is_distributive_add_other_way( 8, d as int, dd as int);
        }
    }
}

pub proof fn from_bytes_as_nat_12(bytes: &[u8; 32])
    ensures
        (load8_at_spec(bytes,  0) as u64 & mask51) +
        pow2(51) * ((load8_at_spec(bytes,  6) as u64 >>  3) & mask51)
        ==
        (bytes[ 0] * pow2( 0 * 8)) +
        (bytes[ 1] * pow2( 1 * 8)) +
        (bytes[ 2] * pow2( 2 * 8)) +
        (bytes[ 3] * pow2( 3 * 8)) +
        (bytes[ 4] * pow2( 4 * 8)) +
        (bytes[ 5] * pow2( 5 * 8)) +
        (bytes[ 6] * pow2( 6 * 8)) +
        (bytes[ 7] * pow2( 7 * 8)) +
        (bytes[ 8] * pow2( 8 * 8)) +
        (bytes[ 9] * pow2( 9 * 8)) +
        (bytes[10] * pow2(10 * 8)) +
        (bytes[11] * pow2(11 * 8)) +
        ((bytes[12] as nat % pow2(6)) * pow2((12 * 8) as nat))
{
    assert(
        (load8_at_spec(bytes,  0) as u64) & mask51
        ==
        (bytes[0] * pow2(0 * 8)) +
        (bytes[1] * pow2(1 * 8)) +
        (bytes[2] * pow2(2 * 8)) +
        (bytes[3] * pow2(3 * 8)) +
        (bytes[4] * pow2(4 * 8)) +
        (bytes[5] * pow2(5 * 8)) +
        ((bytes[6] as nat % pow2(3)) * pow2(6 * 8))
    ) by {
        load8_limb0(bytes);
    }

    assert(
        ((load8_at_spec(bytes,  6) as u64) >> 3) & mask51
        ==
        (bytes[ 6] as nat / pow2(3)) +
        (bytes[ 7] * pow2((1 * 8 - 3) as nat)) +
        (bytes[ 8] * pow2((2 * 8 - 3) as nat)) +
        (bytes[ 9] * pow2((3 * 8 - 3) as nat)) +
        (bytes[10] * pow2((4 * 8 - 3) as nat)) +
        (bytes[11] * pow2((5 * 8 - 3) as nat)) +
        ((bytes[12] as nat % pow2(6)) * pow2((6 * 8 - 3) as nat))
    ) by {
        load8_limb1(bytes);
    }

    assert(
        pow2(51) * ((load8_at_spec(bytes,  6) as u64 >>  3) & mask51)
        ==
        pow2(51) * (bytes[ 6] as nat / pow2(3)) +
        pow2(51) * (bytes[ 7] * pow2((1 * 8 - 3) as nat)) +
        pow2(51) * (bytes[ 8] * pow2((2 * 8 - 3) as nat)) +
        pow2(51) * (bytes[ 9] * pow2((3 * 8 - 3) as nat)) +
        pow2(51) * (bytes[10] * pow2((4 * 8 - 3) as nat)) +
        pow2(51) * (bytes[11] * pow2((5 * 8 - 3) as nat)) +
        pow2(51) * ((bytes[12] as nat % pow2(6)) * pow2((6 * 8 - 3) as nat))
    ) by {
        mul_7_terms(
            pow2(51) as int,
            (bytes[ 6] as nat / pow2(3)) as int,
            (bytes[ 7] * pow2((1 * 8 - 3) as nat)) as int,
            (bytes[ 8] * pow2((2 * 8 - 3) as nat)) as int,
            (bytes[ 9] * pow2((3 * 8 - 3) as nat)) as int,
            (bytes[10] * pow2((4 * 8 - 3) as nat)) as int,
            (bytes[11] * pow2((5 * 8 - 3) as nat)) as int,
            ((bytes[12] as nat % pow2(6)) * pow2((6 * 8 - 3) as nat)) as int
        )
    }

    assert(
        ((bytes[6] as nat % pow2(3)) * pow2(6 * 8)) + pow2(51) * (bytes[ 6] as nat / pow2(3))
        ==
        bytes[6] * pow2(6 * 8)
    ) by {
        assemble_mod_div(bytes[6] as nat, 3, 6 * 8)
    }

    assert(
        pow2(51) * (bytes[ 7] * pow2((1 * 8 - 3) as nat)) +
        pow2(51) * (bytes[ 8] * pow2((2 * 8 - 3) as nat)) +
        pow2(51) * (bytes[ 9] * pow2((3 * 8 - 3) as nat)) +
        pow2(51) * (bytes[10] * pow2((4 * 8 - 3) as nat)) +
        pow2(51) * (bytes[11] * pow2((5 * 8 - 3) as nat)) +
        pow2(51) * ((bytes[12] as nat % pow2(6)) * pow2((6 * 8 - 3) as nat))
        ==
        (bytes[ 7] * pow2( 7 * 8)) +
        (bytes[ 8] * pow2( 8 * 8)) +
        (bytes[ 9] * pow2( 9 * 8)) +
        (bytes[10] * pow2(10 * 8)) +
        (bytes[11] * pow2(11 * 8)) +
        ((bytes[12] as nat % pow2(6)) * pow2((12 * 8) as nat))
    ) by {
        assemble_pow_a_pow(bytes[ 7] as nat, 6, 1, 3);
        assemble_pow_a_pow(bytes[ 8] as nat, 6, 2, 3);
        assemble_pow_a_pow(bytes[ 9] as nat, 6, 3, 3);
        assemble_pow_a_pow(bytes[10] as nat, 6, 4, 3);
        assemble_pow_a_pow(bytes[11] as nat, 6, 5, 3);
        assemble_pow_a_pow(bytes[12] as nat % pow2(6), 6, 6, 3);
    }
}

}
