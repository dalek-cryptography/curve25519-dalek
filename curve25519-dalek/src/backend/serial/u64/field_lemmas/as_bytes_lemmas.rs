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

use super::compute_q_lemmas::*;
use super::field_core::*;
use super::reduce_lemmas::*;

verus! {

pub proof fn as_bytes_boundaries1(raw_limbs: [u64; 5])
    ensures
        spec_reduce(raw_limbs)[0] + 19 < u64::MAX,
        spec_reduce(raw_limbs)[1] + 2 < u64::MAX,
        spec_reduce(raw_limbs)[2] + 2 < u64::MAX,
        spec_reduce(raw_limbs)[3] + 2 < u64::MAX,
        spec_reduce(raw_limbs)[4] + 2 < u64::MAX,
        forall|i: int| 0 <= i <= 4 ==> compute_q_arr(spec_reduce(raw_limbs))[i] as u64 <= 2,
        (1u64 << 52) + 19 <= u64::MAX,
        ((1u64 << 52) + 19) as u64 >> 51 == 2,
        ((1u64 << 52) + 2) as u64 >> 51 == 2,
{
    lemma_reduce(raw_limbs);

    let limbs = spec_reduce(raw_limbs);

    assert((1u64 << 52) + 19 <= u64::MAX) by (compute);
    assert(((1u64 << 52) + 19) as u64 >> 51 == 2) by (compute);
    assert(((1u64 << 52) + 2) as u64 >> 51 == 2) by (compute);

    let q_arr = compute_q_arr(limbs);
    let q0 = q_arr[0];
    let q1 = q_arr[1];
    let q2 = q_arr[2];
    let q3 = q_arr[3];
    let q4 = q_arr[4];

    assert(q0 <= 2) by {
        lemma_shr_le_u64((limbs[0] + 19) as u64, ((1u64 << 52) + 19) as u64, 51);
    }

    assert(q1 <= 2) by {
        lemma_shr_le_u64((limbs[1] + q0) as u64, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(q2 <= 2) by {
        lemma_shr_le_u64((limbs[2] + q1) as u64, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(q3 <= 2) by {
        lemma_shr_le_u64((limbs[3] + q2) as u64, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(q4 <= 2) by {
        lemma_shr_le_u64((limbs[4] + q3) as u64, ((1u64 << 52) + 2) as u64, 51);
    }
}

pub proof fn as_bytes_boundaries2(raw_limbs: [u64; 5])
    ensures
        mask51 == (1u64 << 51) - 1,
        // no `forall` for pattern match reasons
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[0]
            >> 51 <= 2,
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[1]
            >> 51 <= 2,
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[2]
            >> 51 <= 2,
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[3]
            >> 51 <= 2,
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[4]
            >> 51 <= 2,
{
    as_bytes_boundaries1(raw_limbs);
    let limbs = spec_reduce(raw_limbs);
    let q = compute_q_spec(limbs);

    lemma_reduce(raw_limbs);
    lemma_reduce_bound_2p(raw_limbs);

    assert(mask51 == (1u64 << 51) - 1) by (compute);

    assert(q == 0 || q == 1) by {
        lemma_compute_q(limbs, q);
    }

    assert(limbs[0] < 1u64 << 52);

    let l = compute_unmasked_limbs(limbs, q);
    let l0 = l[0];
    let l1 = l[1];
    let l2 = l[2];
    let l3 = l[3];
    let l4 = l[4];

    assert(l0 >> 51 <= 2) by {
        lemma_shr_le_u64(l0, ((1u64 << 52) + 19) as u64, 51);
    }

    assert(l1 >> 51 <= 2) by {
        lemma_shr_le_u64(l1, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(l2 >> 51 <= 2) by {
        lemma_shr_le_u64(l2, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(l3 >> 51 <= 2) by {
        lemma_shr_le_u64(l3, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(l4 >> 51 <= 2) by {
        lemma_shr_le_u64(l4, ((1u64 << 52) + 2) as u64, 51);
    }
}

} // verus!
