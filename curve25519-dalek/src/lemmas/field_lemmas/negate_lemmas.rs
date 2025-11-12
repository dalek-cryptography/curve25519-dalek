#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::as_nat_lemmas::*;
use super::reduce_lemmas::*;

use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

pub open spec fn all_neg_limbs_positive(limbs: [u64; 5]) -> bool {
    &&& 36028797018963664u64 >= limbs[0]
    &&& 36028797018963952u64 >= limbs[1]
    &&& 36028797018963952u64 >= limbs[2]
    &&& 36028797018963952u64 >= limbs[3]
    &&& 36028797018963952u64 >= limbs[4]
}

pub proof fn lemma_neg_no_underflow(limbs: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
    ensures
        all_neg_limbs_positive(limbs),
{
    lemma2_to64_rest();  // pow2(51)
    assert forall|i: int| 0 <= i < 5 implies limbs[i] < 16 * (pow2(51) - 19) by {
        lemma_shift_is_pow2(51);
    }
}

pub proof fn proof_negate(limbs: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
        all_neg_limbs_positive(limbs),
    ensures
        forall|i: int| 0 <= i < 5 ==> spec_negate(limbs)[i] < (1u64 << 52),
        // Assume we start with l = (l0, l1, l2, l3, l4).
        // Using c0 = 2^51 - 19 and c = 2^51 - 1, we can see that
        // ( 36028797018963664u64 - l0,
        //   36028797018963952u64 - l1,
        //   36028797018963952u64 - l2,
        //   36028797018963952u64 - l3,
        //   36028797018963952u64 - l4 )
        // is just 16 * (c0, c, c, c, c) - l (in vector notation)
        // Further, as_nat((c0, c, c, c, c)) = p, so
        // as_nat(16 * (c0, c, c, c, c) - l) is 16p - as_nat(l)
        // We know as_nat(reduce(v)) = as_nat(v) - p * (v4 >> 51) for any v.
        // This gives us the identity
        // as_nat(negate(l)) = as_nat(reduce(16 * (c0, c, c, c, c) - l))
        //                   = 16p - as_nat(l) - p * ((16c - l4) >> 51)
        // Note that (16c - l4) >> 51 is either 14 or 15, in either case < 16.
        as_nat(spec_negate(limbs)) == 16 * p() - as_nat(limbs) - p() * ((36028797018963952u64
            - limbs[4]) as u64 >> 51),
        (as_nat(spec_negate(limbs)) + as_nat(limbs)) % p() == 0,
{
    proof_reduce(pre_reduce_limbs(limbs));

    let c0 = (pow2(51) - 19);
    let c = (pow2(51) - 1);
    lemma2_to64_rest();  // get pow2(51)
    // solver knows 36028797018963664u64 == 16 * c0
    // solver knows 36028797018963952u64 == 16 * c;

    lemma_neg_no_underflow(limbs);

    // Introduce 16p as a vector
    let v = [(16 * c0) as u64, (16 * c) as u64, (16 * c) as u64, (16 * c) as u64, (16 * c) as u64];

    assert(as_nat(v) == 16 * p()) by {
        // by definition of as_nat
        assert(as_nat(v) == 16 * c0 + pow2(51) * (16 * c) + pow2(102) * (16 * c) + pow2(153) * (16
            * c) + pow2(204) * (16 * c));

        // solver can reorder factors and pull out 16 on its own
        // ...

        // Write out `c`s and sum up powers
        assert(p() == c0 + pow2(51) * c + pow2(102) * c + pow2(153) * c + pow2(204) * c) by {
            lemma_pow2_adds(51, 51);
            lemma_pow2_adds(51, 102);
            lemma_pow2_adds(51, 153);
            lemma_pow2_adds(51, 204);
        }
    }

    let l0 = limbs[0];
    let l1 = limbs[1];
    let l2 = limbs[2];
    let l3 = limbs[3];
    let l4 = limbs[4];

    assert(as_nat(
        [
            (16 * c0 - l0) as u64,
            (16 * c - l1) as u64,
            (16 * c - l2) as u64,
            (16 * c - l3) as u64,
            (16 * c - l4) as u64,
        ],
    ) == as_nat(v) - as_nat(limbs)) by {
        lemma_as_nat_sub(v, limbs);
    }

    let k = (16 * c - l4) as u64 >> 51;

    assert(16 * p() - as_nat(limbs) - p() * k + as_nat(limbs) == p() * (16 - k)) by {
        lemma_mul_is_distributive_sub(p() as int, 16, k as int)
    }

    assert((p() * (16 - k)) as nat % p() == 0) by {
        assert(k <= 16) by {
            assert(k <= (16 * pow2(51)) as u64 >> 51) by {
                lemma_shr_le_u64((16 * c - l4) as u64, (16 * pow2(51)) as u64, 51);
            }
            // 16 * 2^51 / 2^51 = 16
            assert(((16 * 0x8000000000000) as u64 >> 51) == 16) by (compute);
        }
        lemma_mod_multiples_basic((16 - k) as int, p() as int);
    }
}

} // verus!
