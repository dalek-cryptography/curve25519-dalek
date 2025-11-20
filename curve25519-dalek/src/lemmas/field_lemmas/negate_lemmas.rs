#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::reduce_lemmas::*;
use super::u64_5_as_nat_lemmas::*;

use super::super::common_lemmas::shift_lemmas::*;

use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::field_specs::*;
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
        // Further, u64_5_as_nat((c0, c, c, c, c)) = p, so
        // u64_5_as_nat(16 * (c0, c, c, c, c) - l) is 16p - u64_5_as_nat(l)
        // We know u64_5_as_nat(reduce(v)) = u64_5_as_nat(v) - p * (v4 >> 51) for any v.
        // This gives us the identity
        // u64_5_as_nat(negate(l)) = u64_5_as_nat(reduce(16 * (c0, c, c, c, c) - l))
        //                   = 16p - u64_5_as_nat(l) - p * ((16c - l4) >> 51)
        // Note that (16c - l4) >> 51 is either 14 or 15, in either case < 16.
        u64_5_as_nat(spec_negate(limbs)) == 16 * p() - u64_5_as_nat(limbs) - p() * ((
        36028797018963952u64 - limbs[4]) as u64 >> 51),
        (u64_5_as_nat(spec_negate(limbs)) + u64_5_as_nat(limbs)) % p() == 0,
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

    assert(u64_5_as_nat(v) == 16 * p()) by {
        // by definition of u64_5_as_nat
        assert(u64_5_as_nat(v) == 16 * c0 + pow2(51) * (16 * c) + pow2(102) * (16 * c) + pow2(153)
            * (16 * c) + pow2(204) * (16 * c));

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

    assert(u64_5_as_nat(
        [
            (16 * c0 - l0) as u64,
            (16 * c - l1) as u64,
            (16 * c - l2) as u64,
            (16 * c - l3) as u64,
            (16 * c - l4) as u64,
        ],
    ) == u64_5_as_nat(v) - u64_5_as_nat(limbs)) by {
        lemma_u64_5_as_nat_sub(v, limbs);
    }

    let k = (16 * c - l4) as u64 >> 51;

    assert(16 * p() - u64_5_as_nat(limbs) - p() * k + u64_5_as_nat(limbs) == p() * (16 - k)) by {
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

pub proof fn lemma_neg(elem: &FieldElement51)
    requires
// negate postcondition

        (u64_5_as_nat(spec_negate(elem.limbs)) + u64_5_as_nat(elem.limbs)) % p() == 0,
    ensures
        u64_5_as_nat(spec_negate(elem.limbs)) % p() == math_field_neg(spec_field_element(elem)),
{
    let x = spec_field_element(elem);
    let y = u64_5_as_nat(spec_negate(elem.limbs)) % p();

    assert(p() > 0) by {
        pow255_gt_19();
    }

    assert(x < p()) by {
        lemma_mod_bound(u64_5_as_nat(elem.limbs) as int, p() as int);
    }
    assert(y < p()) by {
        lemma_mod_bound(u64_5_as_nat(spec_negate(elem.limbs)) as int, p() as int);
    }

    assert((y + x) % p() == 0) by {
        lemma_add_mod_noop(
            u64_5_as_nat(spec_negate(elem.limbs)) as int,
            u64_5_as_nat(elem.limbs) as int,
            p() as int,
        );
    }
    assert(y == (p() - (x % p())) as nat % p()) by {
        assert(p() - (x % p()) >= 0) by {
            lemma_mod_bound(x as int, p() as int);
        }
        assert(x % p() == x) by {
            lemma_mod_twice(spec_field_element_as_nat(elem) as int, p() as int);
        }
        if (x == 0) {
            assert(y % p() == 0);  // follows from (y + x) % p == 0
            assert(y == 0) by {
                // contradiction proof
                if (y > 0) {
                    assert(y >= p()) by {
                        lemma_mod_is_zero(y, p());
                    }
                }
            }
            assert(p() % p() == 0) by {
                lemma_mod_self_0(p() as int);
            }
        } else {
            // x > 0
            // consequences:
            assert(p() - (x % p()) < p());
            assert(y + x > 0);

            assert((p() - (x % p())) as nat % p() == p() - x) by {
                lemma_small_mod((p() - (x % p())) as nat, p());
            }

            assert(y + x == p()) by {
                let z = y + x;
                assert(z == p() * (z / p())) by {
                    // we know z % p == 0
                    lemma_fundamental_div_mod(z as int, p() as int);
                }
                assert(z / p() == 1) by {
                    assert(z / p() >= 1) by {
                        assert(z >= p()) by {
                            lemma_mod_is_zero(z, p());
                        }
                    }
                    assert(z / p() < 2) by {
                        assert(z <= 2 * p()) by {
                            // known
                            assert(x < p());
                            assert(y < p());
                        }
                        assert(2 * p() / p() == 2) by {
                            lemma_div_by_multiple(2, p() as int);
                        }
                        lemma_div_by_multiple_is_strongly_ordered(
                            z as int,
                            (2 * p()) as int,
                            2,
                            p() as int,
                        );
                    }
                }
            }

        }
    }
}

} // verus!
