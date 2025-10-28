#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_verus::div_mod_lemmas::*;
use super::super::common_verus::mask_lemmas::*;
use super::super::common_verus::mul_lemmas::*;
use super::super::common_verus::pow_lemmas::*;
use super::super::common_verus::shift_lemmas::*;
use super::field_core::*;
use super::pow2_51_lemmas::*;

verus! {

// Each component of spec_reduce is bounded.
// The reason we _don't_ write
// ensures forall |i: int| 0 <= i < 5 ==> spec_reduce(limbs)[i] < (1u64 << 52)
// is that the solver treats `spec_reduce`` above as symbolic and does _not_ instantiate e.g.
// ((limbs[4] & mask51) + (limbs[3] >> 51)) as u64 < (1u64 << 52)
pub proof fn lemma_boundaries(limbs: [u64; 5])
    ensures
        ((limbs[0] & mask51) + (limbs[4] >> 51) * 19) < (1u64 << 52),
        ((limbs[1] & mask51) + (limbs[0] >> 51)) < (1u64 << 52),
        ((limbs[2] & mask51) + (limbs[1] >> 51)) < (1u64 << 52),
        ((limbs[3] & mask51) + (limbs[2] >> 51)) < (1u64 << 52),
        ((limbs[4] & mask51) + (limbs[3] >> 51)) < (1u64 << 52),
{
    // \A i. limbs[i] < 2^13
    shifted_lt(limbs[0], 51);
    shifted_lt(limbs[1], 51);
    shifted_lt(limbs[2], 51);
    shifted_lt(limbs[3], 51);
    shifted_lt(limbs[4], 51);

    // \A i. limbs[i] & mask51 < 2^51
    masked_lt_51(limbs[0]);
    masked_lt_51(limbs[1]);
    masked_lt_51(limbs[2]);
    masked_lt_51(limbs[3]);
    masked_lt_51(limbs[4]);

    // Since 19 < 2^5 and (limbs[4] >> 51) < 2^13, their product is less than 2^18
    assert((limbs[4] >> 51) * 19 < (1u64 << 18) as nat) by {
        assert(19 < (1u64 << 5)) by (bit_vector);
        shift_is_pow2(5);
        shift_is_pow2(13);
        shift_is_pow2(18);
        lemma_pow2_adds(13, 5);
        // If (limbs[4] >> 51) < 2^13 and 19 < 2^5 then their product is less than 2^18
        mul_lt((limbs[4] >> 51) as nat, (1u64 << 13) as nat, 19nat, (1u64 << 5) as nat);
    }

    // The final values (limbs[i] += cX) are all bounded by 2^51 + eps, for eps \in {2^18, 2^13}.
    assert(((1u64 << 18)) + (1u64 << 51) < (1u64 << 52)) by (bit_vector);
    assert(((1u64 << 13)) + (1u64 << 51) < (1u64 << 52)) by (bit_vector);

    // In summary, they're all bounded by 2^52
    // The solver can prove this automatically
}

pub proof fn lemma_reduce(limbs: [u64; 5])
    ensures
        forall|i: int| 0 <= i < 5 ==> spec_reduce(limbs)[i] < (1u64 << 52),
        // Suppose l = (l0, l1, l2, l3, l4) are the input limbs.
        // They represent a number
        // e(l) =  l0 + l1 * 2^51 + l2 * 2^102 + l3 * 2^153 + l4 * 2^204
        // in Z_p, for p = 2^255 - 19
        // reduce(l) returns v = (v0, v1, v2, v3, v4), such that
        // v0 = 19 * a4 + b0
        // v1 =      a0 + b1
        // v2 =      a1 + b2
        // v3 =      a2 + b3
        // v4 =      a3 + b4
        // where ai = li >> 51 and bi = li & mask51
        // we can reformulate this as ai = li / 2^51 (flooring division) and bi = li % 2^51
        // Using the following identity connecting integer division and remainder:
        // x = y * (x / y) + x % y
        // we can see that li = ai * 2^51 + bi
        // Plugging the above identities into the equations for v, we can observe that
        // e(v) = e(l) - p * (l4 >> 51)
        // IOW, e(reduce(l)) = e(l) (mod p)
        // additionally, if all limbs are below 2^51, reduce(l) = l
        (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (spec_reduce(limbs) =~= limbs),
        as_nat(spec_reduce(limbs)) == as_nat(limbs) - p() * (limbs[4] >> 51),
        as_nat(spec_reduce(limbs)) % p() == as_nat(limbs) % p(),
{
    // -----
    // reduce identity for small limbs
    // Can't seem to reference r within this proof block, we reconstruct it here
    let rr: [u64; 5] = spec_reduce(limbs);

    assert((forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] < (1u64 << 51)) ==> (rr =~= limbs))
        by {
        if (forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] < (1u64 << 51)) {
            assert forall|i: int| 0 <= i < 5 implies #[trigger] limbs[i] & mask51 == limbs[i] by {
                l51_bit_mask_lt();  // mask51 = low_bits_mask(51)
                shift_is_pow2(51);
                lemma_u64_low_bits_mask_is_mod(limbs[i], 51);
                lemma_small_mod(limbs[i] as nat, pow2(51));
            }
            assert forall|i: int| 0 <= i < 5 implies #[trigger] limbs[i] >> 51 == 0 by {
                l51_bit_mask_lt();  // mask51 = low_bits_mask(51)
                shift_is_pow2(51);
                lemma_u64_shr_is_div(limbs[i], 51);
                lemma_basic_div(limbs[i] as int, pow2(51) as int);
            }
        }
    }

    // -- as_nat identity

    // ai = limbs[i] / 2^52
    let a0 = (limbs[0] >> 51);
    let a1 = (limbs[1] >> 51);
    let a2 = (limbs[2] >> 51);
    let a3 = (limbs[3] >> 51);
    let a4 = (limbs[4] >> 51);

    // bi = limbs[i] % 2^52
    let b0 = (limbs[0] & mask51);
    let b1 = (limbs[1] & mask51);
    let b2 = (limbs[2] & mask51);
    let b3 = (limbs[3] & mask51);
    let b4 = (limbs[4] & mask51);

    lemma_boundaries(limbs);

    // distribute
    assert(as_nat(rr) == 19 * a4 + b0 + pow2(51) * a0 + pow2(51) * b1 + pow2(102) * a1 + pow2(102)
        * b2 + pow2(153) * a2 + pow2(153) * b3 + pow2(204) * a3 + pow2(204) * b4) by {
        lemma_mul_is_distributive_add(pow2(51) as int, a0 as int, b1 as int);
        lemma_mul_is_distributive_add(pow2(102) as int, a1 as int, b2 as int);
        lemma_mul_is_distributive_add(pow2(153) as int, a2 as int, b3 as int);
        lemma_mul_is_distributive_add(pow2(204) as int, a3 as int, b4 as int);
    }

    // factor out
    assert(as_nat(rr) == 19 * a4 + b0 + pow2(51) * a0 + pow2(51) * b1 + pow2(51) * (pow2(51) * a1)
        + pow2(102) * b2 + pow2(102) * (pow2(51) * a2) + pow2(153) * b3 + pow2(153) * (pow2(51)
        * a3) + pow2(204) * b4) by {
        lemma_two_factoring_51(51, a1);
        lemma_two_factoring_51(102, a2);
        lemma_two_factoring_51(153, a3);
    }

    // change groupings
    assert(as_nat(rr) == (b0 + pow2(51) * a0) + pow2(51) * (b1 + pow2(51) * a1) + pow2(102) * (b2
        + pow2(51) * a2) + pow2(153) * (b3 + pow2(51) * a3) + pow2(204) * b4 + 19 * a4) by {
        lemma_mul_is_distributive_add(pow2(51) as int, b1 as int, pow2(51) * a1);
        lemma_mul_is_distributive_add(pow2(102) as int, b2 as int, pow2(51) * a2);
        lemma_mul_is_distributive_add(pow2(153) as int, b3 as int, pow2(51) * a3);
    }

    // invoke div/mod identity
    assert(as_nat(rr) == limbs[0] + pow2(51) * limbs[1] + pow2(102) * limbs[2] + pow2(153)
        * limbs[3] + pow2(204) * b4 + 19 * a4) by {
        lemma_div_and_mod_51(a0, b0, limbs[0]);
        lemma_div_and_mod_51(a1, b1, limbs[1]);
        lemma_div_and_mod_51(a2, b2, limbs[2]);
        lemma_div_and_mod_51(a3, b3, limbs[3]);
    }

    // Add missing limbs[4] parts
    assert(as_nat(rr) == limbs[0] + pow2(51) * limbs[1] + pow2(102) * limbs[2] + pow2(153)
        * limbs[3] + pow2(204) * limbs[4] - pow2(204) * (pow2(51) * a4) + 19 * a4) by {
        lemma_div_and_mod_51(a4, b4, limbs[4]);
        assert(pow2(204) * limbs[4] == pow2(204) * b4 + pow2(204) * (pow2(51) * a4)) by {
            lemma_mul_is_distributive_add(pow2(204) as int, pow2(51) * a4 as int, b4 as int);
        }
    }

    // The solver can collect components of as_nat(limbs) automatically:
    // as_nat(rr) == as_nat(limbs) - pow2(204) * (pow2(51) * a4 ) + 19 * a4
    // ... as well as pull in minus
    // as_nat(rr) == as_nat(limbs) - (pow2(204) * (pow2(51) * a4 ) - 19 * a4)

    // collect components of p() * a4
    assert(pow2(204) * (pow2(51) * a4) - 19 * a4 == p() * a4) by {
        lemma_mul_is_associative(pow2(204) as int, pow2(51) as int, a4 as int);
        lemma_pow2_adds(204, 51);
        lemma_mul_is_distributive_sub_other_way(a4 as int, pow2(255) as int, 19);
        pow255_gt_19();  // we need to prove 2^255 - 19 doesn't underflow
    }

    pow255_gt_19();
    lemma_mod_multiples_vanish(
        (limbs[4] >> 51) as int,
        as_nat(spec_reduce(limbs)) as int,
        p() as int,
    );
}

/// Proves that reduce() ensures as_nat < 2*p()
///
/// This is the key property needed for to_bytes(): after reduce(),
/// the value is bounded by 2*p = 2^256 - 38, not just by the loose
/// bound from individual limb sizes.
pub proof fn lemma_reduce_bound_2p(limbs: [u64; 5])
    ensures
        as_nat(spec_reduce(limbs)) < 2 * p(),
{
    lemma2_to64();
    pow255_gt_19();

    // From lemma_boundaries, we know the tight bounds on each expression in spec_reduce
    lemma_boundaries(limbs);

    let r = spec_reduce(limbs);

    lemma_reduce(limbs);

    assert(1u64 << 51 == pow2(51)) by {
        shift_is_pow2(51);
    }

    // For r[i] where i > 0: (limbs[i] & mask51) + (limbs[i-1] >> 51) < 2^51 + 2^13
    assert forall|i: int| 0 <= i <= 4 implies #[trigger] (limbs[i] & mask51) < pow2(51) by {
        masked_lt_51(limbs[i]);
    }
    // separate foralls, because they trigger on i and i-1
    assert forall|i: int| 0 <= i <= 4 implies #[trigger] limbs[i] >> 51 < pow2(13) by {
        assert(limbs[i] >> 51 <= u64::MAX >> 51) by {
            lemma_shr_le_u64(limbs[i], u64::MAX, 51);
        }
        assert(u64::MAX >> 51 < pow2(13)) by {
            assert(1u64 << 13 == pow2(13)) by {
                shift_is_pow2(13);
            }
            lemma_u64_max_shifting(51);
        }
    }

    // For r[0] we have the extra factor of 19:
    // r[0] = (limbs[0] & mask51) + (limbs[4] >> 51) * 19
    assert((limbs[4] >> 51) * 19 < pow2(18)) by {
        assert(19 < pow2(5)) by {
            lemma2_to64();
        }
        assert(pow2(18) == pow2(13) * pow2(5)) by {
            lemma_pow2_adds(13, 5);
        }
        mul_lt((limbs[4] >> 51) as nat, pow2(13), 19, pow2(5));
    }

    assert forall|i: nat| 1 <= i <= 4 implies #[trigger] pow2(i * 51) * r[i as int] < pow2(i * 51)
        * pow2(13) + pow2((i + 1) * 51) by {
        assert(pow2(i * 51) * r[i as int] < pow2(i * 51) * (pow2(51) + pow2(13))) by {
            lemma_pow2_pos(i * 51);
            lemma_mul_strict_inequality(
                r[i as int] as int,
                (pow2(51) + pow2(13)) as int,
                pow2(i * 51) as int,
            );
            lemma_mul_is_commutative(pow2(i * 51) as int, r[i as int] as int);
            lemma_mul_is_commutative(pow2(i * 51) as int, (pow2(51) + pow2(13)) as int);
        }

        assert(pow2(i * 51) * (pow2(51) + pow2(13)) == pow2((i + 1) * 51) + pow2(i * 51) * pow2(13))
            by {
            assert(pow2(i * 51) * (pow2(51) + pow2(13)) == pow2(i * 51) * pow2(51) + pow2(i * 51)
                * pow2(13)) by {
                lemma_mul_is_distributive_add(
                    pow2(i * 51) as int,
                    pow2(51) as int,
                    pow2(13) as int,
                );
            }
            assert(pow2(i * 51) * pow2(51) == pow2((i + 1) * 51)) by {
                assert(i * 51 + 51 == (i + 1) * 51) by {
                    lemma_mul_is_distributive_add_other_way(51, i as int, 1);
                }
                lemma_pow2_adds(i * 51, 51);
            }
        }
    }

    // write out i * 51s explicitly to trigger forall match
    let tail = (pow2(18) + pow2(51) + pow2(64) + pow2(102) + pow2(115) + pow2(153) + pow2(166)
        + pow2(204) + pow2(217));
    assert(as_nat(r) == r[0] + pow2(1 * 51) * r[1] + pow2(2 * 51) * r[2] + pow2(3 * 51) * r[3]
        + pow2(4 * 51) * r[4] < tail + pow2(255)) by {
        lemma_pow2_adds(51, 13);
        lemma_pow2_adds(102, 13);
        lemma_pow2_adds(153, 13);
        lemma_pow2_adds(204, 13);
    }

    assert(2 * p() == pow2(255) + pow2(255) - 38) by {
        lemma_pow2_adds(255, 1);
        lemma_pow2_plus_one(255);
    }

    // we'll prove the tail is small
    assert(tail < pow2(255) - 38) by {
        assert forall|i: nat| i <= 204 implies #[trigger] pow2(i) < pow2(217) by {
            lemma_pow2_strictly_increases(i, 217);
        }
        assert(tail < 9 * pow2(217) < pow2(221)) by {
            assert(9 < pow2(4));  // known
            assert(pow2(217) > 0) by {
                lemma_pow2_pos(217);
            }
            lemma_mul_strict_inequality(9, pow2(4) as int, pow2(217) as int);
            lemma_pow2_adds(217, 4);
        }

        assert(pow2(254) < pow2(255) - 38) by {
            assert(38 < pow2(6));  // known
            assert(pow2(255) - 38 > pow2(255) - pow2(6) == pow2(254) + pow2(254) - pow2(6)) by {
                lemma_pow2_plus_one(254);
            }
            assert(pow2(254) - pow2(6) > 0) by {
                lemma_pow2_strictly_increases(6, 254);
            }
        }

        assert(pow2(221) < pow2(254)) by {
            lemma_pow2_strictly_increases(221, 254);
        }
    }
}

fn main() {
}

} // verus!
