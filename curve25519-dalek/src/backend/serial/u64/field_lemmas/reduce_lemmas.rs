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
        ((limbs[4] & mask51) + (limbs[3] >> 51)) < (1u64 << 52)

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
        as_nat(spec_reduce(limbs)) % p() == as_nat(limbs) % p()
{

    // -----
    // reduce identity for small limbs

    // Can't seem to reference r within this proof block, we reconstruct it here
    let rr: [u64; 5] = spec_reduce(limbs);

    assert((forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] < (1u64 << 51)) ==> (rr =~= limbs)) by {
        if (forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] < (1u64 << 51)) {
            assert forall|i: int| 0 <= i < 5 implies #[trigger] limbs[i] & mask51 == limbs[i] by {
                l51_bit_mask_lt(); // mask51 = low_bits_mask(51)
                shift_is_pow2(51);
                lemma_u64_low_bits_mask_is_mod(limbs[i], 51);
                lemma_small_mod(limbs[i] as nat, pow2(51));
            }
            assert forall|i: int| 0 <= i < 5 implies #[trigger] limbs[i] >> 51 == 0 by {
                l51_bit_mask_lt(); // mask51 = low_bits_mask(51)
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
    assert(as_nat(rr) ==
        19 *  a4 + b0 +
        pow2(51) * a0 + pow2(51) * b1 +
        pow2(102) * a1 + pow2(102) * b2 +
        pow2(153) * a2 + pow2(153) * b3 +
        pow2(204) * a3 + pow2(204) * b4
    ) by {
        lemma_mul_is_distributive_add(pow2( 51) as int, a0 as int, b1 as int);
        lemma_mul_is_distributive_add(pow2(102) as int, a1 as int, b2 as int);
        lemma_mul_is_distributive_add(pow2(153) as int, a2 as int, b3 as int);
        lemma_mul_is_distributive_add(pow2(204) as int, a3 as int, b4 as int);
    }

    // factor out
    assert(as_nat(rr) ==
        19 *  a4 + b0 +
        pow2(51) * a0 + pow2(51) * b1 +
        pow2(51) * (pow2(51) * a1) + pow2(102) * b2 +
        pow2(102) * (pow2(51) * a2) + pow2(153) * b3 +
        pow2(153) * (pow2(51) * a3) + pow2(204) * b4
    ) by {
        lemma_two_factoring_51(51, a1);
        lemma_two_factoring_51(102, a2);
        lemma_two_factoring_51(153, a3);
    }

    // change groupings
    assert(as_nat(rr) ==
        (b0 + pow2(51) * a0) +
        pow2(51) * (b1 + pow2(51) * a1) +
        pow2(102) * (b2 + pow2(51) * a2) +
        pow2(153) * (b3 + pow2(51) * a3) +
        pow2(204) * b4 + 19 * a4
    ) by {
        lemma_mul_is_distributive_add(pow2( 51) as int, b1 as int, pow2(51) * a1);
        lemma_mul_is_distributive_add(pow2(102) as int, b2 as int, pow2(51) * a2);
        lemma_mul_is_distributive_add(pow2(153) as int, b3 as int, pow2(51) * a3);
    }

    // invoke div/mod identity
    assert(as_nat(rr) ==
        limbs[0] +
        pow2(51) * limbs[1] +
        pow2(102) * limbs[2] +
        pow2(153) * limbs[3] +
        pow2(204) * b4 + 19 * a4
    ) by {
        lemma_div_and_mod_51(a0, b0, limbs[0]);
        lemma_div_and_mod_51(a1, b1, limbs[1]);
        lemma_div_and_mod_51(a2, b2, limbs[2]);
        lemma_div_and_mod_51(a3, b3, limbs[3]);
    }

    // Add missing limbs[4] parts
    assert(as_nat(rr) ==
        limbs[0] +
        pow2(51) * limbs[1] +
        pow2(102) * limbs[2] +
        pow2(153) * limbs[3] +
        pow2(204) * limbs[4] - pow2(204) * (pow2(51) * a4 ) + 19 * a4
    ) by {
        lemma_div_and_mod_51(a4, b4, limbs[4]);
        assert(pow2(204) * limbs[4] == pow2(204) * b4 + pow2(204)* (pow2(51) * a4)) by {
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
        lemma_mul_is_distributive_sub_other_way(a4 as int, pow2(255) as int, 19 );
        pow255_gt_19(); // we need to prove 2^255 - 19 doesn't underflow
    }

    pow255_gt_19();
    lemma_mod_multiples_vanish((limbs[4] >> 51) as int, as_nat(spec_reduce(limbs)) as int, p() as int);
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

    // Establish the relationship: 2*p() = 2^256 - 38
    assert(pow2(256) == 2 * pow2(255)) by {
        lemma_pow2_adds(255, 1);
    }
    assert(2 * p() == 2 * (pow2(255) - 19));
    assert(2 * p() == 2 * pow2(255) - 38);
    assert(2 * p() == pow2(256) - 38);

    // Now we need to establish tighter bounds on each r[i].
    // From the definition of spec_reduce:
    // r[0] = (limbs[0] & mask51) + (limbs[4] >> 51) * 19
    // r[i] = (limbs[i] & mask51) + (limbs[i-1] >> 51) for i > 0

    // We know from lemma_boundaries that these expressions are < 2^52.
    // But we need tighter bounds. Let's derive them:

    // For r[0]: We need to show (limbs[0] & mask51) + (limbs[4] >> 51) * 19 < 2^51 + 2^18
    // - (limbs[0] & mask51) < 2^51 (from masking)
    // - (limbs[4] >> 51) < 2^13 (shifting a u64 right by 51 gives at most 13 bits)
    // - (limbs[4] >> 51) * 19 < 2^13 * 2^5 = 2^18 (since 19 < 2^5)

    masked_lt_51(limbs[0]);
    assert((1u64 << 51) == pow2(51)) by { shift_is_pow2(51); }
    assert((limbs[0] & mask51) < pow2(51));

    shifted_lt(limbs[4], 51);
    assert((1u64 << 13) == pow2(13)) by { shift_is_pow2(13); }
    assert((limbs[4] >> 51) < pow2(13));

    assert(19 < pow2(5)) by {
        assert(pow2(5) == 32) by { lemma2_to64(); }
    }
    lemma_pow2_adds(13, 5);
    assert(pow2(13) * pow2(5) == pow2(18));
    // Use mul_lt: if a1 < b1 and a2 < b2, then a1 * a2 < b1 * b2
    mul_lt((limbs[4] >> 51) as nat, pow2(13), 19, pow2(5));
    assert((limbs[4] >> 51) * 19 < pow2(13) * pow2(5));
    assert((limbs[4] >> 51) * 19 < pow2(18));

    // Therefore: r[0] < 2^51 + 2^18
    assert(r[0] == ((limbs[0] & mask51) + (limbs[4] >> 51) * 19) as u64);
    assert(r[0] < pow2(51) + pow2(18));

    // For r[i] where i > 0: (limbs[i] & mask51) + (limbs[i-1] >> 51) < 2^51 + 2^13
    masked_lt_51(limbs[1]);
    shifted_lt(limbs[0], 51);
    assert(r[1] == ((limbs[1] & mask51) + (limbs[0] >> 51)) as u64);
    assert(r[1] < pow2(51) + pow2(13));

    masked_lt_51(limbs[2]);
    shifted_lt(limbs[1], 51);
    assert(r[2] == ((limbs[2] & mask51) + (limbs[1] >> 51)) as u64);
    assert(r[2] < pow2(51) + pow2(13));

    masked_lt_51(limbs[3]);
    shifted_lt(limbs[2], 51);
    assert(r[3] == ((limbs[3] & mask51) + (limbs[2] >> 51)) as u64);
    assert(r[3] < pow2(51) + pow2(13));

    masked_lt_51(limbs[4]);
    shifted_lt(limbs[3], 51);
    assert(r[4] == ((limbs[4] & mask51) + (limbs[3] >> 51)) as u64);
    assert(r[4] < pow2(51) + pow2(13));

    // Note: The bounds on r[1..4] follow from the same reasoning as r[0],
    // but we already established the shift_is_pow2 conversions above

    // Expand the weighted sum with distributivity:
    // as_nat(r) < (2^51 + 2^18) + 2^51*(2^51 + 2^13) + 2^102*(2^51 + 2^13)
    //                           + 2^153*(2^51 + 2^13) + 2^204*(2^51 + 2^13)
    //           = 2^51 + 2^18 + 2^102 + 2^64 + 2^153 + 2^115
    //                         + 2^204 + 2^166 + 2^255 + 2^217

    // Prove the power additions for the products
    lemma_pow2_adds(51, 51);   // 2^51 * 2^51 = 2^102
    lemma_pow2_adds(51, 13);   // 2^51 * 2^13 = 2^64
    lemma_pow2_adds(102, 51);  // 2^102 * 2^51 = 2^153
    lemma_pow2_adds(102, 13);  // 2^102 * 2^13 = 2^115
    lemma_pow2_adds(153, 51);  // 2^153 * 2^51 = 2^204
    lemma_pow2_adds(153, 13);  // 2^153 * 2^13 = 2^166
    lemma_pow2_adds(204, 51);  // 2^204 * 2^51 = 2^255
    lemma_pow2_adds(204, 13);  // 2^204 * 2^13 = 2^217

    // Compute upper bound on each weighted term:
    // Using distributivity: a * (b + c) = a*b + a*c
    lemma_mul_is_distributive_add(pow2(51) as int, pow2(51) as int, pow2(13) as int);
    assert(pow2(51) * (pow2(51) + pow2(13)) == pow2(51) * pow2(51) + pow2(51) * pow2(13));
    assert(pow2(51) * (pow2(51) + pow2(13)) == pow2(102) + pow2(64));

    lemma_mul_is_distributive_add(pow2(102) as int, pow2(51) as int, pow2(13) as int);
    assert(pow2(102) * (pow2(51) + pow2(13)) == pow2(102) * pow2(51) + pow2(102) * pow2(13));
    assert(pow2(102) * (pow2(51) + pow2(13)) == pow2(153) + pow2(115));

    lemma_mul_is_distributive_add(pow2(153) as int, pow2(51) as int, pow2(13) as int);
    assert(pow2(153) * (pow2(51) + pow2(13)) == pow2(153) * pow2(51) + pow2(153) * pow2(13));
    assert(pow2(153) * (pow2(51) + pow2(13)) == pow2(204) + pow2(166));

    lemma_mul_is_distributive_add(pow2(204) as int, pow2(51) as int, pow2(13) as int);
    assert(pow2(204) * (pow2(51) + pow2(13)) == pow2(204) * pow2(51) + pow2(204) * pow2(13));
    assert(pow2(204) * (pow2(51) + pow2(13)) == pow2(255) + pow2(217));

    // Now bound as_nat(r) using the definition and the individual limb bounds
    // as_nat(r) = r[0] + pow2(51)*r[1] + pow2(102)*r[2] + pow2(153)*r[3] + pow2(204)*r[4]
    //           < (pow2(51) + pow2(18))
    //             + pow2(51)*(pow2(51) + pow2(13))
    //             + pow2(102)*(pow2(51) + pow2(13))
    //             + pow2(153)*(pow2(51) + pow2(13))
    //             + pow2(204)*(pow2(51) + pow2(13))
    //
    // Expanding the products:
    //           = pow2(51) + pow2(18)
    //             + pow2(102) + pow2(64)
    //             + pow2(153) + pow2(115)
    //             + pow2(204) + pow2(166)
    //             + pow2(255) + pow2(217)

    // Define the upper bound explicitly
    let upper_bound = pow2(51) + pow2(18) + pow2(102) + pow2(64) + pow2(153)
                    + pow2(115) + pow2(204) + pow2(166) + pow2(255) + pow2(217);

    // Assert that as_nat(r) is bounded by this sum
    // This follows from the definition of as_nat and the bounds on each limb
    // We need to guide the solver by expanding the terms
    assert(as_nat(r) == r[0] + pow2(51)*r[1] + pow2(102)*r[2] + pow2(153)*r[3] + pow2(204)*r[4]);

    // Use monotonicity: if a < b and c > 0, then c * a < c * b
    assert(r[0] < pow2(51) + pow2(18));

    assert(r[1] < pow2(51) + pow2(13));
    lemma_mul_strict_inequality(r[1] as int, (pow2(51) + pow2(13)) as int, pow2(51) as int);
    assert(pow2(51) * r[1] < pow2(51) * (pow2(51) + pow2(13)));

    assert(r[2] < pow2(51) + pow2(13));
    lemma_mul_strict_inequality(r[2] as int, (pow2(51) + pow2(13)) as int, pow2(102) as int);
    assert(pow2(102) * r[2] < pow2(102) * (pow2(51) + pow2(13)));

    assert(r[3] < pow2(51) + pow2(13));
    lemma_mul_strict_inequality(r[3] as int, (pow2(51) + pow2(13)) as int, pow2(153) as int);
    assert(pow2(153) * r[3] < pow2(153) * (pow2(51) + pow2(13)));

    assert(r[4] < pow2(51) + pow2(13));
    lemma_mul_strict_inequality(r[4] as int, (pow2(51) + pow2(13)) as int, pow2(204) as int);
    assert(pow2(204) * r[4] < pow2(204) * (pow2(51) + pow2(13)));

    // Therefore the sum is bounded
    assert(as_nat(r) < upper_bound);

    // Now we need to show: upper_bound < 2*p() = 2^256 - 38
    // Equivalently: 2^255 + (2^217 + 2^204 + 2^166 + 2^153 + 2^115 + 2^102 + 2^64 + 2^51 + 2^18) < 2^256 - 38
    //
    // Rearranging: 2^255 + tail < 2^256 - 38
    // where tail = 2^217 + 2^204 + 2^166 + 2^153 + 2^115 + 2^102 + 2^64 + 2^51 + 2^18
    //
    // We need: tail < 2^255 - 38

    // The key is to bound the tail. We'll show tail < 2^218.
    // Since each term in the tail is strictly less than 2^217 * 2 = 2^218:

    // First, group the smaller terms
    // Tail = 2^217 + (2^204 + 2^166 + 2^153 + 2^115 + 2^102 + 2^64 + 2^51 + 2^18)

    // Define the tail for clarity
    let tail = pow2(217) + pow2(204) + pow2(166) + pow2(153) + pow2(115)
             + pow2(102) + pow2(64) + pow2(51) + pow2(18);
    assert(upper_bound == pow2(255) + tail);

    // Prove ordering: each term < 2^217
    lemma_pow2_strictly_increases(18, 217);
    lemma_pow2_strictly_increases(51, 217);
    lemma_pow2_strictly_increases(64, 217);
    lemma_pow2_strictly_increases(102, 217);
    lemma_pow2_strictly_increases(115, 217);
    lemma_pow2_strictly_increases(153, 217);
    lemma_pow2_strictly_increases(166, 217);
    lemma_pow2_strictly_increases(204, 217);

    // So all terms except 2^217 itself are < 2^217
    // The sum of terms < 2^217 is dominated by 2^204, which is the largest

    // Using geometric series logic similar to lemma_radix_51_geometric_sum:
    // 2^204 + smaller_terms < 2^205
    lemma_pow2_strictly_increases(18, 204);
    lemma_pow2_strictly_increases(51, 204);
    lemma_pow2_strictly_increases(64, 204);
    lemma_pow2_strictly_increases(102, 204);
    lemma_pow2_strictly_increases(115, 204);
    lemma_pow2_strictly_increases(153, 204);
    lemma_pow2_strictly_increases(166, 204);

    // Actually, 2^166 is the second largest term. Let's bound more carefully.
    // 2^166 + (2^153 + 2^115 + 2^102 + 2^64 + 2^51 + 2^18) < 2^167
    lemma_pow2_adds(166, 1);
    assert(2 * pow2(166) == pow2(167));

    // All terms from 2^18 to 2^153 sum to less than 2^154
    lemma_pow2_strictly_increases(153, 154);
    lemma_pow2_strictly_increases(115, 154);
    lemma_pow2_strictly_increases(102, 154);
    lemma_pow2_strictly_increases(64, 154);
    lemma_pow2_strictly_increases(51, 154);
    lemma_pow2_strictly_increases(18, 154);

    // So: 2^153 + 2^115 + 2^102 + 2^64 + 2^51 + 2^18 < 6*2^153 < 2^156
    // (since 2^3 = 8 > 6, we have 6*2^153 < 2^3 * 2^153 = 2^156)
    lemma_pow2_strictly_increases(154, 166);
    assert(pow2(154) < pow2(166));

    // So: 2^166 + (smaller terms < 2^154) < 2^166 + 2^166 = 2^167
    lemma_pow2_strictly_increases(167, 204);

    // Similarly: 2^204 + (terms < 2^167) < 2^204 + 2^204 = 2^205
    lemma_pow2_adds(204, 1);
    assert(2 * pow2(204) == pow2(205));
    lemma_pow2_strictly_increases(205, 217);

    // So: tail = 2^217 + (terms < 2^205) < 2^217 + 2^217 = 2^218
    lemma_pow2_adds(217, 1);
    assert(2 * pow2(217) == pow2(218));
    assert(tail < pow2(218));

    // Now we have: upper_bound = 2^255 + tail < 2^255 + 2^218
    // We need: 2^255 + 2^218 < 2^256 - 38

    // Since 2^218 << 2^255, we have 2^255 + 2^218 < 2 * 2^255 = 2^256
    lemma_pow2_strictly_increases(218, 255);
    assert(pow2(218) < pow2(255));

    // More precisely: 2^255 + 2^218 < 2^256 - 38 because:
    // 2^256 - (2^255 + 2^218) = 2*2^255 - 2^255 - 2^218 = 2^255 - 2^218
    // and we need 2^255 - 2^218 > 38, which is clearly true since 2^255 >> 2^218

    // Let's prove the final inequality explicitly
    // We need: pow2(218) + 38 < pow2(255)
    // Equivalently: 38 < pow2(255) - pow2(218)
    lemma_pow2_strictly_increases(218, 255);
    assert(pow2(218) < pow2(255));

    // Since 38 << pow2(218) << pow2(255), we have plenty of room
    // Specifically: pow2(218) + 38 < 2 * pow2(218) <= pow2(219) << pow2(255)
    assert(38 < pow2(6)) by {
        assert(pow2(6) == 64) by { lemma2_to64(); }
    }
    lemma_pow2_strictly_increases(6, 218);
    assert(38 < pow2(218));

    // So: pow2(218) + 38 < pow2(218) + pow2(218) = 2 * pow2(218) = pow2(219)
    lemma_pow2_adds(218, 1);
    assert(2 * pow2(218) == pow2(219));
    assert(pow2(218) + 38 < 2 * pow2(218));
    assert(pow2(218) + 38 < pow2(219));

    // And: pow2(219) << pow2(255)
    lemma_pow2_strictly_increases(219, 255);
    assert(pow2(218) + 38 < pow2(255));

    // Combine: upper_bound < 2^255 + 2^218 < 2^256 - 38 = 2*p()
    assert(upper_bound < pow2(255) + pow2(218));
    assert(pow2(255) + pow2(218) < pow2(256) - 38);
    assert(upper_bound < pow2(256) - 38);
    assert(upper_bound < 2 * p());

    // Therefore: as_nat(r) < upper_bound < 2*p()
    assert(as_nat(r) < 2 * p());
}


fn main() {}

}
