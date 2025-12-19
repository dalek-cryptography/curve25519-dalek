#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::pow2_51_lemmas::*;
use super::u64_5_as_nat_lemmas::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mask_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

// Auxiliary lemma for reordering terms in the pow2k proof
pub proof fn lemma_reorder_mul(a: int, b: int)
    ensures
        2 * (a * (19 * b)) == 19 * (2 * (a * b)),
{
    // 2*( a * (19 * b)) = (2 * a) * (19 * b)
    lemma_mul_is_associative(2, a, 19 * b);
    // (2 * a) * (19 * b) = (19 * b) * (2 * a) = 19 * (b * (2 * a))
    lemma_mul_is_associative(19, b, 2 * a);
    // (b * (2 * a)) = (b * (a * 2)) = 2 * (a * b)
    lemma_mul_is_associative(b, a, 2);
}

pub open spec fn c0_0_val(a: [u64; 5]) -> u128 {
    (a[0] * a[0] + 2 * (a[1] * (19 * a[4]) + a[2] * (19 * a[3]))) as u128
}

pub open spec fn c1_0_val(a: [u64; 5]) -> u128 {
    (a[3] * (19 * a[3]) + 2 * (a[0] * a[1] + a[2] * (19 * a[4]))) as u128
}

pub open spec fn c2_0_val(a: [u64; 5]) -> u128 {
    (a[1] * a[1] + 2 * (a[0] * a[2] + a[4] * (19 * a[3]))) as u128
}

pub open spec fn c3_0_val(a: [u64; 5]) -> u128 {
    (a[4] * (19 * a[4]) + 2 * (a[0] * a[3] + a[1] * a[2])) as u128
}

pub open spec fn c4_0_val(a: [u64; 5]) -> u128 {
    (a[2] * a[2] + 2 * (a[0] * a[4] + a[1] * a[3])) as u128
}

pub open spec fn c0_val(a: [u64; 5]) -> u128 {
    c0_0_val(a)
}

pub open spec fn c1_val(a: [u64; 5]) -> u128 {
    (c1_0_val(a) + ((c0_val(a) >> 51) as u64) as u128) as u128
}

pub open spec fn c2_val(a: [u64; 5]) -> u128 {
    (c2_0_val(a) + ((c1_val(a) >> 51) as u64) as u128) as u128
}

pub open spec fn c3_val(a: [u64; 5]) -> u128 {
    (c3_0_val(a) + ((c2_val(a) >> 51) as u64) as u128) as u128
}

pub open spec fn c4_val(a: [u64; 5]) -> u128 {
    (c4_0_val(a) + ((c3_val(a) >> 51) as u64) as u128) as u128
}

pub open spec fn carry_val(a: [u64; 5]) -> u64 {
    (c4_val(a) >> 51) as u64
}

pub open spec fn a0_0_val(a: [u64; 5]) -> u64 {
    (c0_val(a) as u64) & mask51
}

pub open spec fn a1_0_val(a: [u64; 5]) -> u64 {
    (c1_val(a) as u64) & mask51
}

pub open spec fn a2_0_val(a: [u64; 5]) -> u64 {
    (c2_val(a) as u64) & mask51
}

pub open spec fn a3_0_val(a: [u64; 5]) -> u64 {
    (c3_val(a) as u64) & mask51
}

pub open spec fn a4_0_val(a: [u64; 5]) -> u64 {
    (c4_val(a) as u64) & mask51
}

pub open spec fn a0_1_val(a: [u64; 5]) -> u64 {
    (a0_0_val(a) + carry_val(a) * 19) as u64
}

pub open spec fn a1_1_val(a: [u64; 5]) -> u64 {
    (a1_0_val(a) + (a0_1_val(a) >> 51)) as u64
}

pub open spec fn a0_2_val(a: [u64; 5]) -> u64 {
    a0_1_val(a) & mask51
}

pub open spec fn term_product_bounds_spec(a: [u64; 5], bound: u64) -> bool {
    // c0
    &&& (a[0] as u128) * (a[0] as u128) < bound * bound
    &&& (a[1] as u128) * ((19 * a[4]) as u128) < 19 * (bound * bound)
    &&& (a[2] as u128) * ((19 * a[3]) as u128) < 19 * (bound
        * bound)
    // c1
    &&& (a[3] as u128) * ((19 * a[3]) as u128) < 19 * (bound * bound)
    &&& (a[0] as u128) * (a[1] as u128) < (bound * bound)
    &&& (a[2] as u128) * ((19 * a[4]) as u128) < 19 * (bound
        * bound)
    // c2
    &&& (a[1] as u128) * (a[1] as u128) < (bound * bound)
    &&& (a[0] as u128) * (a[2] as u128) < (bound * bound)
    &&& (a[4] as u128) * ((19 * a[3]) as u128) < 19 * (bound
        * bound)
    // c3
    &&& (a[4] as u128) * ((19 * a[4]) as u128) < 19 * (bound * bound)
    &&& (a[0] as u128) * (a[3] as u128) < (bound * bound)
    &&& (a[1] as u128) * (a[2] as u128) < (bound * bound)
    // c4
    &&& (a[2] as u128) * (a[2] as u128) < (bound * bound)
    &&& (a[0] as u128) * (a[4] as u128) < (bound * bound)
    &&& (a[1] as u128) * (a[3] as u128) < (bound * bound)
}

pub proof fn lemma_term_product_bounds(a: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        forall|i: int| 0 <= i < 5 ==> a[i] < bound,
    ensures
        term_product_bounds_spec(a, bound),
{
    let bound19 = (19 * bound) as u64;

    assert(bound * (19 * bound) == 19 * (bound * bound)) by {
        lemma_mul_is_associative(19, bound as int, bound as int);
    }

    assert forall|i: int, j: int| 0 <= i <= 4 && 0 <= j <= 4 implies (a[i] as u128) * (a[j] as u128)
        < bound * bound && (a[i] as u128) * ((19 * a[j]) as u128) < 19 * (bound * bound) by {
        lemma_m(a[i], a[j], bound, bound);
        lemma_m(a[i], (19 * a[j]) as u64, bound, bound19);
    }
}

pub open spec fn ci_0_val_boundaries(a: [u64; 5], bound: u64) -> bool {
    &&& c0_0_val(a) < 77 * (bound * bound)
    &&& c1_0_val(a) < 59 * (bound * bound)
    &&& c2_0_val(a) < 41 * (bound * bound)
    &&& c3_0_val(a) < 23 * (bound * bound)
    &&& c4_0_val(a) < 5 * (bound * bound)
}

pub proof fn lemma_c_i_0_bounded(a: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        forall|i: int| 0 <= i < 5 ==> a[i] < bound,
    ensures
        ci_0_val_boundaries(a, bound),
{
    lemma_term_product_bounds(a, bound);
}

pub open spec fn ci_val_boundaries(a: [u64; 5]) -> bool {
    &&& (c0_val(a) >> 51) <= (u64::MAX as u128)
    &&& (c1_val(a) >> 51) <= (u64::MAX as u128)
    &&& (c2_val(a) >> 51) <= (u64::MAX as u128)
    &&& (c3_val(a) >> 51) <= (u64::MAX as u128)
    &&& (c4_val(a) >> 51) <= (u64::MAX as u128)
}

pub proof fn lemma_c_i_shift_bounded(a: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        77 * (bound * bound) + u64::MAX <= ((u64::MAX as u128) << 51),
        ci_0_val_boundaries(a, bound),
    ensures
        ci_val_boundaries(a),
{
    lemma_shr_51_fits_u64(c0_val(a));
    lemma_shr_51_fits_u64(c1_val(a));
    lemma_shr_51_fits_u64(c2_val(a));
    lemma_shr_51_fits_u64(c3_val(a));
    lemma_shr_51_fits_u64(c4_val(a));
}

pub open spec fn ai_val_boundaries(a: [u64; 5]) -> bool {
    &&& a0_0_val(a) < 1u64 << 51
    &&& a1_0_val(a) < 1u64 << 51
    &&& a2_0_val(a) < 1u64 << 51
    &&& a3_0_val(a) < 1u64 << 51
    &&& a4_0_val(a) < 1u64 << 51
    &&& carry_val(a) < 724618875532318195u64  // ceil(2^59.33)
    &&& a0_0_val(a) + carry_val(a) * 19 < u64::MAX
    &&& a1_0_val(a) + (a0_1_val(a) >> 51) < 1u64 << 52
    &&& a0_2_val(a) < 1u64 << 51
}

pub open spec fn pow2k_loop_return(a: [u64; 5]) -> [u64; 5] {
    let a0 = a0_2_val(a);
    let a1 = a1_1_val(a);
    let a2 = a2_0_val(a);
    let a3 = a3_0_val(a);
    let a4 = a4_0_val(a);

    let r = [a0, a1, a2, a3, a4];
    r
}

pub open spec fn pow2k_loop_boundary_spec(a: [u64; 5]) -> bool {
    &&& 19 * (1u64 << 54) <= u64::MAX
    &&& 77 * ((1u64 << 54) * (1u64 << 54)) <= u128::MAX
    &&& term_product_bounds_spec(a, 1u64 << 54)
    &&& ci_0_val_boundaries(a, 1u64 << 54)
    &&& ci_val_boundaries(a)
    &&& ai_val_boundaries(a)
    &&& pow2k_loop_return(a)[0] < 1u64 << 54
    &&& pow2k_loop_return(a)[1] < 1u64 << 54
    &&& pow2k_loop_return(a)[2] < 1u64 << 54
    &&& pow2k_loop_return(a)[3] < 1u64 << 54
    &&& pow2k_loop_return(a)[4] < 1u64 << 54
}

pub proof fn lemma_pow2k_loop_boundary(a: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> a[i] < 1u64 << 54,
    ensures
        pow2k_loop_boundary_spec(a),
{
    let bound = 1u64 << 54;
    let bound19 = (19 * bound) as u64;
    let bound_sq = 1u128 << 108;

    // // u64 to u128 conversion forces extra assert
    assert(bound * bound == bound_sq) by {
        assert(((1u64 << 54) as u128) * ((1u64 << 54) as u128) == (1u128 << 108)) by (bit_vector);
    }

    assert(bound * bound19 == 19 * bound_sq) by {
        assert((1u64 << 54) * ((19 * (1u64 << 54)) as u64) == 19 * (1u128 << 108)) by (bit_vector);
    }

    assert(19 * bound <= u64::MAX) by {
        assert(19 * (1u64 << 54) <= u64::MAX) by (compute);
    }

    assert(term_product_bounds_spec(a, bound)) by {
        // If a[i] < 2^54 then a[i] * a[j] < 2^108 and a[i] * (19 * a[j]) < 19 * 2^108
        lemma_term_product_bounds(a, bound);
    }

    assert(ci_0_val_boundaries(a, bound)) by {
        // ci_0 < 77 * (1u128 << 108)
        lemma_c_i_0_bounded(a, bound);
    }

    // precond for lemma_c_i_shift_bounded
    assert(77 * bound_sq + u64::MAX <= ((u64::MAX as u128) << 51)) by {
        assert(77 * (1u128 << 108) + u64::MAX <= ((u64::MAX as u128) << 51)) by (compute);
    }

    // ci >> 51 <= u64::MAX
    assert(ci_val_boundaries(a)) by {
        lemma_c_i_shift_bounded(a, bound);
    }

    assert(ai_val_boundaries(a)) by {
        // a0_0 < (1u64 << 51)
        assert(a0_0_val(a) < 1u64 << 51 && a1_0_val(a) < 1u64 << 51 && a2_0_val(a) < 1u64 << 51
            && a3_0_val(a) < 1u64 << 51 && a4_0_val(a) < 1u64 << 51) by {
            lemma_masked_lt_51(c0_val(a) as u64);
            lemma_masked_lt_51(c1_val(a) as u64);
            lemma_masked_lt_51(c2_val(a) as u64);
            lemma_masked_lt_51(c3_val(a) as u64);
            lemma_masked_lt_51(c4_val(a) as u64);
        }

        // ceil(2^59.33)
        let pow2_5933 = 724618875532318195u64;
        assert(carry_val(a) < pow2_5933) by {
            // From the comments in pow2k:
            // c4 < 2^110.33  so that carry < 2^59.33
            // and
            // a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58
            assert(c4_val(a) >> 51 <= (5 * bound_sq + (u64::MAX as u128)) as u128 >> 51) by {
                lemma_shr_51_le(c4_val(a), (5 * bound_sq + (u64::MAX as u128)) as u128);
            }

            assert((5 * (1u128 << 108) + (u64::MAX as u128)) as u128 >> 51 < (
            724618875532318195u64 as u128)) by (compute);
        }

        assert(a0_0_val(a) + carry_val(a) * 19 < u64::MAX) by {
            assert((1u64 << 51) + 19 * 724618875532318195u64 <= u64::MAX) by (compute);
        }

        assert(a1_0_val(a) + (a0_1_val(a) >> 51) < 1u64 << 52) by {
            assert(a0_1_val(a) as u128 >> 51 <= u64::MAX as u128 >> 51) by {
                lemma_shr_51_le(a0_1_val(a) as u128, u64::MAX as u128);
            }
            assert(((u64::MAX as u128) >> 51) < (1u64 << 13)) by (compute);
            assert((1u64 << 51) + (1u64 << 13) < (1u64 << 52)) by (compute);
        }

        assert(a0_2_val(a) < 1u64 << 51) by {
            lemma_masked_lt_51(a0_1_val(a) as u64);
        }
    }

    // bv arithmetic, some bounds have 51, some have 52, all therefore have 54
    assert((1u64 << 51) < (1u64 << 52)) by (bit_vector);
    assert((1u64 << 52) < (1u64 << 54)) by (bit_vector);
}

pub proof fn lemma_pow2k_loop_value(a: [u64; 5], limbs: [u64; 5], i: nat)
    requires
        pow2k_loop_boundary_spec(a),
        u64_5_as_nat(a) % p() == pow(u64_5_as_nat(limbs) as int, pow2(i)) as nat % p(),
    ensures
        u64_5_as_nat(pow2k_loop_return(a)) % p() == pow(
            u64_5_as_nat(limbs) as int,
            pow2(i + 1),
        ) as nat % p(),
{
    lemma2_to64_rest();  // pow2(51)
    assert(p() > 0) by {
        pow255_gt_19();
    }

    assert(mask51 == low_bits_mask(51)) by {
        l51_bit_mask_lt();
    }

    // let a_hat = [a0_2, a1_1, a2, a3, a4];
    let a_hat = pow2k_loop_return(a);
    let a0_1 = a0_1_val(a);
    let a0_2 = a0_2_val(a);
    let a1_0 = a1_0_val(a);
    let a1_1 = a1_1_val(a);
    let a2 = a2_0_val(a);
    let a3 = a3_0_val(a);
    let a4 = a4_0_val(a);

    assert(u64_5_as_nat(a_hat) % p() == (u64_5_as_nat(a) * u64_5_as_nat(a)) % p()) by {
        // it suffices to prove u64_5_as_nat(a_hat) == (u64_5_as_nat(a))^2 (mod p)
        // let s = pow2(51) for brevity
        // By definition, u64_5_as_nat(a_hat) = a0_2 + s * a1_1 + s^2 * a2 + s^3 * a3 + s^4 * a4
        // a0_2 + s * a1_1 cancel out terms via the div/mod identity:
        assert(u64_5_as_nat(a_hat) == a0_1 + pow2(51) * a1_0 + pow2(102) * a2 + pow2(153) * a3
            + pow2(204) * a4) by {
            // a0_2 + s * a1_1 =
            // a0_1 % s  + s * (a1_0 + s * (a0_1 / s)) =
            // s * a1_0 + [s * (a0_1 / s) + a0_1 % s] = (by the div-mod identity)
            // s * a1_0 + a0_1
            assert(a0_2 + pow2(51) * a1_1 == a0_1 + pow2(51) * a1_0) by {
                assert(a0_2 == a0_1 % (pow2(51) as u64)) by {
                    lemma_u64_low_bits_mask_is_mod(a0_1, 51);
                }

                assert(a0_1 >> 51 == a0_1 / (pow2(51) as u64)) by {
                    lemma_u64_shr_is_div(a0_1, 51);
                }

                lemma_u64_div_and_mod_51((a0_1 >> 51), a0_2, a0_1);
            }
        }

        let c0_0 = c0_0_val(a);
        let c1_0 = c1_0_val(a);
        let c2_0 = c2_0_val(a);
        let c3_0 = c3_0_val(a);
        let c4_0 = c4_0_val(a);
        let c1 = c1_val(a);
        let c2 = c2_val(a);
        let c3 = c3_val(a);
        let c4 = c4_val(a);
        let carry = carry_val(a);

        // Next, we replace all _ & LOW_BITS_MASK with (mod s)
        assert(u64_5_as_nat(a_hat) == ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry + pow2(51)
            * ((c1 as u64) % (pow2(51) as u64)) + pow2(102) * ((c2 as u64) % (pow2(51) as u64))
            + pow2(153) * ((c3 as u64) % (pow2(51) as u64)) + pow2(204) * ((c4 as u64) % (pow2(
            51,
        ) as u64))) by {
            l51_bit_mask_lt();

            assert((pow2(51) as u64) == (pow2(51) as u128));

            assert(a0_1 == ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry) by {
                lemma_u64_low_bits_mask_is_mod(c0_0 as u64, 51);
            }

            assert(a1_0 == (c1 as u64) % (pow2(51) as u64)) by {
                lemma_u64_low_bits_mask_is_mod(c1 as u64, 51);
            }

            assert(a2 == (c2 as u64) % (pow2(51) as u64)) by {
                lemma_u64_low_bits_mask_is_mod(c2 as u64, 51);
            }

            assert(a3 == (c3 as u64) % (pow2(51) as u64)) by {
                lemma_u64_low_bits_mask_is_mod(c3 as u64, 51);
            }

            assert(a4 == (c4 as u64) % (pow2(51) as u64)) by {
                lemma_u64_low_bits_mask_is_mod(c4 as u64, 51);
            }
        }

        // We can see all mod operations in u128
        assert(u64_5_as_nat(a_hat) == (c0_0 % (pow2(51) as u128)) + 19 * carry + pow2(51) * (c1 % (
        pow2(51) as u128)) + pow2(102) * (c2 % (pow2(51) as u128)) + pow2(153) * (c3 % (pow2(
            51,
        ) as u128)) + pow2(204) * (c4 % (pow2(51) as u128))) by {
            // pow2(51) is the same in u64 and 128
            lemma_cast_then_mod_51(c0_0);
            lemma_cast_then_mod_51(c1);
            lemma_cast_then_mod_51(c2);
            lemma_cast_then_mod_51(c3);
            lemma_cast_then_mod_51(c4);
        }

        // Next, we categorically replace a % s with a - s * ( a / s )
        assert(u64_5_as_nat(a_hat) == (c0_0 - pow2(51) * (c0_0 / (pow2(51) as u128))) + 19 * carry
            + pow2(51) * (c1 - pow2(51) * (c1 / (pow2(51) as u128))) + pow2(102) * (c2 - pow2(51)
            * (c2 / (pow2(51) as u128))) + pow2(153) * (c3 - pow2(51) * (c3 / (pow2(51) as u128)))
            + pow2(204) * (c4 - pow2(51) * (c4 / (pow2(51) as u128)))) by {
            lemma_fundamental_div_mod(c0_0 as int, pow2(51) as int);
            lemma_fundamental_div_mod(c1 as int, pow2(51) as int);
            lemma_fundamental_div_mod(c2 as int, pow2(51) as int);
            lemma_fundamental_div_mod(c3 as int, pow2(51) as int);
            lemma_fundamental_div_mod(c4 as int, pow2(51) as int);
        }

        // Then, we know that
        // carry = c4/s
        // c4 = c4_0 + c3/s <=> c3/s = c4 - c4_0
        // c3 = c3_0 + c2/s <=> c2/s = c3 - c3_0
        // c2 = c2_0 + c1/s <=> c1/s = c2 - c2_0
        // c1 = c1_0 + c0_0/s <=> c0_0/s = c1 - c1_0
        assert(u64_5_as_nat(a_hat) == (c0_0 - pow2(51) * (c1 - c1_0)) + 19 * carry + pow2(51) * (c1
            - pow2(51) * (c2 - c2_0)) + pow2(102) * (c2 - pow2(51) * (c3 - c3_0)) + pow2(153) * (c3
            - pow2(51) * (c4 - c4_0)) + pow2(204) * (c4 - pow2(51) * carry)) by {
            lemma_u128_shr_is_div(c0_0, 51);
            lemma_u128_shr_is_div(c1, 51);
            lemma_u128_shr_is_div(c2, 51);
            lemma_u128_shr_is_div(c3, 51);
            lemma_u128_shr_is_div(c4, 51);
        }

        // Now we use distributivity and pow exponent sums, which cancels out any ci terms and leaves only ci_0 terms
        // Conveniently, we're left with a difference of c * p
        assert(u64_5_as_nat(a_hat) == c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0
            + pow2(204) * c4_0 - p() * carry) by {
            assert(c0_0 - pow2(51) * (c1 - c1_0) == c0_0 - pow2(51) * c1 + pow2(51) * c1_0) by {
                lemma_mul_is_distributive_sub(pow2(51) as int, c1 as int, c1_0 as int);
            }

            assert(pow2(51) * (c1 - pow2(51) * (c2 - c2_0)) == pow2(51) * c1 - pow2(102) * c2
                + pow2(102) * c2_0) by {
                lemma_mul_sub(c1 as int, c2 as int, c2_0 as int, 51);
            }

            assert(pow2(102) * (c2 - pow2(51) * (c3 - c3_0)) == pow2(102) * c2 - pow2(153) * c3
                + pow2(153) * c3_0) by {
                lemma_mul_sub(c2 as int, c3 as int, c3_0 as int, 102);
            }

            assert(pow2(153) * (c3 - pow2(51) * (c4 - c4_0)) == pow2(153) * c3 - pow2(204) * c4
                + pow2(204) * c4_0) by {
                lemma_mul_sub(c3 as int, c4 as int, c4_0 as int, 153);
            }

            assert(pow2(204) * (c4 - pow2(51) * carry) == pow2(204) * c4 - pow2(255) * carry) by {
                lemma_mul_is_distributive_sub(pow2(204) as int, c4 as int, pow2(51) * carry);
                lemma_mul_is_associative(pow2(204) as int, pow2(51) as int, carry as int);
                lemma_pow2_adds(204, 51);
            }

            // carry on the right, get p
            assert(c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0 + pow2(204) * c4_0
                + 19 * carry - pow2(255) * carry == c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0
                + pow2(153) * c3_0 + pow2(204) * c4_0 - p() * carry) by {
                pow255_gt_19();
                lemma_mul_is_distributive_sub_other_way(carry as int, pow2(255) as int, 19);
            }
        }

        let c_arr_as_nat = (c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0 + pow2(204)
            * c4_0);

        assert(u64_5_as_nat(a_hat) % p() == c_arr_as_nat as nat % p()) by {
            lemma_mod_diff_factor(carry as int, c_arr_as_nat as int, p() as int);
        }

        // We use the lemma_u64_5_as_nat_squared lemma to see what (u64_5_as_nat(a)^2) evaluates to (mod p)

        // The nat_squared lemma gives us the following:
        // u64_5_as_nat(a) * u64_5_as_nat(a) ==
        // pow2(8 * 51) * (a[4] * a[4]) +
        // pow2(7 * 51) * (2 * (a[3] * a[4])) +
        // pow2(6 * 51) * (a[3] * a[3] + 2 * (a[2] * a[4])) +
        // pow2(5 * 51) * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4])) +
        // pow2(4 * 51) * (a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])) +
        // pow2(3 * 51) * (2 * (a[1] * a[2]) + 2 * (a[0] * a[3])) +
        // pow2(2 * 51) * (a[1] * a[1] + 2 * (a[0] * a[2])) +
        // pow2(1 * 51) * (2 * (a[0] * a[1])) +
        //                (a[0] * a[0])
        //
        // AND
        //
        // (u64_5_as_nat(a) * u64_5_as_nat(a)) % p() ==
        // (
        //     pow2(4 * 51) * (a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])) +
        //     pow2(3 * 51) * (2 * (a[1] *  a[2]) + 2 * (a[0] *  a[3]) + 19 * (a[4] * a[4])) +
        //     pow2(2 * 51) * (a[1] * a[1] + 2 * (a[0] *  a[2]) + 19 * (2 * (a[3] * a[4]))) +
        //     pow2(1 * 51) * (2 * (a[0] *  a[1]) + 19 * (a[3] * a[3] + 2 * (a[2] * a[4]))) +
        //                    (a[0] *  a[0] + 19 * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4])))
        // ) as nat % p()
        lemma_u64_5_as_nat_squared(a);

        // We're basically done, what remains is to prove that the coefficients next to pow2(i * 51)
        // are exactly ci_0s (via distributivity and associativity)

        let a3_19 = 19 * a[3];
        let a4_19 = 19 * a[4];

        // let c0_0: u128 = a[0] *  a[0] + 2*( a[1] * a4_19 + a[2] * a3_19);
        assert(c0_0 == (a[0] * a[0] + 19 * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4])))) by {
            // The solver does distributivity on its own.
            // LHS = a[0] *  a[0] + 2*( a[1] * a4_19 + a[2] * a3_19);
            //     = a[0] *  a[0] + 2*( a[1] * a4_19 ) + 2 * (a[2] * a3_19);
            // RHS = a[0] *  a[0] + 19 * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4]))
            //     = a[0] *  a[0] + 19 * (2 * (a[2] * a[3])) + 19 * (2 * (a[1] * a[4]))
            // goals
            // 1) 2 * (a[1] * a4_19) = 19 * (2 * (a[1] * a[4]))
            // 2) 2 * (a[2] * a3_19) = 19 * (2 * (a[2] * a[3]))
            assert(2 * (a[1] * a4_19) == 19 * (2 * (a[1] * a[4]))) by {
                lemma_reorder_mul(a[1] as int, a[4] as int);
            }

            assert(2 * (a[2] * a3_19) == 19 * (2 * (a[2] * a[3]))) by {
                lemma_reorder_mul(a[2] as int, a[3] as int);
            }
        }

        // let c1_0: u128 = a[3] * a3_19 + 2*( a[0] *  a[1] + a[2] * a4_19);
        assert(c1_0 == (2 * (a[0] * a[1]) + 19 * (a[3] * a[3] + 2 * (a[2] * a[4])))) by {
            // The solver does distributivity on its own.
            // LHS = a[3] * a3_19 + 2*( a[0] *  a[1] + a[2] * a4_19)
            //     = a[3] * a3_19 + 2*( a[0] *  a[1]) + 2 * (a[2] * a4_19)
            // RHS = 2 * (a[0] *  a[1]) + 19 * (a[3] * a[3] + 2 * (a[2] * a[4]))
            //     = 2 * (a[0] *  a[1]) + 19 * (a[3] * a[3]) + 19 * (2 * (a[2] * a[4]))
            // goals: 1) a[3] * a3_19 = 19 * (a[3] * a[3])
            //        2) 2 * (a[2] * a4_19) = 19 * (2 * (a[2] * a[4]))
            assert(a[3] * a3_19 == 19 * (a[3] * a[3])) by {
                lemma_mul_is_associative(a[3] as int, a[3] as int, 19);
            }

            assert(2 * (a[2] * a4_19) == 19 * (2 * (a[2] * a[4]))) by {
                lemma_reorder_mul(a[2] as int, a[4] as int);
            }
        }

        // let c2_0: u128 = a[1] *  a[1] + 2*( a[0] *  a[2] + a[4] * a3_19);
        assert(c2_0 == (a[1] * a[1] + 2 * (a[0] * a[2]) + 19 * (2 * (a[3] * a[4])))) by {
            // The solver does distributivity on its own.
            // LHS = a[1] * a[1] + 2 * (a[0] *  a[2] + a[4] * a3_19)
            //     = a[1] * a[1] + 2 * (a[0] *  a[2]) +  2 * (a[4] * a3_19)
            // RHS = a[1] * a[1] + 2 * (a[0] *  a[2]) + 19 * (2 * (a[3] * a[4]))
            // goals: 2 * (a[4] * a3_19) = 19 * (2 * (a[3] * a[4]))
            assert(2 * (a[4] * a3_19) == 19 * (2 * (a[3] * a[4]))) by {
                lemma_mul_is_associative(a[4] as int, a[3] as int, 19);
            }
        }

        // let c3_0: u128 = a[4] * a4_19 + 2*( a[0] *  a[3] + a[1] *  a[2]);
        assert(c3_0 == (2 * (a[1] * a[2]) + 2 * (a[0] * a[3]) + 19 * (a[4] * a[4]))) by {
            // The solver does distributivity on its own.
            // LHS = a[4] * a4_19 + 2 * (a[0] *  a[3] + a[1] *  a[2])
            //     = a[4] * a4_19 + 2 * (a[0] *  a[3]) + 2 * (a[1] *  a[2])
            // RHS = 2 * (a[1] *  a[2]) + 2 * (a[0] *  a[3]) + 19 * (a[4] * a[4])
            // goals: a[4] * a4_19 = 19 * (a[4] * a[4])
            assert(a[4] * a4_19 == 19 * (a[4] * a[4])) by {
                lemma_mul_is_associative(a[4] as int, a[4] as int, 19);
            }
        }

        // let c4_0: u128 = a[2] *  a[2] + 2*( a[0] *  a[4] + a[1] *  a[3]);
        assert(c4_0 == (a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4]))) by {
            // The solver does distributivity on its own.
            // LHS = a[2] * a[2] + 2 * (a[0] * a[4] + a[1] * a[3])
            //     = a[2] * a[2] + 2 * (a[0] * a[4]) + 2 * (a[1] * a[3])
            // RHS = a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])
            // goals: none
        }
    }

    let a_pow_2i_int = pow(u64_5_as_nat(limbs) as int, pow2(i));
    assert(a_pow_2i_int >= 0) by {
        lemma_pow_nat_is_nat(u64_5_as_nat(limbs), i);
    }
    let a_pow_2i: nat = a_pow_2i_int as nat;

    assert(u64_5_as_nat(a_hat) % p() == ((u64_5_as_nat(a) % p()) * (u64_5_as_nat(a) % p())) % p())
        by {
        lemma_mul_mod_noop(u64_5_as_nat(a) as int, u64_5_as_nat(a) as int, p() as int);
    }

    // (a_pow_2i % p)^2 % p = (a_pow_2i^2) % p
    assert(((a_pow_2i % p()) * (a_pow_2i % p())) % p() == (a_pow_2i * a_pow_2i) % p()) by {
        lemma_mul_mod_noop(a_pow_2i as int, a_pow_2i as int, p() as int);
    }

    // We know, by the loop inv, that
    // u64_5_as_nat(a) % p == a_pow_2i % p
    // and, by the above
    // u64_5_as_nat(a_hat) % p  = (u64_5_as_nat(a) * u64_5_as_nat(a)) % p = (a_pow_2i ^ 2)) % p
    // It suffices to prove that
    // (v^(2^i))^2 = v^(2^(i + 1))
    assert(pow(u64_5_as_nat(limbs) as int, pow2(i)) * pow(u64_5_as_nat(limbs) as int, pow2(i))
        == pow(u64_5_as_nat(limbs) as int, pow2(i + 1))) by {
        lemma_pow2_square(u64_5_as_nat(limbs) as int, i);
    }
}

} // verus!
