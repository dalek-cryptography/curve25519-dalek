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
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

// ============================================================================
// Spec functions for multiplication coefficients
// ============================================================================
// Initial coefficient values before carry propagation.
// These match the exec code in mul:
//   c0 = m(a[0],b[0]) + m(a[4],b1_19) + m(a[3],b2_19) + m(a[2],b3_19) + m(a[1],b4_19)
// where bN_19 = b[N] * 19
pub open spec fn mul_c0_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[0] * b[0] + a[4] * (19 * b[1]) + a[3] * (19 * b[2]) + a[2] * (19 * b[3]) + a[1] * (19
        * b[4])) as u128
}

pub open spec fn mul_c1_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[1] * b[0] + a[0] * b[1] + a[4] * (19 * b[2]) + a[3] * (19 * b[3]) + a[2] * (19
        * b[4])) as u128
}

pub open spec fn mul_c2_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[2] * b[0] + a[1] * b[1] + a[0] * b[2] + a[4] * (19 * b[3]) + a[3] * (19 * b[4])) as u128
}

pub open spec fn mul_c3_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[3] * b[0] + a[2] * b[1] + a[1] * b[2] + a[0] * b[3] + a[4] * (19 * b[4])) as u128
}

pub open spec fn mul_c4_0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (a[4] * b[0] + a[3] * b[1] + a[2] * b[2] + a[1] * b[3] + a[0] * b[4]) as u128
}

// Accumulated coefficient values after carry propagation chain
pub open spec fn mul_c0_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    mul_c0_0_val(a, b)
}

pub open spec fn mul_c1_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (mul_c1_0_val(a, b) + ((mul_c0_val(a, b) >> 51) as u64) as u128) as u128
}

pub open spec fn mul_c2_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (mul_c2_0_val(a, b) + ((mul_c1_val(a, b) >> 51) as u64) as u128) as u128
}

pub open spec fn mul_c3_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (mul_c3_0_val(a, b) + ((mul_c2_val(a, b) >> 51) as u64) as u128) as u128
}

pub open spec fn mul_c4_val(a: [u64; 5], b: [u64; 5]) -> u128 {
    (mul_c4_0_val(a, b) + ((mul_c3_val(a, b) >> 51) as u64) as u128) as u128
}

// The final 5-limb output, mirroring the exec carry chain in mul
pub open spec fn mul_return(a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
    let c0 = mul_c0_val(a, b);
    let c1 = mul_c1_val(a, b);
    let c2 = mul_c2_val(a, b);
    let c3 = mul_c3_val(a, b);
    let c4 = mul_c4_val(a, b);
    let out0: u64 = (c0 as u64) & mask51;
    let out1: u64 = (c1 as u64) & mask51;
    let out2: u64 = (c2 as u64) & mask51;
    let out3: u64 = (c3 as u64) & mask51;
    let out4: u64 = (c4 as u64) & mask51;
    let carry: u64 = (c4 >> 51) as u64;
    let out0: u64 = (out0 + carry * 19) as u64;
    let out1: u64 = (out1 + (out0 >> 51)) as u64;
    let out0: u64 = out0 & mask51;
    [out0, out1, out2, out3, out4]
}

// ============================================================================
// Product bound specs and lemmas
// ============================================================================
pub open spec fn mul_term_product_bounds_spec(a: [u64; 5], b: [u64; 5], bound: u64) -> bool {
    // All plain products a[i]*b[j] < bound*bound
    &&& forall|i: int, j: int|
        0 <= i < 5 && 0 <= j < 5 ==> (a[i] as u128) * (b[j] as u128) < bound
            * bound
        // All scaled products a[i]*(19*b[j]) < 19*bound*bound
    &&& forall|i: int, j: int|
        0 <= i < 5 && 0 <= j < 5 ==> (a[i] as u128) * ((19 * b[j]) as u128) < 19 * (bound * bound)
}

pub proof fn lemma_mul_term_product_bounds(a: [u64; 5], b: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        forall|i: int| 0 <= i < 5 ==> a[i] < bound,
        forall|i: int| 0 <= i < 5 ==> b[i] < bound,
    ensures
        mul_term_product_bounds_spec(a, b, bound),
{
    let bound19 = (19 * bound) as u64;

    assert(bound * (19 * bound) == 19 * (bound * bound)) by {
        lemma_mul_is_associative(19, bound as int, bound as int);
    }

    assert forall|i: int, j: int| 0 <= i < 5 && 0 <= j < 5 implies (a[i] as u128) * (b[j] as u128)
        < bound * bound && (a[i] as u128) * ((19 * b[j]) as u128) < 19 * (bound * bound) by {
        lemma_m(a[i], b[j], bound, bound);
        lemma_m(a[i], (19 * b[j]) as u64, bound, bound19);
    }
}

// ============================================================================
// Initial coefficient bound specs and lemmas
// ============================================================================
pub open spec fn mul_ci_0_val_boundaries(a: [u64; 5], b: [u64; 5], bound: u64) -> bool {
    &&& mul_c0_0_val(a, b) < 77 * (bound * bound)
    &&& mul_c1_0_val(a, b) < 59 * (bound * bound)
    &&& mul_c2_0_val(a, b) < 41 * (bound * bound)
    &&& mul_c3_0_val(a, b) < 23 * (bound * bound)
    &&& mul_c4_0_val(a, b) < 5 * (bound * bound)
}

pub proof fn lemma_mul_c_i_0_bounded(a: [u64; 5], b: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        forall|i: int| 0 <= i < 5 ==> a[i] < bound,
        forall|i: int| 0 <= i < 5 ==> b[i] < bound,
    ensures
        mul_ci_0_val_boundaries(a, b, bound),
{
    lemma_mul_term_product_bounds(a, b, bound);
}

// ============================================================================
// Carry chain bound specs and lemmas
// ============================================================================
pub open spec fn mul_ci_val_boundaries(a: [u64; 5], b: [u64; 5]) -> bool {
    &&& (mul_c0_val(a, b) >> 51) <= (u64::MAX as u128)
    &&& (mul_c1_val(a, b) >> 51) <= (u64::MAX as u128)
    &&& (mul_c2_val(a, b) >> 51) <= (u64::MAX as u128)
    &&& (mul_c3_val(a, b) >> 51) <= (u64::MAX as u128)
    &&& (mul_c4_val(a, b) >> 51) <= (u64::MAX as u128)
}

pub proof fn lemma_mul_c_i_shift_bounded(a: [u64; 5], b: [u64; 5], bound: u64)
    requires
        19 * bound <= u64::MAX,
        77 * (bound * bound) + u64::MAX <= ((u64::MAX as u128) << 51),
        mul_ci_0_val_boundaries(a, b, bound),
    ensures
        mul_ci_val_boundaries(a, b),
{
    lemma_shr_51_fits_u64(mul_c0_val(a, b));
    lemma_shr_51_fits_u64(mul_c1_val(a, b));
    lemma_shr_51_fits_u64(mul_c2_val(a, b));
    lemma_shr_51_fits_u64(mul_c3_val(a, b));
    lemma_shr_51_fits_u64(mul_c4_val(a, b));
}

// ============================================================================
// Output limb bound specs and lemmas
// ============================================================================
pub open spec fn mul_out_val_boundaries(a: [u64; 5], b: [u64; 5]) -> bool {
    let c0 = mul_c0_val(a, b);
    let c1 = mul_c1_val(a, b);
    let c2 = mul_c2_val(a, b);
    let c3 = mul_c3_val(a, b);
    let c4 = mul_c4_val(a, b);
    let out0: u64 = (c0 as u64) & mask51;
    let out1: u64 = (c1 as u64) & mask51;
    let carry: u64 = (c4 >> 51) as u64;
    let out0_1: u64 = (out0 + carry * 19) as u64;
    &&& out0 < 1u64 << 51
    &&& out1 < 1u64 << 51
    &&& ((c2 as u64) & mask51) < 1u64 << 51
    &&& ((c3 as u64) & mask51) < 1u64 << 51
    &&& ((c4 as u64) & mask51) < 1u64 << 51
    &&& carry < 724618875532318195u64
    &&& out0 + carry * 19 < u64::MAX
    &&& out1 + (out0_1 >> 51) < 1u64 << 52
    &&& (out0_1 & mask51) < 1u64 << 51
}

// ============================================================================
// Master boundary spec and lemma
// ============================================================================
pub open spec fn mul_boundary_spec(a: [u64; 5], b: [u64; 5]) -> bool {
    &&& 19 * (1u64 << 54) <= u64::MAX
    &&& 77 * ((1u64 << 54) * (1u64 << 54)) <= u128::MAX
    &&& mul_term_product_bounds_spec(a, b, 1u64 << 54)
    &&& mul_ci_0_val_boundaries(a, b, 1u64 << 54)
    &&& mul_ci_val_boundaries(a, b)
    &&& mul_out_val_boundaries(a, b)
    &&& mul_return(a, b)[0] < 1u64 << 52
    &&& mul_return(a, b)[1] < 1u64 << 52
    &&& mul_return(a, b)[2] < 1u64 << 52
    &&& mul_return(a, b)[3] < 1u64 << 52
    &&& mul_return(a, b)[4] < 1u64 << 52
    &&& (1u64 << 52) < (1u64 << 54)
}

pub proof fn lemma_mul_boundary(a: [u64; 5], b: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> a[i] < 1u64 << 54,
        forall|i: int| 0 <= i < 5 ==> b[i] < 1u64 << 54,
    ensures
        mul_boundary_spec(a, b),
{
    let bound = 1u64 << 54;
    let bound19 = (19 * bound) as u64;
    let bound_sq = 1u128 << 108;

    assert(bound * bound == bound_sq) by {
        assert(((1u64 << 54) as u128) * ((1u64 << 54) as u128) == (1u128 << 108)) by (bit_vector);
    }

    assert(bound * bound19 == 19 * bound_sq) by {
        assert((1u64 << 54) * ((19 * (1u64 << 54)) as u64) == 19 * (1u128 << 108)) by (bit_vector);
    }

    assert(19 * bound <= u64::MAX) by {
        assert(19 * (1u64 << 54) <= u64::MAX) by (compute);
    }

    assert(mul_term_product_bounds_spec(a, b, bound)) by {
        lemma_mul_term_product_bounds(a, b, bound);
    }

    assert(mul_ci_0_val_boundaries(a, b, bound)) by {
        lemma_mul_c_i_0_bounded(a, b, bound);
    }

    assert(77 * bound_sq + u64::MAX <= ((u64::MAX as u128) << 51)) by {
        assert(77 * (1u128 << 108) + u64::MAX <= ((u64::MAX as u128) << 51)) by (compute);
    }

    assert(mul_ci_val_boundaries(a, b)) by {
        lemma_mul_c_i_shift_bounded(a, b, bound);
    }

    assert(mul_out_val_boundaries(a, b)) by {
        let c0 = mul_c0_val(a, b);
        let c1 = mul_c1_val(a, b);
        let c2 = mul_c2_val(a, b);
        let c3 = mul_c3_val(a, b);
        let c4 = mul_c4_val(a, b);
        let out0: u64 = (c0 as u64) & mask51;
        let out1: u64 = (c1 as u64) & mask51;
        let carry: u64 = (c4 >> 51) as u64;
        let out0_1: u64 = (out0 + carry * 19) as u64;

        assert(out0 < 1u64 << 51 && out1 < 1u64 << 51 && ((c2 as u64) & mask51) < 1u64 << 51 && ((
        c3 as u64) & mask51) < 1u64 << 51 && ((c4 as u64) & mask51) < 1u64 << 51) by {
            lemma_masked_lt_51(c0 as u64);
            lemma_masked_lt_51(c1 as u64);
            lemma_masked_lt_51(c2 as u64);
            lemma_masked_lt_51(c3 as u64);
            lemma_masked_lt_51(c4 as u64);
        }

        let pow2_5933 = 724618875532318195u64;
        assert(carry < pow2_5933) by {
            assert(c4 >> 51 <= (5 * bound_sq + (u64::MAX as u128)) as u128 >> 51) by {
                lemma_shr_51_le(c4, (5 * bound_sq + (u64::MAX as u128)) as u128);
            }
            assert((5 * (1u128 << 108) + (u64::MAX as u128)) as u128 >> 51 < (
            724618875532318195u64 as u128)) by (compute);
        }

        assert(out0 + carry * 19 < u64::MAX) by {
            assert((1u64 << 51) + 19 * 724618875532318195u64 <= u64::MAX) by (compute);
        }

        assert(out1 + (out0_1 >> 51) < 1u64 << 52) by {
            assert(out0_1 as u128 >> 51 <= u64::MAX as u128 >> 51) by {
                lemma_shr_51_le(out0_1 as u128, u64::MAX as u128);
            }
            assert(((u64::MAX as u128) >> 51) < (1u64 << 13)) by (compute);
            assert((1u64 << 51) + (1u64 << 13) < (1u64 << 52)) by (compute);
        }

        assert((out0_1 & mask51) < 1u64 << 51) by {
            lemma_masked_lt_51(out0_1 as u64);
        }
    }

    assert((1u64 << 51) < (1u64 << 52) < (1u64 << 54)) by (bit_vector);
}

// ============================================================================
// Mathematical correctness lemma
// ============================================================================
pub proof fn lemma_mul_value(a: [u64; 5], b: [u64; 5])
    requires
        mul_boundary_spec(a, b),
    ensures
        u64_5_as_nat(mul_return(a, b)) % p() == (u64_5_as_nat(a) * u64_5_as_nat(b)) % p(),
{
    lemma2_to64_rest();
    assert(p() > 0) by {
        pow255_gt_19();
    }

    assert(mask51 == low_bits_mask(51)) by {
        l51_bit_mask_lt();
    }

    let out_hat = mul_return(a, b);

    let c0_0 = mul_c0_0_val(a, b);
    let c1_0 = mul_c1_0_val(a, b);
    let c2_0 = mul_c2_0_val(a, b);
    let c3_0 = mul_c3_0_val(a, b);
    let c4_0 = mul_c4_0_val(a, b);
    let c1 = mul_c1_val(a, b);
    let c2 = mul_c2_val(a, b);
    let c3 = mul_c3_val(a, b);
    let c4 = mul_c4_val(a, b);
    let carry: u64 = (c4 >> 51) as u64;
    let out0_0: u64 = (c0_0 as u64) & mask51;
    let out1_0: u64 = (c1 as u64) & mask51;
    let out2: u64 = (c2 as u64) & mask51;
    let out3: u64 = (c3 as u64) & mask51;
    let out4: u64 = (c4 as u64) & mask51;
    let out0_1: u64 = (out0_0 + carry * 19) as u64;
    let out1_1: u64 = (out1_0 + (out0_1 >> 51)) as u64;
    let out0_2: u64 = out0_1 & mask51;

    assert(u64_5_as_nat(out_hat) == out0_1 + pow2(51) * out1_0 + pow2(102) * out2 + pow2(153) * out3
        + pow2(204) * out4) by {
        assert(out0_2 + pow2(51) * out1_1 == out0_1 + pow2(51) * out1_0) by {
            assert(out0_2 == out0_1 % (pow2(51) as u64)) by {
                lemma_u64_low_bits_mask_is_mod(out0_1, 51);
            }
            assert(out0_1 >> 51 == out0_1 / (pow2(51) as u64)) by {
                lemma_u64_shr_is_div(out0_1, 51);
            }
            lemma_u64_div_and_mod_51((out0_1 >> 51), out0_2, out0_1);
        }
    }

    assert(u64_5_as_nat(out_hat) == ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry + pow2(51) * ((
    c1 as u64) % (pow2(51) as u64)) + pow2(102) * ((c2 as u64) % (pow2(51) as u64)) + pow2(153) * ((
    c3 as u64) % (pow2(51) as u64)) + pow2(204) * ((c4 as u64) % (pow2(51) as u64))) by {
        l51_bit_mask_lt();

        assert((pow2(51) as u64) == (pow2(51) as u128));

        assert(out0_1 == ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry) by {
            lemma_u64_low_bits_mask_is_mod(c0_0 as u64, 51);
        }

        assert(out1_0 == (c1 as u64) % (pow2(51) as u64)) by {
            lemma_u64_low_bits_mask_is_mod(c1 as u64, 51);
        }

        assert(out2 == (c2 as u64) % (pow2(51) as u64)) by {
            lemma_u64_low_bits_mask_is_mod(c2 as u64, 51);
        }

        assert(out3 == (c3 as u64) % (pow2(51) as u64)) by {
            lemma_u64_low_bits_mask_is_mod(c3 as u64, 51);
        }

        assert(out4 == (c4 as u64) % (pow2(51) as u64)) by {
            lemma_u64_low_bits_mask_is_mod(c4 as u64, 51);
        }
    }

    assert(u64_5_as_nat(out_hat) == (c0_0 % (pow2(51) as u128)) + 19 * carry + pow2(51) * (c1 % (
    pow2(51) as u128)) + pow2(102) * (c2 % (pow2(51) as u128)) + pow2(153) * (c3 % (pow2(
        51,
    ) as u128)) + pow2(204) * (c4 % (pow2(51) as u128))) by {
        lemma_cast_then_mod_51(c0_0);
        lemma_cast_then_mod_51(c1);
        lemma_cast_then_mod_51(c2);
        lemma_cast_then_mod_51(c3);
        lemma_cast_then_mod_51(c4);
    }

    assert(u64_5_as_nat(out_hat) == (c0_0 - pow2(51) * (c0_0 / (pow2(51) as u128))) + 19 * carry
        + pow2(51) * (c1 - pow2(51) * (c1 / (pow2(51) as u128))) + pow2(102) * (c2 - pow2(51) * (c2
        / (pow2(51) as u128))) + pow2(153) * (c3 - pow2(51) * (c3 / (pow2(51) as u128))) + pow2(204)
        * (c4 - pow2(51) * (c4 / (pow2(51) as u128)))) by {
        lemma_fundamental_div_mod(c0_0 as int, pow2(51) as int);
        lemma_fundamental_div_mod(c1 as int, pow2(51) as int);
        lemma_fundamental_div_mod(c2 as int, pow2(51) as int);
        lemma_fundamental_div_mod(c3 as int, pow2(51) as int);
        lemma_fundamental_div_mod(c4 as int, pow2(51) as int);
    }

    // carry = c4/s, c0_0/s = c1 - c1_0, c1/s = c2 - c2_0, etc.
    assert(u64_5_as_nat(out_hat) == (c0_0 - pow2(51) * (c1 - c1_0)) + 19 * carry + pow2(51) * (c1
        - pow2(51) * (c2 - c2_0)) + pow2(102) * (c2 - pow2(51) * (c3 - c3_0)) + pow2(153) * (c3
        - pow2(51) * (c4 - c4_0)) + pow2(204) * (c4 - pow2(51) * carry)) by {
        lemma_u128_shr_is_div(c0_0, 51);
        lemma_u128_shr_is_div(c1, 51);
        lemma_u128_shr_is_div(c2, 51);
        lemma_u128_shr_is_div(c3, 51);
        lemma_u128_shr_is_div(c4, 51);
    }

    // Telescoping: distribute and cancel, leaving only ci_0 terms minus p()*carry
    assert(u64_5_as_nat(out_hat) == c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0
        + pow2(204) * c4_0 - p() * carry) by {
        assert(c0_0 - pow2(51) * (c1 - c1_0) == c0_0 - pow2(51) * c1 + pow2(51) * c1_0) by {
            lemma_mul_is_distributive_sub(pow2(51) as int, c1 as int, c1_0 as int);
        }

        assert(pow2(51) * (c1 - pow2(51) * (c2 - c2_0)) == pow2(51) * c1 - pow2(102) * c2 + pow2(
            102,
        ) * c2_0) by {
            lemma_mul_sub(c1 as int, c2 as int, c2_0 as int, 51);
        }

        assert(pow2(102) * (c2 - pow2(51) * (c3 - c3_0)) == pow2(102) * c2 - pow2(153) * c3 + pow2(
            153,
        ) * c3_0) by {
            lemma_mul_sub(c2 as int, c3 as int, c3_0 as int, 102);
        }

        assert(pow2(153) * (c3 - pow2(51) * (c4 - c4_0)) == pow2(153) * c3 - pow2(204) * c4 + pow2(
            204,
        ) * c4_0) by {
            lemma_mul_sub(c3 as int, c4 as int, c4_0 as int, 153);
        }

        assert(pow2(204) * (c4 - pow2(51) * carry) == pow2(204) * c4 - pow2(255) * carry) by {
            lemma_mul_is_distributive_sub(pow2(204) as int, c4 as int, pow2(51) * carry);
            lemma_mul_is_associative(pow2(204) as int, pow2(51) as int, carry as int);
            lemma_pow2_adds(204, 51);
        }

        assert(c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0 + pow2(204) * c4_0 + 19
            * carry - pow2(255) * carry == c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153)
            * c3_0 + pow2(204) * c4_0 - p() * carry) by {
            pow255_gt_19();
            lemma_mul_is_distributive_sub_other_way(carry as int, pow2(255) as int, 19);
        }
    }

    let c_arr_as_nat = (c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0 + pow2(204)
        * c4_0);

    assert(u64_5_as_nat(out_hat) % p() == c_arr_as_nat as nat % p()) by {
        lemma_mod_diff_factor(carry as int, c_arr_as_nat as int, p() as int);
    }

    // Connect c_i_0 sums to the polynomial product via lemma_u64_5_as_nat_product
    lemma_u64_5_as_nat_product(a, b);

    let s1 = pow2(51);
    let s4 = pow2(204);

    // Rewrite c_i_0 from a[i]*(19*b[j]) form to 19*(a[i]*b[j]) form
    // to match the ensures of lemma_u64_5_as_nat_product
    assert(c0_0 == (a[0] * b[0] + 19 * (a[4] * b[1] + a[3] * b[2] + a[2] * b[3] + a[1] * b[4])))
        by {
        lemma_mul_is_associative(a[4] as int, b[1] as int, 19);
        lemma_mul_is_associative(a[3] as int, b[2] as int, 19);
        lemma_mul_is_associative(a[2] as int, b[3] as int, 19);
        lemma_mul_is_associative(a[1] as int, b[4] as int, 19);
        lemma_mul_distributive_4_terms(19, a[4] * b[1], a[3] * b[2], a[2] * b[3], a[1] * b[4]);
    }

    assert(c1_0 == (a[1] * b[0] + a[0] * b[1] + 19 * (a[4] * b[2] + a[3] * b[3] + a[2] * b[4])))
        by {
        lemma_mul_is_associative(a[4] as int, b[2] as int, 19);
        lemma_mul_is_associative(a[3] as int, b[3] as int, 19);
        lemma_mul_is_associative(a[2] as int, b[4] as int, 19);
        lemma_mul_distributive_3_terms(19, a[4] * b[2], a[3] * b[3], a[2] * b[4]);
    }

    assert(c2_0 == (a[2] * b[0] + a[1] * b[1] + a[0] * b[2] + 19 * (a[4] * b[3] + a[3] * b[4])))
        by {
        lemma_mul_is_associative(a[4] as int, b[3] as int, 19);
        lemma_mul_is_associative(a[3] as int, b[4] as int, 19);
        lemma_mul_is_distributive_add(19, a[4] * b[3], a[3] * b[4]);
    }

    assert(c3_0 == (a[3] * b[0] + a[2] * b[1] + a[1] * b[2] + a[0] * b[3] + 19 * (a[4] * b[4])))
        by {
        lemma_mul_is_associative(a[4] as int, b[4] as int, 19);
    }

    // c4_0 already matches the product lemma form directly
    // c4_0 == a[4]*b[0] + a[3]*b[1] + a[2]*b[2] + a[1]*b[3] + a[0]*b[4]

    // Now chain: c_arr_as_nat matches the reduced product form
    let reduced_sum = (s4 * (a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0])
        + pow2(153) * (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0] + 19 * (a[4] * b[4]))
        + pow2(102) * (a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + 19 * (a[3] * b[4] + a[4] * b[3]))
        + s1 * (a[0] * b[1] + a[1] * b[0] + 19 * (a[2] * b[4] + a[3] * b[3] + a[4] * b[2])) + (a[0]
        * b[0] + 19 * (a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1])));

    assert(c_arr_as_nat == reduced_sum);
    assert((u64_5_as_nat(a) * u64_5_as_nat(b)) % p() == reduced_sum as nat % p());
    assert(c_arr_as_nat as nat % p() == (u64_5_as_nat(a) * u64_5_as_nat(b)) % p());
}

} // verus!
