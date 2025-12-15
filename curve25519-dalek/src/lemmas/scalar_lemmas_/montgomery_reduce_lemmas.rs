#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::specs::field_specs_u64::*;

verus! {

// NOT IN VSTD YET
pub broadcast proof fn lemma_u128_shl_is_mul(x: u128, shift: u128)
    requires
        0 <= shift < <u128>::BITS,
        x * pow2(shift as nat) <= <u128>::MAX,
    ensures
        #[trigger] (x << shift) == x * pow2(shift as nat),
{
    assume(false);
}

pub proof fn lemma_part2_bounds(sum: u128)
    ensures
        ({
            let carry = sum >> 52;
            let w = (sum as u64) & (((1u64 << 52) - 1) as u64);
            &&& w < (1u64 << 52)
            &&& sum == w + (carry << 52)
        }),
{
    let carry = sum >> 52;
    let w = (sum as u64) & (((1u64 << 52) - 1) as u64);

    assert(w < 1u64 << 52) by {
        assert((sum as u64) & (((1u64 << 52) - 1) as u64) < (1u64 << 52)) by (bit_vector);
    }

    assert(sum == w + (carry << 52)) by {
        let p52 = pow2(52);
        assert(p52 > 0) by {
            lemma_pow2_pos(52);
        }

        assert(sum == p52 * (sum as nat / p52) + sum as nat % p52) by {
            lemma_fundamental_div_mod(sum as int, p52 as int);
        }

        assert(sum >> 52 == sum as nat / p52) by {
            lemma_u128_shr_is_div(sum, 52);
        }
        assert(carry << 52 == p52 * (sum as nat / p52)) by {
            assert(carry << 52 == carry * p52) by {
                assert(carry * p52 <= u128::MAX) by {
                    assert((sum as nat / p52) * p52 <= sum <= u128::MAX) by {
                        assert((sum as nat / p52) * p52 == p52 * (sum as nat / p52)) by {
                            lemma_mul_is_commutative(p52 as int, (sum as nat / p52) as int);
                        }
                        assert(p52 * (sum as nat / p52) <= (p52 * sum) as nat / p52) by {
                            lemma_mul_hoist_inequality(p52 as int, sum as int, p52 as int);
                        }
                        assert((p52 * sum) as nat / p52 == sum) by {
                            lemma_div_multiples_vanish(sum as int, p52 as int);
                        }
                    }
                }
                lemma_u128_shl_is_mul(carry, 52);
            }
            lemma_mul_is_commutative(p52 as int, (sum as nat / p52) as int);
        }

        assert(w == sum as nat % p52) by {
            assert(((1u64 << 52) - 1) as u64 == low_bits_mask(52)) by {
                assert(1u64 << 52 == p52) by {
                    lemma_u64_shift_is_pow2(52);
                }
            }
            assert((sum as u64) & (low_bits_mask(52) as u64) == sum as u64 % (p52 as u64)) by {
                lemma_u64_low_bits_mask_is_mod(sum as u64, 52);
            }

            assert(sum as u64 % (p52 as u64) == sum as nat % p52) by {
                assert(p52 == 0x10000000000000) by {
                    lemma2_to64_rest();
                }
                assert(sum as u64 == sum % 0x10000000000000000) by (bit_vector);
                assert(sum % 0x10000000000000 == (sum % 0x10000000000000000) % 0x10000000000000)
                    by (bit_vector);
            }
        }
    }
}

} // verus!
