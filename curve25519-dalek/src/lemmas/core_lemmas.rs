#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::common_lemmas::pow_lemmas::*;

use crate::specs::core_specs::*;

verus! {

pub proof fn as_nat_32_u8_le_pow2_256(bytes: &[u8; 32])
    ensures
        as_nat_32_u8(&bytes) < pow2(256),
        as_nat_32_u8(&bytes) == as_nat_32_u8(&bytes) % pow2(256),
{
    assert forall|i: nat| 0 <= i <= 31 implies #[trigger] bytes[i as int] * pow2(i * 8) <= pow2(
        (i + 1) * 8,
    ) - pow2(i * 8) by {
        let b = bytes[i as int];
        assert(b < pow2(8)) by {
            u8_lt_pow2_8(b);
        }
        pow2_mul_general(b as nat, 8, i * 8);
        assert(i * 8 + 8 == (i + 1) * 8) by {
            lemma_mul_is_distributive_add_other_way(i as int, 1, 8);
        }
    }
    assert(pow2(0 * 8) == 1) by {
        lemma2_to64();
    }
    assert(as_nat_32_u8(&bytes) % pow2(256) == as_nat_32_u8(&bytes)) by {
        lemma_small_mod(as_nat_32_u8(&bytes), pow2(256));
    }
}

} // verus!
