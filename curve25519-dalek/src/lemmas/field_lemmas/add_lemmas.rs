#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

use super::u64_5_as_nat_lemmas::*;

use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;

verus! {

pub proof fn lemma_field51_add(lhs: &FieldElement51, rhs: &FieldElement51)
    requires
        sum_of_limbs_bounded(lhs, rhs, u64::MAX),
    ensures
        u64_5_as_nat(spec_add_fe51_limbs(lhs, rhs).limbs) == u64_5_as_nat(lhs.limbs) + u64_5_as_nat(
            rhs.limbs,
        ),
        spec_field_element(&spec_add_fe51_limbs(lhs, rhs)) == math_field_add(
            spec_field_element(lhs),
            spec_field_element(rhs),
        ),
{
    assert(u64_5_as_nat(spec_add_fe51_limbs(lhs, rhs).limbs) == u64_5_as_nat(lhs.limbs)
        + u64_5_as_nat(rhs.limbs)) by {
        lemma_u64_5_as_nat_add(lhs.limbs, rhs.limbs);
    }

    // trivial consequence: x = y + z => x % p = (y + z) % p
    // Remains to show (y + z) % p = (y % p + z % p) % p

    assert((u64_5_as_nat(lhs.limbs) + u64_5_as_nat(rhs.limbs)) % p() == (u64_5_as_nat(lhs.limbs)
        % p() + u64_5_as_nat(rhs.limbs) % p()) % p()) by {
        assert(p() > 0) by {
            pow255_gt_19();
        }
        lemma_add_mod_noop(
            u64_5_as_nat(lhs.limbs) as int,
            u64_5_as_nat(rhs.limbs) as int,
            p() as int,
        );
    }
}

pub proof fn lemma_field_add_16p_no_overflow(lhs: &FieldElement51, rhs: &FieldElement51)
    requires
        limbs_bounded(lhs, 54),
        limbs_bounded(rhs, 54),
    ensures
// Adding 16p constants won't overflow

        lhs.limbs[0] <= u64::MAX - 36028797018963664u64,
        lhs.limbs[1] <= u64::MAX - 36028797018963952u64,
        lhs.limbs[2] <= u64::MAX - 36028797018963952u64,
        lhs.limbs[3] <= u64::MAX - 36028797018963952u64,
        lhs.limbs[4] <= u64::MAX - 36028797018963952u64,
        rhs.limbs[0] < 36028797018963664u64,
        rhs.limbs[1] < 36028797018963952u64,
        rhs.limbs[2] < 36028797018963952u64,
        rhs.limbs[3] < 36028797018963952u64,
        rhs.limbs[4] < 36028797018963952u64,
{
    let c0 = 36028797018963664u64;  // 16 * (2^51 - 19)
    let c = 36028797018963952u64;  // 16 * (2^51 - 1)

    // Bound lhs limbs so adding the constants cannot overflow a u64
    assert(lhs.limbs[0] <= u64::MAX - c0) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c0) by (compute);
    }
    assert(lhs.limbs[1] <= u64::MAX - c) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c) by (compute);
    }
    assert(lhs.limbs[2] <= u64::MAX - c) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c) by (compute);
    }
    assert(lhs.limbs[3] <= u64::MAX - c) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c) by (compute);
    }
    assert(lhs.limbs[4] <= u64::MAX - c) by {
        assert(((1u64 << 54) - 1) <= u64::MAX - c) by (compute);
    }

    // Bound rhs limbs to be less than the constants
    assert(rhs.limbs[0] < c0) by {
        assert((1u64 << 54) <= c0) by (compute);
    }
    assert(rhs.limbs[1] < c) by {
        assert((1u64 << 54) <= c) by (compute);
    }
    assert(rhs.limbs[2] < c) by {
        assert((1u64 << 54) <= c) by (compute);
    }
    assert(rhs.limbs[3] < c) by {
        assert((1u64 << 54) <= c) by (compute);
    }
    assert(rhs.limbs[4] < c) by {
        assert((1u64 << 54) <= c) by (compute);
    }
}

} // verus!
