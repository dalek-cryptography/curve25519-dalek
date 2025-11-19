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

} // verus!
