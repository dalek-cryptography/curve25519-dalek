#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

use super::u64_5_as_nat_lemmas::*;

use crate::backend::serial::u64::field::FieldElement51;
use crate::edwards::EdwardsPoint;
use crate::specs::edwards_specs::*;
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

/// Lemma: limb-wise equality implies `FieldElement51` equality.
///
/// This is useful when a function specifies equality of each limb (e.g. conditional_select),
/// but a caller needs equality of the whole `FieldElement51` value.
pub proof fn lemma_field_element51_eq_from_limbs_eq(a: FieldElement51, b: FieldElement51)
    requires
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] == b.limbs[i],
    ensures
        a == b,
{
    // Establish extensional equality of the limb arrays; Verus can then lift to struct equality.
    assert(a.limbs =~= b.limbs);
    assert(a == b);
}

pub proof fn lemma_field_add_16p_no_overflow(lhs: &FieldElement51, rhs: &FieldElement51)
    requires
        fe51_limbs_bounded(lhs, 54),
        fe51_limbs_bounded(rhs, 54),
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

/// Lemma: bound weakening - if limbs are bounded by `a` bits, they're also bounded by `b` bits when a < b.
/// This is useful when an invariant guarantees 52-bounded but a precondition requires 54-bounded.
pub proof fn lemma_fe51_limbs_bounded_weaken(fe: &FieldElement51, a: u64, b: u64)
    requires
        fe51_limbs_bounded(fe, a),
        a < b,
        b <= 63,  // so 1u64 << b doesn't overflow

    ensures
        fe51_limbs_bounded(fe, b),
{
    assert forall|i: int| 0 <= i < 5 implies fe.limbs[i] < (1u64 << b) by {
        assert(fe.limbs[i] < (1u64 << a));
        assert((1u64 << a) < (1u64 << b)) by (bit_vector)
            requires
                a < b,
                b <= 63,
        ;
    }
}

/// Weaken EdwardsPoint from 52-bounded (invariant) to 54-bounded (operation precondition)
pub proof fn lemma_edwards_point_weaken_to_54(point: &EdwardsPoint)
    requires
        edwards_point_limbs_bounded(*point),
    ensures
        fe51_limbs_bounded(&point.X, 54),
        fe51_limbs_bounded(&point.Y, 54),
        fe51_limbs_bounded(&point.Z, 54),
        fe51_limbs_bounded(&point.T, 54),
{
    lemma_fe51_limbs_bounded_weaken(&point.X, 52, 54);
    lemma_fe51_limbs_bounded_weaken(&point.Y, 52, 54);
    lemma_fe51_limbs_bounded_weaken(&point.Z, 52, 54);
    lemma_fe51_limbs_bounded_weaken(&point.T, 52, 54);
}

/// Lemma: addition bounds propagation - if both inputs are n-bounded, result is (n+1)-bounded.
/// This is because: limb[i] < 2^n + limb[i] < 2^n implies result[i] < 2^(n+1).
pub proof fn lemma_add_bounds_propagate(a: &FieldElement51, b: &FieldElement51, n: u64)
    requires
        fe51_limbs_bounded(a, n),
        fe51_limbs_bounded(b, n),
        n < 63,  // so n+1 <= 63 and shifts don't overflow

    ensures
        fe51_limbs_bounded(&spec_add_fe51_limbs(a, b), (n + 1) as u64),
{
    let result = spec_add_fe51_limbs(a, b);
    assert forall|i: int| 0 <= i < 5 implies result.limbs[i] < (1u64 << ((n + 1) as u64)) by {
        // Each limb: a.limbs[i] < 2^n and b.limbs[i] < 2^n
        // So: a.limbs[i] + b.limbs[i] < 2^n + 2^n = 2^(n+1)
        assert(a.limbs[i] < (1u64 << n));
        assert(b.limbs[i] < (1u64 << n));
        assert((1u64 << n) + (1u64 << n) == (1u64 << ((n + 1) as u64))) by (bit_vector)
            requires
                n < 63,
        ;
    }
}

/// Lemma: if both inputs are n-bounded (n <= 62), then sum_of_limbs_bounded holds.
/// This is because: 2^n + 2^n = 2^(n+1) <= 2^63 < u64::MAX when n <= 62.
pub proof fn lemma_sum_of_limbs_bounded_from_fe51_bounded(
    a: &FieldElement51,
    b: &FieldElement51,
    n: u64,
)
    requires
        fe51_limbs_bounded(a, n),
        fe51_limbs_bounded(b, n),
        n <= 62,  // so 2^n + 2^n <= 2^63 < u64::MAX

    ensures
        sum_of_limbs_bounded(a, b, u64::MAX),
{
    assert forall|i: int| 0 <= i < 5 implies a.limbs[i] + b.limbs[i] < u64::MAX by {
        assert(a.limbs[i] < (1u64 << n));
        assert(b.limbs[i] < (1u64 << n));
        // 2^n + 2^n = 2^(n+1) < u64::MAX when n <= 62
        assert((1u64 << n) + (1u64 << n) < u64::MAX) by (bit_vector)
            requires
                n <= 62,
        ;
    }
}

} // verus!
