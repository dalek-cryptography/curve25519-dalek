#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::scalar::Scalar52;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Convert a sequence of limbs to nat using 52-bit radix (Horner form).
/// This is the base recursive function for Scalar52 limb interpretation.
/// Computes: limbs[0] + limbs[1]*2^52 + limbs[2]*2^104 + ...
pub open spec fn seq_to_nat_52(limbs: Seq<nat>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        0
    } else {
        limbs[0] + seq_to_nat_52(limbs.subrange(1, limbs.len() as int)) * pow2(52)
    }
}

pub open spec fn slice128_to_nat(limbs: &[u128]) -> nat {
    seq_to_nat_52(limbs@.map(|i, x| x as nat))
}

pub open spec fn seq_u64_to_nat(limbs: Seq<u64>) -> nat {
    seq_to_nat_52(limbs.map(|i, x| x as nat))
}

/// Convert a slice of u64 limbs to nat using 52-bit radix.
/// This is for low-level lemmas that work with raw arrays.
pub open spec fn limbs52_to_nat(limbs: &[u64]) -> nat {
    seq_to_nat_52(limbs@.map(|i, x| x as nat))
}

/// Convert a Scalar52 to its natural number representation.
/// This is the primary spec function for Scalar52 interpretation.
pub open spec fn scalar52_to_nat(s: &Scalar52) -> nat {
    limbs52_to_nat(&s.limbs)
}

#[verusfmt::skip]
pub open spec fn nine_limbs_to_nat_aux(limbs: &[u128; 9]) -> nat {
    (limbs[0] as nat) +
    (limbs[1] as nat) * pow2( 52) +
    (limbs[2] as nat) * pow2(104) +
    (limbs[3] as nat) * pow2(156) +
    (limbs[4] as nat) * pow2(208) +
    (limbs[5] as nat) * pow2(260) +
    (limbs[6] as nat) * pow2(312) +
    (limbs[7] as nat) * pow2(364) +
    (limbs[8] as nat) * pow2(416)
}

#[verusfmt::skip]
pub open spec fn five_limbs_to_nat_aux(limbs: [u64; 5]) -> nat {
                (limbs[0] as nat) +
    pow2( 52) * (limbs[1] as nat) +
    pow2(104) * (limbs[2] as nat) +
    pow2(156) * (limbs[3] as nat) +
    pow2(208) * (limbs[4] as nat)
}

/// Converts 5 u64 limbs to a single nat value in radix-2^52.
///
/// Same as `five_limbs_to_nat_aux` but takes individual arguments instead of an array,
/// and uses `limb * pow2(k)` ordering (vs `pow2(k) * limb` in five_limbs_to_nat_aux).
///
/// Relation: `five_u64_limbs_to_nat(a[0], a[1], a[2], a[3], a[4]) == five_limbs_to_nat_aux(a)`
/// (the two orderings are equivalent by commutativity of multiplication)
#[verusfmt::skip]
pub open spec fn five_u64_limbs_to_nat(n0: u64, n1: u64, n2: u64, n3: u64, n4: u64) -> nat {
    (n0 as nat) +
    (n1 as nat) * pow2( 52) +
    (n2 as nat) * pow2(104) +
    (n3 as nat) * pow2(156) +
    (n4 as nat) * pow2(208)
}

// bytes32_to_nat, bytes_seq_to_nat, and bytes_to_nat_suffix (all generic)
// are now in core_specs.rs. They are imported via `use super::core_specs::*`
// Group order: the value of L as a natural number
pub open spec fn group_order() -> nat {
    pow2(252) + 27742317777372353535851937790883648493nat
}

// Montgomery radix R = 2^260
pub open spec fn montgomery_radix() -> nat {
    pow2(260)
}

// Montgomery radix inverse under L
pub open spec fn inv_montgomery_radix() -> nat {
    0x8e84371e098e4fc4_u64 as nat + pow2(64) * 0xfb2697cda3adacf5_u64 as nat + pow2(128)
        * 0x3614e75438ffa36b_u64 as nat + pow2(192) * 0xc9db6c6f26fe918_u64 as nat
}

// Check that all limbs of a Scalar52 are properly bounded (< 2^52)
pub open spec fn limbs_bounded(s: &Scalar52) -> bool {
    forall|i: int| 0 <= i < 5 ==> s.limbs[i] < (1u64 << 52)
}

/// Relaxed bound for sub's first argument: limbs 0-3 bounded, limb 4 can exceed 2^52 by up to b[4].
///
/// This is needed for montgomery_reduce where the intermediate result has r4 > 2^52.
/// The sub algorithm still works correctly because:
///   - For limbs 0-3: standard bounded subtraction
///   - For limb 4: a[4] - b[4] < 2^52, so masking doesn't lose bits
///
pub open spec fn limbs_bounded_for_sub(a: &Scalar52, b: &Scalar52) -> bool {
    &&& forall|i: int| 0 <= i < 4 ==> a.limbs[i] < (1u64 << 52)
    &&& a.limbs[4] < (1u64 << 52) + b.limbs[4]
}

pub open spec fn limb_prod_bounded_u128(limbs1: [u64; 5], limbs2: [u64; 5], k: nat) -> bool {
    forall|i: int, j: int| 0 <= i < 5 && 0 <= j < 5 ==> (limbs1[i] * limbs2[j]) * k <= u128::MAX
}

/// Checks if a Scalar52 is in canonical form:
/// - All limbs are properly bounded (< 2^52)
/// - The value is reduced modulo group order (< L)
///
/// This is the Scalar52 equivalent of is_canonical_scalar for Scalar.
pub open spec fn is_canonical_scalar52(s: &Scalar52) -> bool {
    limbs_bounded(s) && scalar52_to_nat(s) < group_order()
}

pub open spec fn spec_mul_internal(a: &Scalar52, b: &Scalar52) -> [u128; 9]
    recommends
        limbs_bounded(a),
        limbs_bounded(b),
{
    [
        ((a.limbs[0] as u128) * (b.limbs[0] as u128)) as u128,
        ((a.limbs[0] as u128) * (b.limbs[1] as u128) + (a.limbs[1] as u128) * (
        b.limbs[0] as u128)) as u128,
        ((a.limbs[0] as u128) * (b.limbs[2] as u128) + (a.limbs[1] as u128) * (b.limbs[1] as u128)
            + (a.limbs[2] as u128) * (b.limbs[0] as u128)) as u128,
        ((a.limbs[0] as u128) * (b.limbs[3] as u128) + (a.limbs[1] as u128) * (b.limbs[2] as u128)
            + (a.limbs[2] as u128) * (b.limbs[1] as u128) + (a.limbs[3] as u128) * (
        b.limbs[0] as u128)) as u128,
        ((a.limbs[0] as u128) * (b.limbs[4] as u128) + (a.limbs[1] as u128) * (b.limbs[3] as u128)
            + (a.limbs[2] as u128) * (b.limbs[2] as u128) + (a.limbs[3] as u128) * (
        b.limbs[1] as u128) + (a.limbs[4] as u128) * (b.limbs[0] as u128)) as u128,
        ((a.limbs[1] as u128) * (b.limbs[4] as u128) + (a.limbs[2] as u128) * (b.limbs[3] as u128)
            + (a.limbs[3] as u128) * (b.limbs[2] as u128) + (a.limbs[4] as u128) * (
        b.limbs[1] as u128)) as u128,
        ((a.limbs[2] as u128) * (b.limbs[4] as u128) + (a.limbs[3] as u128) * (b.limbs[3] as u128)
            + (a.limbs[4] as u128) * (b.limbs[2] as u128)) as u128,
        ((a.limbs[3] as u128) * (b.limbs[4] as u128) + (a.limbs[4] as u128) * (
        b.limbs[3] as u128)) as u128,
        ((a.limbs[4] as u128) * (b.limbs[4] as u128)) as u128,
    ]
}

} // verus!
