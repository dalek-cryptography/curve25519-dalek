#[allow(unused_imports)]
use super::scalar::Scalar52;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {
pub open spec fn seq_to_nat(limbs: Seq<nat>) -> nat
decreases limbs.len()
{
    if limbs.len() == 0 {
        0
    } else {
        limbs[0] + seq_to_nat(limbs.subrange(1, limbs.len() as int)) * pow2(52)
    }
}

pub open spec fn slice128_to_nat(limbs: &[u128]) -> nat
{
    seq_to_nat(limbs@.map(|i, x| x as nat))
}

pub open spec fn seq_u64_to_nat(limbs: Seq<u64>) -> nat
{
    seq_to_nat(limbs.map(|i, x| x as nat))
}

pub open spec fn to_nat(limbs: &[u64]) -> nat
{
    seq_to_nat(limbs@.map(|i, x| x as nat))
}

pub open spec fn nine_limbs_to_nat_aux(limbs: &[u128; 9]) -> nat {
    (limbs[0] as nat) +
    (limbs[1] as nat) * pow2(52) +
    (limbs[2] as nat) * pow2(104) +
    (limbs[3] as nat) * pow2(156) +
    (limbs[4] as nat) * pow2(208) +
    (limbs[5] as nat) * pow2(260) +
    (limbs[6] as nat) * pow2(312) +
    (limbs[7] as nat) * pow2(364) +
    (limbs[8] as nat) * pow2(416)
}

pub open spec fn five_limbs_to_nat_aux(limbs: [u64; 5]) -> nat {
    (limbs[0] as nat) +
    pow2(52) * (limbs[1] as nat) +
    pow2(104) * (limbs[2] as nat) +
    pow2(156) * (limbs[3] as nat) +
    pow2(208) * (limbs[4] as nat)
}


// Group order: the value of L as a natural number
pub open spec fn group_order() -> nat {
    pow2(252) + 27742317777372353535851937790883648493nat
}

// Montgomery radix R = 2^260
pub open spec fn montgomery_radix() -> nat {
    pow2(260)
}

// Check that all limbs of a Scalar52 are properly bounded (< 2^52)
pub open spec fn limbs_bounded(s: &Scalar52) -> bool {
    forall|i: int| 0 <= i < 5 ==> s.limbs[i] < (1u64 << 52)
}

} // verus!
