#![allow(unused)]
use super::common_lemmas::pow_lemmas::*;
use super::scalar_lemmas::*;
use crate::backend::serial::u64::constants;
use crate::specs::scalar52_specs::*;
use crate::specs::scalar_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Proves that the precomputed RR constant equals R² mod L
///
/// In Montgomery arithmetic, RR is precomputed as R² mod L where:
/// - R = montgomery_radix() = 2^260
/// - L = group_order() (the curve order)
///
/// This lemma verifies the precomputed constant is correct by showing:
///   scalar52_to_nat(RR.limbs) % L == (R * R) % L
pub(crate) proof fn lemma_rr_equals_radix_squared()
    ensures
        scalar52_to_nat(&constants::RR) % group_order() == (montgomery_radix() * montgomery_radix())
            % group_order(),
{
    // Enable conversion between scalar52_to_nat and five_limbs_to_nat_aux representations
    lemma_five_limbs_equals_to_nat(&constants::RR.limbs);

    // Establish pow2 facts needed for montgomery_radix() == pow2(260)
    // lemma_pow2_adds(a, b) proves: pow2(a + b) == pow2(a) * pow2(b)
    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_adds(52, 52);
    lemma_pow2_adds(104, 52);
    lemma_pow2_adds(156, 52);
    lemma_pow2_adds(208, 44);
    lemma_pow2_adds(208, 52);

    // Get the concrete value stored in the RR constant
    let rr_stored: nat = five_limbs_to_nat_aux(constants::RR.limbs);

    // Key insight: The stored RR value is already reduced (rr_stored < L),
    // so taking mod L is the identity: rr_stored % L == rr_stored
    // This is NOT the conclusion - it's an intermediate fact used in the proof chain.
    lemma_small_mod(rr_stored, group_order());

    // The proof establishes this chain of equalities:
    //   scalar52_to_nat(RR.limbs) % L
    //   == rr_stored % L        (by lemma_five_limbs_equals_to_nat)
    //   == rr_stored            (by lemma_small_mod, since rr_stored < L)
    //   == (R * R) % L          (by direct computation below)
    //
    // Therefore: scalar52_to_nat(RR.limbs) % L == (R * R) % L  ✓

    // Verify by direct computation that (R * R) % L equals the stored value
    // R = 2^260 = 1852673427797059126777135760139006525652319754650249024631321344126610074238976
    // L = group_order() = 7237005577332262213973186563042994240857116359379907606001950938285454250989
    assert((1852673427797059126777135760139006525652319754650249024631321344126610074238976_nat
        * 1852673427797059126777135760139006525652319754650249024631321344126610074238976_nat)
        % 7237005577332262213973186563042994240857116359379907606001950938285454250989_nat
        == rr_stored);
}

} // verus!
