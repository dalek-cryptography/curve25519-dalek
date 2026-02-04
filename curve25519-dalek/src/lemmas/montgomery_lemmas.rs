#![allow(unused)]
use super::common_lemmas::pow_lemmas::*;
use super::scalar_lemmas::*;
use crate::backend::serial::u64::constants;
use crate::specs::scalar52_specs::*;
use crate::specs::scalar_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::specs::core_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::montgomery_specs::*;

use crate::montgomery::ProjectivePoint;
use crate::MontgomeryPoint;

verus! {

/// Swapping the two ladder state points flips the `bit` parameter.
pub proof fn lemma_ladder_invariant_swap(
    x0: ProjectivePoint,
    x1: ProjectivePoint,
    P: MontgomeryAffine,
    k: nat,
    bit: bool,
)
    requires
        montgomery_ladder_invariant(x0, x1, P, k, bit),
    ensures
        montgomery_ladder_invariant(x1, x0, P, k, !bit),
{
    reveal(montgomery_ladder_invariant);
    if bit {
        // bit = true: x0=[k+1]P and x1=[k]P. After swapping, !bit=false expects x1=[k]P and x0=[k+1]P.
        assert(projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k + 1)));
        assert(projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k)));
        assert(projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k)));
        assert(projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k + 1)));
        assert(montgomery_ladder_invariant(x1, x0, P, k, false));
    } else {
        // bit = false: x0=[k]P and x1=[k+1]P. After swapping, !bit=true expects x1=[k+1]P and x0=[k]P.
        assert(projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k)));
        assert(projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k + 1)));
        assert(projective_represents_montgomery_or_infinity(x1, montgomery_scalar_mul(P, k + 1)));
        assert(projective_represents_montgomery_or_infinity(x0, montgomery_scalar_mul(P, k)));
        assert(montgomery_ladder_invariant(x1, x0, P, k, true));
    }
}

pub proof fn lemma_zero_limbs_is_zero(point: MontgomeryPoint)
    requires
        forall|i: int| 0 <= i < 32 ==> #[trigger] point.0[i] == 0u8,
    ensures
        spec_montgomery(point) == 0,
{
    // spec_montgomery(point) ==
    // spec_field_element_from_bytes(point.0) ==
    // (bytes32_to_nat(point.0) % pow2(255)) % p() ==
    // \sum_{i = 0} ^ 31 (bytes[i] as nat) * pow2(i * 8)
    assert(bytes32_to_nat(&point.0) == 0) by {
        assert forall|i: nat| 0 <= i < 32 implies point.0[i as int] * pow2(i * 8) == 0 by {
            /// trigger requirement:
            assert(point.0[i as int] == 0u8);
            assert(0u8 * pow2(i * 8) == 0) by {
                lemma_mul_basics_1(pow2(i * 8) as int);
            }
        }
    }
    assert((0nat % pow2(255)) % p() == 0) by {
        assert(0 < p() < pow2(255)) by {
            pow255_gt_19();
        }
        lemma_small_mod(0, p());
        lemma_small_mod(0, pow2(255));
    }
}

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
