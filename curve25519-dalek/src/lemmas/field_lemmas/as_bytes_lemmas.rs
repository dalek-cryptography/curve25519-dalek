#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::compute_q_lemmas::*;
use super::limbs_to_bytes_lemmas::*;
use super::reduce_lemmas::*;
use super::to_bytes_reduction_lemmas::*;
use super::u8_32_as_nat_injectivity_lemmas::*;

use crate::lemmas::common_lemmas::pow_lemmas::*;

use super::super::common_lemmas::bit_lemmas::*;
use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mask_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;

use crate::backend::serial::u64::field::FieldElement51;
use crate::core_assumes::*;
use crate::specs::core_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;

verus! {

pub proof fn lemma_as_bytes_boundaries1(raw_limbs: [u64; 5])
    ensures
        spec_reduce(raw_limbs)[0] + 19 < u64::MAX,
        spec_reduce(raw_limbs)[1] + 2 < u64::MAX,
        spec_reduce(raw_limbs)[2] + 2 < u64::MAX,
        spec_reduce(raw_limbs)[3] + 2 < u64::MAX,
        spec_reduce(raw_limbs)[4] + 2 < u64::MAX,
        forall|i: int| 0 <= i <= 4 ==> compute_q_arr(spec_reduce(raw_limbs))[i] as u64 <= 2,
        (1u64 << 52) + 19 <= u64::MAX,
        ((1u64 << 52) + 19) as u64 >> 51 == 2,
        ((1u64 << 52) + 2) as u64 >> 51 == 2,
{
    proof_reduce(raw_limbs);

    let limbs = spec_reduce(raw_limbs);

    assert((1u64 << 52) + 19 <= u64::MAX) by (compute);
    assert(((1u64 << 52) + 19) as u64 >> 51 == 2) by (compute);
    assert(((1u64 << 52) + 2) as u64 >> 51 == 2) by (compute);

    let q_arr = compute_q_arr(limbs);
    let q0 = q_arr[0];
    let q1 = q_arr[1];
    let q2 = q_arr[2];
    let q3 = q_arr[3];
    let q4 = q_arr[4];

    assert(q0 <= 2) by {
        lemma_u64_shr_le((limbs[0] + 19) as u64, ((1u64 << 52) + 19) as u64, 51);
    }

    assert(q1 <= 2) by {
        lemma_u64_shr_le((limbs[1] + q0) as u64, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(q2 <= 2) by {
        lemma_u64_shr_le((limbs[2] + q1) as u64, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(q3 <= 2) by {
        lemma_u64_shr_le((limbs[3] + q2) as u64, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(q4 <= 2) by {
        lemma_u64_shr_le((limbs[4] + q3) as u64, ((1u64 << 52) + 2) as u64, 51);
    }
}

pub proof fn lemma_as_bytes_boundaries2(raw_limbs: [u64; 5])
    ensures
        mask51 == (1u64 << 51) - 1,
        // no `forall` for pattern match reasons
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[0]
            >> 51 <= 2,
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[1]
            >> 51 <= 2,
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[2]
            >> 51 <= 2,
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[3]
            >> 51 <= 2,
        compute_unmasked_limbs(spec_reduce(raw_limbs), compute_q_spec(spec_reduce(raw_limbs)))[4]
            >> 51 <= 2,
{
    lemma_as_bytes_boundaries1(raw_limbs);
    let limbs = spec_reduce(raw_limbs);
    let q = compute_q_spec(limbs);

    proof_reduce(raw_limbs);
    lemma_reduce_bound_2p(raw_limbs);

    assert(mask51 == (1u64 << 51) - 1) by (compute);

    assert(q == 0 || q == 1) by {
        lemma_compute_q(limbs, q);
    }

    assert(limbs[0] < 1u64 << 52);

    let l = compute_unmasked_limbs(limbs, q);
    let l0 = l[0];
    let l1 = l[1];
    let l2 = l[2];
    let l3 = l[3];
    let l4 = l[4];

    assert(l0 >> 51 <= 2) by {
        lemma_u64_shr_le(l0, ((1u64 << 52) + 19) as u64, 51);
    }

    assert(l1 >> 51 <= 2) by {
        lemma_u64_shr_le(l1, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(l2 >> 51 <= 2) by {
        lemma_u64_shr_le(l2, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(l3 >> 51 <= 2) by {
        lemma_u64_shr_le(l3, ((1u64 << 52) + 2) as u64, 51);
    }

    assert(l4 >> 51 <= 2) by {
        lemma_u64_shr_le(l4, ((1u64 << 52) + 2) as u64, 51);
    }
}

/// Lemma: as_bytes produces the same result as spec_fe51_to_bytes when converted to sequence
///
/// This is the key lemma for eliminating the assume in ct_eq.
/// It states that for any byte array that is produced by as_bytes() (i.e., satisfies
/// the as_bytes postcondition), when converted to a sequence, it equals spec_fe51_to_bytes().
///
/// The lemma relates:
/// - bytes: a byte array satisfying as_bytes postcondition (u8_32_as_nat(&bytes) == u64_5_as_nat(fe.limbs) % p())
/// - seq_from32(&bytes): the sequence representation of those bytes
/// - spec_fe51_to_bytes(fe): the spec-level byte sequence
///
/// Proof strategy:
/// - Both as_bytes() and spec_fe51_to_bytes() produce canonical representations
/// - Both preserve the value modulo p (u64_5_as_nat(fe.limbs) % p())
/// - The canonical representation modulo p is unique
/// - Therefore, they produce the same byte sequence
pub proof fn lemma_as_bytes_equals_spec_fe51_to_bytes(fe: &FieldElement51, bytes: &[u8; 32])
    requires
        u8_32_as_nat(bytes) == u64_5_as_nat(fe.limbs) % p(),
    ensures
        seq_from32(bytes) == spec_fe51_to_bytes(fe),
{
    // Step 1: Derive that bytes is canonical (< p)
    // This follows from x % p < p for any x
    assert(u8_32_as_nat(bytes) < p()) by {
        pow255_gt_19();
        lemma_mod_is_mod_recursive(u64_5_as_nat(fe.limbs) as int, p() as int);
    }

    // Step 2: Prove element-wise equality between spec and bytes
    lemma_spec_fe51_to_bytes_matches_array(fe, bytes);

    // Step 3: Conclude sequence equality
    assert(spec_fe51_to_bytes(fe).len() == 32);
    assert(seq_from32(bytes).len() == 32);

    assert forall|i: int| 0 <= i < 32 implies seq_from32(bytes)[i] == spec_fe51_to_bytes(fe)[i] by {
        assert(seq_from32(bytes)[i] == bytes[i]);
        assert(spec_fe51_to_bytes(fe)[i] == bytes[i]);
    }

    assert(seq_from32(bytes) =~= spec_fe51_to_bytes(fe));
}

/// Lemma: spec_fe51_to_bytes produces the same bytes as as_bytes, element by element
proof fn lemma_spec_fe51_to_bytes_matches_array(fe: &FieldElement51, bytes: &[u8; 32])
    requires
        u8_32_as_nat(bytes) == u64_5_as_nat(fe.limbs) % p(),
    ensures
        forall|i: int| 0 <= i < 32 ==> spec_fe51_to_bytes(fe)[i] == bytes[i],
{
    // Strategy: Both as_bytes() and spec_fe51_to_bytes() use the identical algorithm.
    // We'll compute the canonical limbs and show that the byte packing formulas
    // in spec_fe51_to_bytes (which are explicit in the seq![...]) match what as_bytes produces.
    // Step 1: Compute the canonical limbs (same as in spec_fe51_to_bytes)
    proof_reduce(fe.limbs);  // Ensures limbs are bounded by 2^52 and value is preserved mod p()
    let limbs = spec_reduce(fe.limbs);

    // Step 2: Prove preconditions for lemma_to_bytes_reduction
    lemma_reduce_bound_2p(fe.limbs);  // Ensures u64_5_as_nat(limbs) < 2 * p()

    // Compute q using compute_q_spec (matches spec_fe51_to_bytes)
    let q = compute_q_spec(limbs);
    lemma_compute_q(limbs, q);  // Establishes: q == 0 || q == 1, and u64_5_as_nat(limbs) >= p() <==> q == 1

    // Step 3: Apply canonical reduction using reduce_with_q_spec
    let canonical_limbs = reduce_with_q_spec(limbs, q);

    // Step 4: Extract canonical limb values
    let limbs0_canon = canonical_limbs[0];
    let limbs1_canon = canonical_limbs[1];
    let limbs2_canon = canonical_limbs[2];
    let limbs3_canon = canonical_limbs[3];
    let limbs4_canon = canonical_limbs[4];

    // Now assert that each byte formula in spec_fe51_to_bytes matches
    // The spec_fe51_to_bytes function defines its output as seq![...] with these exact formulas.
    // By the definition of seq![...], spec_fe51_to_bytes(fe)[i] equals the i-th element.

    assert(spec_fe51_to_bytes(fe)[0] == limbs0_canon as u8);
    assert(spec_fe51_to_bytes(fe)[1] == (limbs0_canon >> 8) as u8);
    assert(spec_fe51_to_bytes(fe)[2] == (limbs0_canon >> 16) as u8);
    assert(spec_fe51_to_bytes(fe)[3] == (limbs0_canon >> 24) as u8);
    assert(spec_fe51_to_bytes(fe)[4] == (limbs0_canon >> 32) as u8);
    assert(spec_fe51_to_bytes(fe)[5] == (limbs0_canon >> 40) as u8);
    assert(spec_fe51_to_bytes(fe)[6] == ((limbs0_canon >> 48) | (limbs1_canon << 3)) as u8);
    assert(spec_fe51_to_bytes(fe)[7] == (limbs1_canon >> 5) as u8);
    assert(spec_fe51_to_bytes(fe)[8] == (limbs1_canon >> 13) as u8);
    assert(spec_fe51_to_bytes(fe)[9] == (limbs1_canon >> 21) as u8);
    assert(spec_fe51_to_bytes(fe)[10] == (limbs1_canon >> 29) as u8);
    assert(spec_fe51_to_bytes(fe)[11] == (limbs1_canon >> 37) as u8);
    assert(spec_fe51_to_bytes(fe)[12] == ((limbs1_canon >> 45) | (limbs2_canon << 6)) as u8);
    assert(spec_fe51_to_bytes(fe)[13] == (limbs2_canon >> 2) as u8);
    assert(spec_fe51_to_bytes(fe)[14] == (limbs2_canon >> 10) as u8);
    assert(spec_fe51_to_bytes(fe)[15] == (limbs2_canon >> 18) as u8);
    assert(spec_fe51_to_bytes(fe)[16] == (limbs2_canon >> 26) as u8);
    assert(spec_fe51_to_bytes(fe)[17] == (limbs2_canon >> 34) as u8);
    assert(spec_fe51_to_bytes(fe)[18] == (limbs2_canon >> 42) as u8);
    assert(spec_fe51_to_bytes(fe)[19] == ((limbs2_canon >> 50) | (limbs3_canon << 1)) as u8);
    assert(spec_fe51_to_bytes(fe)[20] == (limbs3_canon >> 7) as u8);
    assert(spec_fe51_to_bytes(fe)[21] == (limbs3_canon >> 15) as u8);
    assert(spec_fe51_to_bytes(fe)[22] == (limbs3_canon >> 23) as u8);
    assert(spec_fe51_to_bytes(fe)[23] == (limbs3_canon >> 31) as u8);
    assert(spec_fe51_to_bytes(fe)[24] == (limbs3_canon >> 39) as u8);
    assert(spec_fe51_to_bytes(fe)[25] == ((limbs3_canon >> 47) | (limbs4_canon << 4)) as u8);
    assert(spec_fe51_to_bytes(fe)[26] == (limbs4_canon >> 4) as u8);
    assert(spec_fe51_to_bytes(fe)[27] == (limbs4_canon >> 12) as u8);
    assert(spec_fe51_to_bytes(fe)[28] == (limbs4_canon >> 20) as u8);
    assert(spec_fe51_to_bytes(fe)[29] == (limbs4_canon >> 28) as u8);
    assert(spec_fe51_to_bytes(fe)[30] == (limbs4_canon >> 36) as u8);
    assert(spec_fe51_to_bytes(fe)[31] == (limbs4_canon >> 44) as u8);

    // Step 5: Now show that bytes[i] equals each canonical byte formula
    //
    // Key insight: Both as_bytes() and spec_fe51_to_bytes() implement the SAME algorithm.
    // Since they start with the same fe.limbs and apply identical operations, they must
    // produce the same canonical limbs and therefore the same packed bytes.
    //
    // We know:
    // - u8_32_as_nat(bytes) == u64_5_as_nat(fe.limbs) % p() (from requires)
    // - The canonical limbs [limbs0_canon, ...] represent u64_5_as_nat(fe.limbs) % p()
    // - Both are < p() (canonical form)
    // - The byte packing formulas are deterministic
    //
    // Since the canonical representation is unique, and both representations
    // equal u64_5_as_nat(fe.limbs) % p(), we have bytes[i] == (packed canonical byte)[i]

    // The canonical limbs are already bounded by 2^51 (from reduce_with_q_spec)
    // This is guaranteed by lemma_to_bytes_reduction's postcondition

    // Create an array matching the spec_fe51_to_bytes byte packing
    let spec_bytes: [u8; 32] = [
        limbs0_canon as u8,
        (limbs0_canon >> 8) as u8,
        (limbs0_canon >> 16) as u8,
        (limbs0_canon >> 24) as u8,
        (limbs0_canon >> 32) as u8,
        (limbs0_canon >> 40) as u8,
        ((limbs0_canon >> 48) | (limbs1_canon << 3)) as u8,
        (limbs1_canon >> 5) as u8,
        (limbs1_canon >> 13) as u8,
        (limbs1_canon >> 21) as u8,
        (limbs1_canon >> 29) as u8,
        (limbs1_canon >> 37) as u8,
        ((limbs1_canon >> 45) | (limbs2_canon << 6)) as u8,
        (limbs2_canon >> 2) as u8,
        (limbs2_canon >> 10) as u8,
        (limbs2_canon >> 18) as u8,
        (limbs2_canon >> 26) as u8,
        (limbs2_canon >> 34) as u8,
        (limbs2_canon >> 42) as u8,
        ((limbs2_canon >> 50) | (limbs3_canon << 1)) as u8,
        (limbs3_canon >> 7) as u8,
        (limbs3_canon >> 15) as u8,
        (limbs3_canon >> 23) as u8,
        (limbs3_canon >> 31) as u8,
        (limbs3_canon >> 39) as u8,
        ((limbs3_canon >> 47) | (limbs4_canon << 4)) as u8,
        (limbs4_canon >> 4) as u8,
        (limbs4_canon >> 12) as u8,
        (limbs4_canon >> 20) as u8,
        (limbs4_canon >> 28) as u8,
        (limbs4_canon >> 36) as u8,
        (limbs4_canon >> 44) as u8,
    ];

    // Now we need to show: spec_bytes == bytes
    // This follows from uniqueness of canonical representation:
    // Both represent u64_5_as_nat(fe.limbs) % p(), so they must be equal

    // First, show that spec_bytes matches the canonical limbs packing
    assert(bytes_match_limbs_packing(canonical_limbs, spec_bytes));

    // First call lemma_to_bytes_reduction to establish canonical_limbs properties
    // The preconditions are already established:
    // - limbs[i] < 2^52 from proof_reduce
    // - q == 0 || q == 1 from lemma_compute_q
    // - u64_5_as_nat(limbs) >= p() <==> q == 1 from lemma_compute_q
    // - u64_5_as_nat(limbs) < 2*p() from lemma_reduce_bound_2p
    // - canonical_limbs == reduce_with_q_spec(limbs, q) by construction
    lemma_to_bytes_reduction(limbs, canonical_limbs, q);
    // Now we know: canonical_limbs[i] < 2^51 and u64_5_as_nat(canonical_limbs) == u64_5_as_nat(limbs) % p()

    // Use lemma_limbs_to_bytes to show u8_32_as_nat(spec_bytes) == u64_5_as_nat(canonical_limbs)
    lemma_limbs_to_bytes(canonical_limbs, spec_bytes);
    assert(u8_32_as_nat(&spec_bytes) == u64_5_as_nat(canonical_limbs));

    // From proof_reduce (called earlier), we know:
    // u64_5_as_nat(spec_reduce(fe.limbs)) % p() == u64_5_as_nat(fe.limbs) % p()
    // Since limbs = spec_reduce(fe.limbs), we have:
    assert(u64_5_as_nat(limbs) % p() == u64_5_as_nat(fe.limbs) % p());

    // Therefore: u8_32_as_nat(spec_bytes) == u64_5_as_nat(fe.limbs) % p()
    assert(u8_32_as_nat(&spec_bytes) == u64_5_as_nat(fe.limbs) % p());

    // Both bytes and spec_bytes represent u64_5_as_nat(fe.limbs) % p()
    // By uniqueness of canonical representation, they must be equal
    assert(u8_32_as_nat(bytes) == u8_32_as_nat(&spec_bytes));

    // If two byte arrays have the same u8_32_as_nat value,
    // they must be equal element-wise (by injectivity of little-endian encoding)
    lemma_canonical_bytes_equal(bytes, &spec_bytes);
}

/// Lemma: Sequence equality implies array equality
pub proof fn lemma_seq_eq_implies_array_eq(bytes1: &[u8; 32], bytes2: &[u8; 32])
    requires
        seq_from32(bytes1) == seq_from32(bytes2),
    ensures
        *bytes1 == *bytes2,
{
    // If seq representations are equal, then they're equal element-wise
    // seq_from32 is defined as Seq::new(32, |i: int| b[i])
    // So if the sequences are equal, each element must be equal
    assert forall|i: int| 0 <= i < 32 implies bytes1[i] == bytes2[i] by {
        // From the definition of seq_from32, we have:
        // seq_from32(bytes1)[i] == bytes1[i]
        // seq_from32(bytes2)[i] == bytes2[i]
        // Since seq_from32(bytes1) == seq_from32(bytes2), we get:
        // bytes1[i] == bytes2[i]
        assert(seq_from32(bytes1)[i] == bytes1[i]);
        assert(seq_from32(bytes2)[i] == bytes2[i]);
        assert(seq_from32(bytes1)[i] == seq_from32(bytes2)[i]);
    }
    // Verus axiom: arrays are equal iff all elements are equal
    assert(*bytes1 == *bytes2);
}

/// Lemma: from_bytes(as_bytes(fe_orig)) preserves the field element value
///
/// This is the fundamental roundtrip property for field element serialization.
/// Encoding to bytes and decoding back yields the same math field element.
///
/// ## Parameters:
/// - `fe_orig`: the original field element
/// - `bytes`: output of `as_bytes(fe_orig)`
/// - `fe_decoded`: output of `from_bytes(bytes)`
///
/// ## Usage:
/// ```
/// let bytes = fe_orig.as_bytes();
/// let fe_decoded = FieldElement51::from_bytes(&bytes);
/// proof {
///     lemma_from_bytes_as_bytes_roundtrip(&fe_orig, &bytes, &fe_decoded);
///     // Now: spec_field_element(&fe_decoded) == spec_field_element(&fe_orig)
/// }
/// ```
///
/// ## Proof outline (let v = fe_as_nat(fe_orig)):
/// 1. as_bytes postcondition: bytes_as_nat(bytes) = v % p
/// 2. from_bytes postcondition: fe_as_nat(fe_decoded) = bytes_as_nat(bytes) % pow2(255)
/// 3. Since v % p < p < pow2(255), by lemma_small_mod: (v % p) % pow2(255) = v % p
/// 4. By lemma_mod_twice: spec_field_element(fe_decoded) = (v % p) % p = v % p = spec_field_element(fe_orig)
pub proof fn lemma_from_bytes_as_bytes_roundtrip(
    fe_orig: &FieldElement51,
    bytes: &[u8; 32],
    fe_decoded: &FieldElement51,
)
    requires
        as_bytes_post(fe_orig, bytes),  // bytes = as_bytes(fe_orig)
        from_bytes_post(bytes, fe_decoded),  // fe_decoded = from_bytes(bytes)

    ensures
        spec_field_element(fe_decoded) == spec_field_element(fe_orig),
{
    let v = fe_as_nat(fe_orig);

    assert(spec_field_element(fe_decoded) == spec_field_element(fe_orig)) by {
        assert(0 < p() < pow2(255)) by {
            pow255_gt_19();
        };
        // Subgoal 1: (v % p) % pow2(255) == v % p
        // The canonical value fits in 255 bits, so from_bytes preserves it
        assert((v % p()) % pow2(255) == v % p()) by {
            assert(v % p() < p()) by {
                lemma_mod_bound(v as int, p() as int);
            };
            lemma_small_mod((v % p()) as nat, pow2(255));
        };

        // Subgoal 2: (v % p) % p == v % p (mod idempotence)
        // Taking mod p again doesn't change the canonical value
        assert((v % p()) % p() == v % p()) by {
            lemma_mod_twice(v as int, p() as int);
        };
    };
}

/// Lemma: as_bytes(from_bytes(bytes_orig)) preserves the byte value (for canonical inputs)
///
/// This is the reverse roundtrip property for field element serialization.
/// It only holds when the input bytes represent a canonical value (< p).
///
/// ## Parameters:
/// - `bytes_orig`: the original bytes (must be canonical: bytes_as_nat < p)
/// - `fe`: output of `from_bytes(bytes_orig)`
/// - `bytes_decoded`: output of `as_bytes(fe)`
///
/// ## Usage:
/// ```
/// let fe = FieldElement51::from_bytes(&bytes_orig);
/// let bytes_decoded = fe.as_bytes();
/// proof {
///     lemma_as_bytes_from_bytes_roundtrip(&bytes_orig, &fe, &bytes_decoded);
///     // Now: bytes_as_nat(&bytes_decoded) == bytes_as_nat(&bytes_orig)
/// }
/// ```
///
/// ## Why canonical is required:
/// If bytes_orig encodes a value v where p <= v < 2^255, then:
/// - from_bytes preserves v (since v < 2^255)
/// - as_bytes reduces to v % p
/// So as_bytes(from_bytes(bytes)) would encode (v % p), not v.
///
/// ## Proof outline (let v = bytes_as_nat(bytes_orig)):
/// 1. Since v < p < pow2(255), by lemma_small_mod: v % pow2(255) = v
/// 2. So from_bytes gives: fe_as_nat(fe) = v
/// 3. Since v < p, by lemma_small_mod: v % p = v
/// 4. So as_bytes gives: bytes_as_nat(bytes_decoded) = v
pub proof fn lemma_as_bytes_from_bytes_roundtrip(
    bytes_orig: &[u8; 32],
    fe: &FieldElement51,
    bytes_decoded: &[u8; 32],
)
    requires
        bytes_as_nat(bytes_orig) < p(),  // bytes_orig is canonical
        from_bytes_post(bytes_orig, fe),  // fe = from_bytes(bytes_orig)
        as_bytes_post(fe, bytes_decoded),  // bytes_decoded = as_bytes(fe)

    ensures
        bytes_as_nat(bytes_decoded) == bytes_as_nat(bytes_orig),
{
    let v = bytes_as_nat(bytes_orig);

    assert(0 < p() < pow2(255)) by {
        pow255_gt_19();
    };
    assert(bytes_as_nat(bytes_decoded) == v) by {
        // Subgoal 1: v % pow2(255) == v
        // Since v < p < pow2(255), v fits in 255 bits
        assert(v % pow2(255) == v) by {
            lemma_small_mod(v, pow2(255));
        };

        // Subgoal 2: v % p == v
        // Since v < p (canonical), taking mod p doesn't change it
        assert(v % p() == v) by {
            lemma_small_mod(v, p());
        };
    };
}

} // verus!
