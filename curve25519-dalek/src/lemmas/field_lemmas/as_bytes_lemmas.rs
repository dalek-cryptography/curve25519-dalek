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
use crate::lemmas::common_lemmas::to_nat_lemmas::*;

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

/// Lemma: as_bytes produces the same result as spec_fe51_as_bytes when converted to sequence
///
/// This is the key lemma for eliminating the assume in ct_eq.
/// It states that for any byte array that is produced by as_bytes() (i.e., satisfies
/// the as_bytes postcondition), when converted to a sequence, it equals spec_fe51_as_bytes().
///
/// The lemma relates:
/// - bytes: a byte array satisfying as_bytes postcondition (u8_32_as_nat(&bytes) == u64_5_as_nat(fe.limbs) % p())
/// - seq_from32(&bytes): the sequence representation of those bytes
/// - spec_fe51_as_bytes(fe): the spec-level byte sequence
///
/// Proof strategy:
/// - Both as_bytes() and spec_fe51_as_bytes() produce canonical representations
/// - Both preserve the value modulo p (u64_5_as_nat(fe.limbs) % p())
/// - The canonical representation modulo p is unique
/// - Therefore, they produce the same byte sequence
pub proof fn lemma_as_bytes_equals_spec_fe51_to_bytes(fe: &FieldElement51, bytes: &[u8; 32])
    requires
        u8_32_as_nat(bytes) == u64_5_as_nat(fe.limbs) % p(),
    ensures
        seq_from32(bytes) == spec_fe51_as_bytes(fe),
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
    assert(spec_fe51_as_bytes(fe).len() == 32);
    assert(seq_from32(bytes).len() == 32);

    assert forall|i: int| 0 <= i < 32 implies seq_from32(bytes)[i] == spec_fe51_as_bytes(fe)[i] by {
        assert(seq_from32(bytes)[i] == bytes[i]);
        assert(spec_fe51_as_bytes(fe)[i] == bytes[i]);
    }

    assert(seq_from32(bytes) =~= spec_fe51_as_bytes(fe));
}

/// Lemma: spec_fe51_as_bytes produces the same bytes as as_bytes, element by element
proof fn lemma_spec_fe51_to_bytes_matches_array(fe: &FieldElement51, bytes: &[u8; 32])
    requires
        u8_32_as_nat(bytes) == u64_5_as_nat(fe.limbs) % p(),
    ensures
        forall|i: int| 0 <= i < 32 ==> spec_fe51_as_bytes(fe)[i] == bytes[i],
{
    // Strategy: Both as_bytes() and spec_fe51_as_bytes() use the identical algorithm.
    // We'll compute the canonical limbs and show that the byte packing formulas
    // in spec_fe51_as_bytes (which are explicit in the seq![...]) match what as_bytes produces.
    // Step 1: Compute the canonical limbs (same as in spec_fe51_as_bytes)
    proof_reduce(fe.limbs);  // Ensures limbs are bounded by 2^52 and value is preserved mod p()
    let limbs = spec_reduce(fe.limbs);

    // Step 2: Prove preconditions for lemma_to_bytes_reduction
    lemma_reduce_bound_2p(fe.limbs);  // Ensures u64_5_as_nat(limbs) < 2 * p()

    // Compute q using compute_q_spec (matches spec_fe51_as_bytes)
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

    // Now assert that each byte formula in spec_fe51_as_bytes matches
    // The spec_fe51_as_bytes function defines its output as seq![...] with these exact formulas.
    // By the definition of seq![...], spec_fe51_as_bytes(fe)[i] equals the i-th element.

    assert(spec_fe51_as_bytes(fe)[0] == limbs0_canon as u8);
    assert(spec_fe51_as_bytes(fe)[1] == (limbs0_canon >> 8) as u8);
    assert(spec_fe51_as_bytes(fe)[2] == (limbs0_canon >> 16) as u8);
    assert(spec_fe51_as_bytes(fe)[3] == (limbs0_canon >> 24) as u8);
    assert(spec_fe51_as_bytes(fe)[4] == (limbs0_canon >> 32) as u8);
    assert(spec_fe51_as_bytes(fe)[5] == (limbs0_canon >> 40) as u8);
    assert(spec_fe51_as_bytes(fe)[6] == ((limbs0_canon >> 48) | (limbs1_canon << 3)) as u8);
    assert(spec_fe51_as_bytes(fe)[7] == (limbs1_canon >> 5) as u8);
    assert(spec_fe51_as_bytes(fe)[8] == (limbs1_canon >> 13) as u8);
    assert(spec_fe51_as_bytes(fe)[9] == (limbs1_canon >> 21) as u8);
    assert(spec_fe51_as_bytes(fe)[10] == (limbs1_canon >> 29) as u8);
    assert(spec_fe51_as_bytes(fe)[11] == (limbs1_canon >> 37) as u8);
    assert(spec_fe51_as_bytes(fe)[12] == ((limbs1_canon >> 45) | (limbs2_canon << 6)) as u8);
    assert(spec_fe51_as_bytes(fe)[13] == (limbs2_canon >> 2) as u8);
    assert(spec_fe51_as_bytes(fe)[14] == (limbs2_canon >> 10) as u8);
    assert(spec_fe51_as_bytes(fe)[15] == (limbs2_canon >> 18) as u8);
    assert(spec_fe51_as_bytes(fe)[16] == (limbs2_canon >> 26) as u8);
    assert(spec_fe51_as_bytes(fe)[17] == (limbs2_canon >> 34) as u8);
    assert(spec_fe51_as_bytes(fe)[18] == (limbs2_canon >> 42) as u8);
    assert(spec_fe51_as_bytes(fe)[19] == ((limbs2_canon >> 50) | (limbs3_canon << 1)) as u8);
    assert(spec_fe51_as_bytes(fe)[20] == (limbs3_canon >> 7) as u8);
    assert(spec_fe51_as_bytes(fe)[21] == (limbs3_canon >> 15) as u8);
    assert(spec_fe51_as_bytes(fe)[22] == (limbs3_canon >> 23) as u8);
    assert(spec_fe51_as_bytes(fe)[23] == (limbs3_canon >> 31) as u8);
    assert(spec_fe51_as_bytes(fe)[24] == (limbs3_canon >> 39) as u8);
    assert(spec_fe51_as_bytes(fe)[25] == ((limbs3_canon >> 47) | (limbs4_canon << 4)) as u8);
    assert(spec_fe51_as_bytes(fe)[26] == (limbs4_canon >> 4) as u8);
    assert(spec_fe51_as_bytes(fe)[27] == (limbs4_canon >> 12) as u8);
    assert(spec_fe51_as_bytes(fe)[28] == (limbs4_canon >> 20) as u8);
    assert(spec_fe51_as_bytes(fe)[29] == (limbs4_canon >> 28) as u8);
    assert(spec_fe51_as_bytes(fe)[30] == (limbs4_canon >> 36) as u8);
    assert(spec_fe51_as_bytes(fe)[31] == (limbs4_canon >> 44) as u8);

    // Step 5: Now show that bytes[i] equals each canonical byte formula
    //
    // Key insight: Both as_bytes() and spec_fe51_as_bytes() implement the SAME algorithm.
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

    // Create an array matching the spec_fe51_as_bytes byte packing
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
///     // Now: fe51_as_canonical_nat(&fe_decoded) == fe51_as_canonical_nat(&fe_orig)
/// }
/// ```
///
/// ## Proof outline (let v = fe51_as_nat(fe_orig)):
/// 1. as_bytes postcondition: u8_32_as_nat(bytes) = v % p
/// 2. from_bytes postcondition: fe51_as_nat(fe_decoded) = u8_32_as_nat(bytes) % pow2(255)
/// 3. Since v % p < p < pow2(255), by lemma_small_mod: (v % p) % pow2(255) = v % p
/// 4. By lemma_mod_twice: fe51_as_canonical_nat(fe_decoded) = (v % p) % p = v % p = fe51_as_canonical_nat(fe_orig)
pub proof fn lemma_from_bytes_as_bytes_roundtrip(
    fe_orig: &FieldElement51,
    bytes: &[u8; 32],
    fe_decoded: &FieldElement51,
)
    requires
        as_bytes_post(fe_orig, bytes),  // bytes = as_bytes(fe_orig)
        from_bytes_post(bytes, fe_decoded),  // fe_decoded = from_bytes(bytes)

    ensures
        fe51_as_canonical_nat(fe_decoded) == fe51_as_canonical_nat(fe_orig),
{
    let v = fe51_as_nat(fe_orig);

    assert(fe51_as_canonical_nat(fe_decoded) == fe51_as_canonical_nat(fe_orig)) by {
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
/// - `bytes_orig`: the original bytes (must be canonical: u8_32_as_nat < p)
/// - `fe`: output of `from_bytes(bytes_orig)`
/// - `bytes_decoded`: output of `as_bytes(fe)`
///
/// ## Usage:
/// ```
/// let fe = FieldElement51::from_bytes(&bytes_orig);
/// let bytes_decoded = fe.as_bytes();
/// proof {
///     lemma_as_bytes_from_bytes_roundtrip(&bytes_orig, &fe, &bytes_decoded);
///     // Now: u8_32_as_nat(&bytes_decoded) == u8_32_as_nat(&bytes_orig)
/// }
/// ```
///
/// ## Why canonical is required:
/// If bytes_orig encodes a value v where p <= v < 2^255, then:
/// - from_bytes preserves v (since v < 2^255)
/// - as_bytes reduces to v % p
/// So as_bytes(from_bytes(bytes)) would encode (v % p), not v.
///
/// ## Proof outline (let v = u8_32_as_nat(bytes_orig)):
/// 1. Since v < p < pow2(255), by lemma_small_mod: v % pow2(255) = v
/// 2. So from_bytes gives: fe51_as_nat(fe) = v
/// 3. Since v < p, by lemma_small_mod: v % p = v
/// 4. So as_bytes gives: u8_32_as_nat(bytes_decoded) = v
pub proof fn lemma_as_bytes_from_bytes_roundtrip(
    bytes_orig: &[u8; 32],
    fe: &FieldElement51,
    bytes_decoded: &[u8; 32],
)
    requires
        u8_32_as_nat(bytes_orig) < p(),  // bytes_orig is canonical
        from_bytes_post(bytes_orig, fe),  // fe = from_bytes(bytes_orig)
        as_bytes_post(fe, bytes_decoded),  // bytes_decoded = as_bytes(fe)

    ensures
        u8_32_as_nat(bytes_decoded) == u8_32_as_nat(bytes_orig),
{
    let v = u8_32_as_nat(bytes_orig);

    assert(0 < p() < pow2(255)) by {
        pow255_gt_19();
    };
    assert(u8_32_as_nat(bytes_decoded) == v) by {
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

/// Lemma: Equal canonical byte sequences imply equal field element values
///
/// If two field elements have the same canonical byte representation (via spec_fe51_as_bytes),
/// then they represent the same mathematical value in the field.
///
/// ## Mathematical reasoning:
/// - `spec_fe51_as_bytes(fe)` encodes `fe51_as_canonical_nat(fe)` as a canonical little-endian sequence
/// - Little-endian encoding is injective: different values produce different byte sequences
/// - Therefore: equal bytes => equal values
///
/// ## Usage in proofs:
/// ```
/// let result = fe1 == fe2;  // Uses PartialEq which compares spec_fe51_as_bytes
/// proof {
///     lemma_fe51_to_bytes_equal_implies_field_element_equal(&fe1, &fe2);
///     // Now: (spec_fe51_as_bytes(&fe1) == spec_fe51_as_bytes(&fe2)) ==> (fe51_as_canonical_nat(&fe1) == fe51_as_canonical_nat(&fe2))
/// }
/// ```
pub proof fn lemma_fe51_to_bytes_equal_implies_field_element_equal(
    fe1: &FieldElement51,
    fe2: &FieldElement51,
)
    ensures
        (spec_fe51_as_bytes(fe1) == spec_fe51_as_bytes(fe2)) ==> (fe51_as_canonical_nat(fe1)
            == fe51_as_canonical_nat(fe2)),
{
    if spec_fe51_as_bytes(fe1) == spec_fe51_as_bytes(fe2) {
        let bytes1 = seq_to_array_32(spec_fe51_as_bytes(fe1));
        let bytes2 = seq_to_array_32(spec_fe51_as_bytes(fe2));

        assert(u8_32_as_nat(&bytes1) == fe51_as_canonical_nat(fe1)) by {
            lemma_u8_32_as_nat_of_spec_fe51_to_bytes(fe1);
        };
        assert(u8_32_as_nat(&bytes2) == fe51_as_canonical_nat(fe2)) by {
            lemma_u8_32_as_nat_of_spec_fe51_to_bytes(fe2);
        };

        assert(u8_32_as_nat(&bytes1) == u8_32_as_nat(&bytes2));
        assert(fe51_as_canonical_nat(fe1) == fe51_as_canonical_nat(fe2));
    }
}

/// Lemma: Equal field element values imply equal canonical byte encodings
///
/// This is the converse of `lemma_fe51_to_bytes_equal_implies_field_element_equal`.
///
/// ## Mathematical reasoning:
/// - `spec_fe51_as_bytes(fe)` is a deterministic function of `fe51_as_canonical_nat(fe)`
/// - The canonical encoding produces a unique 32-byte representation for each value in [0, p)
/// - Therefore: equal values => equal bytes
///
/// ## Proof strategy:
/// 1. Convert both byte sequences to arrays: `bytes1`, `bytes2`
/// 2. Show `u8_32_as_nat(&bytes1) == u8_32_as_nat(&bytes2)` (both equal the shared field value)
/// 3. Use `lemma_canonical_bytes_equal`: equal nat values => equal byte arrays
/// 4. Convert back to sequences to conclude `spec_fe51_as_bytes(fe1) == spec_fe51_as_bytes(fe2)`
pub proof fn lemma_field_element_equal_implies_fe51_to_bytes_equal(
    fe1: &FieldElement51,
    fe2: &FieldElement51,
)
    ensures
        (fe51_as_canonical_nat(fe1) == fe51_as_canonical_nat(fe2)) ==> (spec_fe51_as_bytes(fe1)
            == spec_fe51_as_bytes(fe2)),
{
    if fe51_as_canonical_nat(fe1) == fe51_as_canonical_nat(fe2) {
        let bytes1 = seq_to_array_32(spec_fe51_as_bytes(fe1));
        let bytes2 = seq_to_array_32(spec_fe51_as_bytes(fe2));

        assert(u8_32_as_nat(&bytes1) == fe51_as_canonical_nat(fe1)) by {
            lemma_u8_32_as_nat_of_spec_fe51_to_bytes(fe1);
        };
        assert(u8_32_as_nat(&bytes2) == fe51_as_canonical_nat(fe2)) by {
            lemma_u8_32_as_nat_of_spec_fe51_to_bytes(fe2);
        };

        assert(u8_32_as_nat(&bytes1) == u8_32_as_nat(&bytes2));

        // Equal nat values => equal byte arrays (u8_32_as_nat is injective)
        assert(forall|i: int| 0 <= i < 32 ==> bytes1[i] == bytes2[i]) by {
            lemma_canonical_bytes_equal(&bytes1, &bytes2);
        };

        // From elementwise equality of arrays, conclude sequence equality.
        assert(seq_from32(&bytes1) == seq_from32(&bytes2)) by {
            assert forall|i: int| 0 <= i < 32 implies seq_from32(&bytes1)[i] == seq_from32(
                &bytes2,
            )[i] by {
                assert(seq_from32(&bytes1)[i] == bytes1[i]);
                assert(seq_from32(&bytes2)[i] == bytes2[i]);
                assert(bytes1[i] == bytes2[i]);
            }
        };

        // Roundtrip: spec_fe51_as_bytes(fe) == seq_from32(seq_to_array_32(spec_fe51_as_bytes(fe))).
        assert(spec_fe51_as_bytes(fe1) == seq_from32(&bytes1)) by {
            assert(spec_fe51_as_bytes(fe1).len() == 32);
            lemma_seq_to_array_32_roundtrip(spec_fe51_as_bytes(fe1));
        };
        assert(spec_fe51_as_bytes(fe2) == seq_from32(&bytes2)) by {
            assert(spec_fe51_as_bytes(fe2).len() == 32);
            lemma_seq_to_array_32_roundtrip(spec_fe51_as_bytes(fe2));
        };

        assert(spec_fe51_as_bytes(fe1) == spec_fe51_as_bytes(fe2));
    }
}

// ============================================================================
// Helper for the above two lemmas: connecting spec_fe51_as_bytes to fe51_as_canonical_nat
// ============================================================================
/// Core lemma: The canonical byte encoding of a field element decodes back to its value.
///
/// This establishes the fundamental property:
///   `u8_32_as_nat(spec_fe51_as_bytes(fe)) == fe51_as_canonical_nat(fe)`
///
///
/// ## Proof outline:
/// 1. Apply reduction lemmas to get canonical limbs from fe.limbs
/// 2. Build an explicit byte array `spec_bytes` from canonical limbs (using the same packing as spec_fe51_as_bytes)
/// 3. Use `lemma_limbs_to_bytes` to show `u8_32_as_nat(&spec_bytes) == u64_5_as_nat(canonical_limbs)`
/// 4. Use reduction lemmas to show `u64_5_as_nat(canonical_limbs) == fe51_as_canonical_nat(fe)`
/// 5. Show `seq_to_array_32(spec_fe51_as_bytes(fe)) == spec_bytes` by element-wise comparison
/// 6. Conclude `u8_32_as_nat(seq_to_array_32(spec_fe51_as_bytes(fe))) == fe51_as_canonical_nat(fe)`
pub proof fn lemma_u8_32_as_nat_of_spec_fe51_to_bytes(fe: &FieldElement51)
    ensures
        u8_32_as_nat(&seq_to_array_32(spec_fe51_as_bytes(fe))) == fe51_as_canonical_nat(fe),
{
    // -------------------------------------------------------------------------
    // STEP 1: Establish that spec_fe51_as_bytes produces 32 bytes
    // -------------------------------------------------------------------------
    assert(spec_fe51_as_bytes(fe).len() == 32);

    // -------------------------------------------------------------------------
    // STEP 2: Reduce limbs and establish bounds
    // -------------------------------------------------------------------------
    let limbs = spec_reduce(fe.limbs);

    // Establishes: u64_5_as_nat(limbs) % p() == u64_5_as_nat(fe.limbs) % p()
    //              AND limbs[i] < 2^52 for all i (needed for later lemmas)
    proof_reduce(fe.limbs);

    // Establishes: u64_5_as_nat(limbs) < 2 * p()
    lemma_reduce_bound_2p(fe.limbs);

    // -------------------------------------------------------------------------
    // STEP 3: Compute q (the quotient for final reduction to [0, p))
    // -------------------------------------------------------------------------
    let q = compute_q_spec(limbs);

    // Establishes: q ∈ {0, 1} and (q == 1 ⟺ u64_5_as_nat(limbs) >= p())
    lemma_compute_q(limbs, q);

    // -------------------------------------------------------------------------
    // STEP 4: Apply final reduction to get canonical limbs in [0, p)
    // -------------------------------------------------------------------------
    let canonical_limbs = reduce_with_q_spec(limbs, q);

    // Establishes: u64_5_as_nat(canonical_limbs) == u64_5_as_nat(limbs) % p()
    lemma_to_bytes_reduction(limbs, canonical_limbs, q);

    let limbs0_canon = canonical_limbs[0];
    let limbs1_canon = canonical_limbs[1];
    let limbs2_canon = canonical_limbs[2];
    let limbs3_canon = canonical_limbs[3];
    let limbs4_canon = canonical_limbs[4];

    // Build the array view of the canonical encoding.
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

    // -------------------------------------------------------------------------
    // STEP 5: Prove u8_32_as_nat(&spec_bytes) == fe51_as_canonical_nat(fe)
    // -------------------------------------------------------------------------

    // Precondition for lemma_limbs_to_bytes: bytes match the limb packing format
    assert(bytes_match_limbs_packing(canonical_limbs, spec_bytes));

    // Establishes: u8_32_as_nat(&spec_bytes) == u64_5_as_nat(canonical_limbs)
    lemma_limbs_to_bytes(canonical_limbs, spec_bytes);

    // Chain of equalities to reach fe51_as_canonical_nat(fe):
    //   u8_32_as_nat(&spec_bytes)
    //   == u64_5_as_nat(canonical_limbs)    [from lemma_limbs_to_bytes]
    //   == u64_5_as_nat(limbs) % p()        [from lemma_to_bytes_reduction]
    //   == u64_5_as_nat(fe.limbs) % p()     [from proof_reduce]
    //   == fe51_as_canonical_nat(fe)           [by definition]
    assert(u8_32_as_nat(&spec_bytes) == fe51_as_canonical_nat(fe));

    // -------------------------------------------------------------------------
    // STEP 6: Bridge between Seq<u8> and [u8; 32]
    // -------------------------------------------------------------------------
    // We need to show: u8_32_as_nat(seq_to_array_32(spec_fe51_as_bytes(fe))) == fe51_as_canonical_nat(fe)
    //
    // The challenge is that spec_fe51_as_bytes returns a Seq<u8> (via seq![...]),
    // but u8_32_as_nat takes a [u8; 32]. We must prove that converting the
    // sequence to an array preserves the byte values.
    //
    // Strategy:
    //   1. Let `bytes = seq_to_array_32(spec_fe51_as_bytes(fe))`
    //   2. Show `bytes[i] == spec_bytes[i]` for all i ∈ [0, 32)
    //   3. Conclude `bytes == spec_bytes`
    //   4. Use transitivity: u8_32_as_nat(&bytes) == u8_32_as_nat(&spec_bytes) == fe51_as_canonical_nat(fe)
    // -------------------------------------------------------------------------

    let bytes = seq_to_array_32(spec_fe51_as_bytes(fe));

    // For each index i, we need to show:
    //   bytes[i] == spec_fe51_as_bytes(fe)[i]  (by seq_to_array_32 definition)
    //            == spec_bytes[i]              (by spec_fe51_as_bytes definition)
    //
    // This requires Verus to unfold spec_fe51_as_bytes and see that its seq![...]
    // produces the same values as our spec_bytes array literal.

    // Byte 0: limbs0_canon as u8
    assert(bytes[0] == spec_bytes[0]);
    // Byte 1: (limbs0_canon >> 8) as u8
    assert(bytes[1] == spec_bytes[1]);
    // Byte 2: (limbs0_canon >> 16) as u8
    assert(bytes[2] == spec_bytes[2]);
    // Byte 3: (limbs0_canon >> 24) as u8
    assert(bytes[3] == spec_bytes[3]);
    // Byte 4: (limbs0_canon >> 32) as u8
    assert(bytes[4] == spec_bytes[4]);
    // Byte 5: (limbs0_canon >> 40) as u8
    assert(bytes[5] == spec_bytes[5]);
    // Byte 6: ((limbs0_canon >> 48) | (limbs1_canon << 3)) as u8  [boundary between limb0 and limb1]
    assert(bytes[6] == spec_bytes[6]);
    // Byte 7: (limbs1_canon >> 5) as u8
    assert(bytes[7] == spec_bytes[7]);
    // Byte 8: (limbs1_canon >> 13) as u8
    assert(bytes[8] == spec_bytes[8]);
    // Byte 9: (limbs1_canon >> 21) as u8
    assert(bytes[9] == spec_bytes[9]);
    // Byte 10: (limbs1_canon >> 29) as u8
    assert(bytes[10] == spec_bytes[10]);
    // Byte 11: (limbs1_canon >> 37) as u8
    assert(bytes[11] == spec_bytes[11]);
    // Byte 12: ((limbs1_canon >> 45) | (limbs2_canon << 6)) as u8  [boundary between limb1 and limb2]
    assert(bytes[12] == spec_bytes[12]);
    // Byte 13: (limbs2_canon >> 2) as u8
    assert(bytes[13] == spec_bytes[13]);
    // Byte 14: (limbs2_canon >> 10) as u8
    assert(bytes[14] == spec_bytes[14]);
    // Byte 15: (limbs2_canon >> 18) as u8
    assert(bytes[15] == spec_bytes[15]);
    // Byte 16: (limbs2_canon >> 26) as u8
    assert(bytes[16] == spec_bytes[16]);
    // Byte 17: (limbs2_canon >> 34) as u8
    assert(bytes[17] == spec_bytes[17]);
    // Byte 18: (limbs2_canon >> 42) as u8
    assert(bytes[18] == spec_bytes[18]);
    // Byte 19: ((limbs2_canon >> 50) | (limbs3_canon << 1)) as u8  [boundary between limb2 and limb3]
    assert(bytes[19] == spec_bytes[19]);
    // Byte 20: (limbs3_canon >> 7) as u8
    assert(bytes[20] == spec_bytes[20]);
    // Byte 21: (limbs3_canon >> 15) as u8
    assert(bytes[21] == spec_bytes[21]);
    // Byte 22: (limbs3_canon >> 23) as u8
    assert(bytes[22] == spec_bytes[22]);
    // Byte 23: (limbs3_canon >> 31) as u8
    assert(bytes[23] == spec_bytes[23]);
    // Byte 24: (limbs3_canon >> 39) as u8
    assert(bytes[24] == spec_bytes[24]);
    // Byte 25: ((limbs3_canon >> 47) | (limbs4_canon << 4)) as u8  [boundary between limb3 and limb4]
    assert(bytes[25] == spec_bytes[25]);
    // Byte 26: (limbs4_canon >> 4) as u8
    assert(bytes[26] == spec_bytes[26]);
    // Byte 27: (limbs4_canon >> 12) as u8
    assert(bytes[27] == spec_bytes[27]);
    // Byte 28: (limbs4_canon >> 20) as u8
    assert(bytes[28] == spec_bytes[28]);
    // Byte 29: (limbs4_canon >> 28) as u8
    assert(bytes[29] == spec_bytes[29]);
    // Byte 30: (limbs4_canon >> 36) as u8
    assert(bytes[30] == spec_bytes[30]);
    // Byte 31: (limbs4_canon >> 44) as u8  [final byte, only uses 7 bits of limb4]
    assert(bytes[31] == spec_bytes[31]);

    // -------------------------------------------------------------------------
    // STEP 7: Conclude the main result
    // -------------------------------------------------------------------------
    // All 32 bytes match, so the arrays are equal
    assert(bytes == spec_bytes);

    // By transitivity:
    //   u8_32_as_nat(&bytes) == u8_32_as_nat(&spec_bytes)  [from bytes == spec_bytes]
    //                          == u64_5_as_nat(canonical_limbs)  [from lemma_limbs_to_bytes]
    //                          == u64_5_as_nat(fe.limbs) % p()   [from reduction lemmas]
    //                          == fe51_as_canonical_nat(fe)         [by definition]
    assert(u8_32_as_nat(&bytes) == fe51_as_canonical_nat(fe));
}

/// Roundtrip lemma: `Seq<u8>` of length 32 equals the sequence view of `seq_to_array_32`.
///
/// This proves that converting a 32-element sequence to an array and back yields the original.
/// The `=~=` operator (extensional equality) handles the element-wise comparison automatically
/// once we establish that lengths match and Verus can unfold the definitions.
proof fn lemma_seq_to_array_32_roundtrip(s: Seq<u8>)
    requires
        s.len() == 32,
    ensures
        s == seq_from32(&seq_to_array_32(s)),
{
    let arr = seq_to_array_32(s);
    // Use extensional equality: two sequences are equal if they have the same length
    // and equal elements at each index. Verus unfolds seq_to_array_32 and seq_from32
    // definitions to verify arr[i] == s[i] for each i.
    assert(s =~= seq_from32(&arr));
}

// =============================================================================
// Lemmas for compress function
// =============================================================================
/// Canonical field element bytes have high bit (bit 255) equal to 0.
///
/// Since p = 2^255 - 19 < 2^255, any value < p has byte[31] < 128,
/// so (byte[31] >> 7) == 0.
pub proof fn lemma_canonical_bytes_bit255_zero(bytes: &[u8; 32], val: nat)
    requires
        u8_32_as_nat(bytes) == val,
        val < p(),
    ensures
        (bytes[31] >> 7) == 0,
{
    // p() = 2^255 - 19 < 2^255, so val < 2^255
    // In little-endian encoding, if val < 2^255, then byte[31] < 128
    // Therefore (byte[31] >> 7) == 0
    let byte31 = bytes[31];

    // Step 1: Establish that val < pow2(255)
    assert(p() < pow2(255)) by {
        pow255_gt_19();
    };

    // Step 2: Use existing lemma to establish relationship between u8_32_as_nat and bytes[31]
    lemma_u8_32_as_nat_lower_bound(bytes, 31);

    // Step 3: Establish pow2 relationships
    assert(pow2(7) == 128) by {
        lemma2_to64();
    };
    assert(pow2(7) * pow2(248) == pow2(255)) by {
        lemma_pow2_adds(7, 248);
    };

    // Step 4: Prove byte31 < 128 by contradiction
    // If byte31 >= 128, then:
    //   u8_32_as_nat(bytes) >= byte31 * pow2(248) >= 128 * pow2(248) = pow2(255)
    // But val = u8_32_as_nat(bytes) < p() < pow2(255), contradiction!
    assert(byte31 < 128) by {
        if byte31 >= 128 {
            // u8_32_as_nat(bytes) >= byte31 * pow2(248)
            assert(u8_32_as_nat(bytes) >= (byte31 as nat) * pow2(248));
            // byte31 >= 128, so byte31 * pow2(248) >= 128 * pow2(248)
            assert((byte31 as nat) * pow2(248) >= 128 * pow2(248)) by (nonlinear_arith)
                requires
                    byte31 >= 128,
            ;
            // 128 * pow2(248) = pow2(255)
            assert(128 * pow2(248) == pow2(255));
            // Therefore u8_32_as_nat(bytes) >= pow2(255)
            assert(u8_32_as_nat(bytes) >= pow2(255));
            // But val = u8_32_as_nat(bytes) and val < pow2(255), contradiction!
            assert(val >= pow2(255));
            assert(false);
        }
    };

    // Step 5: High bit is 0
    // byte31 < 128 means byte31 < 2^7, so bit 7 (the high bit) must be 0
    assert((byte31 >> 7) == 0) by (bit_vector)
        requires
            byte31 < 128,
    ;
}

/// The low bit of the byte encoding equals the parity of the field element.
///
/// (spec_fe51_as_bytes(fe)[0] & 1 == 1) <==> (fe51_as_canonical_nat(fe) % 2 == 1)
pub proof fn lemma_is_negative_equals_parity(fe: &FieldElement51)
    ensures
        (spec_fe51_as_bytes(fe)[0] & 1 == 1) == (fe51_as_canonical_nat(fe) % 2 == 1),
{
    // The canonical byte encoding has u8_32_as_nat(bytes) == fe51_as_canonical_nat(fe)
    // In little-endian: bytes[0] & 1 = value % 2
    // Step 1: Connect spec_fe51_as_bytes to fe51_as_canonical_nat
    lemma_u8_32_as_nat_of_spec_fe51_to_bytes(fe);
    let bytes = seq_to_array_32(spec_fe51_as_bytes(fe));
    assert(u8_32_as_nat(&bytes) == fe51_as_canonical_nat(fe));

    let byte0 = bytes[0];
    assert(byte0 == spec_fe51_as_bytes(fe)[0]);

    // Step 2: Use modulo truncation to show u8_32_as_nat % 2 == byte0 % 2
    lemma_u8_32_as_nat_mod_truncates(&bytes, 1);
    assert(u8_32_as_nat(&bytes) % pow2(8) == bytes_as_nat_prefix(bytes@, 1));

    // bytes_as_nat_prefix(bytes@, 1) = byte0 * pow2(0) = byte0
    assert(bytes_as_nat_prefix(bytes@, 1) == (byte0 as nat)) by {
        reveal_with_fuel(bytes_as_nat_prefix, 2);
        lemma2_to64();
        assert(bytes@[0] == byte0);
        assert(bytes_as_nat_prefix(bytes@, 0) == 0);
        assert(bytes_as_nat_prefix(bytes@, 1) == bytes_as_nat_prefix(bytes@, 0) + pow2(0)
            * bytes@[0] as nat);
        assert(pow2(0) == 1);
        assert(bytes_as_nat_prefix(bytes@, 1) == 0 + 1 * (byte0 as nat));
    };

    // Therefore: u8_32_as_nat(&bytes) % pow2(8) == byte0
    assert(u8_32_as_nat(&bytes) % pow2(8) == (byte0 as nat));

    // Step 3: Show pow2(8) is even, so (x % pow2(8)) % 2 == x % 2
    assert(pow2(8) == 256) by {
        lemma2_to64();
    };
    assert(pow2(8) % 2 == 0) by {
        lemma_pow2_even(8);
    };

    // (u8_32_as_nat % 256) % 2 == u8_32_as_nat % 2
    assert((u8_32_as_nat(&bytes) % pow2(8)) % 2 == u8_32_as_nat(&bytes) % 2) by {
        lemma_mod_mod(u8_32_as_nat(&bytes) as int, pow2(8) as int, 2);
    };

    // byte0 % 2 == u8_32_as_nat % 2
    assert((byte0 as nat) % 2 == u8_32_as_nat(&bytes) % 2);

    // Therefore: byte0 % 2 == fe51_as_canonical_nat(fe) % 2
    assert((byte0 as nat) % 2 == fe51_as_canonical_nat(fe) % 2);

    // Step 4: Use bit_vector to connect byte0 & 1 with byte0 % 2
    assert((byte0 & 1 == 1) == ((byte0 as nat) % 2 == 1)) by (bit_vector);
}

/// Point compression stores the sign of x in bit 255 of the y-encoding.
///
/// After XOR-ing sign_bit into s_before[31]'s high bit:
/// 1. Decoding s_after still recovers y_val (bit 255 is cleared by % pow2(255))
/// 2. s_after[31]'s high bit equals sign_bit
pub proof fn lemma_xor_sign_bit_preserves_y(
    s_before: &[u8; 32],
    s_after: &[u8; 32],
    y_val: nat,
    sign_bit: u8,
)
    requires
// s_before encodes y_val (a canonical field element)

        u8_32_as_nat(s_before) == y_val,
        y_val < p(),
        (s_before[31] >> 7) == 0,  // bit 255 is 0 (since y_val < p < 2^255)
        sign_bit == 0 || sign_bit == 1,
        // s_after = s_before with sign_bit XOR'd into bit 255
        forall|i: int| 0 <= i < 31 ==> s_after[i] == s_before[i],
        s_after[31] == (s_before[31] ^ (sign_bit << 7)),
    ensures
// decoding s_after still yields y_val

        field_element_from_bytes(s_after) == y_val,
        // bit 255 now contains sign_bit
        (s_after[31] >> 7) == sign_bit,
{
    // field_element_from_bytes(bytes) = (u8_32_as_nat(bytes) % pow2(255)) % p()
    // XOR only changes bit 255, which is cleared by % pow2(255)
    // So field_element_from_bytes(s_after) == y_val
    let byte31_before = s_before[31];
    let byte31_after = s_after[31];

    // Establish byte31_before < 128 from the precondition
    assert(byte31_before < 128) by (bit_vector)
        requires
            (byte31_before >> 7) == 0,
    ;

    // Step 1: Show XOR acts as addition when high bit is 0
    assert(byte31_after == byte31_before + sign_bit * 128) by (bit_vector)
        requires
            (byte31_before >> 7) == 0,
            sign_bit == 0 || sign_bit == 1,
            byte31_after == (byte31_before ^ (sign_bit << 7)),
    ;

    // Step 2: Establish pow2 relationships
    assert(pow2(7) == 128) by {
        lemma2_to64();
    };
    assert(pow2(7) * pow2(248) == pow2(255)) by {
        lemma_pow2_adds(7, 248);
    };

    // Step 3: Compute u8_32_as_nat(s_after)
    assert(u8_32_as_nat(s_after) >= (s_after[31] as nat) * pow2(248)) by {
        lemma_u8_32_as_nat_lower_bound(s_after, 31);
    };
    assert(u8_32_as_nat(s_before) >= (s_before[31] as nat) * pow2(248)) by {
        lemma_u8_32_as_nat_lower_bound(s_before, 31);
    };

    // For u8_32_as_nat, we can express the difference due to byte31 change
    // u8_32_as_nat(s_after) = u8_32_as_nat(s_before) + (byte31_after - byte31_before) * pow2(248)
    //                         = u8_32_as_nat(s_before) + sign_bit * 128 * pow2(248)
    //                         = u8_32_as_nat(s_before) + sign_bit * pow2(255)

    // This requires decomposing u8_32_as_nat into lower bytes + byte31 contribution
    // Using the fact that bytes 0-30 are unchanged and byte31 changes by sign_bit * 128
    assert(u8_32_as_nat(s_after) == u8_32_as_nat(s_before) + (sign_bit as nat) * pow2(255)) by {
        // Use decomposition: u8_32_as_nat = prefix(31) + byte31 * pow2(248)
        lemma_decomposition_prefix_rec(s_before, 31);
        lemma_decomposition_prefix_rec(s_after, 31);

        // u8_32_as_nat(s_before) = prefix(s_before@, 31) + u8_32_as_nat_rec(s_before, 31)
        let prefix_before = bytes_as_nat_prefix(s_before@, 31);
        let prefix_after = bytes_as_nat_prefix(s_after@, 31);

        // Since bytes 0-30 are the same, the prefixes are equal
        assert(prefix_before == prefix_after) by {
            lemma_prefix_equal_when_bytes_match(s_before@, s_after@, 31);
        };

        // u8_32_as_nat_rec(s, 31) = byte[31] * pow2(248) + u8_32_as_nat_rec(s, 32)
        // u8_32_as_nat_rec(s, 32) = 0 (base case)
        assert(u8_32_as_nat_rec(s_before, 32) == 0);
        assert(u8_32_as_nat_rec(s_after, 32) == 0);

        assert(u8_32_as_nat_rec(s_before, 31) == (byte31_before as nat) * pow2(248)) by {
            reveal_with_fuel(u8_32_as_nat_rec, 2);
        };
        assert(u8_32_as_nat_rec(s_after, 31) == (byte31_after as nat) * pow2(248)) by {
            reveal_with_fuel(u8_32_as_nat_rec, 2);
        };

        // Compute the difference
        // From lemma_decomposition_prefix_rec:
        // u8_32_as_nat_rec(s, 0) = prefix(s@, 31) + u8_32_as_nat_rec(s, 31)
        // From lemma_u8_32_as_nat_equals_rec:
        // u8_32_as_nat(s) = u8_32_as_nat_rec(s, 0)
        lemma_u8_32_as_nat_equals_rec(s_after);
        lemma_u8_32_as_nat_equals_rec(s_before);

        assert(u8_32_as_nat(s_after) == u8_32_as_nat_rec(s_after, 0));
        assert(u8_32_as_nat(s_before) == u8_32_as_nat_rec(s_before, 0));

        assert(u8_32_as_nat_rec(s_after, 0) == prefix_after + u8_32_as_nat_rec(s_after, 31));
        assert(u8_32_as_nat_rec(s_before, 0) == prefix_before + u8_32_as_nat_rec(s_before, 31));

        assert(u8_32_as_nat(s_after) == prefix_after + u8_32_as_nat_rec(s_after, 31));
        assert(u8_32_as_nat(s_before) == prefix_before + u8_32_as_nat_rec(s_before, 31));

        // prefix_after == prefix_before (bytes 0-30 are the same)
        // u8_32_as_nat_rec(s_after, 31) = (byte31_after as nat) * pow2(248)
        // u8_32_as_nat_rec(s_before, 31) = (byte31_before as nat) * pow2(248)
        // So: u8_32_as_nat(s_after) - u8_32_as_nat(s_before)
        //   = (byte31_after - byte31_before) * pow2(248)
        assert(u8_32_as_nat(s_after) == u8_32_as_nat(s_before) + ((byte31_after as nat) - (
        byte31_before as nat)) * pow2(248)) by (nonlinear_arith)
            requires
                u8_32_as_nat(s_after) == prefix_after + (byte31_after as nat) * pow2(248),
                u8_32_as_nat(s_before) == prefix_before + (byte31_before as nat) * pow2(248),
                prefix_after == prefix_before,
        ;

        assert((byte31_after as nat) == (byte31_before as nat) + (sign_bit as nat) * 128);

        assert(((byte31_after as nat) - (byte31_before as nat)) * pow2(248) == (sign_bit as nat)
            * 128 * pow2(248)) by (nonlinear_arith)
            requires
                (byte31_after as nat) == (byte31_before as nat) + (sign_bit as nat) * 128,
        ;

        assert((sign_bit as nat) * 128 * pow2(248) == (sign_bit as nat) * pow2(255)) by {
            assert((sign_bit as nat) * 128 * pow2(248) == (sign_bit as nat) * (128 * pow2(248)))
                by (nonlinear_arith);
            assert(128 * pow2(248) == pow2(255));
        };
    };

    // Step 4: Take mod pow2(255) - the sign_bit * pow2(255) term vanishes
    assert(u8_32_as_nat(s_after) % pow2(255) == u8_32_as_nat(s_before) % pow2(255)) by {
        // (a + b * pow2(255)) % pow2(255) == a % pow2(255)
        // This is because b * pow2(255) is divisible by pow2(255)
        lemma_pow2_pos(255);
        if sign_bit == 0 {
            assert(u8_32_as_nat(s_after) == u8_32_as_nat(s_before));
        } else {
            // sign_bit == 1
            let a = u8_32_as_nat(s_before);
            let m = pow2(255);
            // We have: u8_32_as_nat(s_after) = a + m
            // We want: (a + m) % m == a % m
            lemma_mod_add_multiples_vanish(a as int, m as int);
        }
    };

    // Step 5: Since y_val < p() < pow2(255), we have u8_32_as_nat(s_before) < pow2(255)
    assert(p() < pow2(255)) by {
        pow255_gt_19();
    };
    assert(u8_32_as_nat(s_before) < pow2(255));

    // Therefore u8_32_as_nat(s_before) % pow2(255) == u8_32_as_nat(s_before) == y_val
    assert(u8_32_as_nat(s_before) % pow2(255) == y_val) by {
        lemma_small_mod(y_val, pow2(255));
    };

    // Step 6: Combine to get field_element_from_bytes(s_after) == y_val
    assert(field_element_from_bytes(s_after) == y_val) by {
        assert(u8_32_as_nat(s_after) % pow2(255) == y_val);
        // field_element_from_bytes(s_after) = (u8_32_as_nat(s_after) % pow2(255)) % p()
        //                                        = y_val % p()
        //                                        = y_val (since y_val < p())
        lemma_small_mod(y_val, p());
    };

    // Step 7: Show (s_after[31] >> 7) == sign_bit
    assert((byte31_after >> 7) == sign_bit) by (bit_vector)
        requires
            byte31_after == byte31_before + sign_bit * 128,
            byte31_before < 128,
            sign_bit == 0 || sign_bit == 1,
    ;
}

} // verus!
