//! Proof lemmas for batch_invert (field elements)
//!
//! These lemmas prove the correctness of the batch inversion algorithm
//! which computes multiplicative inverses for a slice of field elements
//! using Montgomery's trick (shared prefix products).
#![allow(unused_imports)]
use crate::backend::serial::u64::field::FieldElement51;
use crate::core_assumes::*;
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
use crate::lemmas::field_lemmas::as_bytes_lemmas::*;
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
use crate::specs::core_specs::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
use crate::specs::primality_specs::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ============================================================================
// Bridge lemma: is_zero <-> fe51_as_canonical_nat == 0
// ============================================================================
/// Bridge lemma: spec_fe51_as_bytes(fe) is all-zeros iff fe51_as_canonical_nat(fe) == 0
///
/// This connects the bytes-based spec of is_zero to the algebraic canonical nat.
pub proof fn lemma_is_zero_iff_canonical_nat_zero(fe: FieldElement51)
    ensures
        (spec_fe51_as_bytes(&fe) == seq![0u8; 32]) <==> (fe51_as_canonical_nat(&fe) == 0),
{
    let bytes = seq_to_array_32(spec_fe51_as_bytes(&fe));
    assert(u8_32_as_nat(&bytes) == fe51_as_canonical_nat(&fe)) by {
        lemma_u8_32_as_nat_of_spec_fe51_to_bytes(&fe);
    };

    // Forward: all-zero bytes => canonical_nat == 0
    if spec_fe51_as_bytes(&fe) =~= seq![0u8; 32] {
        assert(fe51_as_canonical_nat(&fe) == 0) by {
            assert(forall|i: int| 0 <= i < 32 ==> bytes[i] == 0u8) by {
                assert forall|i: int| 0 <= i < 32 implies bytes[i] == 0u8 by {
                    assert(bytes[i] == spec_fe51_as_bytes(&fe)[i]);
                }
            };
            lemma_u8_32_as_nat_equals_rec(&bytes);
            lemma_suffix_zero_when_bytes_zero(&bytes, 0);
        };
    }
    // Reverse: canonical_nat == 0 => all-zero bytes

    if fe51_as_canonical_nat(&fe) == 0 {
        assert(spec_fe51_as_bytes(&fe) =~= seq![0u8; 32]) by {
            lemma_nat_zero_implies_all_zero_bytes(bytes);
            assert forall|i: int| 0 <= i < 32 implies spec_fe51_as_bytes(&fe)[i] == 0u8 by {
                assert(spec_fe51_as_bytes(&fe)[i] == bytes[i]);
            }
        };
    }
}

/// Helper: u8_32_as_nat == 0 implies all bytes are zero
proof fn lemma_nat_zero_implies_all_zero_bytes(bytes: [u8; 32])
    requires
        u8_32_as_nat(&bytes) == 0,
    ensures
        forall|i: int| 0 <= i < 32 ==> bytes[i] == 0u8,
{
    // u8_32_as_nat is a sum of non-negative terms: bytes[i] * pow2(8*i)
    // If any byte is non-zero, the sum would be positive — contradiction.
    assert forall|k: int| 0 <= k < 32 implies bytes[k] == 0u8 by {
        if bytes[k] != 0u8 {
            let ku = k as usize;
            lemma_u8_32_as_nat_lower_bound(&bytes, ku);
            lemma_pow2_pos((ku * 8) as nat);
            assert((bytes[k] as nat) * pow2((ku * 8) as nat) >= 1) by (nonlinear_arith)
                requires
                    bytes[k] as nat >= 1,
                    pow2((ku * 8) as nat) >= 1,
            ;
            assert(false);
        }
    };
}

// ============================================================================
// Partial product inductive lemmas
// ============================================================================
/// The partial product of non-zero elements is itself non-zero (mod p)
pub proof fn lemma_partial_product_nonzeros_is_nonzero(fields: Seq<FieldElement51>, k: int)
    requires
        0 <= k <= fields.len(),
    ensures
        partial_product_nonzeros(fields, k) % p() != 0,
    decreases k,
{
    p_gt_2();
    if k <= 0 {
        assert(partial_product_nonzeros(fields, k) % p() != 0) by {
            assert(partial_product_nonzeros(fields, 0) == 1);
            lemma_small_mod(1nat, p());
        };
    } else {
        lemma_partial_product_nonzeros_is_nonzero(fields, k - 1);
        let rest = partial_product_nonzeros(fields, k - 1);
        let a_k = fe51_as_canonical_nat(&fields[k - 1]);
        if a_k == 0 {
        } else {
            assert(a_k % p() != 0) by {
                lemma_mod_bound(u64_5_as_nat(fields[k - 1].limbs) as int, p() as int);
                lemma_small_mod(a_k, p());
            };
            let fm = field_mul(rest, a_k);
            assert(fm % p() != 0) by {
                assert(fm != 0) by {
                    lemma_nonzero_product(rest, a_k);
                };
                lemma_mod_bound((rest * a_k) as int, p() as int);
                lemma_small_mod(fm, p());
            };
        }
    }
}

/// Lemma: In the backward loop, both the result and accumulator invariants hold.
///
/// If field_mul(old_acc, PP(i+1)) == 1 and a_i != 0, then:
/// - field_mul(field_mul(old_acc, PP(i)), a_i) == 1  (result is inverse of a_i)
/// - field_mul(field_mul(old_acc, a_i), PP(i)) == 1  (acc invariant maintained)
pub proof fn lemma_backward_step(old_acc: nat, a_i: nat, fields: Seq<FieldElement51>, i: int)
    requires
        0 <= i < fields.len(),
        a_i == fe51_as_canonical_nat(&fields[i]),
        a_i != 0,
        field_mul(old_acc, partial_product_nonzeros(fields, i + 1)) == 1,
    ensures
        field_mul(field_mul(old_acc, partial_product_nonzeros(fields, i)), a_i) == 1,
        field_mul(field_mul(old_acc, a_i), partial_product_nonzeros(fields, i)) == 1,
{
    let pp_i = partial_product_nonzeros(fields, i);
    let pp_i1 = partial_product_nonzeros(fields, i + 1);

    // PP(i+1) = field_mul(PP(i), a_i) since a_i != 0
    assert(pp_i1 == field_mul(pp_i, a_i));

    // First postcondition: (old_acc * PP(i)) * a_i == 1
    assert(field_mul(field_mul(old_acc, pp_i), a_i) == 1) by {
        lemma_field_mul_assoc(old_acc, pp_i, a_i);
    };

    // Second postcondition: (old_acc * a_i) * PP(i) == 1
    assert(field_mul(field_mul(old_acc, a_i), pp_i) == 1) by {
        lemma_field_mul_assoc(old_acc, a_i, pp_i);
        lemma_field_mul_comm(a_i, pp_i);
    };
}

} // verus!
