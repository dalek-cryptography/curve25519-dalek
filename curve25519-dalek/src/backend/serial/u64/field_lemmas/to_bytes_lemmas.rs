#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_verus::div_mod_lemmas::*;
use super::super::common_verus::shift_lemmas::*;
use super::field_core::*;

verus! {

// ============================================================================
// LEMMA 1: Computing q (the quotient when dividing by p)
// ============================================================================

/// Spec function to compute q value from limbs
pub open spec fn compute_q_spec(limbs: [u64; 5]) -> u64 {
    let q0 = ((limbs[0] + 19) as u64 >> 51) as u64;
    let q1 = ((limbs[1] + q0) as u64 >> 51) as u64;
    let q2 = ((limbs[2] + q1) as u64 >> 51) as u64;
    let q3 = ((limbs[3] + q2) as u64 >> 51) as u64;
    let q4 = ((limbs[4] + q3) as u64 >> 51) as u64;
    q4
}

/// Proves that q computed via successive carry propagation equals 1 iff h >= p, 0 otherwise
/// where h = as_nat(limbs) and limbs[i] < 2^52 for all i
pub proof fn lemma_compute_q(limbs: [u64; 5], q: u64)
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        q == compute_q_spec(limbs),
    ensures
        q == 0 || q == 1,
        as_nat(limbs) >= p() <==> q == 1,
        as_nat(limbs) < p() <==> q == 0,
{
    assume(false); // TODO: prove this
}

// ============================================================================
// LEMMA 2: Value preservation through modular reduction
// ============================================================================

/// Spec function to compute the reduction result
pub open spec fn reduce_with_q_spec(input_limbs: [u64; 5], q: u64) -> [u64; 5] {
    let l0 = (input_limbs[0] + 19 * q) as u64;
    let l1 = (input_limbs[1] + (l0 >> 51)) as u64;
    let l0_masked = (l0 & mask51) as u64;
    let l2 = (input_limbs[2] + (l1 >> 51)) as u64;
    let l1_masked = (l1 & mask51) as u64;
    let l3 = (input_limbs[3] + (l2 >> 51)) as u64;
    let l2_masked = (l2 & mask51) as u64;
    let l4 = (input_limbs[4] + (l3 >> 51)) as u64;
    let l3_masked = (l3 & mask51) as u64;
    let l4_masked = (l4 & mask51) as u64;
    [l0_masked, l1_masked, l2_masked, l3_masked, l4_masked]
}

/// Proves that after adding 19*q and propagating carries while masking to 51 bits,
/// the result equals as_nat(input_limbs) mod p
pub proof fn lemma_to_bytes_reduction(input_limbs: [u64; 5], final_limbs: [u64; 5], q: u64)
    requires
        forall |i: int| 0 <= i < 5 ==> input_limbs[i] < (1u64 << 52),
        q == 0 || q == 1,
        as_nat(input_limbs) >= p() <==> q == 1,
        final_limbs == reduce_with_q_spec(input_limbs, q),
    ensures
        forall |i: int| 0 <= i < 5 ==> final_limbs[i] < (1u64 << 51),
        as_nat(final_limbs) == as_nat(input_limbs) % p(),
{
    assume(false); // TODO: prove this
}

// ============================================================================
// LEMMA 3: Packing 51-bit limbs into 8-bit bytes
// ============================================================================

/// Core lemma: proves that packing 51-bit limbs into bytes preserves the value
pub proof fn lemma_limbs_to_bytes(limbs: [u64; 5], bytes: [u8; 32])
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
        // bytes are packed according to the to_bytes algorithm (lines 380-410)
        bytes[ 0] ==   limbs[0]                           as u8,
        bytes[ 1] ==  (limbs[0] >>  8)                    as u8,
        bytes[ 2] ==  (limbs[0] >> 16)                    as u8,
        bytes[ 3] ==  (limbs[0] >> 24)                    as u8,
        bytes[ 4] ==  (limbs[0] >> 32)                    as u8,
        bytes[ 5] ==  (limbs[0] >> 40)                    as u8,
        bytes[ 6] == ((limbs[0] >> 48) | (limbs[1] << 3)) as u8,
        bytes[ 7] ==  (limbs[1] >>  5)                    as u8,
        bytes[ 8] ==  (limbs[1] >> 13)                    as u8,
        bytes[ 9] ==  (limbs[1] >> 21)                    as u8,
        bytes[10] ==  (limbs[1] >> 29)                    as u8,
        bytes[11] ==  (limbs[1] >> 37)                    as u8,
        bytes[12] == ((limbs[1] >> 45) | (limbs[2] << 6)) as u8,
        bytes[13] ==  (limbs[2] >>  2)                    as u8,
        bytes[14] ==  (limbs[2] >> 10)                    as u8,
        bytes[15] ==  (limbs[2] >> 18)                    as u8,
        bytes[16] ==  (limbs[2] >> 26)                    as u8,
        bytes[17] ==  (limbs[2] >> 34)                    as u8,
        bytes[18] ==  (limbs[2] >> 42)                    as u8,
        bytes[19] == ((limbs[2] >> 50) | (limbs[3] << 1)) as u8,
        bytes[20] ==  (limbs[3] >>  7)                    as u8,
        bytes[21] ==  (limbs[3] >> 15)                    as u8,
        bytes[22] ==  (limbs[3] >> 23)                    as u8,
        bytes[23] ==  (limbs[3] >> 31)                    as u8,
        bytes[24] ==  (limbs[3] >> 39)                    as u8,
        bytes[25] == ((limbs[3] >> 47) | (limbs[4] << 4)) as u8,
        bytes[26] ==  (limbs[4] >>  4)                    as u8,
        bytes[27] ==  (limbs[4] >> 12)                    as u8,
        bytes[28] ==  (limbs[4] >> 20)                    as u8,
        bytes[29] ==  (limbs[4] >> 28)                    as u8,
        bytes[30] ==  (limbs[4] >> 36)                    as u8,
        bytes[31] ==  (limbs[4] >> 44)                    as u8,
    ensures
        as_nat_32_u8(bytes) == as_nat(limbs),
{
    assume(false); // TODO: prove this
}

// ============================================================================
// HELPER LEMMAS for packing bytes
// ============================================================================

/// Helper: Extract a range of bits from a u64 as a u8
pub proof fn lemma_extract_byte(x: u64, shift: nat, byte_val: u8)
    requires
        shift % 8 == 0,
        shift < 64,
        byte_val == (x >> shift) as u8,
    ensures
        byte_val as nat == (x as nat / pow2(shift)) % 256,
{
    // Step 1: Establish that x >> shift == x / pow2(shift)
    lemma_u64_shr_is_div(x, shift as u64);
    let shifted = x >> shift;
    assert(shifted as nat == x as nat / pow2(shift));
    
    // Step 2: Establish key facts about u8 and pow2(8)
    lemma2_to64();
    assert(u8::MAX + 1 == pow2(8));
    assert(u8::MAX == 255) by (compute);
    assert(pow2(8) == 256) by (compute);
    
    // Step 3: byte_val is a u8, so it's bounded
    assert(byte_val <= u8::MAX);
    assert(byte_val < 256);
    
    // Step 4: Relate casting to masking
    // In Rust/Verus, casting to u8 is equivalent to & 0xFF
    assert(0xFF == 255) by (compute);
    assert(0xFF == u8::MAX) by (compute);
    assert(0xFF + 1 == 256) by (compute);
    
    // Use the low_bits_mask lemma: shifted & 0xFF == shifted % 256
    lemma_u64_low_bits_mask_is_mod(shifted, 8);
    assert((shifted & (low_bits_mask(8) as u64)) == shifted % (pow2(8) as u64));
    
    // Establish that low_bits_mask(8) == 0xFF
    assert(low_bits_mask(8) == 0xFF) by (compute);
    assert((shifted & 0xFF) == shifted % 256);
    
    // The key missing piece: prove that (shifted as u8) == (shifted & 0xFF) as u8
    // At the u64 level before casting, these should be equal by bit_vector
    assert(shifted as u8 == (shifted & 0xFF) as u8) by (bit_vector);
    
    // Now we know byte_val == shifted as u8 == (shifted & 0xFF) as u8
    // And we need byte_val as nat == (shifted & 0xFF) as nat
    // This should follow from the equality of the u8 values
    assert(byte_val == (shifted & 0xFF) as u8);
    assert(byte_val as nat == (shifted & 0xFF) as nat);
    assert((shifted & 0xFF) as nat == shifted as nat % 256);
}

/// Helper: Combine parts of two limbs into one byte
pub proof fn lemma_packed_byte(low: u64, high: u64, low_shift: nat, high_shift: nat, byte_val: u8)
    requires
        low_shift < 51,
        high_shift <= 51,
        low_shift + high_shift == 8,
        low < pow2(51),
        high < pow2(51),
        byte_val == ((low >> ((51 - low_shift) as u64)) | (high << (low_shift as u64))) as u8,
    ensures
        byte_val as nat == ((low as nat / pow2((51 - low_shift) as nat)) + (high as nat % pow2(high_shift)) * pow2(low_shift)) % 256,
{
    assume(false); // TODO: prove this
}

/// Proves that the recursive and non-recursive definitions are equivalent
pub proof fn lemma_as_nat_32_u8_equivalence(limbs: [u8; 32])
    ensures
        as_nat_32_u8(limbs) == as_nat_32_u8_nonrec(limbs)
{
    assume(false); // TODO: prove this by induction
}

// ============================================================================
// OVERFLOW HELPER LEMMAS for to_bytes
// ============================================================================

use super::super::common_verus::shift_lemmas::*;

/// Simple monotonicity of right shift for u64
/// (This is just a wrapper around the existing lemma_shr_le_u64)
pub proof fn lemma_shr_mono_u64(a: u64, b: u64, k: u64)
    requires
        a <= b,
        k < 64,
    ensures
        a >> k <= b >> k,
{
    lemma_shr_le_u64(a, b, k as nat);
}

/// If a value is less than a bound, it stays less after adding a small constant
pub proof fn lemma_add_preserves_bound(a: u64, bound: u64, add: u64)
    requires
        a < bound,
        bound + add <= u64::MAX,
    ensures
        a + add < bound + add,
{
    // This is trivial arithmetic
}

}

