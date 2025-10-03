#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_verus::div_mod_lemmas::*;
use super::super::common_verus::mul_lemmas::*;
use super::super::common_verus::pow_lemmas::*;
use super::super::common_verus::shift_lemmas::*;
use super::field_core::*;
use super::load8_lemmas::*;

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
    let low_bits = low >> ((51 - low_shift) as u64);
    let high_bits = high << (low_shift as u64);
    let combined = low_bits | high_bits;
    
    // Step 1: Relate shift to division
    lemma_u64_shr_is_div(low, (51 - low_shift) as u64);
    assert(low_bits as nat == low as nat / pow2((51 - low_shift) as nat));
    
    // Step 2: Relate left shift to multiplication (need to check overflow)
    // high < pow2(51) and we shift by low_shift < 51, so high << low_shift < pow2(51 + low_shift)
    // Since low_shift + high_shift == 8 and high_shift <= 51, we have low_shift <= 8
    // So high << low_shift < pow2(51 + 8) = pow2(59) < pow2(64) = safe
    assert(low_shift <= 8);
    assert(51 + low_shift <= 59);
    lemma_pow2_adds(51, low_shift);
    assert(pow2(51) * pow2(low_shift) == pow2(51 + low_shift));
    mul_le(high as nat, pow2(51), pow2(low_shift), pow2(low_shift));
    assert(high * pow2(low_shift) <= pow2(51) * pow2(low_shift));
    assert(high * pow2(low_shift) <= pow2(51 + low_shift));
    lemma2_to64_rest();
    assert(pow2(64) == u64::MAX + 1) by {
        lemma2_to64_rest();
    };
    lemma_pow2_strictly_increases(51 + low_shift, 64);
    assert(pow2(51 + low_shift) < pow2(64));
    assert(high * pow2(low_shift) < pow2(64));
    assert(high * pow2(low_shift) <= u64::MAX);
    lemma_u64_shl_is_mul(high, low_shift as u64);
    assert(high_bits as nat == high as nat * pow2(low_shift));
    
    // Step 3: Show that OR equals addition (bits don't overlap)
    //
    // We need to prove: combined as nat == low_bits as nat + high_bits as nat
    // where combined = low_bits | high_bits
    //
    // This requires two properties:
    //
    // Property 1: low_bits < pow2(low_shift) ✅ PROVEN
    // - We have: low < pow2(51) and low_bits = low >> (51 - low_shift)
    // - Use lemma_shr_bound to prove that right shifting gives a bounded result
    lemma_shr_bound(low, 51, low_shift);
    assert(low_bits < pow2(low_shift));
    
    // Property 2: OR equals addition when bits don't overlap ✅ PROVEN
    // - Since low_bits < pow2(low_shift), it occupies bits [0, low_shift)
    // - Since high_bits = high << low_shift, it occupies bits [low_shift, 64)
    // - Therefore low_bits & high_bits == 0
    // - The fundamental property: a | b == a + b when a & b == 0
    
    // Convert pow2(low_shift) to (1u64 << low_shift) for bit_or_is_plus_u64
    shift_is_pow2(low_shift);
    assert(pow2(low_shift) == (1u64 << low_shift));
    assert(low_bits < (1u64 << low_shift));
    
    // Use bit_or_is_plus_u64 to prove OR equals addition
    assert(combined == low_bits | high_bits);
    assert(high_bits == high << low_shift);
    bit_or_is_plus_u64(low_bits, high, low_shift);
    assert(low_bits | (high << low_shift) == low_bits + (high << low_shift));
    assert(combined == low_bits + high_bits);
    assert(combined as nat == low_bits as nat + high_bits as nat);
    
    // Step 4: Relate high_bits to (high % pow2(high_shift)) * pow2(low_shift)
    // We have: high_bits = high * pow2(low_shift)
    // We want: high_bits % 256 == (high % pow2(high_shift)) * pow2(low_shift) % 256
    //
    // Key insight: Since high_shift + low_shift == 8 and 256 = pow2(8),
    // when we compute (high * pow2(low_shift)) % 256, only the lower high_shift bits of high matter.
    
    // Use lemma_mod_shift_equivalence with k = low_shift, m = high_shift
    assert(low_shift + high_shift == 8);
    lemma2_to64(); // This provides pow2(8) == 256
    lemma_mod_shift_equivalence(high, low_shift, high_shift);
    assert((high as nat * pow2(low_shift)) % pow2(low_shift + high_shift) 
           == ((high as nat % pow2(high_shift)) * pow2(low_shift)) % pow2(low_shift + high_shift));
    assert(low_shift + high_shift == 8);
    assert(high_bits as nat == high as nat * pow2(low_shift));
    assert(high_bits as nat % 256 == (high as nat % pow2(high_shift)) * pow2(low_shift) % 256);
    
    // Step 5: Cast to u8 = mod 256 (same as lemma_extract_byte)
    lemma2_to64();
    lemma_u64_low_bits_mask_is_mod(combined, 8);
    assert(low_bits_mask(8) == 0xFF) by (compute);
    assert((combined & 0xFF) == combined % 256);
    assert(combined as u8 == (combined & 0xFF) as u8) by (bit_vector);
    assert(byte_val == (combined & 0xFF) as u8);
    assert(byte_val as nat == (combined & 0xFF) as nat);
    assert((combined & 0xFF) as nat == combined as nat % 256);
}

/// Proves that the recursive and non-recursive definitions are equivalent
pub proof fn lemma_as_nat_32_u8_equivalence(limbs: [u8; 32])
    ensures
        as_nat_32_u8(limbs) == as_nat_32_u8_nonrec(limbs)
{
    assume(false); // TODO: prove this by induction
}

// ============================================================================
// BIT MANIPULATION HELPER LEMMAS
// ============================================================================

/// Lemma: Modular arithmetic with shift - only low bits matter
/// When shifting left by k and taking mod 2^(k+m), only the low m bits of the original value matter
/// 
/// Specifically: (x * 2^k) % 2^(k+m) == ((x % 2^m) * 2^k) % 2^(k+m)
///
/// This is because x = q * 2^m + (x % 2^m), so:
/// x * 2^k = q * 2^(k+m) + (x % 2^m) * 2^k
/// Taking mod 2^(k+m) eliminates the q * 2^(k+m) term.
pub proof fn lemma_mod_shift_equivalence(x: u64, k: nat, m: nat)
    requires
        k < 64,
        m <= 64,
        k + m <= 64,
        x < pow2(51),  // For our use case (limbs are < 2^51)
    ensures
        (x as nat * pow2(k)) % pow2(k + m) == ((x as nat % pow2(m)) * pow2(k)) % pow2(k + m),
{
    // DIVIDE-AND-CONQUER PROOF SKETCH
    // This is a classic modular arithmetic property that can be proven using vstd lemmas.
    // The proof is straightforward but the SMT solver struggles with nat/int conversions.
    //
    // Proof strategy:
    //
    // Step 1: Apply lemma_fundamental_div_mod
    //   x = q * 2^m + r  where r = x % 2^m
    //
    // Step 2: Multiply both sides by 2^k  
    //   x * 2^k = q * 2^m * 2^k + r * 2^k
    //
    // Step 3: Use lemma_pow2_adds
    //   2^m * 2^k = 2^(k+m)
    //   So: x * 2^k = q * 2^(k+m) + r * 2^k
    //
    // Step 4: Take mod 2^(k+m)
    //   (x * 2^k) % 2^(k+m) = (q * 2^(k+m) + r * 2^k) % 2^(k+m)
    //
    // Step 5: Use modular addition property
    //   (a + b) % n = ((a % n) + (b % n)) % n
    //   With a = q * 2^(k+m) and b = r * 2^k:
    //   = ((q * 2^(k+m)) % 2^(k+m) + (r * 2^k) % 2^(k+m)) % 2^(k+m)
    //
    // Step 6: The first term vanishes
    //   (q * 2^(k+m)) % 2^(k+m) = 0  (fundamental property of modular arithmetic)
    //   So: (x * 2^k) % 2^(k+m) = (r * 2^k) % 2^(k+m)
    //
    // Step 7: Substitute r = x % 2^m
    //   (x * 2^k) % 2^(k+m) = ((x % 2^m) * 2^k) % 2^(k+m)  ✓
    //
    // The challenge is not the mathematical reasoning, but handling nat/int type conversions
    // in a way that doesn't exceed the SMT solver's resource limits. Each step above is
    // mathematically trivial, but requires careful type management in Verus.
    //
    // TODO: Implement this proof with explicit type conversions and simpler assertions,
    // or break it into smaller helper lemmas to reduce SMT solver load.
    
    assume((x as nat * pow2(k)) % pow2(k + m) == ((x as nat % pow2(m)) * pow2(k)) % pow2(k + m));
}

/// Lemma: OR equals addition when bits don't overlap (u64 version)
/// Generalization of bit_or_is_plus from load8_lemmas.rs to work with u64
pub proof fn bit_or_is_plus_u64(a: u64, b: u64, k: nat)
    requires
        k < 64,
        a < (1u64 << k),
    ensures
        a | (b << k) == a + (b << k),
{
    // The key insight: if a < 2^k, then a occupies only bits [0, k)
    // and (b << k) occupies only bits [k, 64)
    // So they don't overlap: a & (b << k) == 0
    // Therefore: a | (b << k) == a + (b << k)
    
    // Convert k to u64 for bit_vector
    let k_u64 = k as u64;
    assert(a < (1u64 << k_u64));
    assert(b << k == b << k_u64);
    
    // Prove with bit_vector
    assert(a | (b << k_u64) == a + (b << k_u64)) by (bit_vector)
        requires
            k_u64 < 64,
            a < (1u64 << k_u64);
}

/// Lemma: Division by a positive number preserves strict inequality
/// If x < a * b and a > 0, then x / a < b
pub proof fn lemma_div_strictly_bounded(x: int, a: int, b: int)
    requires
        a > 0,
        b >= 0,
        x < a * b,
    ensures
        x / a < b,
{
   // (b * a) / a == b
   lemma_div_by_multiple(b, a);
   // x < b * a && a > 0 => x / a < (b * a) / a
   lemma_div_by_multiple_is_strongly_ordered(x, a * b, b, a);
}

/// Lemma: Right shifting a bounded value gives a smaller bound
/// If x < 2^n, then x >> (n - k) < 2^k
pub proof fn lemma_shr_bound(x: u64, n: nat, k: nat)
    requires
        x < pow2(n),
        k <= n,
        n < 64,
    ensures
        (x >> ((n - k) as u64)) < pow2(k),
{
    // Key insight: x >> (n - k) = x / 2^(n - k)
    lemma_u64_shr_is_div(x, (n - k) as u64);
    assert((x >> ((n - k) as u64)) as nat == x as nat / pow2((n - k) as nat));
    
    // Since x < 2^n, we have x / 2^(n - k) < 2^n / 2^(n - k)
    lemma_pow2_pos((n - k) as nat);
    lemma_div_is_ordered(x as int, pow2(n) as int, pow2((n - k) as nat) as int);
    assert(x as nat / pow2((n - k) as nat) <= pow2(n) / pow2((n - k) as nat));
    
    // Now show that 2^n / 2^(n - k) = 2^k
    // This follows from: 2^n / 2^(n - k) = 2^(n - (n - k)) = 2^k
    // We need to use the power subtraction property
    
    // 2^n = 2^(n - k) * 2^k
    lemma_pow2_adds((n - k) as nat, k);
    assert(pow2((n - k) as nat) * pow2(k) == pow2(((n - k) + k) as nat));
    assert(((n - k) + k) as nat == n);
    assert(pow2((n - k) as nat) * pow2(k) == pow2(n));
    
    // Therefore: 2^n / 2^(n - k) = 2^k
    lemma_pow2_pos((n - k) as nat);
    assert(pow2((n - k) as nat) > 0);
    lemma_div_multiples_vanish(pow2(k) as int, pow2((n - k) as nat) as int);
    assert(pow2((n - k) as nat) * pow2(k) / pow2((n - k) as nat) == pow2(k));
    assert(pow2(n) / pow2((n - k) as nat) == pow2(k));
    
    // Combine: x / 2^(n - k) <= 2^n / 2^(n - k) = 2^k
    assert((x >> ((n - k) as u64)) as nat <= pow2(k));
    
    // For strict inequality: x < 2^n = 2^(n-k) * 2^k
    // So x / 2^(n-k) < 2^n / 2^(n-k) = 2^k
    // Use lemma_div_strictly_bounded to prove this
    
    // We have: x < pow2(n) = pow2(n - k) * pow2(k)
    assert(x < pow2(n));
    assert(pow2(n) == pow2((n - k) as nat) * pow2(k));
    lemma_pow2_pos((n - k) as nat);
    assert(pow2((n - k) as nat) > 0);
    
    // Apply lemma_div_strictly_bounded with a = pow2(n - k), b = pow2(k)
    lemma_div_strictly_bounded(x as int, pow2((n - k) as nat) as int, pow2(k) as int);
    let shifted_val = x as int / pow2((n - k) as nat) as int;
    assert(shifted_val < pow2(k) as int);
    assert((x >> ((n - k) as u64)) as nat == shifted_val);
    assert((x >> ((n - k) as u64)) < pow2(k));
}

// ============================================================================
// OVERFLOW HELPER LEMMAS for to_bytes
// ============================================================================

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

