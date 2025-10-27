#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_verus::bit_lemmas::*;
use super::super::common_verus::div_mod_lemmas::*;
use super::super::common_verus::mul_lemmas::*;
use super::super::common_verus::pow_lemmas::*;
use super::super::common_verus::shift_lemmas::*;
use super::field_core::*;
use super::load8_lemmas::*;
use super::pow2_51_lemmas::*;

verus! {

// ============================================================================
// LEMMA 3: Packing 51-bit limbs into 8-bit bytes
// ============================================================================
/// Predicate: bytes are packed from limbs according to the to_bytes algorithm
/// This captures the byte-packing relationship used in FieldElement51::to_bytes (lines 380-410)
pub open spec fn bytes_match_limbs_packing(limbs: [u64; 5], bytes: [u8; 32]) -> bool {
    bytes[0] == limbs[0] as u8 && bytes[1] == (limbs[0] >> 8) as u8 && bytes[2] == (limbs[0]
        >> 16) as u8 && bytes[3] == (limbs[0] >> 24) as u8 && bytes[4] == (limbs[0] >> 32) as u8
        && bytes[5] == (limbs[0] >> 40) as u8 && bytes[6] == ((limbs[0] >> 48) | (limbs[1]
        << 3)) as u8 && bytes[7] == (limbs[1] >> 5) as u8 && bytes[8] == (limbs[1] >> 13) as u8
        && bytes[9] == (limbs[1] >> 21) as u8 && bytes[10] == (limbs[1] >> 29) as u8 && bytes[11]
        == (limbs[1] >> 37) as u8 && bytes[12] == ((limbs[1] >> 45) | (limbs[2] << 6)) as u8
        && bytes[13] == (limbs[2] >> 2) as u8 && bytes[14] == (limbs[2] >> 10) as u8 && bytes[15]
        == (limbs[2] >> 18) as u8 && bytes[16] == (limbs[2] >> 26) as u8 && bytes[17] == (limbs[2]
        >> 34) as u8 && bytes[18] == (limbs[2] >> 42) as u8 && bytes[19] == ((limbs[2] >> 50) | (
    limbs[3] << 1)) as u8 && bytes[20] == (limbs[3] >> 7) as u8 && bytes[21] == (limbs[3]
        >> 15) as u8 && bytes[22] == (limbs[3] >> 23) as u8 && bytes[23] == (limbs[3] >> 31) as u8
        && bytes[24] == (limbs[3] >> 39) as u8 && bytes[25] == ((limbs[3] >> 47) | (limbs[4]
        << 4)) as u8 && bytes[26] == (limbs[4] >> 4) as u8 && bytes[27] == (limbs[4] >> 12) as u8
        && bytes[28] == (limbs[4] >> 20) as u8 && bytes[29] == (limbs[4] >> 28) as u8 && bytes[30]
        == (limbs[4] >> 36) as u8 && bytes[31] == (limbs[4] >> 44) as u8
}

/// Core lemma: proves that packing 51-bit limbs into bytes preserves the value
///
/// This is the main lemma we need to complete the `to_bytes` proof.
/// It connects the byte representation with the limb representation.
pub proof fn lemma_limbs_to_bytes(limbs: [u64; 5], bytes: [u8; 32])
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        as_nat_32_u8(&bytes) == as_nat(limbs),
{
    // Connect the bit shift in the requires clause to pow2
    shift_is_pow2(51);
    lemma_byte_sum_equals_limb_sum(limbs, bytes);
}

// ============================================================================
// Phase 3: Algebraic Expansion Helper Lemmas
// ============================================================================
/// Core algebraic lemma: The sum of bytes equals the sum of limbs
/// This is where we do the heavy algebraic lifting to show the equivalence
proof fn lemma_byte_sum_equals_limb_sum(limbs: [u64; 5], bytes: [u8; 32])
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < pow2(51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        as_nat_32_u8(&bytes) == as_nat(limbs),
{
    // This lemma performs the complete algebraic expansion:
    //
    // LHS: as_nat_32_u8(bytes)
    //    = bytes[0] + bytes[1]*256 + bytes[2]*256^2 + ... + bytes[31]*256^31
    //
    // Substitute each byte[i] from bytes_match_limbs_packing:
    //    = (limbs[0])
    //      + (limbs[0]>>8)*256
    //      + (limbs[0]>>16)*256^2
    //      + ... [and so on for all 32 bytes]
    //
    // Group terms by limb:
    //    = [terms involving limbs[0]]
    //      + [terms involving limbs[1]]
    //      + [terms involving limbs[2]]
    //      + [terms involving limbs[3]]
    //      + [terms involving limbs[4]]
    //
    // Show each group equals limbs[i] * pow2(i*51):
    //    = limbs[0]*pow2(0) + limbs[1]*pow2(51) + limbs[2]*pow2(102) + limbs[3]*pow2(153) + limbs[4]*pow2(204)
    //    = as_nat(limbs)
    //
    // The proof strategy is:
    // 1. Define each limb's byte contribution as a spec function
    // 2. Prove each contribution equals limbs[i] * pow2(i*51) using helper lemmas
    // 3. Prove the sum of contributions equals as_nat_32_u8(bytes)
    // 4. Therefore as_nat_32_u8(bytes) == as_nat(limbs)
    //
    // Key insight: pow2(48) * 8 = pow2(51) (the radix change point)
    lemma2_to64();
    lemma_pow2_adds(48, 3);  // Establishes pow2(51) = pow2(48) * 8

    // Prove each limb's contribution to the byte sum
    // Each lemma shows that the bytes from that limb contribute exactly limbs[i] * pow2(i*51)
    let limb0_contribution = limb0_byte_contribution(limbs, bytes);
    let limb1_contribution = limb1_byte_contribution(limbs, bytes);
    let limb2_contribution = limb2_byte_contribution(limbs, bytes);
    let limb3_contribution = limb3_byte_contribution(limbs, bytes);
    let limb4_contribution = limb4_byte_contribution(limbs, bytes);

    // Prove each contribution equals limbs[i] * pow2(i*51)
    lemma_limb0_contribution_correctness(limbs, bytes);

    lemma_limb1_contribution_correctness(limbs, bytes);

    lemma_limb2_contribution_correctness(limbs, bytes);

    lemma_limb3_contribution_correctness(limbs, bytes);

    lemma_limb4_contribution_correctness(limbs, bytes);

    // Prove the sum of contributions equals as_nat_32_u8(&bytes)
    lemma_sum_equals_byte_nat(limbs, bytes);
    assert(as_nat_32_u8(&bytes) == limb0_contribution + limb1_contribution + limb2_contribution
        + limb3_contribution + limb4_contribution);

    // Therefore, the sum equals as_nat(limbs)
}

/// Helper: A byte formed by simple right shift has a direct arithmetic interpretation
proof fn lemma_byte_from_limb_shift(limb: u64, shift: u64, byte: u8)
    requires
        limb < pow2(51),
        shift < 64,
        byte == (limb >> shift) as u8,
    ensures
        byte as nat == (limb as nat / pow2(shift as nat)) % 256,
{
    // Bitwise shift to arithmetic conversion
    // When we shift right by `shift` bits and cast to u8, we extract 8 bits starting at position `shift`
    // In arithmetic terms: (limb / 2^shift) % 256
    lemma2_to64();
    lemma_u64_shr_is_div(limb, shift);
    assert((limb >> shift) as nat == limb as nat / pow2(shift as nat));

    // The u8 cast takes the low 8 bits, which is % 256
    assert((limb >> shift) as u8 == (limb >> shift) as nat % 256) by {
        lemma_u8_cast_is_mod_256(limb >> shift);
    }
}

// ============================================================================
// Phase 3: Per-Limb Byte Contribution Functions
// ============================================================================
/// Compute limb 0's contribution to the byte sum
/// Limb 0 contributes to bytes 0-6 (fully to 0-5, partially to 6)
spec fn limb0_byte_contribution(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    bytes[0] as nat * pow2(0 * 8) + bytes[1] as nat * pow2(1 * 8) + bytes[2] as nat * pow2(2 * 8)
        + bytes[3] as nat * pow2(3 * 8) + bytes[4] as nat * pow2(4 * 8) + bytes[5] as nat * pow2(
        5 * 8,
    )
        +
    // Byte 6 is a boundary byte - limb 0 contributes only the low 3 bits
    // These 3 bits represent limbs[0]'s bits 48-50
    ((limbs[0] as nat / pow2(48)) % 8) * pow2(6 * 8)
}

/// Compute limb 1's contribution to the byte sum
/// Limb 1 contributes to bytes 6-12 (partially to 6, fully to 7-11, partially to 12)
spec fn limb1_byte_contribution(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    // Byte 6 high 5 bits (limbs[1]'s bits 0-4)
    ((limbs[1] as nat % pow2(5)) * 8) * pow2(6 * 8) + bytes[7] as nat * pow2(7 * 8)
        + bytes[8] as nat * pow2(8 * 8) + bytes[9] as nat * pow2(9 * 8) + bytes[10] as nat * pow2(
        10 * 8,
    ) + bytes[11] as nat * pow2(11 * 8)
        +
    // Byte 12 low 6 bits (limbs[1]'s bits 45-50)
    ((limbs[1] as nat / pow2(45)) % pow2(6)) * pow2(12 * 8)
}

/// Compute limb 2's contribution to the byte sum
/// Limb 2 contributes to bytes 12-19
spec fn limb2_byte_contribution(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    // Byte 12 high 2 bits (limbs[2]'s bits 0-1)
    ((limbs[2] as nat % pow2(2)) * pow2(6)) * pow2(12 * 8) + bytes[13] as nat * pow2(13 * 8)
        + bytes[14] as nat * pow2(14 * 8) + bytes[15] as nat * pow2(15 * 8) + bytes[16] as nat
        * pow2(16 * 8) + bytes[17] as nat * pow2(17 * 8) + bytes[18] as nat * pow2(18 * 8)
        +
    // Byte 19 low 1 bit (limbs[2]'s bit 50)
    ((limbs[2] as nat / pow2(50)) % 2) * pow2(19 * 8)
}

/// Compute limb 3's contribution to the byte sum
/// Limb 3 contributes to bytes 19-25
spec fn limb3_byte_contribution(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    // Byte 19 high 7 bits (limbs[3]'s bits 0-6)
    ((limbs[3] as nat % pow2(7)) * 2) * pow2(19 * 8) + bytes[20] as nat * pow2(20 * 8)
        + bytes[21] as nat * pow2(21 * 8) + bytes[22] as nat * pow2(22 * 8) + bytes[23] as nat
        * pow2(23 * 8) + bytes[24] as nat * pow2(24 * 8)
        +
    // Byte 25 low 4 bits (limbs[3]'s bits 47-50)
    ((limbs[3] as nat / pow2(47)) % pow2(4)) * pow2(25 * 8)
}

/// Compute limb 4's contribution to the byte sum
/// Limb 4 contributes to bytes 25-31
spec fn limb4_byte_contribution(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    // Byte 25 high 4 bits (limbs[4]'s bits 0-3)
    ((limbs[4] as nat % pow2(4)) * pow2(4)) * pow2(25 * 8) + bytes[26] as nat * pow2(26 * 8)
        + bytes[27] as nat * pow2(27 * 8) + bytes[28] as nat * pow2(28 * 8) + bytes[29] as nat
        * pow2(29 * 8) + bytes[30] as nat * pow2(30 * 8) + bytes[31] as nat * pow2(31 * 8)
}

// ============================================================================
// Phase 3: Helper Lemmas for Limb Contribution Proofs
// ============================================================================

/// Helper: Byte extraction commutes with modulo for low-order bytes
/// If we extract a byte at position k*8 where k*8+8 <= m, then:
/// (x / 2^(k*8)) % 256 == ((x % 2^m) / 2^(k*8)) % 256
///
/// This is a specialized version of lemma_chunk_extraction_commutes_with_mod for bytes (b=8).
proof fn lemma_byte_extraction_commutes_with_mod(x: nat, k: nat, m: nat)
    requires
        k * 8 + 8
            <= m,  // The byte we're extracting is entirely below the modulo boundary

    ensures
        (x / pow2(k * 8)) % 256 == ((x % pow2(m)) / pow2(k * 8)) % 256,
{
    // Call the generalized version with b=8 (byte size)
    lemma_chunk_extraction_commutes_with_mod(x, k, 8, m);

    // Establish that pow2(8) == 256
    lemma2_to64();
}

// ============================================================================
// Phase 3: Per-Limb Contribution Correctness Proofs
// ============================================================================
/// Proves that limb 0's byte contribution equals limbs[0] * pow2(0) = limbs[0]
proof fn lemma_limb0_contribution_correctness(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[0] < pow2(51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        limb0_byte_contribution(limbs, bytes) == limbs[0] as nat,
{
    // Limb 0 is stored in bytes 0-6
    // - Bytes 0-5: full bytes containing limbs[0]'s bits 0-47 (48 bits total)
    // - Byte 6 (low 3 bits): limbs[0]'s bits 48-50 (3 bits)
    // Total: 51 bits, which matches limbs[0] < 2^51
    //
    // Strategy: Apply div-mod theorem at the 48-bit boundary
    // limbs[0] = (limbs[0] % 2^48) + (limbs[0] / 2^48) * 2^48
    lemma2_to64();
    assert(pow2(8) == 256);

    // Step 1: Show bytes 0-5 contribute (limbs[0] % 2^48)
    // From bytes_match_limbs_packing, we know:
    // bytes[0] = limbs[0] as u8
    // bytes[1] = (limbs[0] >> 8) as u8
    // ... and so on

    // These bytes, when summed with their position weights, reconstruct limbs[0] % 2^48
    let low_48_bits = bytes[0] as nat * pow2(0 * 8) + bytes[1] as nat * pow2(1 * 8)
        + bytes[2] as nat * pow2(2 * 8) + bytes[3] as nat * pow2(3 * 8) + bytes[4] as nat * pow2(
        4 * 8,
    ) + bytes[5] as nat * pow2(5 * 8);

    // Prove this equals limbs[0] % 2^48
    // From bytes_match_limbs_packing, we know each byte is exactly (limbs[0] >> (i*8)) as u8

    // Use lemma_byte_from_limb_shift to establish arithmetic value of each byte
    shr_zero_is_id(limbs[0]);  // Explicit call instead of broadcast for better Z3 performance
    assert(bytes[0] == (limbs[0] >> 0) as u8);
    lemma_byte_from_limb_shift(limbs[0], 0, bytes[0]);
    assert(bytes[0] as nat == (limbs[0] as nat / pow2(0)) % 256);

    lemma_byte_from_limb_shift(limbs[0], 8, bytes[1]);
    assert(bytes[1] as nat == (limbs[0] as nat / pow2(8)) % 256);

    lemma_byte_from_limb_shift(limbs[0], 16, bytes[2]);
    assert(bytes[2] as nat == (limbs[0] as nat / pow2(16)) % 256);

    lemma_byte_from_limb_shift(limbs[0], 24, bytes[3]);

    lemma_byte_from_limb_shift(limbs[0], 32, bytes[4]);
    assert(bytes[4] as nat == (limbs[0] as nat / pow2(32)) % 256);

    lemma_byte_from_limb_shift(limbs[0], 40, bytes[5]);
    assert(bytes[5] as nat == (limbs[0] as nat / pow2(40)) % 256);

    // Now we know the arithmetic value of each byte!
    // We need to show that summing them reconstructs limbs[0] % 2^48

    // Key insight: We have bytes extracted from limbs[0], but our reconstruction lemma
    // expects bytes extracted from (limbs[0] % 2^48). We need to show these are the same.

    // For each byte i (i=0..5), show that extraction from limbs[0] equals extraction from limbs[0] % 2^48
    // This holds because byte i is at position i*8, and i*8+7 < 48, so it's below the modulo boundary

    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 0, 48);
    assert(bytes[0] as nat == ((limbs[0] as nat % pow2(48)) / pow2(0)) % 256);

    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 1, 48);

    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 2, 48);
    assert(bytes[2] as nat == ((limbs[0] as nat % pow2(48)) / pow2(16)) % 256);

    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 3, 48);
    assert(bytes[3] as nat == ((limbs[0] as nat % pow2(48)) / pow2(24)) % 256);

    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 4, 48);
    assert(bytes[4] as nat == ((limbs[0] as nat % pow2(48)) / pow2(32)) % 256);

    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 5, 48);

    // Now the bytes satisfy the preconditions of our reconstruction lemma!
    // We also need to show that (limbs[0] % 2^48) < 2^48
    lemma_pow2_pos(48);
    assert(pow2(48) > 0);
    assert(limbs[0] as nat % pow2(48) < pow2(48)) by {
        lemma_mod_bound(limbs[0] as int, pow2(48) as int);
    }

    // The modulo value fits in u64 since 2^48 < 2^64
    let modulo_value = limbs[0] as nat % pow2(48);
    assert(pow2(48) < pow2(64)) by {
        lemma_pow2_strictly_increases(48, 64);
    }
    assert(modulo_value < pow2(64));

    let limb0_low48 = modulo_value as u64;

    // Show that limb0_low48 satisfies the preconditions
    // The cast to u64 and back to nat preserves the value since modulo_value < 2^64
    // For x < 2^64, (x as u64) as nat == x - this is a fundamental property of u64 casting
    // Verus should be able to verify this directly
    assert(limb0_low48 as nat == modulo_value);
    assert(limb0_low48 as nat == limbs[0] as nat % pow2(48));

    // The bytes we extracted from limbs[0] % pow2(48) satisfy the preconditions
    // We already proved: bytes[i] == ((limbs[0] % pow2(48)) / pow2(i*8)) % 256
    assert(bytes[0] as nat == (limb0_low48 as nat / pow2(0)) % 256);
    assert(bytes[1] as nat == (limb0_low48 as nat / pow2(8)) % 256);
    assert(bytes[2] as nat == (limb0_low48 as nat / pow2(16)) % 256);
    assert(bytes[3] as nat == (limb0_low48 as nat / pow2(24)) % 256);
    assert(bytes[4] as nat == (limb0_low48 as nat / pow2(32)) % 256);
    assert(bytes[5] as nat == (limb0_low48 as nat / pow2(40)) % 256);

    // Now apply our reconstruction lemma
    lemma_6_bytes_reconstruct(
        limb0_low48 as nat,
        bytes[0],
        bytes[1],
        bytes[2],
        bytes[3],
        bytes[4],
        bytes[5],
    );

    // The reconstruction lemma tells us: low_48_bits == limbs[0] % 2^48
    assert(low_48_bits == (limbs[0] as nat % pow2(48)));

    // Step 2: Show the contribution from byte 6
    // From bytes_match_limbs_packing: bytes[6] == ((limbs[0] >> 48) | (limbs[1] << 3)) as u8
    // The low 3 bits of bytes[6] come from limbs[0] >> 48
    // which is limbs[0] / 2^48

    // Since limbs[0] < 2^51, we have limbs[0] / 2^48 < 2^3 = 8
    assert(limbs[0] < pow2(51));
    lemma_div_bound(limbs[0] as nat, 48, 51);
    assert(limbs[0] as nat / pow2(48) < pow2((51 - 48) as nat));
    assert(limbs[0] as nat / pow2(48) < pow2(3));
    lemma2_to64();
    assert(pow2(3) == 8);
    assert(limbs[0] as nat / pow2(48) < 8);

    // The high 5 bits of byte 6 come from limbs[1], so the low 3 bits are:
    let high_3_bits_contribution = ((limbs[0] as nat / pow2(48)) % 8) * pow2(6 * 8);

    // Since limbs[0]/2^48 < 8, taking % 8 is identity
    assert((limbs[0] as nat / pow2(48)) % 8 == limbs[0] as nat / pow2(48));
    assert(high_3_bits_contribution == (limbs[0] as nat / pow2(48)) * pow2(48));

    // Step 3: Apply div-mod theorem
    // limbs[0] = (limbs[0] % 2^48) + (limbs[0] / 2^48) * 2^48
    lemma_pow2_pos(48);  // Establishes pow2(48) > 0
    assert(pow2(48) > 0);
    lemma_fundamental_div_mod(limbs[0] as int, pow2(48) as int);
    assert(limbs[0] as nat == (limbs[0] as nat % pow2(48)) + (limbs[0] as nat / pow2(48)) * pow2(
        48,
    ));

    // Step 4: Show this equals limb0_byte_contribution
    assert(limb0_byte_contribution(limbs, bytes) == low_48_bits + high_3_bits_contribution);
    assert(limb0_byte_contribution(limbs, bytes) == (limbs[0] as nat % pow2(48)) + (limbs[0] as nat
        / pow2(48)) * pow2(48));
    assert(limb0_byte_contribution(limbs, bytes) == limbs[0] as nat);
}

/// Helper: 5-byte reconstruction lemma
/// Proves that 5 consecutive bytes reconstruct a 40-bit value
proof fn lemma_5_bytes_reconstruct(
    value: nat,
    byte0: u8,
    byte1: u8,
    byte2: u8,
    byte3: u8,
    byte4: u8,
)
    requires
        byte0 as nat == (value / pow2(0)) % 256,
        byte1 as nat == (value / pow2(8)) % 256,
        byte2 as nat == (value / pow2(16)) % 256,
        byte3 as nat == (value / pow2(24)) % 256,
        byte4 as nat == (value / pow2(32)) % 256,
        value < pow2(40),  // 5 bytes = 40 bits

    ensures
        byte0 as nat * pow2(0) + byte1 as nat * pow2(8) + byte2 as nat * pow2(16) + byte3 as nat
            * pow2(24) + byte4 as nat * pow2(32) == value,
{
    lemma2_to64();

    // Same pattern as lemma_sum_extracted_bytes_reconstructs_value, but for 5 bytes
    // Use fundamental property: a = (a % d) + (a / d) * d

    // Step 0: value = byte0 + (value / 256) * 256
    lemma_fundamental_div_mod(value as int, 256);
    assert(byte0 as nat == value % 256);

    let rest1 = value / pow2(8);
    assert(value == byte0 as nat + rest1 * pow2(8));

    // Step 1: rest1 = byte1 + (rest1 / 256) * 256
    lemma_pow2_pos(8);
    lemma_fundamental_div_mod(rest1 as int, 256);

    let rest2 = rest1 / 256;
    lemma_pow2_adds(8, 8);
    lemma_div_denominator(value as int, 256, 256);

    // Step 2: rest2 = byte2 + (rest2 / 256) * 256
    lemma_fundamental_div_mod(rest2 as int, 256);

    let rest3 = rest2 / 256;
    lemma_pow2_adds(16, 8);
    lemma_div_denominator(value as int, pow2(16) as int, 256);
    assert(rest3 == value / pow2(24));

    // Step 3: rest3 = byte3 + (rest3 / 256) * 256
    lemma_fundamental_div_mod(rest3 as int, 256);
    assert(rest3 % 256 == byte3 as nat);

    let rest4 = rest3 / 256;
    lemma_pow2_adds(24, 8);
    lemma_div_denominator(value as int, pow2(24) as int, 256);
    assert(value == byte0 as nat + byte1 as nat * pow2(8) + byte2 as nat * pow2(16) + byte3 as nat
        * pow2(24) + rest4 * pow2(32));

    // Step 4: rest4 = byte4 (since value < 2^40, rest4 < 2^8 = 256)
    lemma_div_bound(value, 32, 40);

    lemma_mod_bound(rest4 as int, 256);

    // Final result
    assert(value == byte0 as nat + byte1 as nat * pow2(8) + byte2 as nat * pow2(16) + byte3 as nat
        * pow2(24) + byte4 as nat * pow2(32));
}

/// Helper: 6-byte reconstruction lemma
/// Proves that 6 consecutive bytes reconstruct a 48-bit value
proof fn lemma_6_bytes_reconstruct(
    value: nat,
    byte0: u8,
    byte1: u8,
    byte2: u8,
    byte3: u8,
    byte4: u8,
    byte5: u8,
)
    requires
        byte0 as nat == (value / pow2(0)) % 256,
        byte1 as nat == (value / pow2(8)) % 256,
        byte2 as nat == (value / pow2(16)) % 256,
        byte3 as nat == (value / pow2(24)) % 256,
        byte4 as nat == (value / pow2(32)) % 256,
        byte5 as nat == (value / pow2(40)) % 256,
        value < pow2(48),  // 6 bytes = 48 bits

    ensures
        byte0 as nat * pow2(0) + byte1 as nat * pow2(8) + byte2 as nat * pow2(16) + byte3 as nat
            * pow2(24) + byte4 as nat * pow2(32) + byte5 as nat * pow2(40) == value,
{
    lemma2_to64();

    // Same pattern as lemma_5_bytes_reconstruct, extended to 6 bytes
    // Use fundamental property: a = (a % d) + (a / d) * d

    // Step 0: value = byte0 + (value / 256) * 256
    lemma_fundamental_div_mod(value as int, 256);

    let rest1 = value / pow2(8);
    assert(value == byte0 as nat + rest1 * pow2(8));

    // Step 1: rest1 = byte1 + (rest1 / 256) * 256
    lemma_pow2_pos(8);
    lemma_fundamental_div_mod(rest1 as int, 256);

    let rest2 = rest1 / 256;
    lemma_pow2_adds(8, 8);
    lemma_div_denominator(value as int, 256, 256);

    // Step 2: rest2 = byte2 + (rest2 / 256) * 256
    lemma_fundamental_div_mod(rest2 as int, 256);
    assert(byte2 as nat == (value / pow2(16)) % 256);

    let rest3 = rest2 / 256;
    lemma_pow2_adds(16, 8);
    lemma_div_denominator(value as int, pow2(16) as int, 256);

    // Step 3: rest3 = byte3 + (rest3 / 256) * 256
    lemma_fundamental_div_mod(rest3 as int, 256);

    let rest4 = rest3 / 256;
    lemma_pow2_adds(24, 8);
    lemma_div_denominator(value as int, pow2(24) as int, 256);
    assert(value == byte0 as nat + byte1 as nat * pow2(8) + byte2 as nat * pow2(16) + byte3 as nat
        * pow2(24) + rest4 * pow2(32));

    // Step 4: rest4 = byte4 + (rest4 / 256) * 256
    lemma_fundamental_div_mod(rest4 as int, 256);

    let rest5 = rest4 / 256;
    lemma_pow2_adds(32, 8);
    lemma_div_denominator(value as int, pow2(32) as int, 256);
    assert(value == byte0 as nat + byte1 as nat * pow2(8) + byte2 as nat * pow2(16) + byte3 as nat
        * pow2(24) + byte4 as nat * pow2(32) + rest5 * pow2(40));

    // Step 5: rest5 = byte5 (since value < 2^48, rest5 < 2^8 = 256)
    lemma_div_bound(value, 40, 48);
    assert(rest5 < pow2(8));

    lemma_mod_bound(rest5 as int, 256);

    // Final result
    assert(value == byte0 as nat + byte1 as nat * pow2(8) + byte2 as nat * pow2(16) + byte3 as nat
        * pow2(24) + byte4 as nat * pow2(32) + byte5 as nat * pow2(40));
}

/// Proves that limb 1's byte contribution equals limbs[1] * pow2(51)
proof fn lemma_limb1_contribution_correctness(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[0] < pow2(51),  // Need limb 0 for boundary byte 6
        limbs[1] < pow2(51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        limb1_byte_contribution(limbs, bytes) == limbs[1] as nat * pow2(51),
{
    // Limb 1 is stored in bytes 6-12, but positioned at 2^51
    // - Byte 6 (high 5 bits): limbs[1]'s bits 0-4
    // - Bytes 7-11: limbs[1]'s bits 5-44 (40 bits)
    // - Byte 12 (low 6 bits): limbs[1]'s bits 45-50
    // Total: 5 + 40 + 6 = 51 bits
    lemma2_to64();
    lemma_pow2_adds(48, 3);

    // KEY INSIGHT: From bytes_match_limbs_packing, we know:
    // bytes[7] = (limbs[1] >> 5) as u8
    // bytes[8] = (limbs[1] >> 13) as u8
    // ... and so on
    //
    // So limb1_byte_contribution is actually:
    //   (limbs[1] % 2^5) * 8 * 2^48 +              // Low 5 bits at position 2^51
    //   (limbs[1] >> 5 ... >> 37) * positions +    // Middle 40 bits starting at position 2^56
    //   (limbs[1] / 2^45) % 2^6 * 2^96             // High 6 bits at position 2^96
    //
    // This is just limbs[1] * 2^51 with bits partitioned across the byte array!

    // Strategy: Show that the contribution reconstructs limbs[1] * 2^51
    // We'll use the same approach as limb 0:
    // 1. Convert bytes 7-11 to arithmetic form
    // 2. Show they reconstruct (limbs[1] >> 5) at position 2^56
    // 3. Handle boundary bits
    // 4. Combine using div-mod theorem

    // Step 1: Extract arithmetic values for bytes 7-11
    // These bytes come from limbs[1] >> 5, 13, 21, 29, 37
    lemma_byte_from_limb_shift(limbs[1], 5, bytes[7]);

    lemma_byte_from_limb_shift(limbs[1], 13, bytes[8]);

    lemma_byte_from_limb_shift(limbs[1], 21, bytes[9]);

    lemma_byte_from_limb_shift(limbs[1], 29, bytes[10]);

    lemma_byte_from_limb_shift(limbs[1], 37, bytes[11]);

    // Step 2: Recognize that bytes 7-11 weighted by their positions reconstruct
    // (limbs[1] >> 5) at position 2^56 = 2^(7*8)
    //
    // bytes[7]*2^56 + bytes[8]*2^64 + ... = (limbs[1] >> 5) * 2^56
    //
    // Note: The byte positions in limb1_byte_contribution are:
    // bytes[7] * pow2(7*8) = bytes[7] * 2^56
    // bytes[8] * pow2(8*8) = bytes[8] * 2^64 = bytes[8] * 2^(56+8)
    // etc.

    // Prove that bytes[7-11] reconstruct ((limbs[1] / 2^5) % 2^40) at position 2^56
    //
    // From lemma_byte_from_limb_shift, we have:
    // bytes[7] as nat == (limbs[1] / pow2(5)) % 256
    // bytes[8] as nat == (limbs[1] / pow2(13)) % 256
    // bytes[9] as nat == (limbs[1] / pow2(21)) % 256
    // bytes[10] as nat == (limbs[1] / pow2(29)) % 256
    // bytes[11] as nat == (limbs[1] / pow2(37)) % 256
    //
    // The key insight: these bytes extract consecutive 8-bit chunks from (limbs[1] / 2^5)

    // First, rewrite the byte extractions in terms of (limbs[1] / 2^5)
    // bytes[7] == (limbs[1] / 2^5) / 2^0 % 256
    lemma_pow2_adds(0, 5);
    lemma_div_denominator(limbs[1] as int, pow2(5) as int, pow2(0) as int);

    // bytes[8] == (limbs[1] / 2^13) % 256 == (limbs[1] / 2^5) / 2^8 % 256
    lemma_pow2_adds(5, 8);
    lemma_div_denominator(limbs[1] as int, pow2(5) as int, pow2(8) as int);

    // bytes[9] == (limbs[1] / 2^21) % 256 == (limbs[1] / 2^5) / 2^16 % 256
    lemma_pow2_adds(5, 16);
    lemma_div_denominator(limbs[1] as int, pow2(5) as int, pow2(16) as int);

    // bytes[10] == (limbs[1] / 2^29) % 256 == (limbs[1] / 2^5) / 2^24 % 256
    lemma_pow2_adds(5, 24);
    lemma_div_denominator(limbs[1] as int, pow2(5) as int, pow2(24) as int);

    // bytes[11] == (limbs[1] / 2^37) % 256 == (limbs[1] / 2^5) / 2^32 % 256
    lemma_pow2_adds(5, 32);
    lemma_div_denominator(limbs[1] as int, pow2(5) as int, pow2(32) as int);

    // Now handle the % 2^40 truncation
    // Since limbs[1] < 2^51, we have limbs[1] / 2^5 < 2^46
    lemma_div_bound(limbs[1] as nat, 5, 51);

    // The bytes extract bits at positions [0..8), [8..16), [16..24), [24..32), [32..40)
    // from (limbs[1] / 2^5). Since all these bit positions are < 40, taking % 2^40
    // doesn't change the extracted bytes.
    //
    // For k < 40, if we extract byte k from value v, we get: (v / 2^(k*8)) % 256
    // If v < 2^46, then taking (v % 2^40) only affects bits 40+
    // So for k*8 < 40 (i.e., k < 5), we have:
    //   (v / 2^(k*8)) % 256 == ((v % 2^40) / 2^(k*8)) % 256
    //
    // Since our bytes extract at offsets 0, 8, 16, 24, 32 (all < 40), they extract
    // from (limbs[1] / 2^5) % 2^40 the same way.

    let middle_value = (limbs[1] as nat / pow2(5)) % pow2(40);

    // Prove middle_value < 2^40 (trivial by definition of %)
    lemma_pow2_pos(40);
    assert(pow2(40) > 0);
    lemma_mod_bound(middle_value as int, pow2(40) as int);

    // Now prove that the bytes extract from middle_value
    // Since we're extracting at bit positions [0, 8, 16, 24, 32], all < 40,
    // extracting from (limbs[1] / 2^5) or from ((limbs[1] / 2^5) % 2^40) gives the same result
    //
    // For byte extraction at position k where k*8 < 40:
    //   (v / 2^(k*8)) % 256 == ((v % 2^40) / 2^(k*8)) % 256
    //
    // This is because v % 2^40 only affects bits >= 40, and byte extraction at k*8
    // only looks at bits [k*8, k*8+8), which are all < 40.

    let v = limbs[1] as nat / pow2(5);

    // Use lemma_byte_extraction_commutes_with_mod to show extraction commutes with % 2^40
    // For byte at position k, we need k*8 + 8 <= 40
    lemma_byte_extraction_commutes_with_mod(v, 0, 40);  // 0*8 + 8 = 8 <= 40 ✓
    assert(bytes[7] as nat == (middle_value / pow2(0)) % 256);

    lemma_byte_extraction_commutes_with_mod(v, 1, 40);  // 1*8 + 8 = 16 <= 40 ✓

    lemma_byte_extraction_commutes_with_mod(v, 2, 40);  // 2*8 + 8 = 24 <= 40 ✓

    lemma_byte_extraction_commutes_with_mod(v, 3, 40);  // 3*8 + 8 = 32 <= 40 ✓

    lemma_byte_extraction_commutes_with_mod(v, 4, 40);  // 4*8 + 8 = 40 <= 40 ✓

    // Now apply lemma_5_bytes_reconstruct
    lemma_5_bytes_reconstruct(middle_value, bytes[7], bytes[8], bytes[9], bytes[10], bytes[11]);

    // This gives us:
    assert(bytes[7] as nat * pow2(0) + bytes[8] as nat * pow2(8) + bytes[9] as nat * pow2(16)
        + bytes[10] as nat * pow2(24) + bytes[11] as nat * pow2(32) == middle_value);

    // Now multiply both sides by 2^56 to get the bytes at their actual positions
    lemma_mul_is_distributive_add(
        pow2(56) as int,
        (bytes[7] as nat * pow2(0)) as int,
        (bytes[8] as nat * pow2(8)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(56) as int,
        (bytes[7] as nat * pow2(0) + bytes[8] as nat * pow2(8)) as int,
        (bytes[9] as nat * pow2(16)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(56) as int,
        (bytes[7] as nat * pow2(0) + bytes[8] as nat * pow2(8) + bytes[9] as nat * pow2(16)) as int,
        (bytes[10] as nat * pow2(24)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(56) as int,
        (bytes[7] as nat * pow2(0) + bytes[8] as nat * pow2(8) + bytes[9] as nat * pow2(16)
            + bytes[10] as nat * pow2(24)) as int,
        (bytes[11] as nat * pow2(32)) as int,
    );

    // Distribute the multiplication into each term
    lemma_mul_is_associative(bytes[7] as int, pow2(0) as int, pow2(56) as int);
    lemma_mul_is_associative(bytes[8] as int, pow2(8) as int, pow2(56) as int);
    lemma_mul_is_associative(bytes[9] as int, pow2(16) as int, pow2(56) as int);
    lemma_mul_is_associative(bytes[10] as int, pow2(24) as int, pow2(56) as int);
    lemma_mul_is_associative(bytes[11] as int, pow2(32) as int, pow2(56) as int);

    // Simplify using pow2 addition: 2^56 * 2^k = 2^(56+k)
    lemma_pow2_adds(56, 0);

    lemma_pow2_adds(56, 8);

    lemma_pow2_adds(56, 16);

    lemma_pow2_adds(56, 24);

    lemma_pow2_adds(56, 32);
    assert(pow2(88) == pow2(11 * 8));

    // Final result
    assert(bytes[7] as nat * pow2(7 * 8) + bytes[8] as nat * pow2(8 * 8) + bytes[9] as nat * pow2(
        9 * 8,
    ) + bytes[10] as nat * pow2(10 * 8) + bytes[11] as nat * pow2(11 * 8) == middle_value * pow2(
        56,
    ));

    // Step 3: Handle boundary bytes
    // Low 5 bits (byte 6 high part): (limbs[1] % 2^5) * 8 * 2^48 = (limbs[1] % 2^5) * 2^51
    // High 6 bits (byte 12 low part): (limbs[1] / 2^45) % 2^6 * 2^96

    assert(8 * pow2(48) == pow2(51)) by {
        lemma_pow2_adds(48, 3);
    }

    // Step 4: Prove the final equality using division-modulo reconstruction
    // Goal: Show limb1_byte_contribution == limbs[1] * 2^51

    // First, expand limb1_byte_contribution using its definition
    let contribution = limb1_byte_contribution(limbs, bytes);
    assert(contribution == ((limbs[1] as nat % pow2(5)) * 8) * pow2(6 * 8) + bytes[7] as nat * pow2(
        7 * 8,
    ) + bytes[8] as nat * pow2(8 * 8) + bytes[9] as nat * pow2(9 * 8) + bytes[10] as nat * pow2(
        10 * 8,
    ) + bytes[11] as nat * pow2(11 * 8) + ((limbs[1] as nat / pow2(45)) % pow2(6)) * pow2(12 * 8));

    // Create a variable for the middle bytes sum
    let middle_bytes_sum = bytes[7] as nat * pow2(7 * 8) + bytes[8] as nat * pow2(8 * 8)
        + bytes[9] as nat * pow2(9 * 8) + bytes[10] as nat * pow2(10 * 8) + bytes[11] as nat * pow2(
        11 * 8,
    );

    // From the proof above, we have:
    // middle_bytes_sum == ((limbs[1] / pow2(5)) % pow2(40)) * pow2(56)
    let middle_value_at_position = ((limbs[1] as nat / pow2(5)) % pow2(40)) * pow2(56);

    // Substitute into contribution
    assert(contribution == ((limbs[1] as nat % pow2(5)) * 8) * pow2(48) + middle_bytes_sum + ((
    limbs[1] as nat / pow2(45)) % pow2(6)) * pow2(96));

    assert(contribution == ((limbs[1] as nat % pow2(5)) * 8) * pow2(48) + middle_value_at_position
        + ((limbs[1] as nat / pow2(45)) % pow2(6)) * pow2(96));

    // Now complete the algebraic proof using division-modulo reconstruction
    // Goal: Show contribution = limbs[1] * 2^51

    // Step 1: Simplify the low contribution term
    // We have: ((limbs[1] % 2^5) * 8) * 2^48
    // We proved earlier that 8 * 2^48 = 2^51
    // So: ((limbs[1] % 2^5) * 8) * 2^48 = (limbs[1] % 2^5) * (8 * 2^48) = (limbs[1] % 2^5) * 2^51
    // For now, accept this simplification (requires multiplication associativity)
    let low_term = (limbs[1] as nat % pow2(5)) * pow2(51);
    let middle_term = ((limbs[1] as nat / pow2(5)) % pow2(40)) * pow2(56);
    let high_term = ((limbs[1] as nat / pow2(45)) % pow2(6)) * pow2(96);

    // Step 2: Establish power relationships needed for factoring
    lemma_pow2_adds(51, 5);  // 2^56 = 2^51 * 2^5

    lemma_pow2_adds(51, 45);  // 2^96 = 2^51 * 2^45

    // Step 3: Prove limbs[1] can be reconstructed from the three parts
    // We'll show: limbs[1] = (limbs[1] % 2^5) + ((limbs[1] / 2^5) % 2^40) * 2^5 + ((limbs[1] / 2^45) % 2^6) * 2^45

    // First, reconstruct limbs[1] / 2^5 from its low 40 bits and high part
    lemma_pow2_pos(40);
    let shifted_value = limbs[1] as nat / pow2(5);
    lemma_fundamental_div_mod(shifted_value as int, pow2(40) as int);
    // lemma_fundamental_div_mod gives: shifted_value == pow2(40) * (shifted_value / pow2(40)) + (shifted_value % pow2(40))
    // We need: shifted_value == (shifted_value % pow2(40)) + (shifted_value / pow2(40)) * pow2(40)
    assert(pow2(40) * (shifted_value / pow2(40)) == (shifted_value / pow2(40)) * pow2(40)) by {
        lemma_mul_is_commutative(pow2(40) as int, (shifted_value / pow2(40)) as int);
    }

    // Show that (limbs[1] / 2^5) / 2^40 = limbs[1] / 2^45
    lemma_div_denominator(limbs[1] as int, pow2(5) as int, pow2(40) as int);
    lemma_pow2_adds(5, 40);

    // So: limbs[1] / 2^5 = ((limbs[1] / 2^5) % 2^40) + (limbs[1] / 2^45) * 2^40
    assert(shifted_value == (shifted_value % pow2(40)) + (limbs[1] as nat / pow2(45)) * pow2(40));

    // Next, reconstruct limbs[1] from its low 5 bits and (limbs[1] / 2^5)
    lemma_pow2_pos(5);
    lemma_fundamental_div_mod(limbs[1] as int, pow2(5) as int);
    // lemma_fundamental_div_mod gives: limbs[1] == pow2(5) * (limbs[1] / pow2(5)) + (limbs[1] % pow2(5))
    assert(pow2(5) * shifted_value == shifted_value * pow2(5)) by {
        lemma_mul_is_commutative(pow2(5) as int, shifted_value as int);
    }

    // Substitute the reconstruction of shifted_value (limbs[1] / 2^5)
    assert(limbs[1] as nat == (limbs[1] as nat % pow2(5)) + ((shifted_value % pow2(40)) + (
    limbs[1] as nat / pow2(45)) * pow2(40)) * pow2(5));

    // Distribute the * 2^5
    assert(limbs[1] as nat == (limbs[1] as nat % pow2(5)) + (shifted_value % pow2(40)) * pow2(5) + (
    limbs[1] as nat / pow2(45)) * pow2(40) * pow2(5)) by {
        lemma_mul_is_distributive_add(
            pow2(5) as int,
            (shifted_value % pow2(40)) as int,
            (limbs[1] as nat / pow2(45) * pow2(40)) as int,
        );
    }

    // Use 2^40 * 2^5 = 2^45
    lemma_pow2_adds(40, 5);
    assert((limbs[1] as nat / pow2(45)) * pow2(40) * pow2(5) == (limbs[1] as nat / pow2(45)) * pow2(
        45,
    )) by {
        lemma_mul_is_associative(
            (limbs[1] as nat / pow2(45)) as int,
            pow2(40) as int,
            pow2(5) as int,
        );
    }

    assert(limbs[1] as nat == (limbs[1] as nat % pow2(5)) + ((limbs[1] as nat / pow2(5)) % pow2(40))
        * pow2(5) + (limbs[1] as nat / pow2(45)) * pow2(45));

    // Handle the % 2^6 on the high bits
    // Since limbs[1] < 2^51, we have limbs[1] / 2^45 < 2^6
    lemma_div_bound(limbs[1] as nat, 45, 51);
    lemma_small_mod(limbs[1] as nat / pow2(45), pow2(6));

    // Therefore:
    assert(limbs[1] as nat == (limbs[1] as nat % pow2(5)) + ((limbs[1] as nat / pow2(5)) % pow2(40))
        * pow2(5) + ((limbs[1] as nat / pow2(45)) % pow2(6)) * pow2(45));

    // Step 4: Now connect the contribution to limbs[1] * 2^51
    // We have: contribution = ((limbs[1] % 2^5) * 8) * 2^48 + middle_value_at_position + ((limbs[1] / 2^45) % 2^6) * 2^96
    // Where: middle_value_at_position = ((limbs[1] / 2^5) % 2^40) * 2^56

    // First, simplify the low term: ((limbs[1] % 2^5) * 8) * 2^48 = (limbs[1] % 2^5) * (8 * 2^48) = (limbs[1] % 2^5) * 2^51
    // We proved earlier that 8 * 2^48 = 2^51
    let low_part = (limbs[1] as nat % pow2(5));
    assert(((limbs[1] as nat % pow2(5)) * 8) * pow2(48) == low_part * (8 * pow2(48))) by {
        lemma_mul_is_associative(low_part as int, 8, pow2(48) as int);
    }

    // So contribution = (limbs[1] % 2^5) * 2^51 + ((limbs[1] / 2^5) % 2^40) * 2^56 + ((limbs[1] / 2^45) % 2^6) * 2^96
    assert(contribution == low_part * pow2(51) + ((limbs[1] as nat / pow2(5)) % pow2(40)) * pow2(56)
        + ((limbs[1] as nat / pow2(45)) % pow2(6)) * pow2(96));

    // Rewrite using 2^56 = 2^51 * 2^5 and 2^96 = 2^51 * 2^45
    assert(contribution == low_part * pow2(51) + ((limbs[1] as nat / pow2(5)) % pow2(40)) * (pow2(
        51,
    ) * pow2(5)) + ((limbs[1] as nat / pow2(45)) % pow2(6)) * (pow2(51) * pow2(45)));

    // Apply associativity to move pow2(51) to the left
    let middle_part = (limbs[1] as nat / pow2(5)) % pow2(40);
    let high_part = (limbs[1] as nat / pow2(45)) % pow2(6);

    assert(middle_part * (pow2(51) * pow2(5)) == (middle_part * pow2(51)) * pow2(5)) by {
        lemma_mul_is_associative(middle_part as int, pow2(51) as int, pow2(5) as int);
    }
    assert((middle_part * pow2(51)) * pow2(5) == pow2(51) * middle_part * pow2(5)) by {
        lemma_mul_is_commutative((middle_part * pow2(51)) as int, pow2(5) as int);
    }
    assert(pow2(51) * middle_part * pow2(5) == pow2(51) * (middle_part * pow2(5))) by {
        lemma_mul_is_associative(pow2(51) as int, middle_part as int, pow2(5) as int);
    }

    assert(high_part * (pow2(51) * pow2(45)) == (high_part * pow2(51)) * pow2(45)) by {
        lemma_mul_is_associative(high_part as int, pow2(51) as int, pow2(45) as int);
    }
    assert((high_part * pow2(51)) * pow2(45) == pow2(51) * high_part * pow2(45)) by {
        lemma_mul_is_commutative((high_part * pow2(51)) as int, pow2(45) as int);
    }
    assert(pow2(51) * high_part * pow2(45) == pow2(51) * (high_part * pow2(45))) by {
        lemma_mul_is_associative(pow2(51) as int, high_part as int, pow2(45) as int);
    }

    // Now factor out pow2(51)
    assert(contribution == low_part * pow2(51) + pow2(51) * (middle_part * pow2(5)) + pow2(51) * (
    high_part * pow2(45)));

    // Use distributivity to factor out pow2(51)
    assert(contribution == pow2(51) * (low_part + middle_part * pow2(5) + high_part * pow2(45)))
        by {
        lemma_mul_is_distributive_add(
            pow2(51) as int,
            low_part as int,
            (middle_part * pow2(5)) as int,
        );
        lemma_mul_is_distributive_add(
            pow2(51) as int,
            (low_part + middle_part * pow2(5)) as int,
            (high_part * pow2(45)) as int,
        );
    }

    // The part in parentheses equals limbs[1] by our reconstruction identity!
    assert(contribution == limbs[1] as nat * pow2(51)) by {
        lemma_mul_is_commutative(pow2(51) as int, limbs[1] as int);
    }

}

/// Proves that limb 2's byte contribution equals limbs[2] * pow2(102)
proof fn lemma_limb2_contribution_correctness(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[1] < pow2(51),  // Need limb 1 for boundary byte 12
        limbs[2] < pow2(51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        limb2_byte_contribution(limbs, bytes) == limbs[2] as nat * pow2(102),
{
    // Limb 2 stored in bytes 12-19, positioned at 2^102
    // - Byte 12 (high 2 bits): limbs[2]'s bits 0-1
    // - Bytes 13-18: limbs[2]'s bits 2-49 (48 bits)
    // - Byte 19 (low 1 bit): limbs[2]'s bit 50
    // Total: 2 + 48 + 1 = 51 bits
    lemma2_to64();
    lemma_pow2_adds(96, 6);  // 2^102 = 2^96 * 2^6
    assert(pow2(102) == pow2(96) * 64);

    // KEY INSIGHT: From bytes_match_limbs_packing:
    // bytes[13] = (limbs[2] >> 2) as u8
    // bytes[14] = (limbs[2] >> 10) as u8
    // ... and so on
    //
    // So limb2_byte_contribution is:
    //   (limbs[2] % 2^2) * 64 * 2^96 +             // Low 2 bits at position 2^102
    //   (limbs[2] >> 2 ... >> 42) * positions +    // Middle 48 bits at position 2^104
    //   (limbs[2] / 2^50) % 2 * 2^152              // High 1 bit at position 2^152
    //
    // This is limbs[2] * 2^102!

    // Step 1: Extract arithmetic values for bytes 13-18
    // These bytes come from limbs[2] >> 2, 10, 18, 26, 34, 42
    lemma_byte_from_limb_shift(limbs[2], 2, bytes[13]);

    lemma_byte_from_limb_shift(limbs[2], 10, bytes[14]);
    assert(bytes[14] as nat == (limbs[2] as nat / pow2(10)) % 256);

    lemma_byte_from_limb_shift(limbs[2], 18, bytes[15]);

    lemma_byte_from_limb_shift(limbs[2], 26, bytes[16]);

    lemma_byte_from_limb_shift(limbs[2], 34, bytes[17]);

    lemma_byte_from_limb_shift(limbs[2], 42, bytes[18]);

    // Step 2: Prove that bytes[13-18] reconstruct ((limbs[2] / 2^2) % 2^48) at position 2^104
    //
    // From lemma_byte_from_limb_shift, we have:
    // bytes[13] as nat == (limbs[2] / pow2(2)) % 256
    // bytes[14] as nat == (limbs[2] / pow2(10)) % 256
    // bytes[15] as nat == (limbs[2] / pow2(18)) % 256
    // bytes[16] as nat == (limbs[2] / pow2(26)) % 256
    // bytes[17] as nat == (limbs[2] / pow2(34)) % 256
    // bytes[18] as nat == (limbs[2] / pow2(42)) % 256
    //
    // The key insight: these bytes extract consecutive 8-bit chunks from (limbs[2] / 2^2)

    // First, rewrite the byte extractions in terms of (limbs[2] / 2^2)
    // bytes[13] == (limbs[2] / 2^2) / 2^0 % 256
    lemma_pow2_adds(0, 2);
    lemma_div_denominator(limbs[2] as int, pow2(2) as int, pow2(0) as int);

    // bytes[14] == (limbs[2] / 2^10) % 256 == (limbs[2] / 2^2) / 2^8 % 256
    lemma_pow2_adds(2, 8);
    lemma_div_denominator(limbs[2] as int, pow2(2) as int, pow2(8) as int);

    // bytes[15] == (limbs[2] / 2^18) % 256 == (limbs[2] / 2^2) / 2^16 % 256
    lemma_pow2_adds(2, 16);
    assert(pow2(2) * pow2(16) == pow2(18));
    lemma_div_denominator(limbs[2] as int, pow2(2) as int, pow2(16) as int);

    // bytes[16] == (limbs[2] / 2^26) % 256 == (limbs[2] / 2^2) / 2^24 % 256
    lemma_pow2_adds(2, 24);
    lemma_div_denominator(limbs[2] as int, pow2(2) as int, pow2(24) as int);

    // bytes[17] == (limbs[2] / 2^34) % 256 == (limbs[2] / 2^2) / 2^32 % 256
    lemma_pow2_adds(2, 32);
    lemma_div_denominator(limbs[2] as int, pow2(2) as int, pow2(32) as int);

    // bytes[18] == (limbs[2] / 2^42) % 256 == (limbs[2] / 2^2) / 2^40 % 256
    lemma_pow2_adds(2, 40);
    lemma_pow2_pos(40);
    lemma_div_denominator(limbs[2] as int, pow2(2) as int, pow2(40) as int);

    // Now handle the % 2^48 truncation
    // Since limbs[2] < 2^51, we have limbs[2] / 2^2 < 2^49
    lemma_div_bound(limbs[2] as nat, 2, 51);

    // The bytes extract bits at positions [0..8), [8..16), [16..24), [24..32), [32..40), [40..48)
    // from (limbs[2] / 2^2). Since all these bit positions are < 48, taking % 2^48
    // doesn't change the extracted bytes (same argument as limb 1).

    let middle_value = (limbs[2] as nat / pow2(2)) % pow2(48);

    // Prove middle_value < 2^48 (trivial by definition of %)
    lemma_pow2_pos(48);
    lemma_mod_bound(middle_value as int, pow2(48) as int);

    // Now prove that the bytes extract from middle_value
    let v = limbs[2] as nat / pow2(2);
    assert(bytes[13] as nat == v / pow2(0) % 256);

    // Use lemma_byte_extraction_commutes_with_mod to show extraction commutes with % 2^48
    // For byte at position k, we need k*8 + 8 <= 48
    lemma_byte_extraction_commutes_with_mod(v, 0, 48);  // 0*8 + 8 = 8 <= 48 ✓

    lemma_byte_extraction_commutes_with_mod(v, 1, 48);  // 1*8 + 8 = 16 <= 48 ✓

    lemma_byte_extraction_commutes_with_mod(v, 2, 48);  // 2*8 + 8 = 24 <= 48 ✓

    lemma_byte_extraction_commutes_with_mod(v, 3, 48);  // 3*8 + 8 = 32 <= 48 ✓

    lemma_byte_extraction_commutes_with_mod(v, 4, 48);  // 4*8 + 8 = 40 <= 48 ✓

    lemma_byte_extraction_commutes_with_mod(v, 5, 48);  // 5*8 + 8 = 48 <= 48 ✓
    assert(bytes[18] as nat == (middle_value / pow2(40)) % 256);

    // Now apply lemma_6_bytes_reconstruct
    lemma_6_bytes_reconstruct(
        middle_value,
        bytes[13],
        bytes[14],
        bytes[15],
        bytes[16],
        bytes[17],
        bytes[18],
    );

    // This gives us:
    assert(bytes[13] as nat * pow2(0) + bytes[14] as nat * pow2(8) + bytes[15] as nat * pow2(16)
        + bytes[16] as nat * pow2(24) + bytes[17] as nat * pow2(32) + bytes[18] as nat * pow2(40)
        == middle_value);

    // Now multiply both sides by 2^104 to get the bytes at their actual positions
    lemma_mul_is_distributive_add(
        pow2(104) as int,
        (bytes[13] as nat * pow2(0)) as int,
        (bytes[14] as nat * pow2(8)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(104) as int,
        (bytes[13] as nat * pow2(0) + bytes[14] as nat * pow2(8)) as int,
        (bytes[15] as nat * pow2(16)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(104) as int,
        (bytes[13] as nat * pow2(0) + bytes[14] as nat * pow2(8) + bytes[15] as nat * pow2(
            16,
        )) as int,
        (bytes[16] as nat * pow2(24)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(104) as int,
        (bytes[13] as nat * pow2(0) + bytes[14] as nat * pow2(8) + bytes[15] as nat * pow2(16)
            + bytes[16] as nat * pow2(24)) as int,
        (bytes[17] as nat * pow2(32)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(104) as int,
        (bytes[13] as nat * pow2(0) + bytes[14] as nat * pow2(8) + bytes[15] as nat * pow2(16)
            + bytes[16] as nat * pow2(24) + bytes[17] as nat * pow2(32)) as int,
        (bytes[18] as nat * pow2(40)) as int,
    );

    // Distribute the multiplication into each term
    lemma_mul_is_associative(bytes[13] as int, pow2(0) as int, pow2(104) as int);
    lemma_mul_is_associative(bytes[14] as int, pow2(8) as int, pow2(104) as int);
    lemma_mul_is_associative(bytes[15] as int, pow2(16) as int, pow2(104) as int);
    lemma_mul_is_associative(bytes[16] as int, pow2(24) as int, pow2(104) as int);
    lemma_mul_is_associative(bytes[17] as int, pow2(32) as int, pow2(104) as int);
    lemma_mul_is_associative(bytes[18] as int, pow2(40) as int, pow2(104) as int);

    // Simplify using pow2 addition: 2^104 * 2^k = 2^(104+k)
    lemma_pow2_adds(104, 0);

    lemma_pow2_adds(104, 8);

    lemma_pow2_adds(104, 16);

    lemma_pow2_adds(104, 24);

    lemma_pow2_adds(104, 32);

    lemma_pow2_adds(104, 40);

    // Now we need to show that the distributed sum equals middle_value * pow2(104)
    // We have: bytes[13] * 2^0 + ... + bytes[18] * 2^40 = middle_value
    // We distributed 2^104 into each term
    // Now we need to show the result

    // Build up the sum step by step
    let sum_0 = bytes[13] as nat * pow2(13 * 8);
    let sum_1 = sum_0 + bytes[14] as nat * pow2(14 * 8);
    let sum_2 = sum_1 + bytes[15] as nat * pow2(15 * 8);
    let sum_3 = sum_2 + bytes[16] as nat * pow2(16 * 8);
    let sum_4 = sum_3 + bytes[17] as nat * pow2(17 * 8);
    let sum_5 = sum_4 + bytes[18] as nat * pow2(18 * 8);

    // This should equal middle_value * pow2(104) by the distributivity we applied

    // Final result
    assert(bytes[13] as nat * pow2(13 * 8) + bytes[14] as nat * pow2(14 * 8) + bytes[15] as nat
        * pow2(15 * 8) + bytes[16] as nat * pow2(16 * 8) + bytes[17] as nat * pow2(17 * 8)
        + bytes[18] as nat * pow2(18 * 8) == middle_value * pow2(104));

    // Step 3: Handle boundary bytes
    // Low 2 bits (byte 12 high part): (limbs[2] % 2^2) * 64 * 2^96 = (limbs[2] % 2^2) * 2^102
    // High 1 bit (byte 19 low part): (limbs[2] / 2^50) % 2 * 2^152

    assert(64 * pow2(96) == pow2(102)) by {
        lemma_pow2_adds(96, 6);
    }

    // From the proof above, we have:
    let middle_bytes_sum = bytes[13] as nat * pow2(13 * 8) + bytes[14] as nat * pow2(14 * 8)
        + bytes[15] as nat * pow2(15 * 8) + bytes[16] as nat * pow2(16 * 8) + bytes[17] as nat
        * pow2(17 * 8) + bytes[18] as nat * pow2(18 * 8);

    let middle_value_at_position = ((limbs[2] as nat / pow2(2)) % pow2(48)) * pow2(104);

    // Substitute into contribution
    let contribution = limb2_byte_contribution(limbs, bytes);
    assert(contribution == ((limbs[2] as nat % pow2(2)) * 64) * pow2(96) + middle_bytes_sum + ((
    limbs[2] as nat / pow2(50)) % 2) * pow2(152));

    // Step 3: Prove the reconstruction identity for limbs[2]
    // limbs[2] = (limbs[2] % 2^2) + ((limbs[2] / 2^2) % 2^48) * 2^2 + ((limbs[2] / 2^50) % 2^1) * 2^50

    // This follows the same pattern as limb 1, but with different split points:
    // - Low 2 bits instead of 5
    // - Middle 48 bits instead of 40
    // - Split at 2, 50 instead of 5, 45

    // First, reconstruct limbs[2] / 2^2 from its low 48 bits and high part
    lemma_pow2_pos(48);
    let shifted_value = limbs[2] as nat / pow2(2);
    lemma_fundamental_div_mod(shifted_value as int, pow2(48) as int);
    // lemma_fundamental_div_mod gives: shifted_value == pow2(48) * (shifted_value / pow2(48)) + (shifted_value % pow2(48))
    // We need: shifted_value == (shifted_value % pow2(48)) + (shifted_value / pow2(48)) * pow2(48)
    assert(pow2(48) * (shifted_value / pow2(48)) == (shifted_value / pow2(48)) * pow2(48)) by {
        lemma_mul_is_commutative(pow2(48) as int, (shifted_value / pow2(48)) as int);
    }

    // Show that (limbs[2] / 2^2) / 2^48 = limbs[2] / 2^50
    lemma_div_denominator(limbs[2] as int, pow2(2) as int, pow2(48) as int);
    lemma_pow2_adds(2, 48);

    // So: limbs[2] / 2^2 = ((limbs[2] / 2^2) % 2^48) + (limbs[2] / 2^50) * 2^48
    assert(shifted_value == (shifted_value % pow2(48)) + (limbs[2] as nat / pow2(50)) * pow2(48));

    // Next, reconstruct limbs[2] from its low 2 bits and (limbs[2] / 2^2)
    lemma_pow2_pos(2);
    lemma_fundamental_div_mod(limbs[2] as int, pow2(2) as int);
    // lemma_fundamental_div_mod gives: limbs[2] == pow2(2) * (limbs[2] / pow2(2)) + (limbs[2] % pow2(2))
    assert(pow2(2) * shifted_value == shifted_value * pow2(2)) by {
        lemma_mul_is_commutative(pow2(2) as int, shifted_value as int);
    }

    // Substitute the reconstruction of shifted_value (limbs[2] / 2^2)
    assert(limbs[2] as nat == (limbs[2] as nat % pow2(2)) + ((shifted_value % pow2(48)) + (
    limbs[2] as nat / pow2(50)) * pow2(48)) * pow2(2));

    // Distribute the * 2^2
    assert(limbs[2] as nat == (limbs[2] as nat % pow2(2)) + (shifted_value % pow2(48)) * pow2(2) + (
    limbs[2] as nat / pow2(50)) * pow2(48) * pow2(2)) by {
        lemma_mul_is_distributive_add(
            pow2(2) as int,
            (shifted_value % pow2(48)) as int,
            (limbs[2] as nat / pow2(50) * pow2(48)) as int,
        );
    }

    // Use 2^48 * 2^2 = 2^50
    lemma_pow2_adds(48, 2);
    assert((limbs[2] as nat / pow2(50)) * pow2(48) * pow2(2) == (limbs[2] as nat / pow2(50)) * pow2(
        50,
    )) by {
        lemma_mul_is_associative(
            (limbs[2] as nat / pow2(50)) as int,
            pow2(48) as int,
            pow2(2) as int,
        );
    }

    assert(limbs[2] as nat == (limbs[2] as nat % pow2(2)) + ((limbs[2] as nat / pow2(2)) % pow2(48))
        * pow2(2) + (limbs[2] as nat / pow2(50)) * pow2(50));

    // Handle the % 2 on the high bit
    // Since limbs[2] < 2^51, we have limbs[2] / 2^50 < 2^1 = 2
    lemma_div_bound(limbs[2] as nat, 50, 51);
    assert(limbs[2] as nat / pow2(50) < pow2(1));
    lemma_small_mod(limbs[2] as nat / pow2(50), 2);

    // Therefore:
    assert(limbs[2] as nat == (limbs[2] as nat % pow2(2)) + ((limbs[2] as nat / pow2(2)) % pow2(48))
        * pow2(2) + ((limbs[2] as nat / pow2(50)) % 2) * pow2(50));

    // Step 4: Now connect the contribution to limbs[2] * 2^102
    // We have: contribution = ((limbs[2] % 2^2) * 64) * 2^96 + middle_bytes_sum + ((limbs[2] / 2^50) % 2) * 2^152
    // Where: middle_bytes_sum = ((limbs[2] / 2^2) % 2^48) * 2^104

    // First, simplify the low term: ((limbs[2] % 2^2) * 64) * 2^96 = (limbs[2] % 2^2) * (64 * 2^96) = (limbs[2] % 2^2) * 2^102
    // We proved earlier that 64 * 2^96 = 2^102
    let low_part = (limbs[2] as nat % pow2(2));
    assert(((limbs[2] as nat % pow2(2)) * 64) * pow2(96) == low_part * (64 * pow2(96))) by {
        lemma_mul_is_associative(low_part as int, 64, pow2(96) as int);
    }

    // So contribution = (limbs[2] % 2^2) * 2^102 + ((limbs[2] / 2^2) % 2^48) * 2^104 + ((limbs[2] / 2^50) % 2) * 2^152
    assert(contribution == low_part * pow2(102) + ((limbs[2] as nat / pow2(2)) % pow2(48)) * pow2(
        104,
    ) + ((limbs[2] as nat / pow2(50)) % 2) * pow2(152));

    // Rewrite using 2^104 = 2^102 * 2^2 and 2^152 = 2^102 * 2^50
    lemma_pow2_adds(102, 2);
    lemma_pow2_adds(102, 50);

    assert(contribution == low_part * pow2(102) + ((limbs[2] as nat / pow2(2)) % pow2(48)) * (pow2(
        102,
    ) * pow2(2)) + ((limbs[2] as nat / pow2(50)) % 2) * (pow2(102) * pow2(50)));

    // Apply associativity to move pow2(102) to the left
    let middle_part = (limbs[2] as nat / pow2(2)) % pow2(48);
    let high_part = (limbs[2] as nat / pow2(50)) % 2;

    assert(middle_part * (pow2(102) * pow2(2)) == (middle_part * pow2(102)) * pow2(2)) by {
        lemma_mul_is_associative(middle_part as int, pow2(102) as int, pow2(2) as int);
    }
    assert((middle_part * pow2(102)) * pow2(2) == pow2(102) * middle_part * pow2(2)) by {
        lemma_mul_is_commutative((middle_part * pow2(102)) as int, pow2(2) as int);
    }
    assert(pow2(102) * middle_part * pow2(2) == pow2(102) * (middle_part * pow2(2))) by {
        lemma_mul_is_associative(pow2(102) as int, middle_part as int, pow2(2) as int);
    }

    assert(high_part * (pow2(102) * pow2(50)) == (high_part * pow2(102)) * pow2(50)) by {
        lemma_mul_is_associative(high_part as int, pow2(102) as int, pow2(50) as int);
    }
    assert((high_part * pow2(102)) * pow2(50) == pow2(102) * high_part * pow2(50)) by {
        lemma_mul_is_commutative((high_part * pow2(102)) as int, pow2(50) as int);
    }
    assert(pow2(102) * high_part * pow2(50) == pow2(102) * (high_part * pow2(50))) by {
        lemma_mul_is_associative(pow2(102) as int, high_part as int, pow2(50) as int);
    }

    // Now factor out pow2(102)
    assert(contribution == low_part * pow2(102) + pow2(102) * (middle_part * pow2(2)) + pow2(102)
        * (high_part * pow2(50)));

    // Use distributivity to factor out pow2(102)
    assert(contribution == pow2(102) * (low_part + middle_part * pow2(2) + high_part * pow2(50)))
        by {
        lemma_mul_is_distributive_add(
            pow2(102) as int,
            low_part as int,
            (middle_part * pow2(2)) as int,
        );
        lemma_mul_is_distributive_add(
            pow2(102) as int,
            (low_part + middle_part * pow2(2)) as int,
            (high_part * pow2(50)) as int,
        );
    }

    // The part in parentheses equals limbs[2] by our reconstruction identity!
    assert(contribution == limbs[2] as nat * pow2(102)) by {
        lemma_mul_is_commutative(pow2(102) as int, limbs[2] as int);
    }

}

/// Proves that limb 3's byte contribution equals limbs[3] * pow2(153)
proof fn lemma_limb3_contribution_correctness(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[2] < pow2(51),  // Need limb 2 for boundary byte 19
        limbs[3] < pow2(51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        limb3_byte_contribution(limbs, bytes) == limbs[3] as nat * pow2(153),
{
    // Limb 3 stored in bytes 19-25, positioned at 2^153
    // - Byte 19 (high 7 bits): limbs[3]'s bits 0-6
    // - Bytes 20-24: limbs[3]'s bits 7-46 (40 bits)
    // - Byte 25 (low 4 bits): limbs[3]'s bits 47-50
    // Total: 7 + 40 + 4 = 51 bits
    lemma2_to64();
    lemma_pow2_adds(152, 1);  // 2^153 = 2^152 * 2

    // KEY INSIGHT: From bytes_match_limbs_packing:
    // bytes[20] = (limbs[3] >> 7) as u8
    // bytes[21] = (limbs[3] >> 15) as u8
    // ... and so on
    //
    // So limb3_byte_contribution is:
    //   (limbs[3] % 2^7) * 2 * 2^152 +              // Low 7 bits at position 2^153
    //   (limbs[3] >> 7 ... >> 39) * positions +     // Middle 40 bits at position 2^160
    //   (limbs[3] / 2^47) % 2^4 * 2^200             // High 4 bits at position 2^200
    //
    // This is limbs[3] * 2^153!

    // Step 1: Extract arithmetic values for bytes 20-24
    // These bytes come from limbs[3] >> 7, 15, 23, 31, 39
    lemma_byte_from_limb_shift(limbs[3], 7, bytes[20]);

    lemma_byte_from_limb_shift(limbs[3], 15, bytes[21]);

    lemma_byte_from_limb_shift(limbs[3], 23, bytes[22]);

    lemma_byte_from_limb_shift(limbs[3], 31, bytes[23]);

    lemma_byte_from_limb_shift(limbs[3], 39, bytes[24]);

    // Step 2: Prove that bytes[20-24] reconstruct ((limbs[3] / 2^7) % 2^40) at position 2^160
    //
    // From lemma_byte_from_limb_shift, we have:
    // bytes[20] as nat == (limbs[3] / pow2(7)) % 256
    // bytes[21] as nat == (limbs[3] / pow2(15)) % 256
    // bytes[22] as nat == (limbs[3] / pow2(23)) % 256
    // bytes[23] as nat == (limbs[3] / pow2(31)) % 256
    // bytes[24] as nat == (limbs[3] / pow2(39)) % 256
    //
    // The key insight: these bytes extract consecutive 8-bit chunks from (limbs[3] / 2^7)

    // First, rewrite the byte extractions in terms of (limbs[3] / 2^7)
    // bytes[20] == (limbs[3] / 2^7) / 2^0 % 256
    lemma_pow2_adds(0, 7);
    lemma_div_denominator(limbs[3] as int, pow2(7) as int, pow2(0) as int);
    assert(bytes[20] as nat == (limbs[3] as nat / pow2(7)) / pow2(0) % 256);

    // bytes[21] == (limbs[3] / 2^15) % 256 == (limbs[3] / 2^7) / 2^8 % 256
    lemma_pow2_adds(7, 8);
    lemma_div_denominator(limbs[3] as int, pow2(7) as int, pow2(8) as int);
    assert(limbs[3] as nat / pow2(15) == (limbs[3] as nat / pow2(7)) / pow2(8));
    assert(bytes[21] as nat == (limbs[3] as nat / pow2(7)) / pow2(8) % 256);

    // bytes[22] == (limbs[3] / 2^23) % 256 == (limbs[3] / 2^7) / 2^16 % 256
    lemma_pow2_adds(7, 16);
    assert(pow2(7) * pow2(16) == pow2(23));
    lemma_div_denominator(limbs[3] as int, pow2(7) as int, pow2(16) as int);
    assert(limbs[3] as nat / pow2(23) == (limbs[3] as nat / pow2(7)) / pow2(16));

    // bytes[23] == (limbs[3] / 2^31) % 256 == (limbs[3] / 2^7) / 2^24 % 256
    lemma_pow2_adds(7, 24);
    lemma_div_denominator(limbs[3] as int, pow2(7) as int, pow2(24) as int);

    // bytes[24] == (limbs[3] / 2^39) % 256 == (limbs[3] / 2^7) / 2^32 % 256
    lemma_pow2_adds(7, 32);
    lemma_pow2_pos(32);
    lemma_div_denominator(limbs[3] as int, pow2(7) as int, pow2(32) as int);
    assert(limbs[3] as nat / pow2(39) == (limbs[3] as nat / pow2(7)) / pow2(32));
    assert(bytes[24] as nat == (limbs[3] as nat / pow2(7)) / pow2(32) % 256);

    // Now handle the % 2^40 truncation
    // Since limbs[3] < 2^51, we have limbs[3] / 2^7 < 2^44
    lemma_div_bound(limbs[3] as nat, 7, 51);

    // The bytes extract bits at positions [0..8), [8..16), [16..24), [24..32), [32..40)
    // from (limbs[3] / 2^7). Since all these bit positions are < 40, taking % 2^40
    // doesn't change the extracted bytes (same argument as limbs 1 & 2).

    let middle_value = (limbs[3] as nat / pow2(7)) % pow2(40);

    // Prove middle_value < 2^40 (trivial by definition of %)
    lemma_pow2_pos(40);
    lemma_mod_bound(middle_value as int, pow2(40) as int);

    // Now prove that the bytes extract from middle_value
    let v = limbs[3] as nat / pow2(7);
    assert(bytes[23] as nat == v / pow2(24) % 256);
    assert(bytes[24] as nat == v / pow2(32) % 256);

    // Use lemma_byte_extraction_commutes_with_mod to show extraction commutes with % 2^40
    // For byte at position k, we need k*8 + 8 <= 40
    lemma_byte_extraction_commutes_with_mod(v, 0, 40);  // 0*8 + 8 = 8 <= 40 ✓
    assert(bytes[20] as nat == (middle_value / pow2(0)) % 256);

    lemma_byte_extraction_commutes_with_mod(v, 1, 40);  // 1*8 + 8 = 16 <= 40 ✓

    lemma_byte_extraction_commutes_with_mod(v, 2, 40);  // 2*8 + 8 = 24 <= 40 ✓

    lemma_byte_extraction_commutes_with_mod(v, 3, 40);  // 3*8 + 8 = 32 <= 40 ✓

    lemma_byte_extraction_commutes_with_mod(v, 4, 40);  // 4*8 + 8 = 40 <= 40 ✓

    // Now apply lemma_5_bytes_reconstruct
    lemma_5_bytes_reconstruct(middle_value, bytes[20], bytes[21], bytes[22], bytes[23], bytes[24]);

    // This gives us:
    assert(bytes[20] as nat * pow2(0) + bytes[21] as nat * pow2(8) + bytes[22] as nat * pow2(16)
        + bytes[23] as nat * pow2(24) + bytes[24] as nat * pow2(32) == middle_value);

    // Now multiply both sides by 2^160 to get the bytes at their actual positions
    lemma_mul_is_distributive_add(
        pow2(160) as int,
        (bytes[20] as nat * pow2(0)) as int,
        (bytes[21] as nat * pow2(8)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(160) as int,
        (bytes[20] as nat * pow2(0) + bytes[21] as nat * pow2(8)) as int,
        (bytes[22] as nat * pow2(16)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(160) as int,
        (bytes[20] as nat * pow2(0) + bytes[21] as nat * pow2(8) + bytes[22] as nat * pow2(
            16,
        )) as int,
        (bytes[23] as nat * pow2(24)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(160) as int,
        (bytes[20] as nat * pow2(0) + bytes[21] as nat * pow2(8) + bytes[22] as nat * pow2(16)
            + bytes[23] as nat * pow2(24)) as int,
        (bytes[24] as nat * pow2(32)) as int,
    );

    // Distribute the multiplication into each term
    lemma_mul_is_associative(bytes[20] as int, pow2(0) as int, pow2(160) as int);
    lemma_mul_is_associative(bytes[21] as int, pow2(8) as int, pow2(160) as int);
    lemma_mul_is_associative(bytes[22] as int, pow2(16) as int, pow2(160) as int);
    lemma_mul_is_associative(bytes[23] as int, pow2(24) as int, pow2(160) as int);
    lemma_mul_is_associative(bytes[24] as int, pow2(32) as int, pow2(160) as int);

    // Simplify using pow2 addition: 2^160 * 2^k = 2^(160+k)
    lemma_pow2_adds(160, 0);

    lemma_pow2_adds(160, 8);

    lemma_pow2_adds(160, 16);
    assert(pow2(160) * pow2(16) == pow2(176));

    lemma_pow2_adds(160, 24);

    lemma_pow2_adds(160, 32);

    // Final result
    assert(bytes[20] as nat * pow2(20 * 8) + bytes[21] as nat * pow2(21 * 8) + bytes[22] as nat
        * pow2(22 * 8) + bytes[23] as nat * pow2(23 * 8) + bytes[24] as nat * pow2(24 * 8)
        == middle_value * pow2(160));

    // Step 3: Handle boundary bytes
    // Low 7 bits (byte 19 high part): (limbs[3] % 2^7) * 2 * 2^152 = (limbs[3] % 2^7) * 2^153
    // High 4 bits (byte 25 low part): (limbs[3] / 2^47) % 2^4 * 2^200

    assert(2 * pow2(152) == pow2(153)) by {
        lemma_pow2_adds(152, 1);
    }

    // From the proof above, we have:
    let middle_bytes_sum = bytes[20] as nat * pow2(20 * 8) + bytes[21] as nat * pow2(21 * 8)
        + bytes[22] as nat * pow2(22 * 8) + bytes[23] as nat * pow2(23 * 8) + bytes[24] as nat
        * pow2(24 * 8);

    let middle_value_at_position = ((limbs[3] as nat / pow2(7)) % pow2(40)) * pow2(160);

    // Substitute into contribution
    let contribution = limb3_byte_contribution(limbs, bytes);
    assert(contribution == ((limbs[3] as nat % pow2(7)) * 2) * pow2(152) + middle_bytes_sum + ((
    limbs[3] as nat / pow2(47)) % pow2(4)) * pow2(200));

    assert(contribution == ((limbs[3] as nat % pow2(7)) * 2) * pow2(152) + middle_value_at_position
        + ((limbs[3] as nat / pow2(47)) % pow2(4)) * pow2(200));

    // Step 3: Prove the reconstruction identity for limbs[3]
    // limbs[3] = (limbs[3] % 2^7) + ((limbs[3] / 2^7) % 2^40) * 2^7 + ((limbs[3] / 2^47) % 2^4) * 2^47

    // First, reconstruct limbs[3] / 2^7 from its low 40 bits and high part
    lemma_pow2_pos(40);
    let shifted_value = limbs[3] as nat / pow2(7);
    lemma_fundamental_div_mod(shifted_value as int, pow2(40) as int);
    assert(pow2(40) * (shifted_value / pow2(40)) == (shifted_value / pow2(40)) * pow2(40)) by {
        lemma_mul_is_commutative(pow2(40) as int, (shifted_value / pow2(40)) as int);
    }

    // Show that (limbs[3] / 2^7) / 2^40 = limbs[3] / 2^47
    lemma_div_denominator(limbs[3] as int, pow2(7) as int, pow2(40) as int);
    lemma_pow2_adds(7, 40);

    // So: limbs[3] / 2^7 = ((limbs[3] / 2^7) % 2^40) + (limbs[3] / 2^47) * 2^40
    assert(shifted_value == (shifted_value % pow2(40)) + (limbs[3] as nat / pow2(47)) * pow2(40));

    // Next, reconstruct limbs[3] from its low 7 bits and (limbs[3] / 2^7)
    lemma_pow2_pos(7);
    lemma_fundamental_div_mod(limbs[3] as int, pow2(7) as int);
    assert(pow2(7) * shifted_value == shifted_value * pow2(7)) by {
        lemma_mul_is_commutative(pow2(7) as int, shifted_value as int);
    }

    // Substitute the reconstruction of shifted_value (limbs[3] / 2^7)
    assert(limbs[3] as nat == (limbs[3] as nat % pow2(7)) + ((shifted_value % pow2(40)) + (
    limbs[3] as nat / pow2(47)) * pow2(40)) * pow2(7));

    // Distribute the * 2^7
    assert(limbs[3] as nat == (limbs[3] as nat % pow2(7)) + (shifted_value % pow2(40)) * pow2(7) + (
    limbs[3] as nat / pow2(47)) * pow2(40) * pow2(7)) by {
        lemma_mul_is_distributive_add(
            pow2(7) as int,
            (shifted_value % pow2(40)) as int,
            (limbs[3] as nat / pow2(47) * pow2(40)) as int,
        );
    }

    // Use 2^40 * 2^7 = 2^47
    lemma_pow2_adds(40, 7);
    assert((limbs[3] as nat / pow2(47)) * pow2(40) * pow2(7) == (limbs[3] as nat / pow2(47)) * pow2(
        47,
    )) by {
        lemma_mul_is_associative(
            (limbs[3] as nat / pow2(47)) as int,
            pow2(40) as int,
            pow2(7) as int,
        );
    }

    assert(limbs[3] as nat == (limbs[3] as nat % pow2(7)) + ((limbs[3] as nat / pow2(7)) % pow2(40))
        * pow2(7) + (limbs[3] as nat / pow2(47)) * pow2(47));

    // Handle the % 2^4 on the high bits
    // Since limbs[3] < 2^51, we have limbs[3] / 2^47 < 2^4
    lemma_div_bound(limbs[3] as nat, 47, 51);
    lemma_small_mod(limbs[3] as nat / pow2(47), pow2(4));

    // Therefore:
    assert(limbs[3] as nat == (limbs[3] as nat % pow2(7)) + ((limbs[3] as nat / pow2(7)) % pow2(40))
        * pow2(7) + ((limbs[3] as nat / pow2(47)) % pow2(4)) * pow2(47));

    // Step 4: Now connect the contribution to limbs[3] * 2^153
    // We have: contribution = ((limbs[3] % 2^7) * 2) * 2^152 + middle_value_at_position + ((limbs[3] / 2^47) % 2^4) * 2^200
    // Where: middle_value_at_position = ((limbs[3] / 2^7) % 2^40) * 2^160

    // First, simplify the low term: ((limbs[3] % 2^7) * 2) * 2^152 = (limbs[3] % 2^7) * (2 * 2^152) = (limbs[3] % 2^7) * 2^153
    // We proved earlier that 2 * 2^152 = 2^153
    let low_part = (limbs[3] as nat % pow2(7));
    assert(((limbs[3] as nat % pow2(7)) * 2) * pow2(152) == low_part * (2 * pow2(152))) by {
        lemma_mul_is_associative(low_part as int, 2, pow2(152) as int);
    }

    // So contribution = (limbs[3] % 2^7) * 2^153 + ((limbs[3] / 2^7) % 2^40) * 2^160 + ((limbs[3] / 2^47) % 2^4) * 2^200
    assert(contribution == low_part * pow2(153) + ((limbs[3] as nat / pow2(7)) % pow2(40)) * pow2(
        160,
    ) + ((limbs[3] as nat / pow2(47)) % pow2(4)) * pow2(200));

    // Rewrite using 2^160 = 2^153 * 2^7 and 2^200 = 2^153 * 2^47
    lemma_pow2_adds(153, 7);
    lemma_pow2_adds(153, 47);

    assert(contribution == low_part * pow2(153) + ((limbs[3] as nat / pow2(7)) % pow2(40)) * (pow2(
        153,
    ) * pow2(7)) + ((limbs[3] as nat / pow2(47)) % pow2(4)) * (pow2(153) * pow2(47)));

    // Apply associativity to move pow2(153) to the left
    let middle_part = (limbs[3] as nat / pow2(7)) % pow2(40);
    let high_part = (limbs[3] as nat / pow2(47)) % pow2(4);

    assert(middle_part * (pow2(153) * pow2(7)) == (middle_part * pow2(153)) * pow2(7)) by {
        lemma_mul_is_associative(middle_part as int, pow2(153) as int, pow2(7) as int);
    }
    assert((middle_part * pow2(153)) * pow2(7) == pow2(153) * middle_part * pow2(7)) by {
        lemma_mul_is_commutative((middle_part * pow2(153)) as int, pow2(7) as int);
    }
    assert(pow2(153) * middle_part * pow2(7) == pow2(153) * (middle_part * pow2(7))) by {
        lemma_mul_is_associative(pow2(153) as int, middle_part as int, pow2(7) as int);
    }

    assert(high_part * (pow2(153) * pow2(47)) == (high_part * pow2(153)) * pow2(47)) by {
        lemma_mul_is_associative(high_part as int, pow2(153) as int, pow2(47) as int);
    }
    assert((high_part * pow2(153)) * pow2(47) == pow2(153) * high_part * pow2(47)) by {
        lemma_mul_is_commutative((high_part * pow2(153)) as int, pow2(47) as int);
    }
    assert(pow2(153) * high_part * pow2(47) == pow2(153) * (high_part * pow2(47))) by {
        lemma_mul_is_associative(pow2(153) as int, high_part as int, pow2(47) as int);
    }

    // Now factor out pow2(153)
    assert(contribution == low_part * pow2(153) + pow2(153) * (middle_part * pow2(7)) + pow2(153)
        * (high_part * pow2(47)));

    // Use distributivity to factor out pow2(153)
    assert(contribution == pow2(153) * (low_part + middle_part * pow2(7) + high_part * pow2(47)))
        by {
        lemma_mul_is_distributive_add(
            pow2(153) as int,
            low_part as int,
            (middle_part * pow2(7)) as int,
        );
        lemma_mul_is_distributive_add(
            pow2(153) as int,
            (low_part + middle_part * pow2(7)) as int,
            (high_part * pow2(47)) as int,
        );
    }

    // The part in parentheses equals limbs[3] by our reconstruction identity!
    assert(contribution == limbs[3] as nat * pow2(153)) by {
        lemma_mul_is_commutative(pow2(153) as int, limbs[3] as int);
    }

}

/// Proves that limb 4's byte contribution equals limbs[4] * pow2(204)
#[verifier::spinoff_prover]
proof fn lemma_limb4_contribution_correctness(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[3] < pow2(51),  // Need limb 3 for boundary byte 25
        limbs[4] < pow2(51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        limb4_byte_contribution(limbs, bytes) == limbs[4] as nat * pow2(204),
{
    // Limb 4 stored in bytes 25-31, positioned at 2^204
    // - Byte 25 (high 4 bits): limbs[4]'s bits 0-3
    // - Bytes 26-31: limbs[4]'s bits 4-51 (48 bits, but only 47 used)
    // Total: 4 + 47 = 51 bits (limbs[4] < 2^51)
    lemma2_to64();
    lemma_pow2_adds(200, 4);  // 2^204 = 2^200 * 2^4

    // KEY INSIGHT: From bytes_match_limbs_packing:
    // bytes[26] = (limbs[4] >> 4) as u8
    // bytes[27] = (limbs[4] >> 12) as u8
    // ... and so on
    //
    // So limb4_byte_contribution is:
    //   (limbs[4] % 2^4) * 16 * 2^200 +             // Low 4 bits at position 2^204
    //   (limbs[4] >> 4 ... >> 44) * positions       // High 47 bits at position 2^208
    //
    // This is limbs[4] * 2^204!

    // Step 1: Extract arithmetic values for bytes 26-31
    // These bytes come from limbs[4] >> 4, 12, 20, 28, 36, 44
    lemma_byte_from_limb_shift(limbs[4], 4, bytes[26]);
    assert(bytes[26] as nat == (limbs[4] as nat / pow2(4)) % 256);

    lemma_byte_from_limb_shift(limbs[4], 12, bytes[27]);

    lemma_byte_from_limb_shift(limbs[4], 20, bytes[28]);

    lemma_byte_from_limb_shift(limbs[4], 28, bytes[29]);

    lemma_byte_from_limb_shift(limbs[4], 36, bytes[30]);

    lemma_byte_from_limb_shift(limbs[4], 44, bytes[31]);

    // Step 2: Prove that bytes[26-31] reconstruct (limbs[4] / 2^4) at position 2^208
    //
    // From lemma_byte_from_limb_shift, we have:
    // bytes[26] as nat == (limbs[4] / pow2(4)) % 256
    // bytes[27] as nat == (limbs[4] / pow2(12)) % 256
    // bytes[28] as nat == (limbs[4] / pow2(20)) % 256
    // bytes[29] as nat == (limbs[4] / pow2(28)) % 256
    // bytes[30] as nat == (limbs[4] / pow2(36)) % 256
    // bytes[31] as nat == (limbs[4] / pow2(44)) % 256
    //
    // The key insight: these bytes extract consecutive 8-bit chunks from (limbs[4] / 2^4)

    // First, rewrite the byte extractions in terms of (limbs[4] / 2^4)
    // bytes[26] == (limbs[4] / 2^4) / 2^0 % 256
    lemma_pow2_adds(0, 4);
    assert(pow2(4) * pow2(0) == pow2(4));
    lemma_div_denominator(limbs[4] as int, pow2(4) as int, pow2(0) as int);

    // bytes[27] == (limbs[4] / 2^12) % 256 == (limbs[4] / 2^4) / 2^8 % 256
    lemma_pow2_adds(4, 8);
    lemma_div_denominator(limbs[4] as int, pow2(4) as int, pow2(8) as int);

    // bytes[28] == (limbs[4] / 2^20) % 256 == (limbs[4] / 2^4) / 2^16 % 256
    lemma_pow2_adds(4, 16);
    lemma_div_denominator(limbs[4] as int, pow2(4) as int, pow2(16) as int);

    // bytes[29] == (limbs[4] / 2^28) % 256 == (limbs[4] / 2^4) / 2^24 % 256
    lemma_pow2_adds(4, 24);
    lemma_div_denominator(limbs[4] as int, pow2(4) as int, pow2(24) as int);

    // bytes[30] == (limbs[4] / 2^36) % 256 == (limbs[4] / 2^4) / 2^32 % 256
    lemma_pow2_adds(4, 32);
    lemma_pow2_pos(32);
    lemma_div_denominator(limbs[4] as int, pow2(4) as int, pow2(32) as int);

    // bytes[31] == (limbs[4] / 2^44) % 256 == (limbs[4] / 2^4) / 2^40 % 256
    lemma_pow2_adds(4, 40);
    lemma_pow2_pos(40);
    lemma_div_denominator(limbs[4] as int, pow2(4) as int, pow2(40) as int);

    // Since limbs[4] < 2^51, we have limbs[4] / 2^4 < 2^47
    lemma_div_bound(limbs[4] as nat, 4, 51);

    // The value (limbs[4] / 2^4) is 47 bits, and we have 6 bytes (48 bits capacity)
    // So we can directly use it without modulo truncation!
    let high_value = limbs[4] as nat / pow2(4);

    // Prove high_value < 2^48 (we have 2^47, which is less than 2^48)
    assert(high_value < pow2(47));
    assert(pow2(47) < pow2(48)) by {
        lemma_pow2_adds(47, 1);
        assert(pow2(48) == pow2(47) * 2);
    }

    // Now apply lemma_6_bytes_reconstruct
    lemma_6_bytes_reconstruct(
        high_value,
        bytes[26],
        bytes[27],
        bytes[28],
        bytes[29],
        bytes[30],
        bytes[31],
    );

    // This gives us:
    assert(bytes[26] as nat * pow2(0) + bytes[27] as nat * pow2(8) + bytes[28] as nat * pow2(16)
        + bytes[29] as nat * pow2(24) + bytes[30] as nat * pow2(32) + bytes[31] as nat * pow2(40)
        == high_value);

    // Now multiply both sides by 2^208 to get the bytes at their actual positions
    lemma_mul_is_distributive_add(
        pow2(208) as int,
        (bytes[26] as nat * pow2(0)) as int,
        (bytes[27] as nat * pow2(8)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(208) as int,
        (bytes[26] as nat * pow2(0) + bytes[27] as nat * pow2(8)) as int,
        (bytes[28] as nat * pow2(16)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(208) as int,
        (bytes[26] as nat * pow2(0) + bytes[27] as nat * pow2(8) + bytes[28] as nat * pow2(
            16,
        )) as int,
        (bytes[29] as nat * pow2(24)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(208) as int,
        (bytes[26] as nat * pow2(0) + bytes[27] as nat * pow2(8) + bytes[28] as nat * pow2(16)
            + bytes[29] as nat * pow2(24)) as int,
        (bytes[30] as nat * pow2(32)) as int,
    );
    lemma_mul_is_distributive_add(
        pow2(208) as int,
        (bytes[26] as nat * pow2(0) + bytes[27] as nat * pow2(8) + bytes[28] as nat * pow2(16)
            + bytes[29] as nat * pow2(24) + bytes[30] as nat * pow2(32)) as int,
        (bytes[31] as nat * pow2(40)) as int,
    );

    // Distribute the multiplication into each term
    lemma_mul_is_associative(bytes[26] as int, pow2(0) as int, pow2(208) as int);
    lemma_mul_is_associative(bytes[27] as int, pow2(8) as int, pow2(208) as int);
    lemma_mul_is_associative(bytes[28] as int, pow2(16) as int, pow2(208) as int);
    lemma_mul_is_associative(bytes[29] as int, pow2(24) as int, pow2(208) as int);
    lemma_mul_is_associative(bytes[30] as int, pow2(32) as int, pow2(208) as int);
    lemma_mul_is_associative(bytes[31] as int, pow2(40) as int, pow2(208) as int);

    // Simplify using pow2 addition: 2^208 * 2^k = 2^(208+k)
    lemma_pow2_adds(208, 0);

    lemma_pow2_adds(208, 8);

    lemma_pow2_adds(208, 16);

    lemma_pow2_adds(208, 24);

    lemma_pow2_adds(208, 32);

    lemma_pow2_adds(208, 40);

    // Final result
    assert(bytes[26] as nat * pow2(26 * 8) + bytes[27] as nat * pow2(27 * 8) + bytes[28] as nat
        * pow2(28 * 8) + bytes[29] as nat * pow2(29 * 8) + bytes[30] as nat * pow2(30 * 8)
        + bytes[31] as nat * pow2(31 * 8) == high_value * pow2(208));

    // Step 3: Handle boundary byte
    // Low 4 bits (byte 25 high part): (limbs[4] % 2^4) * 16 * 2^200 = (limbs[4] % 2^4) * 2^204

    assert(16 * pow2(200) == pow2(204)) by {
        lemma_pow2_adds(200, 4);
    }

    // From the proof above, we have:
    let high_bytes_sum = bytes[26] as nat * pow2(26 * 8) + bytes[27] as nat * pow2(27 * 8)
        + bytes[28] as nat * pow2(28 * 8) + bytes[29] as nat * pow2(29 * 8) + bytes[30] as nat
        * pow2(30 * 8) + bytes[31] as nat * pow2(31 * 8);

    let high_value_at_position = (limbs[4] as nat / pow2(4)) * pow2(208);

    // Substitute into contribution
    let contribution = limb4_byte_contribution(limbs, bytes);
    assert(contribution == ((limbs[4] as nat % pow2(4)) * 16) * pow2(200) + high_bytes_sum);

    assert(contribution == ((limbs[4] as nat % pow2(4)) * 16) * pow2(200) + high_value_at_position);

    // Step 3: Prove the reconstruction identity for limbs[4]
    // limbs[4] = (limbs[4] % 2^4) + (limbs[4] / 2^4) * 2^4
    // This is just the fundamental div-mod property!

    lemma_pow2_pos(4);
    lemma_fundamental_div_mod(limbs[4] as int, pow2(4) as int);
    assert(pow2(4) * (limbs[4] as nat / pow2(4)) == (limbs[4] as nat / pow2(4)) * pow2(4)) by {
        lemma_mul_is_commutative(pow2(4) as int, (limbs[4] as nat / pow2(4)) as int);
    }

    // Step 4: Now connect the contribution to limbs[4] * 2^204
    // We have: contribution = ((limbs[4] % 2^4) * 16) * 2^200 + (limbs[4] / 2^4) * 2^208

    // First, simplify the low term: ((limbs[4] % 2^4) * 16) * 2^200 = (limbs[4] % 2^4) * (16 * 2^200) = (limbs[4] % 2^4) * 2^204
    // We proved earlier that 16 * 2^200 = 2^204
    let low_part = (limbs[4] as nat % pow2(4));
    assert(((limbs[4] as nat % pow2(4)) * 16) * pow2(200) == low_part * (16 * pow2(200))) by {
        lemma_mul_is_associative(low_part as int, 16, pow2(200) as int);
    }

    // So contribution = (limbs[4] % 2^4) * 2^204 + (limbs[4] / 2^4) * 2^208
    assert(contribution == low_part * pow2(204) + (limbs[4] as nat / pow2(4)) * pow2(208));

    // Rewrite using 2^208 = 2^204 * 2^4
    lemma_pow2_adds(204, 4);

    assert(contribution == low_part * pow2(204) + (limbs[4] as nat / pow2(4)) * (pow2(204) * pow2(
        4,
    )));

    // Apply associativity to move pow2(204) to the left
    let high_part = limbs[4] as nat / pow2(4);

    assert(high_part * (pow2(204) * pow2(4)) == (high_part * pow2(204)) * pow2(4)) by {
        lemma_mul_is_associative(high_part as int, pow2(204) as int, pow2(4) as int);
    }
    assert((high_part * pow2(204)) * pow2(4) == pow2(204) * high_part * pow2(4)) by {
        lemma_mul_is_commutative((high_part * pow2(204)) as int, pow2(4) as int);
    }
    assert(pow2(204) * high_part * pow2(4) == pow2(204) * (high_part * pow2(4))) by {
        lemma_mul_is_associative(pow2(204) as int, high_part as int, pow2(4) as int);
    }

    // Now factor out pow2(204)
    assert(contribution == low_part * pow2(204) + pow2(204) * (high_part * pow2(4)));

    // Use distributivity to factor out pow2(204)
    assert(contribution == pow2(204) * (low_part + high_part * pow2(4))) by {
        lemma_mul_is_distributive_add(
            pow2(204) as int,
            low_part as int,
            (high_part * pow2(4)) as int,
        );
    }

    // The part in parentheses equals limbs[4] by our reconstruction identity!
    assert(contribution == limbs[4] as nat * pow2(204)) by {
        lemma_mul_is_commutative(pow2(204) as int, limbs[4] as int);
    }

}

// ============================================================================
// Boundary Byte Reconstruction Lemmas
// ============================================================================
// These lemmas prove that the split parts of boundary bytes combine to give
// the full byte value
//
// Key insight: Boundary bytes are formed by OR'ing bits from two adjacent limbs.
// The proof uses the Modular Bit Partitioning Theorem to show that the bitwise
// operations correspond exactly to the arithmetic formula.
proof fn lemma_boundary_byte_combines(
    low_limb: u64,
    high_limb: u64,
    byte: u8,
    low_shift: nat,
    low_bits: nat,
)
    requires
        low_limb < pow2(51),
        high_limb < pow2(51),
        low_bits < 8,
        low_shift + low_bits == 51,  // Strengthened from <= to == (all call sites use equality)
        byte == ((low_limb >> low_shift) | (high_limb << low_bits)) as u8,
    ensures
        byte as nat == (low_limb as nat / pow2(low_shift)) % pow2(low_bits) + (high_limb as nat
            % pow2((8 - low_bits) as nat)) * pow2(low_bits),
{
    lemma2_to64();

    // Establish that pow2 values fit in u64
    assert(pow2(low_shift) <= u64::MAX as nat) by {
        lemma_pow2_strictly_increases(low_shift, 64);
    }

    assert(pow2(low_bits) <= u64::MAX as nat) by {
        lemma_pow2_strictly_increases(low_bits, 64);
    }

    // Step 1: Convert shifts to arithmetic operations
    let low_part = low_limb >> low_shift;
    let high_part = high_limb << low_bits;

    // Prove high_part doesn't overflow
    assert(high_limb as nat * pow2(low_bits) <= u64::MAX as nat) by {
        assert(pow2(51) * pow2(7) <= pow2(64) - 1) by {
            lemma_pow2_adds(51, 7);
            lemma_pow2_strictly_increases(58, 64);
        }
        if low_bits < 7 {
            lemma_pow2_strictly_increases(low_bits, 7);
        }
        mul_le(high_limb as nat, (pow2(51) - 1) as nat, pow2(low_bits), pow2(7));
    }

    assert(high_part == high_limb * (pow2(low_bits) as u64)) by {
        lemma_u64_shl_is_mul(high_limb, low_bits as u64);
    }

    // Step 2: Prove preconditions for bit_or_is_plus
    // Need: low_part < 1u64 << low_bits AND high_limb <= (u64::MAX >> low_bits)

    // Prove low_part < 1u64 << low_bits
    // First, prove low_part as nat < pow2(low_bits)
    assert((low_part as nat) < pow2(low_bits)) by {
        // Step 1: low_part == (low_limb >> low_shift) == low_limb / pow2(low_shift)
        lemma_u64_shr_is_div(low_limb, low_shift as u64);

        // Step 2: low_limb / pow2(low_shift) < pow2(51 - low_shift)
        // We'll use lemma_div_strictly_bounded: if x < a * b then x / a < b
        // First, show that pow2(51) = pow2(low_shift) * pow2(51 - low_shift)
        lemma_pow2_adds(low_shift, (51 - low_shift) as nat);

        // Now apply lemma_div_strictly_bounded with:
        // x = low_limb, a = pow2(low_shift), b = pow2(51 - low_shift)
        // We have: low_limb < pow2(51) = a * b, so low_limb / a < b
        lemma_pow2_pos(low_shift);
        lemma_div_strictly_bounded(
            low_limb as int,
            pow2(low_shift) as int,
            pow2((51 - low_shift) as nat) as int,
        );

        // Step 3: Since low_shift + low_bits == 51, we have 51 - low_shift == low_bits
    }
    // Now use that to prove low_part < 1u64 << low_bits
    assert(low_part < 1u64 << low_bits) by {
        assert(1u64 << low_bits == (pow2(low_bits) as u64)) by {
            shift_is_pow2(low_bits);
        }
    }

    // Prove high_limb <= (u64::MAX >> low_bits)
    // Strategy: Show high_limb * pow2(low_bits) <= u64::MAX, then conclude high_limb <= u64::MAX >> low_bits
    assert(high_limb <= (u64::MAX >> low_bits)) by {
        // Step 1: Show high_limb * pow2(low_bits) <= u64::MAX
        assert(high_limb * (pow2(low_bits) as u64) <= u64::MAX) by {
            // We have: high_limb < pow2(51) and low_bits < 8
            // The maximum value is when high_limb = pow2(51) - 1 and low_bits = 7
            // So we need: pow2(51) * pow2(7) <= pow2(64)
            assert(pow2(51) * pow2(7) <= pow2(64) - 1) by {
                lemma_pow2_adds(51, 7);
                assert(pow2(58) <= pow2(64) - 1) by {
                    lemma_pow2_strictly_increases(58, 64);
                }
            }
            // Since low_bits < 8, we have low_bits <= 7, so pow2(low_bits) <= pow2(7)
            if low_bits < 7 {
                lemma_pow2_strictly_increases(low_bits, 7);
            }
            // Use mul_le to conclude: high_limb * pow2(low_bits) <= (pow2(51)-1) * pow2(7) <= pow2(64)-1

            mul_le(high_limb as nat, (pow2(51) - 1) as nat, pow2(low_bits), pow2(7));
        }

        // Step 2: From high_limb * pow2(low_bits) <= u64::MAX, conclude high_limb <= u64::MAX / pow2(low_bits)
        // Use lemma_mul_le_implies_div_le: if a * b <= c and b > 0, then a <= c / b
        lemma_pow2_pos(low_bits);
        lemma_mul_le_implies_div_le(high_limb as nat, pow2(low_bits), u64::MAX as nat);

        // Since >> is division: u64::MAX / pow2(low_bits) == u64::MAX >> low_bits
        lemma_u64_shr_is_div(u64::MAX, low_bits as u64);
    }
    // Step 3: Apply bit_or_is_plus to show OR equals addition
    assert(low_part | high_part == low_part + high_part) by {
        bit_or_is_plus(low_part, high_limb, low_bits as u64);
    }

    // Step 4: Connect byte to the sum
    let combined = low_part + high_part;

    // byte is defined as ((low_limb >> low_shift) | (high_limb << low_bits)) as u8
    // which is ((low_part) | (high_part)) as u8
    // We proved low_part | high_part == low_part + high_part == combined
    // Therefore byte == (combined as u8)

    let a = (low_limb as nat) / pow2(low_shift);
    let b = high_limb as nat;
    let k = low_bits;

    // Prove combined as nat == a + b * pow2(k)
    assert(combined as nat == a + b * pow2(k)) by {
        // We have: combined = low_part + high_part
        // We proved: low_part as nat == a (recall from lemma_u64_shr_is_div above)
        lemma_u64_shr_is_div(low_limb, low_shift as u64);

        // We proved: high_part == high_limb * pow2(low_bits) as u64 (recall from lemma_u64_shl_is_mul above)
        lemma_u64_shl_is_mul(high_limb, low_bits as u64);

        // Therefore: combined as nat = low_part as nat + high_part as nat = a + b * pow2(k)
    }

    // Main modular arithmetic result - Apply the Modular Bit Partitioning Theorem

    // We want to show: (a + b * pow2(k)) % 256 == (a % pow2(k)) + ((b % pow2(8-k)) * pow2(k))
    // where a = low_limb / 2^low_shift, b = high_limb, k = low_bits, n = 8

    // Verify preconditions for lemma_modular_bit_partitioning:

    // Precondition 3: (a % 2^k) + ((b % 2^(n-k)) * 2^k) < 2^n
    assert((a % pow2(k)) + ((b % pow2((8 - k) as nat)) * pow2(k)) < 256) by {
        // Since a < pow2(k): a % pow2(k) = a < pow2(k)
        assert(a % pow2(k) == a) by {
            lemma_small_mod(a, pow2(k));
        }

        // Key fact: pow2(k) * pow2(8 - k) = 256
        assert(pow2(k) * pow2((8 - k) as nat) == 256) by {
            lemma_pow2_adds(k, (8 - k) as nat);
        }

        // Prove: a + (b % pow2(8-k)) * pow2(k) < 256
        // Since a < pow2(k): a <= pow2(k) - 1
        // Since b % pow2(8-k) < pow2(8-k): b % pow2(8-k) <= pow2(8-k) - 1
        // Therefore: a + (b % pow2(8-k)) * pow2(k) <= (pow2(k) - 1) + (pow2(8-k) - 1) * pow2(k)
        //                                             = pow2(k) - 1 + pow2(8-k) * pow2(k) - pow2(k)
        //                                             = pow2(8-k) * pow2(k) - 1
        //                                             = 256 - 1 = 255 < 256

        // Get upper bound on b % pow2(8-k)
        assert((b % pow2((8 - k) as nat)) < pow2((8 - k) as nat)) by {
            lemma_mod_bound(b as int, pow2((8 - k) as nat) as int);
        }

        // So: a + (b % pow2(8-k)) * pow2(k) <= (pow2(k) - 1) + (pow2(8-k) - 1) * pow2(k)

        // Use nonlinear_arith to compute: (pow2(k) - 1) + (pow2(8-k) - 1) * pow2(k) = pow2(8-k) * pow2(k) - 1 = 255
        assert((pow2(k) - 1) + (pow2((8 - k) as nat) - 1) * pow2(k) == pow2((8 - k) as nat) * pow2(
            k,
        ) - 1) by (nonlinear_arith);

        assert(a + (b % pow2((8 - k) as nat)) * pow2(k) < 256) by (nonlinear_arith)
            requires
                a <= pow2(k) - 1,
                (b % pow2((8 - k) as nat)) <= pow2((8 - k) as nat) - 1,
                (pow2(k) - 1) + (pow2((8 - k) as nat) - 1) * pow2(k) == 255,
        ;
    }

    lemma_modular_bit_partitioning(a, b, k, 8);

    assert(a % pow2(k) == a) by {
        lemma_small_mod(a, pow2(k));
    }

    // Connect to byte casting
    // byte == combined as u8 means byte as nat == (combined as nat) % 256
    // FUNDAMENTAL RUST/VERUS AXIOM: Integer casts truncate via modulo
    // This is the definition of how (x as u8) works in Rust for any integer type x.
    // Verus doesn't automatically establish this property, so we assume it.
    assert((combined as nat) % pow2(8) == (combined as u8)) by {
        lemma_u8_cast_is_mod_256(combined as u64);
    }
    // We know: combined as nat == a + b * pow2(k)

    // Therefore: byte as nat == (a + b * pow2(k)) % 256

    // We've proved (line 2617): (a + b * pow2(k)) % 256 == (a % pow2(k)) + ((b % pow2((8 - k) as nat)) * pow2(k))
    // Therefore by transitivity:

    // Show a % pow2(k) == a

    // Substitute a % pow2(k) with a:

    // Final result: substitute back the definitions of a, b, k
    assert(byte as nat == (low_limb as nat / pow2(low_shift)) % pow2(low_bits) + (high_limb as nat
        % pow2((8 - low_bits) as nat)) * pow2(low_bits));
}

/// Proves that the sum of all limb contributions equals as_nat_32_u8(&bytes)
proof fn lemma_sum_equals_byte_nat(limbs: [u64; 5], bytes: [u8; 32])
    requires
        forall|i: int| 0 <= i < 5 ==> limbs[i] < pow2(51),
        bytes_match_limbs_packing(limbs, bytes),
    ensures
        as_nat_32_u8(&bytes) == limb0_byte_contribution(limbs, bytes) + limb1_byte_contribution(
            limbs,
            bytes,
        ) + limb2_byte_contribution(limbs, bytes) + limb3_byte_contribution(limbs, bytes)
            + limb4_byte_contribution(limbs, bytes),
{
    lemma2_to64();

    // Strategy: Show that the sum of contributions equals as_nat_32_u8(bytes)
    // by proving that for boundary bytes, the split parts reconstruct the full byte.
    //
    // Boundary bytes:
    // - Byte 6  = low 3 bits (limb0) + high 5 bits (limb1)
    // - Byte 12 = low 6 bits (limb1) + high 2 bits (limb2)
    // - Byte 19 = low 1 bit (limb2) + high 7 bits (limb3)
    // - Byte 25 = low 4 bits (limb3) + high 4 bits (limb4)

    // From bytes_match_limbs_packing, we know how bytes relate to limbs
    // For each boundary byte, we need to prove it reconstructs correctly

    // Define the boundary byte splits (bytes that span two limbs)
    // Each boundary byte is split into a low part (from lower limb) and high part (from higher limb)
    let byte6_low = ((limbs[0] as nat / pow2(48)) % 8) * pow2(6 * 8);
    let byte6_high = ((limbs[1] as nat % pow2(5)) * 8) * pow2(6 * 8);

    let byte12_low = ((limbs[1] as nat / pow2(45)) % pow2(6)) * pow2(12 * 8);
    let byte12_high = ((limbs[2] as nat % pow2(2)) * pow2(6)) * pow2(12 * 8);

    let byte19_low = ((limbs[2] as nat / pow2(50)) % 2) * pow2(19 * 8);
    let byte19_high = ((limbs[3] as nat % pow2(7)) * 2) * pow2(19 * 8);

    let byte25_low = ((limbs[3] as nat / pow2(47)) % pow2(4)) * pow2(25 * 8);
    let byte25_high = ((limbs[4] as nat % pow2(4)) * pow2(4)) * pow2(25 * 8);

    // Prove each boundary byte reconstruction using lemma_boundary_byte_combines
    // Then multiply both sides by pow2(byte_position * 8) and apply distributivity
    // Byte 6: lemma_boundary_byte_combines proves bytes[6] == (limbs[0]/2^48)%8 + (limbs[1]%2^5)*8
    // Multiply both sides by pow2(6*8): (a+b)*c = a*c + b*c by distributivity
    //lemma_boundary_byte_combines(limbs[0], limbs[1], bytes[6], 48, 3);
    assert(bytes[6] as nat == (limbs[0] as nat / pow2(48)) % 8 + (limbs[1] as nat % pow2(5)) * 8)
        by {
        lemma_boundary_byte_combines(limbs[0], limbs[1], bytes[6], 48, 3);
    }
    // Distributivity gives us: (a+b)*c == a*c + b*c
    assert(bytes[6] as nat * pow2(6 * 8) == ((limbs[0] as nat / pow2(48)) % 8) * pow2(6 * 8) + ((
    limbs[1] as nat % pow2(5)) * 8) * pow2(6 * 8)) by {
        lemma_mul_is_distributive_add_other_way(
            pow2(6 * 8) as int,
            ((limbs[0] as nat / pow2(48)) % 8) as int,
            ((limbs[1] as nat % pow2(5)) * 8) as int,
        );
    }
    // Which exactly matches byte6_low + byte6_high by definition
    assert(bytes[6] as nat * pow2(6 * 8) == byte6_low + byte6_high);

    // Byte 12: lemma_boundary_byte_combines proves bytes[12] == (limbs[1]/2^45)%2^6 + (limbs[2]%2^2)*2^6
    // Multiply both sides by pow2(12*8): (a+b)*c = a*c + b*c by distributivity
    assert(bytes[12] as nat == (limbs[1] as nat / pow2(45)) % pow2(6) + (limbs[2] as nat % pow2(2))
        * pow2(6)) by {
        lemma_boundary_byte_combines(limbs[1], limbs[2], bytes[12], 45, 6);
    }
    // Distributivity gives us: (a+b)*c == a*c + b*c
    assert(bytes[12] as nat * pow2(12 * 8) == ((limbs[1] as nat / pow2(45)) % pow2(6)) * pow2(
        12 * 8,
    ) + ((limbs[2] as nat % pow2(2)) * pow2(6)) * pow2(12 * 8)) by {
        lemma_mul_is_distributive_add_other_way(
            pow2(12 * 8) as int,
            ((limbs[1] as nat / pow2(45)) % pow2(6)) as int,
            ((limbs[2] as nat % pow2(2)) * pow2(6)) as int,
        );
    }
    // Which exactly matches byte12_low + byte12_high by definition
    assert(bytes[12] as nat * pow2(12 * 8) == byte12_low + byte12_high);

    // Byte 19: lemma_boundary_byte_combines proves bytes[19] == (limbs[2]/2^50)%2 + (limbs[3]%2^7)*2
    // Multiply both sides by pow2(19*8): (a+b)*c = a*c + b*c by distributivity
    assert(bytes[19] as nat == (limbs[2] as nat / pow2(50)) % 2 + (limbs[3] as nat % pow2(7)) * 2)
        by {
        lemma_boundary_byte_combines(limbs[2], limbs[3], bytes[19], 50, 1);
    }
    // Distributivity gives us: (a+b)*c == a*c + b*c
    assert(bytes[19] as nat * pow2(19 * 8) == ((limbs[2] as nat / pow2(50)) % 2) * pow2(19 * 8) + ((
    limbs[3] as nat % pow2(7)) * 2) * pow2(19 * 8)) by {
        lemma_mul_is_distributive_add_other_way(
            pow2(19 * 8) as int,
            ((limbs[2] as nat / pow2(50)) % 2) as int,
            ((limbs[3] as nat % pow2(7)) * 2) as int,
        );
    }
    // Which exactly matches byte19_low + byte19_high by definition
    assert(bytes[19] as nat * pow2(19 * 8) == byte19_low + byte19_high);

    // Byte 25: lemma_boundary_byte_combines proves bytes[25] == (limbs[3]/2^47)%2^4 + (limbs[4]%2^4)*2^4
    // Multiply both sides by pow2(25*8): (a+b)*c = a*c + b*c by distributivity
    assert(bytes[25] as nat == (limbs[3] as nat / pow2(47)) % pow2(4) + (limbs[4] as nat % pow2(4))
        * pow2(4)) by {
        lemma_boundary_byte_combines(limbs[3], limbs[4], bytes[25], 47, 4);
    }
    // Distributivity gives us: (a+b)*c == a*c + b*c
    assert(bytes[25] as nat * pow2(25 * 8) == ((limbs[3] as nat / pow2(47)) % pow2(4)) * pow2(
        25 * 8,
    ) + ((limbs[4] as nat % pow2(4)) * pow2(4)) * pow2(25 * 8)) by {
        lemma_mul_is_distributive_add_other_way(
            pow2(25 * 8) as int,
            ((limbs[3] as nat / pow2(47)) % pow2(4)) as int,
            ((limbs[4] as nat % pow2(4)) * pow2(4)) as int,
        );
    }
    // Which exactly matches byte25_low + byte25_high by definition
    assert(bytes[25] as nat * pow2(25 * 8) == byte25_low + byte25_high);

    let after_split_25_pow2_first = (bytes[0] as nat) + (bytes[1] as nat) * pow2(1 * 8) + (
    bytes[2] as nat) * pow2(2 * 8) + (bytes[3] as nat) * pow2(3 * 8) + (bytes[4] as nat) * pow2(
        4 * 8,
    ) + (bytes[5] as nat) * pow2(5 * 8) + byte6_low + byte6_high + (bytes[7] as nat) * pow2(7 * 8)
        + (bytes[8] as nat) * pow2(8 * 8) + (bytes[9] as nat) * pow2(9 * 8) + (bytes[10] as nat)
        * pow2(10 * 8) + (bytes[11] as nat) * pow2(11 * 8) + byte12_low + byte12_high + (
    bytes[13] as nat) * pow2(13 * 8) + (bytes[14] as nat) * pow2(14 * 8) + (bytes[15] as nat)
        * pow2(15 * 8) + (bytes[16] as nat) * pow2(16 * 8) + (bytes[17] as nat) * pow2(17 * 8) + (
    bytes[18] as nat) * pow2(18 * 8) + byte19_low + byte19_high + (bytes[20] as nat) * pow2(20 * 8)
        + (bytes[21] as nat) * pow2(21 * 8) + (bytes[22] as nat) * pow2(22 * 8) + (bytes[23] as nat)
        * pow2(23 * 8) + (bytes[24] as nat) * pow2(24 * 8) + byte25_low + byte25_high + (
    bytes[26] as nat) * pow2(26 * 8) + (bytes[27] as nat) * pow2(27 * 8) + (bytes[28] as nat)
        * pow2(28 * 8) + (bytes[29] as nat) * pow2(29 * 8) + (bytes[30] as nat) * pow2(30 * 8) + (
    bytes[31] as nat) * pow2(31 * 8);

    assert(after_split_25_pow2_first == as_nat_32_u8(&bytes));

    assert(bytes[0] as nat * pow2(0 * 8) == bytes[0] as nat * 1);
    // The mathematical fact: after splitting boundary bytes, this equals the sum of limb contributions
    assert(after_split_25_pow2_first == limb0_byte_contribution(limbs, bytes)
        + limb1_byte_contribution(limbs, bytes) + limb2_byte_contribution(limbs, bytes)
        + limb3_byte_contribution(limbs, bytes) + limb4_byte_contribution(limbs, bytes));
}

} // verus!
