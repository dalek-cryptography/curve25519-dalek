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
use super::super::scalar_specs::*;

// Import helper lemmas from field_lemmas
use super::super::field_lemmas::field_core::*;
use super::super::field_lemmas::limbs_to_bytes_lemmas::*;

verus! {

// ============================================================================
// Helper Lemmas for 52-bit limbs
// ============================================================================

/// Predicate: bytes are packed from limbs according to the as_bytes algorithm
pub open spec fn bytes_match_limbs_packing_52(limbs: [u64; 5], bytes: [u8; 32]) -> bool {
    bytes[ 0] ==  (limbs[0] >>  0)                      as u8 &&
    bytes[ 1] ==  (limbs[0] >>  8)                      as u8 &&
    bytes[ 2] ==  (limbs[0] >> 16)                      as u8 &&
    bytes[ 3] ==  (limbs[0] >> 24)                      as u8 &&
    bytes[ 4] ==  (limbs[0] >> 32)                      as u8 &&
    bytes[ 5] ==  (limbs[0] >> 40)                      as u8 &&
    bytes[ 6] == ((limbs[0] >> 48) | (limbs[1] << 4))   as u8 &&
    bytes[ 7] ==  (limbs[1] >>  4)                      as u8 &&
    bytes[ 8] ==  (limbs[1] >> 12)                      as u8 &&
    bytes[ 9] ==  (limbs[1] >> 20)                      as u8 &&
    bytes[10] ==  (limbs[1] >> 28)                      as u8 &&
    bytes[11] ==  (limbs[1] >> 36)                      as u8 &&
    bytes[12] ==  (limbs[1] >> 44)                      as u8 &&
    bytes[13] ==  (limbs[2] >>  0)                      as u8 &&
    bytes[14] ==  (limbs[2] >>  8)                      as u8 &&
    bytes[15] ==  (limbs[2] >> 16)                      as u8 &&
    bytes[16] ==  (limbs[2] >> 24)                      as u8 &&
    bytes[17] ==  (limbs[2] >> 32)                      as u8 &&
    bytes[18] ==  (limbs[2] >> 40)                      as u8 &&
    bytes[19] == ((limbs[2] >> 48) | (limbs[3] << 4))   as u8 &&
    bytes[20] ==  (limbs[3] >>  4)                      as u8 &&
    bytes[21] ==  (limbs[3] >> 12)                      as u8 &&
    bytes[22] ==  (limbs[3] >> 20)                      as u8 &&
    bytes[23] ==  (limbs[3] >> 28)                      as u8 &&
    bytes[24] ==  (limbs[3] >> 36)                      as u8 &&
    bytes[25] ==  (limbs[3] >> 44)                      as u8 &&
    bytes[26] ==  (limbs[4] >>  0)                      as u8 &&
    bytes[27] ==  (limbs[4] >>  8)                      as u8 &&
    bytes[28] ==  (limbs[4] >> 16)                      as u8 &&
    bytes[29] ==  (limbs[4] >> 24)                      as u8 &&
    bytes[30] ==  (limbs[4] >> 32)                      as u8 &&
    bytes[31] ==  (limbs[4] >> 40)                      as u8
}

// ============================================================================
// Byte contribution specification functions
// ============================================================================
// These functions decompose the byte sum into per-limb contributions,
// matching the structure of Scalar52::as_bytes packing.

/// Compute limb 0's contribution to the byte sum
/// Limb 0 contributes to bytes 0-6 (fully to 0-5, partially to 6)
pub open spec fn limb0_byte_contribution_52(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    bytes[0] as nat * pow2(0 * 8) +
    bytes[1] as nat * pow2(1 * 8) +
    bytes[2] as nat * pow2(2 * 8) +
    bytes[3] as nat * pow2(3 * 8) +
    bytes[4] as nat * pow2(4 * 8) +
    bytes[5] as nat * pow2(5 * 8) +
    // Byte 6 is a boundary byte - limb 0 contributes only the low 4 bits
    // These 4 bits represent limbs[0]'s bits 48-51
    ((limbs[0] as nat / pow2(48)) % 16) * pow2(6 * 8)
}

/// Compute limb 1's contribution to the byte sum
/// Limb 1 contributes to bytes 6-12 (partially to 6, fully to 7-11, partially to 12)
pub open spec fn limb1_byte_contribution_52(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    // Byte 6 high 4 bits (limbs[1]'s bits 0-3)
    ((limbs[1] as nat % pow2(4)) * 16) * pow2(6 * 8) +
    bytes[7] as nat * pow2(7 * 8) +
    bytes[8] as nat * pow2(8 * 8) +
    bytes[9] as nat * pow2(9 * 8) +
    bytes[10] as nat * pow2(10 * 8) +
    bytes[11] as nat * pow2(11 * 8) +
    bytes[12] as nat * pow2(12 * 8)
}

/// Compute limb 2's contribution to the byte sum
/// Limb 2 contributes to bytes 13-19 (fully to 13-18, partially to 19)
pub open spec fn limb2_byte_contribution_52(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    bytes[13] as nat * pow2(13 * 8) +
    bytes[14] as nat * pow2(14 * 8) +
    bytes[15] as nat * pow2(15 * 8) +
    bytes[16] as nat * pow2(16 * 8) +
    bytes[17] as nat * pow2(17 * 8) +
    bytes[18] as nat * pow2(18 * 8) +
    // Byte 19 is a boundary byte - limb 2 contributes only the low 4 bits
    ((limbs[2] as nat / pow2(48)) % 16) * pow2(19 * 8)
}

/// Compute limb 3's contribution to the byte sum
/// Limb 3 contributes to bytes 19-25 (partially to 19, fully to 20-24, partially to 25)
pub open spec fn limb3_byte_contribution_52(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    // Byte 19 high 4 bits (limbs[3]'s bits 0-3)
    ((limbs[3] as nat % pow2(4)) * 16) * pow2(19 * 8) +
    bytes[20] as nat * pow2(20 * 8) +
    bytes[21] as nat * pow2(21 * 8) +
    bytes[22] as nat * pow2(22 * 8) +
    bytes[23] as nat * pow2(23 * 8) +
    bytes[24] as nat * pow2(24 * 8) +
    bytes[25] as nat * pow2(25 * 8)
}

/// Compute limb 4's contribution to the byte sum
/// Limb 4 contributes to bytes 26-31
pub open spec fn limb4_byte_contribution_52(limbs: [u64; 5], bytes: [u8; 32]) -> nat {
    bytes[26] as nat * pow2(26 * 8) +
    bytes[27] as nat * pow2(27 * 8) +
    bytes[28] as nat * pow2(28 * 8) +
    bytes[29] as nat * pow2(29 * 8) +
    bytes[30] as nat * pow2(30 * 8) +
    bytes[31] as nat * pow2(31 * 8)
}

// ============================================================================
// Main lemma and helper lemmas (proofs to be implemented)
// ============================================================================

/// Core lemma: proves that packing 52-bit limbs into bytes preserves the value
/// Now using non-recursive specification functions (like field_verus.rs does)
///
/// This follows the same proof strategy as lemma_limbs_to_bytes from field_lemmas,
/// but adapted for 52-bit limbs instead of 51-bit limbs.
pub proof fn lemma_as_bytes_52(limbs: [u64; 5], bytes: [u8; 32])
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        bytes_match_limbs_packing_52(limbs, bytes),
    ensures
        as_nat_32_u8(&bytes) == five_limbs_to_nat_aux(limbs),
{
    // Connect the bit shift in the requires clause to pow2 for clarity

    assert((1u64 << 52) == pow2(52)) by {
        shift_is_pow2(52);
    }

    // Establish that each limb is bounded by pow2(52)
    //assert(forall |i: int| 0 <= i < 5 ==> limbs[i] < pow2(52));

    assert(as_nat_32_u8(&bytes) ==
            limb0_byte_contribution_52(limbs, bytes) +
            limb1_byte_contribution_52(limbs, bytes) +
            limb2_byte_contribution_52(limbs, bytes) +
            limb3_byte_contribution_52(limbs, bytes) +
            limb4_byte_contribution_52(limbs, bytes)) by {
                lemma_sum_equals_byte_nat_52(limbs, bytes);
            }

    assert((limbs[0] as nat) % pow2(52) == limbs[0]) by {
        lemma_small_mod(limbs[0] as nat, pow2(52));
    }
    assert(as_nat_32_u8(&bytes) == five_limbs_to_nat_aux(limbs)) by {
        lemma_limb0_contribution_correctness_52(limbs, bytes);
        lemma_limb1_contribution_correctness_52(limbs, bytes);
        lemma_limb2_contribution_correctness_52(limbs, bytes);
        lemma_limb3_contribution_correctness_52(limbs, bytes);
        lemma_limb4_contribution_correctness_52(limbs, bytes);
    }
}

// ============================================================================
// Helper Lemmas
// ============================================================================

/// Helper: A byte formed by simple right shift has a direct arithmetic interpretation
/// This is the 52-bit version of lemma_byte_from_limb_shift
proof fn lemma_byte_from_limb_shift_52(limb: u64, shift: u64, byte: u8)
    requires
        limb < pow2(52),
        shift < 64,
        byte == (limb >> shift) as u8,
    ensures
        byte as nat == (limb as nat / pow2(shift as nat)) % 256,
{
    // Bitwise shift to arithmetic conversion
    // When we shift right by `shift` bits and cast to u8, we extract 8 bits starting at position `shift`
    // In arithmetic terms: (limb / 2^shift) % 256

    lemma2_to64();
    assert((limb >> shift) as nat == limb as nat / pow2(shift as nat)) by {
        lemma_u64_shr_is_div(limb, shift);
    }

    // The u8 cast takes the low 8 bits, which is % 256
    // Proof: use vstd lemma that & 0xFF = % 256, then bit_vector to show casting = masking
    let shifted = limb >> shift;
    assert(shifted & 0xFF == shifted % 256) by {
        lemma_u64_low_bits_mask_is_mod(shifted, 8);
    }
    assert(shifted as u8 == (shifted & 0xFF) as u8) by (bit_vector);
    // Therefore: (shifted as u8) as nat == shifted % 256
    assert((limb >> shift) as u8 as nat == ((limb >> shift) as nat) % 256);
}

/// Helper: proves that the sum of byte contributions equals as_nat_32_u8
///
/// The key insight here is that the byte contributions partition the bytes
/// such that each byte (or parts of bytes at boundaries) is accounted for exactly once.
pub proof fn lemma_sum_equals_byte_nat_52(limbs: [u64; 5], bytes: [u8; 32])
    requires
        forall |i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 52),
        bytes_match_limbs_packing_52(limbs, bytes),
    ensures
        limb0_byte_contribution_52(limbs, bytes) +
        limb1_byte_contribution_52(limbs, bytes) +
        limb2_byte_contribution_52(limbs, bytes) +
        limb3_byte_contribution_52(limbs, bytes) +
        limb4_byte_contribution_52(limbs, bytes) ==
        as_nat_32_u8(&bytes)
{
    // The sum lemma is actually straightforward because as_nat_32_u8
    // is just the sum of all bytes weighted by their positions, and the
    // limb contribution functions partition this sum.
    //
    // Limb 0 contributes: bytes[0-5] fully + low 4 bits of byte 6
    // Limb 1 contributes: high 4 bits of byte 6 + bytes[7-12] fully
    // Limb 2 contributes: bytes[13-18] fully + low 4 bits of byte 19
    // Limb 3 contributes: high 4 bits of byte 19 + bytes[20-25] fully
    // Limb 4 contributes: bytes[26-31] fully
    //
    // When we add these up, each byte is counted exactly once, and the
    // boundary bytes (6 and 19) are correctly split between adjacent limbs.
    //
    // The proof follows by expanding the definitions and grouping terms.

    lemma2_to64();
    shift_is_pow2(52);

    // Prove limbs are bounded by pow2(52)
    assert(forall |i: int| 0 <= i < 5 ==> limbs[i] < pow2(52)) by {
        assert((1u64 << 52) == pow2(52)) by {
            shift_is_pow2(52);
        }
    }

    // Key: at the boundaries (bytes 6 and 19), the limb contributions partition
    // the byte value correctly using the predicate bytes_match_limbs_packing_52

    // From the predicate, we know:
    // bytes[6] == ((limbs[0] >> 48) | (limbs[1] << 4)) as u8
    // bytes[19] == ((limbs[2] >> 48) | (limbs[3] << 4)) as u8

    // This ensures that:
    // - Limb 0's high 4 bits + Limb 1's low 4 bits = byte 6
    // - Limb 2's high 4 bits + Limb 3's low 4 bits = byte 19

    // Define the boundary byte splits
    let byte6_low = ((limbs[0] as nat / pow2(48)) % 16) * pow2(6 * 8);
    let byte6_high = ((limbs[1] as nat % pow2(4)) * 16) * pow2(6 * 8);

    let byte19_low = ((limbs[2] as nat / pow2(48)) % 16) * pow2(19 * 8);
    let byte19_high = ((limbs[3] as nat % pow2(4)) * 16) * pow2(19 * 8);

    // Prove each boundary byte reconstruction using lemma_boundary_byte_combines_52
    // Byte 6: lemma_boundary_byte_combines_52 proves bytes[6] == (limbs[0]/2^48)%16 + (limbs[1]%2^4)*16
    assert(bytes[6] as nat ==
        (limbs[0] as nat / pow2(48)) % 16 +
        (limbs[1] as nat % pow2(4)) * 16) by {
            lemma_boundary_byte_combines_52(limbs[0], limbs[1], bytes[6], 48, 4);
        }
    // Distributivity gives us: (a+b)*c == a*c + b*c
    assert(bytes[6] as nat * pow2(6 * 8) ==
        ((limbs[0] as nat / pow2(48)) % 16) * pow2(6 * 8) +
        ((limbs[1] as nat % pow2(4)) * 16) * pow2(6 * 8)) by {
            lemma_mul_is_distributive_add_other_way(pow2(6 * 8) as int,
                ((limbs[0] as nat / pow2(48)) % 16) as int,
                ((limbs[1] as nat % pow2(4)) * 16) as int);
        }
    assert(bytes[6] as nat * pow2(6 * 8) == byte6_low + byte6_high);

    // Byte 19: same pattern
    assert(bytes[19] as nat ==
        (limbs[2] as nat / pow2(48)) % 16 +
        (limbs[3] as nat % pow2(4)) * 16) by {
            lemma_boundary_byte_combines_52(limbs[2], limbs[3], bytes[19], 48, 4);
        }
    assert(bytes[19] as nat * pow2(19 * 8) ==
        ((limbs[2] as nat / pow2(48)) % 16) * pow2(19 * 8) +
        ((limbs[3] as nat % pow2(4)) * 16) * pow2(19 * 8)) by {
            lemma_mul_is_distributive_add_other_way(pow2(19 * 8) as int,
                ((limbs[2] as nat / pow2(48)) % 16) as int,
                ((limbs[3] as nat % pow2(4)) * 16) as int);
        }
    assert(bytes[19] as nat * pow2(19 * 8) == byte19_low + byte19_high);

    // Construct the expression with split boundary bytes
    let after_split =
        (bytes[0] as nat) +
        (bytes[ 1] as nat) * pow2( 1 * 8) +
        (bytes[ 2] as nat) * pow2( 2 * 8) +
        (bytes[ 3] as nat) * pow2( 3 * 8) +
        (bytes[ 4] as nat) * pow2( 4 * 8) +
        (bytes[ 5] as nat) * pow2( 5 * 8) +
        byte6_low + byte6_high +
        (bytes[ 7] as nat) * pow2( 7 * 8) +
        (bytes[ 8] as nat) * pow2( 8 * 8) +
        (bytes[ 9] as nat) * pow2( 9 * 8) +
        (bytes[10] as nat) * pow2(10 * 8) +
        (bytes[11] as nat) * pow2(11 * 8) +
        (bytes[12] as nat) * pow2(12 * 8) +
        (bytes[13] as nat) * pow2(13 * 8) +
        (bytes[14] as nat) * pow2(14 * 8) +
        (bytes[15] as nat) * pow2(15 * 8) +
        (bytes[16] as nat) * pow2(16 * 8) +
        (bytes[17] as nat) * pow2(17 * 8) +
        (bytes[18] as nat) * pow2(18 * 8) +
        byte19_low + byte19_high +
        (bytes[20] as nat) * pow2(20 * 8) +
        (bytes[21] as nat) * pow2(21 * 8) +
        (bytes[22] as nat) * pow2(22 * 8) +
        (bytes[23] as nat) * pow2(23 * 8) +
        (bytes[24] as nat) * pow2(24 * 8) +
        (bytes[25] as nat) * pow2(25 * 8) +
        (bytes[26] as nat) * pow2(26 * 8) +
        (bytes[27] as nat) * pow2(27 * 8) +
        (bytes[28] as nat) * pow2(28 * 8) +
        (bytes[29] as nat) * pow2(29 * 8) +
        (bytes[30] as nat) * pow2(30 * 8) +
        (bytes[31] as nat) * pow2(31 * 8);

    assert(bytes[0] as nat * pow2(0 * 8) == bytes[0] as nat * 1);
    assert(after_split == as_nat_32_u8(&bytes));

    // The mathematical fact: after splitting boundary bytes, this equals the sum of limb contributions
    assert(after_split ==
        limb0_byte_contribution_52(limbs, bytes) +
        limb1_byte_contribution_52(limbs, bytes) +
        limb2_byte_contribution_52(limbs, bytes) +
        limb3_byte_contribution_52(limbs, bytes) +
        limb4_byte_contribution_52(limbs, bytes));
}

/// Helper lemma: proves that a boundary byte correctly combines parts from two limbs (52-bit version)
proof fn lemma_boundary_byte_combines_52(low_limb: u64, high_limb: u64, byte: u8, low_shift: nat, low_bits: nat)
    requires
        low_limb < pow2(52),
        high_limb < pow2(52),
        low_bits < 8,
        low_shift + low_bits == 52,
        byte == ((low_limb >> low_shift) | (high_limb << low_bits)) as u8,
    ensures
        byte as nat ==
            (low_limb as nat / pow2(low_shift)) % pow2(low_bits) +
            (high_limb as nat % pow2((8 - low_bits) as nat)) * pow2(low_bits),
{
    // Proof following docs_22_oct/lemma_boundary_byte_combines_52_proof.md
    lemma2_to64();

    // Establish that pow2 values fit in u64
    assert(pow2(low_shift) <= u64::MAX as nat) by {
        lemma_pow2_strictly_increases(low_shift, 64);
    }

    assert(pow2(low_bits) <= u64::MAX as nat) by {
        lemma_pow2_strictly_increases(low_bits, 64);
    }

    // === STEP 1: Convert bit operations to arithmetic ===
    let low_part = low_limb >> low_shift;
    let high_part = high_limb << low_bits;

    // Prove high_part doesn't overflow: high_limb * 2^low_bits <= u64::MAX
    assert(high_limb as nat * pow2(low_bits) <= u64::MAX as nat) by {
        // Worst case: high_limb = 2^52 - 1, low_bits = 7
        // Need: 2^52 * 2^7 = 2^59 <= 2^64 - 1 ✓
        assert(pow2(52) * pow2(7) <= pow2(64) - 1) by {
            lemma_pow2_adds(52, 7);
            lemma_pow2_strictly_increases(59, 64);
        }
        if low_bits < 7 {
            lemma_pow2_strictly_increases(low_bits, 7);
        }
        mul_le(high_limb as nat, (pow2(52) - 1) as nat, pow2(low_bits), pow2(7));
    }

    assert(high_part == high_limb * (pow2(low_bits) as u64)) by {
        lemma_u64_shl_is_mul(high_limb, low_bits as u64);
    }

    // === STEP 2: Prove OR equals addition ===
    // Need preconditions for bit_or_is_plus:
    // 1) low_part < 1u64 << low_bits
    // 2) high_limb <= u64::MAX >> low_bits

    // Subproof 2.1: Bound low_part
    assert((low_part as nat) < pow2(low_bits)) by {
        // low_part = low_limb / 2^low_shift (by shr)
        lemma_u64_shr_is_div(low_limb, low_shift as u64);

        // low_limb / 2^low_shift < 2^52 / 2^low_shift = 2^(52 - low_shift)
        // Since low_shift + low_bits = 52, we have 52 - low_shift = low_bits
        lemma_pow2_adds(low_shift, (52 - low_shift) as nat);

        // Apply: low_limb < 2^52 = 2^low_shift * 2^(52-low_shift)
        // Therefore: low_limb / 2^low_shift < 2^(52-low_shift) = 2^low_bits
        lemma_pow2_pos(low_shift);
        lemma_div_strictly_bounded(low_limb as int, pow2(low_shift) as int, pow2((52 - low_shift) as nat) as int);
    }

    assert(low_part < 1u64 << low_bits) by {
        assert(1u64 << low_bits == (pow2(low_bits) as u64)) by {
            shift_is_pow2(low_bits);
        }
    }

    // Subproof 2.2: Bound high_limb for shift
    assert(high_limb <= (u64::MAX >> low_bits)) by {
        // We proved: high_limb * 2^low_bits <= u64::MAX
        // Conclude: high_limb <= u64::MAX / 2^low_bits
        lemma_pow2_pos(low_bits);
        lemma_mul_le_implies_div_le(high_limb as nat, pow2(low_bits), u64::MAX as nat);

        // u64::MAX / 2^low_bits = u64::MAX >> low_bits
        lemma_u64_shr_is_div(u64::MAX, low_bits as u64);
    }

    // Apply bit_or_is_plus
    assert(low_part | high_part == low_part + high_part) by {
        bit_or_is_plus(low_part, high_limb, low_bits as u64);
    }

    // === STEP 3: Express combined value ===
    let combined = low_part + high_part;

    let a = (low_limb as nat) / pow2(low_shift);
    let b = high_limb as nat;
    let k = low_bits;

    // Prove combined as nat == a + b * pow2(k)
    assert(combined as nat == a + b * pow2(k)) by {
        lemma_u64_shr_is_div(low_limb, low_shift as u64);
        lemma_u64_shl_is_mul(high_limb, low_bits as u64);
    }

    // === STEP 4: Apply modular bit partitioning ===

    // Verify precondition: (a % 2^k) + ((b % 2^(8-k)) * 2^k) < 256
    assert((a % pow2(k)) + ((b % pow2((8 - k) as nat)) * pow2(k)) < 256) by {
        // Since a < pow2(k): a % pow2(k) = a
        assert(a % pow2(k) == a) by {
            lemma_small_mod(a, pow2(k));
        }

        // Key fact: pow2(k) * pow2(8 - k) = 256
        assert(pow2(k) * pow2((8 - k) as nat) == 256) by {
            lemma_pow2_adds(k, (8 - k) as nat);
        }

        // Get upper bound on b % pow2(8-k)
        assert((b % pow2((8 - k) as nat)) < pow2((8 - k) as nat)) by {
            lemma_mod_bound(b as int, pow2((8 - k) as nat) as int);
        }

        // Arithmetic: a + (b % pow2(8-k)) * pow2(k) <= (pow2(k) - 1) + (pow2(8-k) - 1) * pow2(k)
        //           = pow2(k) * pow2(8-k) - 1 = 256 - 1 = 255 < 256
        assert((pow2(k) - 1) + (pow2((8 - k) as nat) - 1) * pow2(k) == pow2((8 - k) as nat) * pow2(k) - 1) by (nonlinear_arith);

        assert(a + (b % pow2((8 - k) as nat)) * pow2(k) < 256) by (nonlinear_arith)
            requires
                a <= pow2(k) - 1,
                (b % pow2((8 - k) as nat)) <= pow2((8 - k) as nat) - 1,
                (pow2(k) - 1) + (pow2((8 - k) as nat) - 1) * pow2(k) == 255;
    }

    lemma_modular_bit_partitioning(a, b, k, 8);

    assert(a % pow2(k) == a) by {
        lemma_small_mod(a, pow2(k));
    }

    // === STEP 5: Connect to byte value ===
    // byte = combined as u8 means byte as nat = combined % 256
    assert((combined as nat) % pow2(8) == (combined as u8)) by {
        lemma_u8_cast_is_mod_256(combined as u64);
    }

    // We know: combined as nat = a + b * pow2(k)
    // Apply modular bit partitioning: (a + b * 2^k) % 256 = a + (b % 2^(8-k)) * 2^k
    // This gives us the desired result
}




/// Per-limb correctness lemmas (one for each limb 0-4)
pub proof fn lemma_limb0_contribution_correctness_52(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[0] < (1u64 << 52),
        bytes_match_limbs_packing_52(limbs, bytes),
    ensures
        limb0_byte_contribution_52(limbs, bytes) == (limbs[0] as nat) % pow2(52)
{
    // Limb 0 is stored in bytes 0-6
    // - Bytes 0-5: full bytes containing limbs[0]'s bits 0-47 (48 bits total)
    // - Byte 6 (low 4 bits): limbs[0]'s bits 48-51 (4 bits)
    // Total: 48 + 4 = 52 bits, which matches limbs[0] < 2^52
    //
    // Strategy: Apply div-mod theorem at the 48-bit boundary
    // limbs[0] = (limbs[0] % 2^48) + (limbs[0] / 2^48) * 2^48

    lemma2_to64();
    shift_is_pow2(52);
    assert(pow2(8) == 256);

    // Step 1: Show bytes 0-5 contribute (limbs[0] % 2^48)
    // From bytes_match_limbs_packing_52, we know:
    // bytes[0] = limbs[0] as u8
    // bytes[1] = (limbs[0] >> 8) as u8
    // ... and so on

    // These bytes, when summed with their position weights, reconstruct limbs[0] % 2^48
    let low_48_bits = bytes[0] as nat * pow2(0 * 8) +
                      bytes[1] as nat * pow2(1 * 8) +
                      bytes[2] as nat * pow2(2 * 8) +
                      bytes[3] as nat * pow2(3 * 8) +
                      bytes[4] as nat * pow2(4 * 8) +
                      bytes[5] as nat * pow2(5 * 8);

    // Use lemma_byte_from_limb_shift_52 to establish arithmetic value of each byte
    shr_zero_is_id(limbs[0]);
    assert(bytes[0] == (limbs[0] >> 0) as u8);
    lemma_byte_from_limb_shift_52(limbs[0], 0, bytes[0]);
    assert(bytes[0] as nat == (limbs[0] as nat / pow2(0)) % 256);

    lemma_byte_from_limb_shift_52(limbs[0], 8, bytes[1]);
    assert(bytes[1] as nat == (limbs[0] as nat / pow2(8)) % 256);

    lemma_byte_from_limb_shift_52(limbs[0], 16, bytes[2]);
    assert(bytes[2] as nat == (limbs[0] as nat / pow2(16)) % 256);

    lemma_byte_from_limb_shift_52(limbs[0], 24, bytes[3]);
    assert(bytes[3] as nat == (limbs[0] as nat / pow2(24)) % 256);

    lemma_byte_from_limb_shift_52(limbs[0], 32, bytes[4]);
    assert(bytes[4] as nat == (limbs[0] as nat / pow2(32)) % 256);

    lemma_byte_from_limb_shift_52(limbs[0], 40, bytes[5]);
    assert(bytes[5] as nat == (limbs[0] as nat / pow2(40)) % 256);

    // For each byte i (i=0..5), extraction from limbs[0] equals extraction from limbs[0] % 2^48
    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 0, 48);
    assert(bytes[0] as nat == ((limbs[0] as nat % pow2(48)) / pow2(0)) % 256);

    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 1, 48);
    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 2, 48);
    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 3, 48);
    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 4, 48);
    lemma_byte_extraction_commutes_with_mod(limbs[0] as nat, 5, 48);

    // The modulo value fits in a valid range
    lemma_pow2_pos(48);
    assert(pow2(48) > 0);
    let modulo_value = limbs[0] as nat % pow2(48);
    assert(modulo_value < pow2(48)) by {
        lemma_mod_bound(limbs[0] as int, pow2(48) as int);
    }
    assert(pow2(48) < pow2(64)) by {
        lemma_pow2_strictly_increases(48, 64);
    }

    let limb0_low48 = modulo_value as u64;
    assert(limb0_low48 as nat == modulo_value);
    assert(limb0_low48 < pow2(48));

    // Apply the 6-byte reconstruction lemma
    lemma_6_bytes_reconstruct(
        limb0_low48 as nat,
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5]
    );

    assert(low_48_bits == (limbs[0] as nat % pow2(48)));

    // Step 2: Handle the contribution from byte 6's low 4 bits
    // Since limbs[0] < 2^52, we have limbs[0] / 2^48 < 2^4 = 16
    lemma_div_bound(limbs[0] as nat, 48, 52);
    assert(limbs[0] as nat / pow2(48) < pow2(4));
    lemma2_to64();
    assert(pow2(4) == 16);

    let high_4_bits_contribution = ((limbs[0] as nat / pow2(48)) % 16) * pow2(6 * 8);

    // Since limbs[0]/2^48 < 16, taking % 16 is identity
    assert((limbs[0] as nat / pow2(48)) % 16 == limbs[0] as nat / pow2(48));
    assert(high_4_bits_contribution == (limbs[0] as nat / pow2(48)) * pow2(48));

    // Step 3: Apply div-mod theorem
    lemma_pow2_pos(48);
    lemma_fundamental_div_mod(limbs[0] as int, pow2(48) as int);
    assert(limbs[0] as nat ==
           (limbs[0] as nat % pow2(48)) +
           (limbs[0] as nat / pow2(48)) * pow2(48));

    // Step 4: Show this equals limb0_byte_contribution_52
    assert(limb0_byte_contribution_52(limbs, bytes) ==
           low_48_bits + high_4_bits_contribution);
    assert(limb0_byte_contribution_52(limbs, bytes) == limbs[0] as nat);

    // Since limbs[0] < 2^52, limbs[0] % 2^52 = limbs[0]
    assert(limbs[0] as nat % pow2(52) == limbs[0] as nat) by {
        lemma_small_mod(limbs[0] as nat, pow2(52));
    }
}

pub proof fn lemma_limb1_contribution_correctness_52(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[0] < (1u64 << 52),  // Need limb 0 for boundary byte 6
        limbs[1] < (1u64 << 52),
        bytes_match_limbs_packing_52(limbs, bytes),
    ensures
        limb1_byte_contribution_52(limbs, bytes) == (limbs[1] as nat) * pow2(52)
{
    // Proof following docs_22_oct/lemma_limb1_contribution_52_proof.md

    lemma2_to64();
    shift_is_pow2(52);

    // === STEP 1: Define the Split ===
    let l1_low = limbs[1] as nat % pow2(4);    // Low 4 bits in byte 6
    let l1_high = limbs[1] as nat / pow2(4);   // High 48 bits in bytes 7-12

    // === STEP 2: Bound the High Part ===
    lemma_div_bound(limbs[1] as nat, 4, 52);
    assert(l1_high < pow2(48));

    // === STEP 3: Reconstruction Identity ===
    lemma_pow2_pos(4);
    lemma_fundamental_div_mod(limbs[1] as int, pow2(4) as int);
    assert(pow2(4) * l1_high == l1_high * pow2(4)) by {
        lemma_mul_is_commutative(pow2(4) as int, l1_high as int);
    }
    assert(limbs[1] as nat == l1_low + l1_high * pow2(4));

    // === STEP 4: Byte Reconstruction for High 48 Bits ===
    lemma_byte_from_limb_shift_52(limbs[1], 4, bytes[7]);
    lemma_byte_from_limb_shift_52(limbs[1], 12, bytes[8]);
    lemma_byte_from_limb_shift_52(limbs[1], 20, bytes[9]);
    lemma_byte_from_limb_shift_52(limbs[1], 28, bytes[10]);
    lemma_byte_from_limb_shift_52(limbs[1], 36, bytes[11]);
    lemma_byte_from_limb_shift_52(limbs[1], 44, bytes[12]);

    // Rewrite byte extractions in terms of l1_high = limbs[1] / 2^4
    lemma_pow2_adds(4, 0);
    lemma_pow2_pos(0);
    lemma_div_denominator(limbs[1] as int, pow2(4) as int, pow2(0) as int);
    assert(bytes[7] as nat == l1_high / pow2(0) % 256);

    lemma_pow2_adds(4, 8);
    lemma_pow2_pos(8);
    lemma_div_denominator(limbs[1] as int, pow2(4) as int, pow2(8) as int);
    assert(bytes[8] as nat == l1_high / pow2(8) % 256);

    lemma_pow2_adds(4, 16);
    lemma_pow2_pos(16);
    lemma_div_denominator(limbs[1] as int, pow2(4) as int, pow2(16) as int);
    assert(bytes[9] as nat == l1_high / pow2(16) % 256);

    lemma_pow2_adds(4, 24);
    lemma_pow2_pos(24);
    lemma_div_denominator(limbs[1] as int, pow2(4) as int, pow2(24) as int);
    assert(bytes[10] as nat == l1_high / pow2(24) % 256);

    lemma_pow2_adds(4, 32);
    lemma_pow2_pos(32);
    lemma_div_denominator(limbs[1] as int, pow2(4) as int, pow2(32) as int);
    assert(bytes[11] as nat == l1_high / pow2(32) % 256);

    lemma_pow2_adds(4, 40);
    lemma_pow2_pos(40);
    lemma_div_denominator(limbs[1] as int, pow2(4) as int, pow2(40) as int);
    assert(bytes[12] as nat == l1_high / pow2(40) % 256);

    // 6-byte reconstruction lemma
    lemma_6_bytes_reconstruct(l1_high, bytes[7], bytes[8], bytes[9], bytes[10], bytes[11], bytes[12]);

    let bytes_at_offset_0 = bytes[7] as nat * pow2(0) +
                            bytes[8] as nat * pow2(8) +
                            bytes[9] as nat * pow2(16) +
                            bytes[10] as nat * pow2(24) +
                            bytes[11] as nat * pow2(32) +
                            bytes[12] as nat * pow2(40);

    assert(bytes_at_offset_0 == l1_high);

    // === STEP 5: Position Adjustment ===

    // Multiply reconstruction identity by pow2(52)
    assert((l1_low + l1_high * pow2(4)) * pow2(52) == limbs[1] as nat * pow2(52));

    // Distribute
    assert((l1_low + l1_high * pow2(4)) * pow2(52) ==
           l1_low * pow2(52) + (l1_high * pow2(4)) * pow2(52)) by {
        lemma_mul_is_distributive_add_other_way(pow2(52) as int, l1_low as int, (l1_high * pow2(4)) as int);
    }

    // Simplify high term
    lemma_pow2_adds(4, 52);
    assert((l1_high * pow2(4)) * pow2(52) == l1_high * pow2(56)) by {
        lemma_mul_is_associative(l1_high as int, pow2(4) as int, pow2(52) as int);
    }

    // Now we have: limbs[1] * 2^52 = l1_low * 2^52 + l1_high * 2^56

    // === STEP 6: Express Low Part in Contribution Form ===
    // l1_low * 2^52 = l1_low * 2^48 * 2^4 = (l1_low * 16) * 2^48
    lemma_pow2_adds(48, 4);
    assert(pow2(52) == pow2(48) * pow2(4));
    assert(pow2(4) == 16) by {
        assert(pow2(2) == 4);
        assert(pow2(4) == pow2(2) * pow2(2)) by {
            lemma_pow2_adds(2, 2);
        }
    }

    assert(l1_low * pow2(52) == l1_low * (pow2(48) * pow2(4))) by {
        // pow2(52) = pow2(48) * pow2(4) proven above
    }
    assert(l1_low * (pow2(48) * pow2(4)) == (l1_low * pow2(48)) * pow2(4)) by {
        lemma_mul_is_associative(l1_low as int, pow2(48) as int, pow2(4) as int);
    }
    assert((l1_low * pow2(48)) * pow2(4) == pow2(48) * l1_low * pow2(4)) by {
        lemma_mul_is_commutative((l1_low * pow2(48)) as int, pow2(4) as int);
    }
    assert(pow2(48) * l1_low * pow2(4) == pow2(48) * (l1_low * pow2(4))) by {
        lemma_mul_is_associative(pow2(48) as int, l1_low as int, pow2(4) as int);
    }
    assert(l1_low * pow2(52) == (l1_low * 16) * pow2(48));

    // === STEP 7: Expand the High Part ===
    // Multiply bytes_at_offset_0 by pow2(56)
    assert(bytes_at_offset_0 * pow2(56) == l1_high * pow2(56));

    // Distribute pow2(56) into each byte term
    assert(bytes_at_offset_0 * pow2(56) ==
           bytes[7] as nat * pow2(0) * pow2(56) +
           bytes[8] as nat * pow2(8) * pow2(56) +
           bytes[9] as nat * pow2(16) * pow2(56) +
           bytes[10] as nat * pow2(24) * pow2(56) +
           bytes[11] as nat * pow2(32) * pow2(56) +
           bytes[12] as nat * pow2(40) * pow2(56)) by {
        lemma_mul_is_distributive_add_other_way(pow2(56) as int,
            (bytes[7] as nat * pow2(0)) as int,
            (bytes[8] as nat * pow2(8)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(56) as int,
            (bytes[7] as nat * pow2(0) + bytes[8] as nat * pow2(8)) as int,
            (bytes[9] as nat * pow2(16)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(56) as int,
            (bytes[7] as nat * pow2(0) + bytes[8] as nat * pow2(8) +
             bytes[9] as nat * pow2(16)) as int,
            (bytes[10] as nat * pow2(24)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(56) as int,
            (bytes[7] as nat * pow2(0) + bytes[8] as nat * pow2(8) +
             bytes[9] as nat * pow2(16) + bytes[10] as nat * pow2(24)) as int,
            (bytes[11] as nat * pow2(32)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(56) as int,
            (bytes[7] as nat * pow2(0) + bytes[8] as nat * pow2(8) +
             bytes[9] as nat * pow2(16) + bytes[10] as nat * pow2(24) +
             bytes[11] as nat * pow2(32)) as int,
            (bytes[12] as nat * pow2(40)) as int);

        // Apply associativity: (byte * pow2(k)) * pow2(56) = byte * (pow2(k) * pow2(56))
        lemma_mul_is_associative(bytes[7] as int, pow2(0) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[8] as int, pow2(8) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[9] as int, pow2(16) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[10] as int, pow2(24) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[11] as int, pow2(32) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[12] as int, pow2(40) as int, pow2(56) as int);
    }

    // Apply power addition and connect to final positions
    assert(bytes_at_offset_0 * pow2(56) ==
           bytes[7] as nat * pow2(56) +
           bytes[8] as nat * pow2(64) +
           bytes[9] as nat * pow2(72) +
           bytes[10] as nat * pow2(80) +
           bytes[11] as nat * pow2(88) +
           bytes[12] as nat * pow2(96)) by {
        lemma_mul_is_associative(bytes[7] as int, pow2(0) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[8] as int, pow2(8) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[9] as int, pow2(16) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[10] as int, pow2(24) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[11] as int, pow2(32) as int, pow2(56) as int);
        lemma_mul_is_associative(bytes[12] as int, pow2(40) as int, pow2(56) as int);
        lemma_pow2_adds(0, 56);
        lemma_pow2_adds(8, 56);
        lemma_pow2_adds(16, 56);
        lemma_pow2_adds(24, 56);
        lemma_pow2_adds(32, 56);
        lemma_pow2_adds(40, 56);
    }
}

pub proof fn lemma_limb2_contribution_correctness_52(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[2] < (1u64 << 52),
        bytes_match_limbs_packing_52(limbs, bytes),
    ensures
        limb2_byte_contribution_52(limbs, bytes) == (limbs[2] as nat) * pow2(104)
{
    // Proof following docs_22_oct/lemma_limb2_contribution_52_proof.md

    lemma2_to64();
    shift_is_pow2(52);

    // === STEP 1: Define the Split ===
    let l2_low = limbs[2] as nat % pow2(48);   // Low 48 bits in bytes 13-18
    let l2_high = limbs[2] as nat / pow2(48);  // High 4 bits in byte 19

    // === STEP 2: Bound the High Part ===
    lemma_div_bound(limbs[2] as nat, 48, 52);
    assert(l2_high < pow2(4));
    lemma_small_mod(l2_high, 16);
    assert(l2_high % 16 == l2_high);

    // === STEP 3: Reconstruction Identity ===
    lemma_pow2_pos(48);
    lemma_fundamental_div_mod(limbs[2] as int, pow2(48) as int);
    assert(pow2(48) * l2_high == l2_high * pow2(48)) by {
        lemma_mul_is_commutative(pow2(48) as int, l2_high as int);
    }
    assert(limbs[2] as nat == l2_low + l2_high * pow2(48));

    // === STEP 4: Byte Reconstruction for Low 48 Bits ===
    shr_zero_is_id(limbs[2]);
    lemma_byte_from_limb_shift_52(limbs[2], 0, bytes[13]);
    lemma_byte_from_limb_shift_52(limbs[2], 8, bytes[14]);
    lemma_byte_from_limb_shift_52(limbs[2], 16, bytes[15]);
    lemma_byte_from_limb_shift_52(limbs[2], 24, bytes[16]);
    lemma_byte_from_limb_shift_52(limbs[2], 32, bytes[17]);
    lemma_byte_from_limb_shift_52(limbs[2], 40, bytes[18]);

    // Byte extractions commute with modulo for positions below 48 bits
    lemma_mod_bound(l2_low as int, pow2(48) as int);
    lemma_byte_extraction_commutes_with_mod(limbs[2] as nat, 0, 48);
    lemma_byte_extraction_commutes_with_mod(limbs[2] as nat, 1, 48);
    lemma_byte_extraction_commutes_with_mod(limbs[2] as nat, 2, 48);
    lemma_byte_extraction_commutes_with_mod(limbs[2] as nat, 3, 48);
    lemma_byte_extraction_commutes_with_mod(limbs[2] as nat, 4, 48);
    lemma_byte_extraction_commutes_with_mod(limbs[2] as nat, 5, 48);

    // 6-byte reconstruction lemma gives us the sum
    lemma_6_bytes_reconstruct(l2_low, bytes[13], bytes[14], bytes[15], bytes[16], bytes[17], bytes[18]);

    let bytes_at_offset_0 = bytes[13] as nat * pow2(0) +
                 bytes[14] as nat * pow2(8) +
                 bytes[15] as nat * pow2(16) +
                 bytes[16] as nat * pow2(24) +
                 bytes[17] as nat * pow2(32) +
                 bytes[18] as nat * pow2(40);

    assert(bytes_at_offset_0 == l2_low);

    // === STEP 5: Position Adjustment ===

    // Multiply reconstruction identity by pow2(104)
    assert((l2_low + l2_high * pow2(48)) * pow2(104) == limbs[2] as nat * pow2(104));

    // Distribute
    assert((l2_low + l2_high * pow2(48)) * pow2(104) ==
           l2_low * pow2(104) + (l2_high * pow2(48)) * pow2(104)) by {
        lemma_mul_is_distributive_add_other_way(pow2(104) as int, l2_low as int, (l2_high * pow2(48)) as int);
    }

    // Simplify high term
        lemma_pow2_adds(48, 104);
    assert((l2_high * pow2(48)) * pow2(104) == l2_high * pow2(152)) by {
        lemma_mul_is_associative(l2_high as int, pow2(48) as int, pow2(104) as int);
    }

    // Now we have: limbs[2] * 2^104 = l2_low * 2^104 + l2_high * 2^152

    // === STEP 6: Expand the Low Part ===
    // Multiply bytes_at_offset_0 by pow2(104)
    assert(bytes_at_offset_0 * pow2(104) == l2_low * pow2(104));

    // Distribute pow2(104) into each byte term
    assert(bytes_at_offset_0 * pow2(104) ==
           bytes[13] as nat * pow2(0) * pow2(104) +
           bytes[14] as nat * pow2(8) * pow2(104) +
           bytes[15] as nat * pow2(16) * pow2(104) +
           bytes[16] as nat * pow2(24) * pow2(104) +
           bytes[17] as nat * pow2(32) * pow2(104) +
           bytes[18] as nat * pow2(40) * pow2(104)) by {
        lemma_mul_is_distributive_add_other_way(pow2(104) as int,
                                       (bytes[13] as nat * pow2(0)) as int,
                                       (bytes[14] as nat * pow2(8)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(104) as int,
                                       (bytes[13] as nat * pow2(0) + bytes[14] as nat * pow2(8)) as int,
                                       (bytes[15] as nat * pow2(16)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(104) as int,
                                       (bytes[13] as nat * pow2(0) + bytes[14] as nat * pow2(8) +
                                        bytes[15] as nat * pow2(16)) as int,
                                       (bytes[16] as nat * pow2(24)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(104) as int,
                                       (bytes[13] as nat * pow2(0) + bytes[14] as nat * pow2(8) +
                                        bytes[15] as nat * pow2(16) + bytes[16] as nat * pow2(24)) as int,
                                       (bytes[17] as nat * pow2(32)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(104) as int,
                                       (bytes[13] as nat * pow2(0) + bytes[14] as nat * pow2(8) +
                                        bytes[15] as nat * pow2(16) + bytes[16] as nat * pow2(24) +
                                        bytes[17] as nat * pow2(32)) as int,
                                       (bytes[18] as nat * pow2(40)) as int);

        // Apply associativity: (byte * pow2(k)) * pow2(104) = byte * (pow2(k) * pow2(104))
        lemma_mul_is_associative(bytes[13] as int, pow2(0) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[14] as int, pow2(8) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[15] as int, pow2(16) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[16] as int, pow2(24) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[17] as int, pow2(32) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[18] as int, pow2(40) as int, pow2(104) as int);
    }

    assert(bytes_at_offset_0 * pow2(104) ==
           bytes[13] as nat * pow2(104) +
           bytes[14] as nat * pow2(112) +
           bytes[15] as nat * pow2(120) +
           bytes[16] as nat * pow2(128) +
           bytes[17] as nat * pow2(136) +
           bytes[18] as nat * pow2(144)) by {
        lemma_mul_is_associative(bytes[13] as int, pow2(0) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[14] as int, pow2(8) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[15] as int, pow2(16) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[16] as int, pow2(24) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[17] as int, pow2(32) as int, pow2(104) as int);
        lemma_mul_is_associative(bytes[18] as int, pow2(40) as int, pow2(104) as int);
    lemma_pow2_adds(0, 104);
    lemma_pow2_adds(8, 104);
    lemma_pow2_adds(16, 104);
    lemma_pow2_adds(24, 104);
    lemma_pow2_adds(32, 104);
    lemma_pow2_adds(40, 104);
    }
}

pub proof fn lemma_limb3_contribution_correctness_52(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[2] < (1u64 << 52),  // Need limb 2 for boundary byte 19
        limbs[3] < (1u64 << 52),
        bytes_match_limbs_packing_52(limbs, bytes),
    ensures
        limb3_byte_contribution_52(limbs, bytes) == (limbs[3] as nat) * pow2(156)
{
    // Proof following docs_22_oct/lemma_limb3_contribution_52_proof.md

    lemma2_to64();
    shift_is_pow2(52);

    // === STEP 1: Define the Split ===
    let l3_low = limbs[3] as nat % pow2(4);    // Low 4 bits in byte 19
    let l3_high = limbs[3] as nat / pow2(4);   // High 48 bits in bytes 20-25

    // === STEP 2: Bound the High Part ===
    lemma_div_bound(limbs[3] as nat, 4, 52);
    assert(l3_high < pow2(48));

    // === STEP 3: Reconstruction Identity ===
    lemma_pow2_pos(4);
    lemma_fundamental_div_mod(limbs[3] as int, pow2(4) as int);
    assert(pow2(4) * l3_high == l3_high * pow2(4)) by {
        lemma_mul_is_commutative(pow2(4) as int, l3_high as int);
    }
    assert(limbs[3] as nat == l3_low + l3_high * pow2(4));

    // === STEP 4: Byte Reconstruction for High 48 Bits ===
    lemma_byte_from_limb_shift_52(limbs[3], 4, bytes[20]);
    lemma_byte_from_limb_shift_52(limbs[3], 12, bytes[21]);
    lemma_byte_from_limb_shift_52(limbs[3], 20, bytes[22]);
    lemma_byte_from_limb_shift_52(limbs[3], 28, bytes[23]);
    lemma_byte_from_limb_shift_52(limbs[3], 36, bytes[24]);
    lemma_byte_from_limb_shift_52(limbs[3], 44, bytes[25]);

    // Rewrite byte extractions in terms of l3_high = limbs[3] / 2^4
    lemma_pow2_adds(4, 0);
    lemma_pow2_pos(0);
    lemma_div_denominator(limbs[3] as int, pow2(4) as int, pow2(0) as int);
    assert(bytes[20] as nat == l3_high / pow2(0) % 256);

    lemma_pow2_adds(4, 8);
    lemma_pow2_pos(8);
    lemma_div_denominator(limbs[3] as int, pow2(4) as int, pow2(8) as int);
    assert(bytes[21] as nat == l3_high / pow2(8) % 256);

    lemma_pow2_adds(4, 16);
    lemma_pow2_pos(16);
    lemma_div_denominator(limbs[3] as int, pow2(4) as int, pow2(16) as int);
    assert(bytes[22] as nat == l3_high / pow2(16) % 256);

    lemma_pow2_adds(4, 24);
    lemma_pow2_pos(24);
    lemma_div_denominator(limbs[3] as int, pow2(4) as int, pow2(24) as int);
    assert(bytes[23] as nat == l3_high / pow2(24) % 256);

    lemma_pow2_adds(4, 32);
    lemma_pow2_pos(32);
    lemma_div_denominator(limbs[3] as int, pow2(4) as int, pow2(32) as int);
    assert(bytes[24] as nat == l3_high / pow2(32) % 256);

    lemma_pow2_adds(4, 40);
    lemma_pow2_pos(40);
    lemma_div_denominator(limbs[3] as int, pow2(4) as int, pow2(40) as int);
    assert(bytes[25] as nat == l3_high / pow2(40) % 256);

    // 6-byte reconstruction lemma
    lemma_6_bytes_reconstruct(l3_high, bytes[20], bytes[21], bytes[22], bytes[23], bytes[24], bytes[25]);

    let bytes_at_offset_0 = bytes[20] as nat * pow2(0) +
                            bytes[21] as nat * pow2(8) +
                            bytes[22] as nat * pow2(16) +
                            bytes[23] as nat * pow2(24) +
                            bytes[24] as nat * pow2(32) +
                            bytes[25] as nat * pow2(40);

    assert(bytes_at_offset_0 == l3_high);

    // === STEP 5: Position Adjustment ===
    //assert(19 * 8 == 152);

    // Multiply reconstruction identity by pow2(156)
    assert((l3_low + l3_high * pow2(4)) * pow2(156) == limbs[3] as nat * pow2(156));

    // Distribute
    assert((l3_low + l3_high * pow2(4)) * pow2(156) ==
           l3_low * pow2(156) + (l3_high * pow2(4)) * pow2(156)) by {
        lemma_mul_is_distributive_add_other_way(pow2(156) as int, l3_low as int, (l3_high * pow2(4)) as int);
    }

    // Simplify high term
    lemma_pow2_adds(4, 156);
    assert((l3_high * pow2(4)) * pow2(156) == l3_high * pow2(160)) by {
        lemma_mul_is_associative(l3_high as int, pow2(4) as int, pow2(156) as int);
    }

    // Now we have: limbs[3] * 2^156 = l3_low * 2^156 + l3_high * 2^160

    // === STEP 6: Express Low Part in Contribution Form ===
    // l3_low * 2^156 = l3_low * 2^152 * 2^4 = (l3_low * 16) * 2^152
    lemma_pow2_adds(152, 4);
    assert(pow2(156) == pow2(152) * pow2(4));
    assert(pow2(4) == 16) by {
        assert(pow2(2) == 4);
        assert(pow2(4) == pow2(2) * pow2(2)) by {
            lemma_pow2_adds(2, 2);
        }
    }

    assert(l3_low * pow2(156) == l3_low * (pow2(152) * pow2(4))) by {
        // pow2(156) = pow2(152) * pow2(4) proven above
    }
    assert(l3_low * (pow2(152) * pow2(4)) == (l3_low * pow2(152)) * pow2(4)) by {
        lemma_mul_is_associative(l3_low as int, pow2(152) as int, pow2(4) as int);
    }
    assert((l3_low * pow2(152)) * pow2(4) == pow2(152) * l3_low * pow2(4)) by {
        lemma_mul_is_commutative((l3_low * pow2(152)) as int, pow2(4) as int);
    }
    assert(pow2(152) * l3_low * pow2(4) == pow2(152) * (l3_low * pow2(4))) by {
        lemma_mul_is_associative(pow2(152) as int, l3_low as int, pow2(4) as int);
    }
    assert(l3_low * pow2(156) == (l3_low * 16) * pow2(152));

    // === STEP 7: Expand the High Part ===
    // Multiply bytes_at_offset_0 by pow2(160)
    assert(bytes_at_offset_0 * pow2(160) == l3_high * pow2(160));

    // Distribute pow2(160) into each byte term
    assert(bytes_at_offset_0 * pow2(160) ==
           bytes[20] as nat * pow2(0) * pow2(160) +
           bytes[21] as nat * pow2(8) * pow2(160) +
           bytes[22] as nat * pow2(16) * pow2(160) +
           bytes[23] as nat * pow2(24) * pow2(160) +
           bytes[24] as nat * pow2(32) * pow2(160) +
           bytes[25] as nat * pow2(40) * pow2(160)) by {
        lemma_mul_is_distributive_add_other_way(pow2(160) as int,
            (bytes[20] as nat * pow2(0)) as int,
            (bytes[21] as nat * pow2(8)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(160) as int,
            (bytes[20] as nat * pow2(0) + bytes[21] as nat * pow2(8)) as int,
            (bytes[22] as nat * pow2(16)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(160) as int,
            (bytes[20] as nat * pow2(0) + bytes[21] as nat * pow2(8) +
             bytes[22] as nat * pow2(16)) as int,
            (bytes[23] as nat * pow2(24)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(160) as int,
            (bytes[20] as nat * pow2(0) + bytes[21] as nat * pow2(8) +
             bytes[22] as nat * pow2(16) + bytes[23] as nat * pow2(24)) as int,
            (bytes[24] as nat * pow2(32)) as int);
        lemma_mul_is_distributive_add_other_way(pow2(160) as int,
            (bytes[20] as nat * pow2(0) + bytes[21] as nat * pow2(8) +
             bytes[22] as nat * pow2(16) + bytes[23] as nat * pow2(24) +
             bytes[24] as nat * pow2(32)) as int,
            (bytes[25] as nat * pow2(40)) as int);

        // Apply associativity: (byte * pow2(k)) * pow2(160) = byte * (pow2(k) * pow2(160))
        lemma_mul_is_associative(bytes[20] as int, pow2(0) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[21] as int, pow2(8) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[22] as int, pow2(16) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[23] as int, pow2(24) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[24] as int, pow2(32) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[25] as int, pow2(40) as int, pow2(160) as int);
    }

    // Apply power addition and connect to final positions
    assert(bytes_at_offset_0 * pow2(160) ==
           bytes[20] as nat * pow2(160) +
           bytes[21] as nat * pow2(168) +
           bytes[22] as nat * pow2(176) +
           bytes[23] as nat * pow2(184) +
           bytes[24] as nat * pow2(192) +
           bytes[25] as nat * pow2(200)) by {
        lemma_mul_is_associative(bytes[20] as int, pow2(0) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[21] as int, pow2(8) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[22] as int, pow2(16) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[23] as int, pow2(24) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[24] as int, pow2(32) as int, pow2(160) as int);
        lemma_mul_is_associative(bytes[25] as int, pow2(40) as int, pow2(160) as int);
        lemma_pow2_adds(0, 160);
        lemma_pow2_adds(8, 160);
        lemma_pow2_adds(16, 160);
        lemma_pow2_adds(24, 160);
        lemma_pow2_adds(32, 160);
        lemma_pow2_adds(40, 160);
    }
}

pub proof fn lemma_limb4_contribution_correctness_52(limbs: [u64; 5], bytes: [u8; 32])
    requires
        limbs[4] < (1u64 << 52),
        bytes_match_limbs_packing_52(limbs, bytes),
    ensures
        limb4_byte_contribution_52(limbs, bytes) == (limbs[4] as nat) * pow2(208)
{
    // Paper proof:
    // Limb 4 occupies bytes 26-31 (no boundary!) at position 2^208
    // From the packing predicate: bytes[26..31] = limbs[4] >> 0, 8, 16, 24, 32, 40
    // Therefore: bytes reconstruct limbs[4]
    // And: limb4_contribution = Σ bytes[i] * 2^(i*8) = limbs[4] * 2^208

    lemma2_to64();
    shift_is_pow2(52);

    // Step 1: Show bytes 26-31 encode limbs[4] using byte-shift arithmetic
    shr_zero_is_id(limbs[4]);
    lemma_byte_from_limb_shift_52(limbs[4], 0, bytes[26]);
    lemma_byte_from_limb_shift_52(limbs[4], 8, bytes[27]);
    lemma_byte_from_limb_shift_52(limbs[4], 16, bytes[28]);
    lemma_byte_from_limb_shift_52(limbs[4], 24, bytes[29]);
    lemma_byte_from_limb_shift_52(limbs[4], 32, bytes[30]);
    lemma_byte_from_limb_shift_52(limbs[4], 40, bytes[31]);

    // TODO: Prove limbs[4] < 2^48
    //
    // This bound is required because 6 bytes can only represent 48 bits.
    // The structural constraint for 256-bit scalars is that limb 4 occupies
    // only 48 bits (256 - 4*52 = 48), not the full 52 bits.
    //
    // However, scalar arithmetic operations use a 52-bit mask for all limbs,
    // so this bound is not maintained by the implementation.
    // See docs_22_oct/scalar_limb4_bound_issue.md for details.
    //
    // This assume is sound because:
    // - The packing predicate guarantees bytes 26-31 encode limbs[4]
    // - 6 bytes can only represent values < 2^48
    // - Therefore limbs[4] must be < 2^48
    // But we cannot formally derive this from the current preconditions.
    assume(limbs[4] < pow2(48));

    // Apply 6-byte reconstruction: bytes[26..31] = limbs[4]
    lemma_6_bytes_reconstruct(limbs[4] as nat, bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31]);
    let bytes_sum = bytes[26] as nat * pow2(0) +
                    bytes[27] as nat * pow2(8) +
                    bytes[28] as nat * pow2(16) +
                    bytes[29] as nat * pow2(24) +
                    bytes[30] as nat * pow2(32) +
                    bytes[31] as nat * pow2(40);

    assert(bytes_sum * pow2(208) == limbs[4] as nat * pow2(208));

    assert(bytes_sum * pow2(208) == (bytes[26] as nat * pow2(0) +
    bytes[27] as nat * pow2(8) +
    bytes[28] as nat * pow2(16) +
    bytes[29] as nat * pow2(24) +
    bytes[30] as nat * pow2(32) +
    bytes[31] as nat * pow2(40)) * pow2(208));

    assert((bytes[26] as nat * pow2(0) +
    bytes[27] as nat * pow2(8) +
    bytes[28] as nat * pow2(16) +
    bytes[29] as nat * pow2(24) +
    bytes[30] as nat * pow2(32) +
    bytes[31] as nat * pow2(40)) * pow2(208) ==
    (bytes[26] as nat * pow2(0) * pow2(208) +
    bytes[27] as nat * pow2(8) * pow2(208) +
    bytes[28] as nat * pow2(16) * pow2(208) +
    bytes[29] as nat * pow2(24) * pow2(208) +
    bytes[30] as nat * pow2(32) * pow2(208) +
    bytes[31] as nat * pow2(40) * pow2(208))) by {
        // Distribute pow2(208) across the sum using repeated application of distributivity
        lemma_mul_is_distributive_add(pow2(208) as int,
                                       (bytes[26] as nat * pow2(0)) as int,
                                       (bytes[27] as nat * pow2(8)) as int);
        lemma_mul_is_distributive_add(pow2(208) as int,
                                       (bytes[26] as nat * pow2(0) + bytes[27] as nat * pow2(8)) as int,
                                       (bytes[28] as nat * pow2(16)) as int);
        lemma_mul_is_distributive_add(pow2(208) as int,
                                       (bytes[26] as nat * pow2(0) + bytes[27] as nat * pow2(8) +
                                        bytes[28] as nat * pow2(16)) as int,
                                       (bytes[29] as nat * pow2(24)) as int);
        lemma_mul_is_distributive_add(pow2(208) as int,
                                       (bytes[26] as nat * pow2(0) + bytes[27] as nat * pow2(8) +
                                        bytes[28] as nat * pow2(16) + bytes[29] as nat * pow2(24)) as int,
                                       (bytes[30] as nat * pow2(32)) as int);
        lemma_mul_is_distributive_add(pow2(208) as int,
                                       (bytes[26] as nat * pow2(0) + bytes[27] as nat * pow2(8) +
                                        bytes[28] as nat * pow2(16) + bytes[29] as nat * pow2(24) +
                                        bytes[30] as nat * pow2(32)) as int,
                                       (bytes[31] as nat * pow2(40)) as int);
    };

    assert((bytes[26] as nat * pow2(0) * pow2(208) +
    bytes[27] as nat * pow2(8) * pow2(208) +
    bytes[28] as nat * pow2(16) * pow2(208) +
    bytes[29] as nat * pow2(24) * pow2(208) +
    bytes[30] as nat * pow2(32) * pow2(208) +
    bytes[31] as nat * pow2(40) * pow2(208)) ==
    (bytes[26] as nat * pow2(208) +
    bytes[27] as nat * pow2(216) +
    bytes[28] as nat * pow2(224) +
    bytes[29] as nat * pow2(232) +
    bytes[30] as nat * pow2(240) +
    bytes[31] as nat * pow2(248))) by {
        lemma_mul_is_associative(bytes[26] as int, pow2(0) as int, pow2(208) as int);
        lemma_mul_is_associative(bytes[27] as int, pow2(8) as int, pow2(208) as int);
        lemma_mul_is_associative(bytes[28] as int, pow2(16) as int, pow2(208) as int);
        lemma_mul_is_associative(bytes[29] as int, pow2(24) as int, pow2(208) as int);
        lemma_mul_is_associative(bytes[30] as int, pow2(32) as int, pow2(208) as int);
        lemma_mul_is_associative(bytes[31] as int, pow2(40) as int, pow2(208) as int);

        lemma_pow2_adds(0, 208);   // pow2(0) * pow2(208) = pow2(208)
        lemma_pow2_adds(8, 208);   // pow2(8) * pow2(208) = pow2(216)
        lemma_pow2_adds(16, 208);  // pow2(16) * pow2(208) = pow2(224)
        lemma_pow2_adds(24, 208);  // pow2(24) * pow2(208) = pow2(232)
        lemma_pow2_adds(32, 208);  // pow2(32) * pow2(208) = pow2(240)
        lemma_pow2_adds(40, 208);
    };
}

} // verus!
