//! Lemmas about Edwards curve constants
//!
//! This module contains proofs about the properties of Edwards curve constants:
//! - `EDWARDS_D`: the curve parameter `d` in the twisted Edwards equation
//! - `BASEPOINT_ORDER_PRIVATE`: the group order ℓ encoded as a Scalar
//!
//! ## Mathematical Background
//!
//! EDWARDS_D is the curve parameter `d` in the twisted Edwards curve equation:
//! ```text
//! -x² + y² = 1 + d·x²·y²
//! ```
//!
//! The constant is represented in 51-bit limb form:
//! ```text
//! d = limbs[0] + 2^51·limbs[1] + 2^102·limbs[2] + 2^153·limbs[3] + 2^204·limbs[4]
//! ```
//!
//! ## Note
//!
//! - EDWARDS_D2 (= 2·d) lemmas are in `unused_constants_lemmas.rs` (currently unused).
#![allow(unused_imports)]
use crate::backend::serial::u64::constants::EDWARDS_D;
use crate::backend::serial::u64::field::FieldElement51;
use crate::constants;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar52_specs::group_order;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::scalar_to_nat;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma2_to64, lemma2_to64_rest, lemma_pow2_adds, pow2};
use vstd::prelude::*;

verus! {

// =============================================================================
// EDWARDS_D Lemmas
// =============================================================================
/// EDWARDS_D has 51-bit bounded limbs
///
/// ## Mathematical Proof
/// Each limb of EDWARDS_D is a specific constant < 2^51:
/// - limbs[0] = 929955233495203 < 2^51 ✓
/// - limbs[1] = 466365720129213 < 2^51 ✓
/// - limbs[2] = 1662059464998953 < 2^51 ✓
/// - limbs[3] = 2033849074728123 < 2^51 ✓
/// - limbs[4] = 1442794654840575 < 2^51 ✓
pub(crate) proof fn lemma_edwards_d_limbs_bounded()
    ensures
        fe51_limbs_bounded(&EDWARDS_D, 51),
{
    // Goal: All EDWARDS_D limbs < 2^51
    assert(fe51_limbs_bounded(&EDWARDS_D, 51)) by {
        assert(929955233495203u64 < (1u64 << 51)) by (bit_vector);
        assert(466365720129213u64 < (1u64 << 51)) by (bit_vector);
        assert(1662059464998953u64 < (1u64 << 51)) by (bit_vector);
        assert(2033849074728123u64 < (1u64 << 51)) by (bit_vector);
        assert(1442794654840575u64 < (1u64 << 51)) by (bit_vector);
    };
}

/// EDWARDS_D has 54-bit bounded limbs
///
/// ## Mathematical Proof
/// 51-bit bounded ⟹ 54-bit bounded since 2^51 < 2^54
pub(crate) proof fn lemma_edwards_d_limbs_bounded_54()
    ensures
        fe51_limbs_bounded(&EDWARDS_D, 54),
{
    // Goal: All EDWARDS_D limbs < 2^54
    assert(fe51_limbs_bounded(&EDWARDS_D, 54)) by {
        lemma_edwards_d_limbs_bounded();
        assert((1u64 << 51) < (1u64 << 54)) by (bit_vector);
    };
}

// =============================================================================
// EDWARDS_D2 Lemmas
// =============================================================================
/// EDWARDS_D2 has 51-bit bounded limbs
///
/// ## Mathematical Proof
/// Each limb of EDWARDS_D2 is a specific constant < 2^51:
/// - limbs[0] = 1859910466990425 < 2^51 ✓
/// - limbs[1] = 932731440258426 < 2^51 ✓
/// - limbs[2] = 1072319116312658 < 2^51 ✓
/// - limbs[3] = 1815898335770999 < 2^51 ✓
/// - limbs[4] = 633789495995903 < 2^51 ✓
pub(crate) proof fn lemma_edwards_d2_limbs_bounded()
    ensures
        fe51_limbs_bounded(&constants::EDWARDS_D2, 51),
{
    assert(fe51_limbs_bounded(&constants::EDWARDS_D2, 51)) by {
        assert(1859910466990425u64 < (1u64 << 51)) by (bit_vector);
        assert(932731440258426u64 < (1u64 << 51)) by (bit_vector);
        assert(1072319116312658u64 < (1u64 << 51)) by (bit_vector);
        assert(1815898335770999u64 < (1u64 << 51)) by (bit_vector);
        assert(633789495995903u64 < (1u64 << 51)) by (bit_vector);
    };
}

/// EDWARDS_D2 has 54-bit bounded limbs
///
/// ## Mathematical Proof
/// 51-bit bounded ⟹ 54-bit bounded since 2^51 < 2^54
pub(crate) proof fn lemma_edwards_d2_limbs_bounded_54()
    ensures
        fe51_limbs_bounded(&constants::EDWARDS_D2, 54),
{
    assert(fe51_limbs_bounded(&constants::EDWARDS_D2, 54)) by {
        lemma_edwards_d2_limbs_bounded();
        assert((1u64 << 51) < (1u64 << 54)) by (bit_vector);
    };
}

/// EDWARDS_D2 equals 2 * EDWARDS_D in the field
///
/// ## Mathematical Background
/// EDWARDS_D2 is precomputed as 2*d mod p in the curve25519-dalek library.
/// This is a well-established relationship for the curve25519 constants.
///
/// The postcondition states that spec_field_element(&EDWARDS_D2) equals
/// math_field_mul(2, spec_field_element(&EDWARDS_D)), i.e., 2*d mod p.
pub(crate) proof fn axiom_edwards_d2_is_2d()
    ensures
        spec_field_element(&constants::EDWARDS_D2) == math_field_mul(
            2,
            spec_field_element(&EDWARDS_D),
        ),
{
    // Trusted assumption.
    //
    // `constants::EDWARDS_D2` is the concrete FieldElement constant intended to equal
    // `2 * constants::EDWARDS_D` in GF(p), where p = 2^255 - 19.
    //
    // This relationship is enforced by a runtime unit test (see `curve25519-dalek/src/constants.rs`)
    // and matches the upstream curve25519-dalek definition of EDWARDS_D2.
    admit();
}

// =============================================================================
// BASEPOINT_ORDER_PRIVATE Lemmas
// =============================================================================
/// BASEPOINT_ORDER_PRIVATE encodes the (prime) subgroup order ℓ in little-endian bytes.
///
/// This lemma bridges the byte-level constant to the `group_order()` nat used in specs.
/// The group order is: ℓ = 2^252 + 27742317777372353535851937790883648493
pub(crate) proof fn lemma_scalar_to_nat_basepoint_order_private_equals_group_order()
    ensures
        scalar_to_nat(&constants::BASEPOINT_ORDER_PRIVATE) == group_order(),
{
    // Expand the (little-endian) 32-byte constant into its nat value.
    //
    // bytes = [ed, d3, f5, 5c, 1a, 63, 12, 58, d6, 9c, f7, a2, de, f9, de, 14,
    //          00 .. 00, 10]
    let expanded: nat = 237nat * pow2(0) + 211nat * pow2(8) + 245nat * pow2(16) + 92nat * pow2(24)
        + 26nat * pow2(32) + 99nat * pow2(40) + 18nat * pow2(48) + 88nat * pow2(56) + 214nat * pow2(
        64,
    ) + 156nat * pow2(72) + 247nat * pow2(80) + 162nat * pow2(88) + 222nat * pow2(96) + 249nat
        * pow2(104) + 222nat * pow2(112) + 20nat * pow2(120) + 16nat * pow2(248);

    // Make the constant bytes available to SMT (compute can read the array, SMT typically won't).
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[0] == 0xed_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[1] == 0xd3_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[2] == 0xf5_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[3] == 0x5c_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[4] == 0x1a_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[5] == 0x63_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[6] == 0x12_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[7] == 0x58_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[8] == 0xd6_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[9] == 0x9c_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[10] == 0xf7_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[11] == 0xa2_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[12] == 0xde_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[13] == 0xf9_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[14] == 0xde_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[15] == 0x14_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[16] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[17] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[18] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[19] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[20] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[21] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[22] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[23] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[24] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[25] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[26] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[27] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[28] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[29] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[30] == 0_u8) by (compute_only);
    assert(constants::BASEPOINT_ORDER_PRIVATE.bytes[31] == 0x10_u8) by (compute_only);

    // Now the spec-level conversion agrees with our concrete expansion.
    assert(scalar_to_nat(&constants::BASEPOINT_ORDER_PRIVATE) == expanded);

    // Basic pow2 facts for the 64-bit word computations.
    // Call lemmas once at the top for all pow2 values needed below.
    lemma2_to64();
    lemma2_to64_rest();
    assert(pow2(0) == 1);
    assert(pow2(4) == 16);
    assert(pow2(8) == 256);
    assert(pow2(16) == 65536);
    assert(pow2(24) == 16777216);
    assert(pow2(32) == 4294967296);
    assert(pow2(40) == 1099511627776);
    assert(pow2(48) == 281474976710656);
    assert(pow2(56) == 72057594037927936);
    assert(pow2(64) == 0x10000000000000000);

    // Split into two 64-bit words (low 128 bits) plus the top byte (bit 252 set).
    let word0: nat = 237nat * pow2(0) + 211nat * pow2(8) + 245nat * pow2(16) + 92nat * pow2(24)
        + 26nat * pow2(32) + 99nat * pow2(40) + 18nat * pow2(48) + 88nat * pow2(56);

    let word1: nat = 214nat * pow2(0) + 156nat * pow2(8) + 247nat * pow2(16) + 162nat * pow2(24)
        + 222nat * pow2(32) + 249nat * pow2(40) + 222nat * pow2(48) + 20nat * pow2(56);

    // The upper word is shifted by 64 bits in the full 256-bit value.
    let shifted_word1: nat = 214nat * pow2(64) + 156nat * pow2(72) + 247nat * pow2(80) + 162nat
        * pow2(88) + 222nat * pow2(96) + 249nat * pow2(104) + 222nat * pow2(112) + 20nat * pow2(
        120,
    );

    // Relate the shifted word to `word1 * 2^64` using pow2-addition identities.
    assert(shifted_word1 == word1 * pow2(64)) by {
        lemma_pow2_adds(64, 0);
        lemma_pow2_adds(64, 8);
        lemma_pow2_adds(64, 16);
        lemma_pow2_adds(64, 24);
        lemma_pow2_adds(64, 32);
        lemma_pow2_adds(64, 40);
        lemma_pow2_adds(64, 48);
        lemma_pow2_adds(64, 56);
    }

    // The high byte is 16 at position 248, i.e. 16 * 2^248 = 2^252.
    assert(16nat * pow2(248) == pow2(252)) by {
        lemma_pow2_adds(4, 248);
        assert(pow2(252) == pow2(4) * pow2(248));
    }

    // Evaluate the 64-bit words to concrete constants.
    let word0_num: nat = 237nat * 1nat + 211nat * 256nat + 245nat * 65536nat + 92nat * 16777216nat
        + 26nat * 4294967296nat + 99nat * 1099511627776nat + 18nat * 281474976710656nat + 88nat
        * 72057594037927936nat;
    assert(237nat * 1nat + 211nat * 256nat + 245nat * 65536nat + 92nat * 16777216nat + 26nat
        * 4294967296nat + 99nat * 1099511627776nat + 18nat * 281474976710656nat + 88nat
        * 72057594037927936nat == 0x5812631a5cf5d3ed_u64 as nat) by (compute_only);
    assert(word0 == word0_num);

    let word1_num: nat = 214nat * 1nat + 156nat * 256nat + 247nat * 65536nat + 162nat * 16777216nat
        + 222nat * 4294967296nat + 249nat * 1099511627776nat + 222nat * 281474976710656nat + 20nat
        * 72057594037927936nat;
    assert(214nat * 1nat + 156nat * 256nat + 247nat * 65536nat + 162nat * 16777216nat + 222nat
        * 4294967296nat + 249nat * 1099511627776nat + 222nat * 281474976710656nat + 20nat
        * 72057594037927936nat == 0x14def9dea2f79cd6_u64 as nat) by (compute_only);
    assert(word1 == word1_num);

    // Compute the low 128-bit constant c.
    assert(0x5812631a5cf5d3ed_u64 as nat + (0x14def9dea2f79cd6_u64 as nat) * 0x10000000000000000
        == 27742317777372353535851937790883648493nat) by (compute_only);
    assert(word0 + word1 * pow2(64) == 27742317777372353535851937790883648493nat);

    // Reconstruct expanded and conclude.
    assert(expanded == word0 + shifted_word1 + 16nat * pow2(248));
    assert(expanded == pow2(252) + 27742317777372353535851937790883648493nat);
    assert(group_order() == pow2(252) + 27742317777372353535851937790883648493nat);
    assert(scalar_to_nat(&constants::BASEPOINT_ORDER_PRIVATE) == group_order());
}

} // verus!
