//! Specification functions for high-level Scalar operations
#[allow(unused_imports)]
use crate::scalar::Scalar;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use super::scalar52_specs::*;

verus! {

pub open spec fn scalar_as_nat(s: &Scalar) -> nat {
    u8_32_as_nat(&s.bytes)
}

pub open spec fn u8_32_as_group_canonical(bytes: [u8; 32]) -> nat {
    group_canonical(u8_32_as_nat(&bytes))
}

/// Returns the scalar value reduced modulo group order.
/// This is the value used in scalar multiplication: [n]P where n = scalar_as_canonical(s).
pub open spec fn scalar_as_canonical(s: &Scalar) -> nat {
    u8_32_as_group_canonical(s.bytes)
}

/// Checks if a Scalar satisfies the canonical representation invariants:
/// - Invariant #1: High bit (bit 255) is clear, ensuring s < 2^255
/// - Invariant #2: Scalar is reduced modulo group order, i.e., s < ℓ
pub open spec fn is_canonical_scalar(s: &Scalar) -> bool {
    // Invariant #2: Scalar is reduced (< group order)
    u8_32_as_nat(&s.bytes)
        < group_order()
    // Invariant #1: High bit is clear (< 2^255)
     && s.bytes[31] <= 127
}

/// Returns true iff a and b are multiplicative inverses modulo group_order
/// i.e., a * b ≡ 1 (mod group_order)
pub open spec fn is_inverse(a: &Scalar, b: &Scalar) -> bool {
    group_canonical(scalar_as_nat(a) * scalar_as_nat(b)) == 1
}

/// Spec function to compute product of all scalars in a sequence (mod group_order)
/// Returns the natural number representation
/// Note: Processes from back to front to match iterative loop order
pub open spec fn product_of_scalars(scalars: Seq<Scalar>) -> nat
    decreases scalars.len(),
{
    if scalars.len() == 0 {
        1
    } else {
        let last = (scalars.len() - 1) as int;
        group_canonical(
            (product_of_scalars(scalars.subrange(0, last)) * scalar_as_nat(&scalars[last])),
        )
    }
}

/// Spec function to compute sum of all scalars in a sequence (mod group_order)
/// Returns the natural number representation
/// Note: Processes from back to front to match iterative loop order
pub open spec fn sum_of_scalars(scalars: Seq<Scalar>) -> nat
    decreases scalars.len(),
{
    if scalars.len() == 0 {
        0
    } else {
        let last = (scalars.len() - 1) as int;
        group_canonical((sum_of_scalars(scalars.subrange(0, last)) + scalar_as_nat(&scalars[last])))
    }
}

/// Returns true iff a scalar's byte representation equals the given natural number (mod group_order)
pub open spec fn scalar_congruent_nat(s: &Scalar, n: nat) -> bool {
    scalar_as_canonical(s) == group_canonical(n)
}

/// Returns true iff a scalar is the inverse of a natural number (mod group_order)
pub open spec fn is_inverse_of_nat(s: &Scalar, n: nat) -> bool {
    group_canonical(scalar_as_nat(s) * n) == 1
}

/// Returns true iff a byte array represents a clamped integer for X25519.
/// A clamped integer has:
/// - The 3 least significant bits cleared (divisible by 8)
/// - Bit 255 (MSB) cleared (< 2^255), which means bytes[31] <= 127
/// - Bit 254 set (>= 2^254)
/// This creates values in range: 2^254 + 8*{0, 1, 2, ..., 2^251 - 1}
pub open spec fn is_clamped_integer(bytes: &[u8; 32]) -> bool {
    // The 3 least significant bits are cleared (divisible by 8)
    bytes[0] & 0b0000_0111
        == 0
    // Bit 255 (MSB) is cleared, making it < 2^255
     && bytes[31] & 0b1000_0000 == 0
    // Bit 254 is set, so result >= 2^254
     && bytes[31] & 0b0100_0000
        == 0b0100_0000
    // MSB cleared implies bytes[31] <= 127 (needed for mul_req precondition)
     && bytes[31] <= 127
}

/// Spec function for clamping a byte array to produce a valid X25519 scalar.
/// This is the spec-level version of the `clamp_integer` exec function.
///
/// The clamping operation:
/// - Clears the 3 least significant bits (bits 0-2 of byte 0)
/// - Clears bit 255 (bit 7 of byte 31)
/// - Sets bit 6 of byte 31)
///
/// This produces a value in the range [2^254, 2^255) that is divisible by 8.
pub open spec fn spec_clamp_integer(bytes: [u8; 32]) -> [u8; 32] {
    // Build the result array element by element
    [
        bytes[0] & 0b1111_1000,  // Clear low 3 bits of byte 0
        bytes[1],
        bytes[2],
        bytes[3],
        bytes[4],
        bytes[5],
        bytes[6],
        bytes[7],
        bytes[8],
        bytes[9],
        bytes[10],
        bytes[11],
        bytes[12],
        bytes[13],
        bytes[14],
        bytes[15],
        bytes[16],
        bytes[17],
        bytes[18],
        bytes[19],
        bytes[20],
        bytes[21],
        bytes[22],
        bytes[23],
        bytes[24],
        bytes[25],
        bytes[26],
        bytes[27],
        bytes[28],
        bytes[29],
        bytes[30],
        (bytes[31] & 0b0111_1111) | 0b0100_0000,  // Clear bit 7 and set bit 6 of byte 31
    ]
}

// spec functions for NAF
// integer value of a NAF, little-endian
pub open spec fn reconstruct(naf: Seq<i8>) -> int
    decreases naf.len(),
{
    if naf.len() == 0 {
        0
    } else {
        (naf[0] as int) + 2 * reconstruct(naf.skip(1))
    }
}

/// Predicate describing a valid width-w Non-Adjacent Form.
pub open spec fn is_valid_naf(naf: Seq<i8>, w: nat) -> bool {
    forall|i: int|
        0 <= i < naf.len() ==> {
            let digit = (#[trigger] naf[i]) as int;
            // Each nonzero digit is odd and within bound
            (digit == 0 || (digit % 2 != 0 && -pow2((w - 1) as nat) < digit && digit < pow2(
                (w - 1) as nat,
            ))) &&
            // At most one nonzero in any w consecutive digits
            forall|j: int|
                1 <= j < w && #[trigger] (i + j) < naf.len() ==> !(digit != 0 && (naf[#[trigger] (i
                    + j)] as int) != 0)
        }
}

/// Interprets four u64 words as a 256-bit little-endian number:
///   words[0] + words[1]*2^64 + words[2]*2^128 + words[3]*2^192
pub open spec fn u64_4_as_nat(words: &[u64; 4]) -> nat {
    words[0] as nat + words[1] as nat * pow2(64) + words[2] as nat * pow2(128) + words[3] as nat
        * pow2(192)
}

// Spec functions for radix-2^w representation (generic)
/// Reconstructs an integer from a radix-2^w digit representation
/// The scalar is represented as: a_0 + a_1*2^w + a_2*2^(2w) + ...
pub open spec fn reconstruct_radix_2w(digits: Seq<i8>, w: nat) -> int
    decreases digits.len(),
{
    if digits.len() == 0 {
        0
    } else {
        (digits[0] as int) + pow2(w) * reconstruct_radix_2w(digits.skip(1), w)
    }
}

/// Predicate describing a valid radix-2^w representation with signed digits.
/// For window size w, coefficients are in [-2^(w-1), 2^(w-1)) for all indices except the last,
/// and [-2^(w-1), 2^(w-1)] for the last index.
///
/// The inclusive bound `<=` for the last digit comes from `as_radix_16` (w=4): its nibble-based
/// algorithm can produce a last digit equal to 8 (= 2^(w-1)). For `as_radix_2w` with w >= 5, the
/// last digit is strictly less than the bound, but the spec stays general so both representations
/// are valid.
pub open spec fn is_valid_radix_2w(digits: &[i8; 64], w: nat, digits_count: nat) -> bool {
    4 <= w <= 8 && digits_count <= 64 && forall|i: int|
        0 <= i < digits_count ==> {
            let bound = pow2((w - 1) as nat) as int;
            if i < digits_count - 1 {
                -bound <= (#[trigger] digits[i]) && (#[trigger] digits[i]) < bound
            } else {
                -bound <= (#[trigger] digits[i]) && (#[trigger] digits[i]) <= bound
            }
        }
}

// Spec functions for radix-16 representation (w=4 specialization)
/// Reconstructs the integer value from a radix-16 representation
/// This is just radix-2^w with w=4
pub open spec fn reconstruct_radix_16(digits: Seq<i8>) -> int {
    reconstruct_radix_2w(digits, 4)
}

/// Predicate describing a valid radix-16 representation with signed digits
/// This is just radix-2^w with w=4
pub open spec fn is_valid_radix_16(digits: &[i8; 64]) -> bool {
    is_valid_radix_2w(digits, 4, 64)
}

/// Simple bounds check for radix-16 digits: all digits in [-8, 8]
/// This is a simpler predicate than is_valid_radix_16 for easier use
pub open spec fn radix_16_digit_bounded(digit: i8) -> bool {
    -8 <= digit && digit <= 8
}

/// All radix-16 digits are bounded by [-8, 8]
pub open spec fn radix_16_all_bounded(digits: &[i8; 64]) -> bool {
    forall|i: int| 0 <= i < 64 ==> radix_16_digit_bounded(#[trigger] digits[i])
}

/// Convert a boolean slice (bits in big-endian order) to a natural number
/// This interprets bits[0] as the most significant bit
/// Used for scalar multiplication where bits are processed MSB first
pub open spec fn bits_be_as_nat(bits: &[bool], len: int) -> nat
    recommends
        0 <= len <= bits.len(),
    decreases len,
{
    if len <= 0 {
        0
    } else {
        let bit_value = if bits[len - 1] {
            1nat
        } else {
            0nat
        };
        bit_value + 2 * bits_be_as_nat(bits, len - 1)
    }
}

} // verus!
