#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use crate::lemmas::common_lemmas::shift_lemmas::*;
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
use crate::specs::core_specs::*;

verus! {

/// Connect `bits_as_nat_rec` (absolute indexing with powers of two) with
/// `bits_from_index_to_nat` (relative indexing from `start`).
pub proof fn lemma_bits_as_nat_rec_eq_pow2_mul_bits_from_index(bits: [bool; 256], start: nat)
    requires
        start <= 256,
    ensures
        bits_as_nat_rec(bits, start as int) == pow2(start) * bits_from_index_to_nat(
            bits,
            start,
            (256 - start) as nat,
        ),
    decreases 256 - start,
{
    if start == 256 {
        assert(bits_as_nat_rec(bits, 256) == 0);
        assert(bits_from_index_to_nat(bits, 256, 0) == 0);
        assert(pow2(256) * 0nat == 0nat) by { lemma_mul_basics_3(pow2(256) as int) }
    } else {
        let bit_value = if bits[start as int] {
            1nat
        } else {
            0nat
        };

        // By definition unfolding
        assert(bits_as_nat_rec(bits, start as int) == bit_value * pow2(start) + bits_as_nat_rec(
            bits,
            (start + 1) as int,
        ));
        assert(bits_from_index_to_nat(bits, start, (256 - start) as nat) == bit_value + 2
            * bits_from_index_to_nat(bits, (start + 1) as nat, (255 - start) as nat));

        assert(pow2((start + 1) as nat) == pow2(start) * 2) by {
            lemma_pow2_adds(start, 1);
            lemma2_to64();
        }

        let tail = bits_from_index_to_nat(bits, (start + 1) as nat, (255 - start) as nat);
        assert(pow2(start) * bits_from_index_to_nat(bits, start, (256 - start) as nat) == bit_value
            * pow2(start) + pow2((start + 1) as nat) * tail) by (nonlinear_arith)
            requires
                bits_from_index_to_nat(bits, start, (256 - start) as nat) == bit_value + 2 * tail,
                pow2((start + 1) as nat) == pow2(start) * 2,
        {}

        // By induction hypothesis
        assert(bits_as_nat_rec(bits, (start + 1) as int) == pow2((start + 1) as nat)
            * bits_from_index_to_nat(bits, (start + 1) as nat, (255 - start) as nat)) by {
            lemma_bits_as_nat_rec_eq_pow2_mul_bits_from_index(bits, (start + 1) as nat);
        }

        assert(bits_as_nat_rec(bits, start as int) == pow2(start) * bits_from_index_to_nat(
            bits,
            start,
            (256 - start) as nat,
        ));
    }
}

pub proof fn lemma_bits_as_nat_eq_bits_from_index(bits: [bool; 256])
    ensures
        bits_as_nat(bits) == bits_from_index_to_nat(bits, 0, 256),
{
    assert(bits_as_nat_rec(bits, 0) == pow2(0) * bits_from_index_to_nat(bits, 0, 256)) by {
        lemma_bits_as_nat_rec_eq_pow2_mul_bits_from_index(bits, 0);
    }
    assert(pow2(0) == 1) by {
        lemma2_to64();
    }
    assert(bits_as_nat(bits) == bits_as_nat_rec(bits, 0));
    assert(pow2(0) * bits_from_index_to_nat(bits, 0, 256) == bits_from_index_to_nat(bits, 0, 256))
        by { lemma_mul_basics_3(bits_from_index_to_nat(bits, 0, 256) as int) }
}

/// If a 256-bit little-endian bitvector represents a value strictly less than `2^255`,
/// then the top bit (bit 255) must be false.
pub proof fn lemma_bits_as_nat_lt_pow2_255_implies_msb_false(bits: [bool; 256])
    requires
        bits_as_nat(bits) < pow2(255),
    ensures
        !bits[255],
{
    assert(bits_as_nat(bits) == bits_from_index_to_nat(bits, 0, 256)) by {
        lemma_bits_as_nat_eq_bits_from_index(bits);
    }
    // split(bits, 0, 255, 1): f(0, 256) = f(0, 255) + pow2(255) * f(255, 1)
    // where f(255, 1) = if bits[255] { 1 } else { 0 }
    assert(bits_from_index_to_nat(bits, 0, 256) == bits_from_index_to_nat(bits, 0, 255) + pow2(255)
        * bits_from_index_to_nat(bits, 255, 1)) by {
        lemma_bits_from_index_split(bits, 0, 255, 1);
    }

    if bits[255] {
        // Help solver unfold: f(255, 1) = 1 + 2*f(256, 0) = 1
        assert(bits_from_index_to_nat(bits, 256, 0) == 0nat);
        assert(bits_from_index_to_nat(bits, 255, 1) == 1nat);
        assert(bits_from_index_to_nat(bits, 0, 256) >= pow2(255));
        assert(bits_as_nat(bits) >= pow2(255));
        assert(false);
    }
}

/// Relate `bits_be_as_nat` on a reversed big-endian view to the corresponding
/// little-endian `bits_from_index_to_nat` range.
pub proof fn lemma_bits_be_as_nat_eq_bits_from_index(
    bits_le: [bool; 256],
    bits_be: &[bool],
    len: nat,
)
    requires
        len <= 255,
        bits_be.len() == 255,
        forall|i: int| 0 <= i < 255 ==> #[trigger] bits_be[i] == bits_le[254 - i],
    ensures
        bits_be_as_nat(bits_be, len as int) == bits_from_index_to_nat(
            bits_le,
            (255 - len) as nat,
            len,
        ),
    decreases len,
{
    if len == 0 {
        assert(bits_be_as_nat(bits_be, 0) == 0);
        assert(bits_from_index_to_nat(bits_le, 255, 0) == 0);
    } else {
        let start = (255 - len) as nat;
        let bit_value = if bits_le[start as int] {
            1nat
        } else {
            0nat
        };

        assert(bits_be[len as int - 1] == bits_le[start as int]) by {
            assert((len - 1) < 255);
            assert(bits_be[(len - 1) as int] == bits_le[254 - (len - 1) as int]);
            assert(254 - (len - 1) as int == start as int);
        }
        assert(bits_be_as_nat(bits_be, len as int) == (if bits_be[len as int - 1] {
            1nat
        } else {
            0nat
        }) + 2 * bits_be_as_nat(bits_be, (len - 1) as int));

        assert(bits_from_index_to_nat(bits_le, start, len) == bit_value + 2
            * bits_from_index_to_nat(bits_le, (start + 1) as nat, (len - 1) as nat));

        assert(bits_be_as_nat(bits_be, len as int) == bit_value + 2 * bits_be_as_nat(
            bits_be,
            (len - 1) as int,
        ));

        // By induction hypothesis
        assert(bits_be_as_nat(bits_be, (len - 1) as int) == bits_from_index_to_nat(
            bits_le,
            (start + 1) as nat,
            (len - 1) as nat,
        )) by {
            lemma_bits_be_as_nat_eq_bits_from_index(bits_le, bits_be, (len - 1) as nat);
        }

        assert(bits_be_as_nat(bits_be, len as int) == bit_value + 2 * bits_from_index_to_nat(
            bits_le,
            (start + 1) as nat,
            (len - 1) as nat,
        ));
        assert(bits_be_as_nat(bits_be, len as int) == bits_from_index_to_nat(bits_le, start, len));
    }
}

// ============================================================================
// Byte-to-bits decomposition and bits_as_nat == u8_32_as_nat bridge
// ============================================================================
// The `byte_bits_value` spec function is defined in `specs/core_specs.rs`.
/// Key identity: `byte_bits_value` equals the corresponding bit range extracted via shift and mod.
///
/// `byte_bits_value(byte, s, n) == (byte >> s) % 2^n`
///
/// Proven by induction on `len` using the modular breakdown identity:
/// `x % 2^n == (x % 2) + 2 * ((x / 2) % 2^(n-1))`
///
/// Note: the `bit_start + 1 < 8` / `else` branch handles a u8 shift overflow edge case.
/// When `bit_start == 7` and `len == 1`, the induction hypothesis references `byte >> 8`
/// which overflows to 0 for u8. The else-branch proves `x / 2 == 0` by showing the
/// shifted value is at most 1 (since `byte >> 7` is either 0 or 1).
pub proof fn lemma_byte_bits_value_is_mod(byte: u8, bit_start: nat, len: nat)
    requires
        bit_start + len <= 8,
    ensures
        byte_bits_value(byte, bit_start, len) == ((byte >> (bit_start as u8)) as nat) % pow2(len),
    decreases len,
{
    let shifted = byte >> (bit_start as u8);
    let x = shifted as nat;

    if len == 0 {
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
    } else {
        // By induction hypothesis
        assert(byte_bits_value(byte, (bit_start + 1) as nat, (len - 1) as nat) == ((byte >> ((
        bit_start + 1) as u8)) as nat) % pow2((len - 1) as nat)) by {
            lemma_byte_bits_value_is_mod(byte, (bit_start + 1) as nat, (len - 1) as nat);
        }

        let bit_val: nat = if (shifted & 1u8) == 1u8 {
            1
        } else {
            0
        };

        // Fact 1: (shifted & 1) as nat == x % 2
        assert(bit_val == x % 2) by {
            lemma_u8_low_bits_mask_is_mod(shifted, 1);
            lemma2_to64();
        }

        // Fact 2: (byte >> (bit_start + 1)) as nat == x / 2
        if bit_start + 1 < 8 {
            assert(((byte >> ((bit_start + 1) as u8)) as nat) == x / 2) by {
                lemma_u8_shr_by_sum(byte, bit_start, 1);
                lemma_u8_shr_is_div(shifted, 1);
                lemma2_to64();
            }
        } else {
            // bit_start == 7, len == 1: (byte >> 8) overflows to 0
            assert(byte >> 8u8 == 0u8) by (bit_vector);
            assert(x / 2 == 0) by {
                lemma_u8_shr_is_div(shifted, 1);
                lemma2_to64();
                assert(shifted <= 1) by {
                    lemma_u8_shr_is_div(byte, 7);
                    lemma2_to64();
                    assert(pow2(7) == 128);
                    lemma_div_is_ordered(byte as int, 255, 128);
                }
            }
        }

        // Fact 3: pow2(len) == 2 * pow2(len - 1)
        assert(pow2(len) == 2 * pow2((len - 1) as nat)) by {
            lemma_pow2_adds(1, (len - 1) as nat);
            lemma2_to64();
        }

        // Fact 4: mod breakdown — x % (2 * D) == (x % 2) + 2 * ((x / 2) % D)
        assert(pow2((len - 1) as nat) > 0) by {
            lemma_pow2_pos((len - 1) as nat);
        }
        assert(x % pow2(len) == (x % 2) + 2 * ((x / 2) % pow2((len - 1) as nat))) by {
            lemma_mod_breakdown(x as int, 2, pow2((len - 1) as nat) as int);
        }
    }
}

/// Corollary: `byte_bits_value` for the full byte (8 bits from position 0) equals the byte value.
pub proof fn lemma_byte_bits_value_full(byte: u8)
    ensures
        byte_bits_value(byte, 0, 8) == byte as nat,
{
    assert(byte_bits_value(byte, 0, 8) == ((byte >> 0u8) as nat) % pow2(8)) by {
        lemma_byte_bits_value_is_mod(byte, 0, 8);
    }
    assert(byte >> 0u8 == byte) by {
        lemma_u8_shr_zero_is_id(byte);
    }
    assert(pow2(8) == 256) by {
        lemma2_to64();
    }
    assert((byte as nat) % 256 == byte as nat) by {
        lemma_small_mod(byte as nat, 256);
    }
}

/// When bits of an array are extracted from a byte, `bits_from_index_to_nat` equals `byte_bits_value`.
///
/// Both functions share the same recursive Horner structure, so the proof is by structural induction.
pub proof fn lemma_bits_from_index_eq_byte_bits(
    bits: [bool; 256],
    byte: u8,
    start: nat,
    bit_offset: nat,
    len: nat,
)
    requires
        start + len <= 256,
        bit_offset + len <= 8,
        forall|j: nat|
            j < len ==> #[trigger] bits[(start + j) as int] == (((byte >> ((bit_offset + j) as u8))
                & 1u8) == 1u8),
    ensures
        bits_from_index_to_nat(bits, start, len) == byte_bits_value(byte, bit_offset, len),
    decreases len,
{
    if len == 0 {
    } else {
        // Establish IH precondition: shift indices by 1
        assert forall|j: nat| j < (len - 1) as nat implies #[trigger] bits[((start + 1) + j) as int]
            == (((byte >> (((bit_offset + 1) + j) as u8)) & 1u8) == 1u8) by {
            assert(bits[(start + (j + 1)) as int] == (((byte >> ((bit_offset + (j + 1)) as u8))
                & 1u8) == 1u8));
        }

        // By induction hypothesis
        assert(bits_from_index_to_nat(bits, (start + 1) as nat, (len - 1) as nat)
            == byte_bits_value(byte, (bit_offset + 1) as nat, (len - 1) as nat)) by {
            lemma_bits_from_index_eq_byte_bits(
                bits,
                byte,
                (start + 1) as nat,
                (bit_offset + 1) as nat,
                (len - 1) as nat,
            );
        }

        // The first bit values match (from precondition with j=0)
        assert(bits[(start + 0) as int] == (((byte >> ((bit_offset + 0) as u8)) & 1u8) == 1u8));
    }
}

/// Splitting lemma: `bits_from_index_to_nat` over `m + n` bits decomposes into
/// the first `m` bits plus `pow2(m)` times the remaining `n` bits.
pub proof fn lemma_bits_from_index_split(bits: [bool; 256], start: nat, m: nat, n: nat)
    requires
        start + m + n <= 256,
    ensures
        bits_from_index_to_nat(bits, start, (m + n) as nat) == bits_from_index_to_nat(
            bits,
            start,
            m,
        ) + pow2(m) * bits_from_index_to_nat(bits, (start + m) as nat, n),
    decreases m,
{
    if m == 0 {
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(1 * bits_from_index_to_nat(bits, start, n) == bits_from_index_to_nat(bits, start, n))
            by {
            lemma_mul_basics_4(bits_from_index_to_nat(bits, start, n) as int);
        }
    } else {
        // By induction hypothesis
        assert(bits_from_index_to_nat(bits, (start + 1) as nat, ((m - 1) + n) as nat)
            == bits_from_index_to_nat(bits, (start + 1) as nat, (m - 1) as nat) + pow2(
            (m - 1) as nat,
        ) * bits_from_index_to_nat(bits, (start + m) as nat, n)) by {
            lemma_bits_from_index_split(bits, (start + 1) as nat, (m - 1) as nat, n);
        }

        assert(pow2(m) == 2 * pow2((m - 1) as nat)) by {
            lemma_pow2_adds(1, (m - 1) as nat);
            lemma2_to64();
        }

        let A = bits_from_index_to_nat(bits, (start + 1) as nat, (m - 1) as nat);
        let B = bits_from_index_to_nat(bits, (start + m) as nat, n);

        assert(2 * (A + pow2((m - 1) as nat) * B) == 2 * A + pow2(m) * B) by (nonlinear_arith)
            requires
                pow2(m) == 2 * pow2((m - 1) as nat),
        {}
    }
}

/// Inductive assembly: the first `8*k` bits of the array, interpreted via `bits_from_index_to_nat`,
/// equal the little-endian byte prefix sum `bytes_as_nat_prefix(bytes@, k)`.
pub proof fn lemma_bits_chunks_eq_bytes_prefix(bits: [bool; 256], bytes: [u8; 32], k: nat)
    requires
        k <= 32,
        forall|i: int|
            0 <= i < (8 * k) as int ==> bits[i] == (((bytes[(i / 8) as int] >> ((i % 8) as u8))
                & 1u8) == 1u8),
    ensures
        bits_from_index_to_nat(bits, 0, (8 * k) as nat) == bytes_as_nat_prefix(bytes@, k),
    decreases k,
{
    if k == 0 {
    } else {
        let m = (8 * (k - 1)) as nat;

        // By induction hypothesis
        assert(bits_from_index_to_nat(bits, 0, m) == bytes_as_nat_prefix(bytes@, (k - 1) as nat))
            by {
            lemma_bits_chunks_eq_bytes_prefix(bits, bytes, (k - 1) as nat);
        }

        // Split: first 8*(k-1) bits + next 8 bits
        assert(bits_from_index_to_nat(bits, 0, (m + 8) as nat) == bits_from_index_to_nat(bits, 0, m)
            + pow2(m) * bits_from_index_to_nat(bits, m, 8)) by {
            lemma_bits_from_index_split(bits, 0, m, 8);
        }

        // Show the 8-bit chunk at position m equals bytes[k-1]
        assert forall|j: nat| j < 8 implies #[trigger] bits[(m + j) as int] == (((bytes[(k
            - 1) as int] >> (j as u8)) & 1u8) == 1u8) by {
            let i = (m + j) as int;
            assert(0 <= i < (8 * k) as int);
            assert(i == (k - 1) as int * 8 + j as int);
            lemma_fundamental_div_mod(i, 8);
        }

        assert(bits_from_index_to_nat(bits, m, 8) == byte_bits_value(bytes[(k - 1) as int], 0, 8))
            by {
            lemma_bits_from_index_eq_byte_bits(bits, bytes[(k - 1) as int], m, 0, 8);
        }

        assert(byte_bits_value(bytes[(k - 1) as int], 0, 8) == bytes[(k - 1) as int] as nat) by {
            lemma_byte_bits_value_full(bytes[(k - 1) as int]);
        }

        // bytes_as_nat_prefix(bytes@, k) unfolds to prefix(k-1) + pow2((k-1)*8) * bytes[k-1]
        // and from split + IH this matches bits_from_index_to_nat(bits, 0, 8*k)
        assert(m as int * 8 == ((k - 1) as int) * 8 * 8) by {
            lemma_mul_is_associative(8, (k - 1) as int, 8);
        }
        assert(pow2(m) * bytes[(k - 1) as int] as nat == bytes[(k - 1) as int] as nat * pow2(
            ((k - 1) * 8) as nat,
        )) by {
            lemma_mul_is_commutative(pow2(m) as int, bytes[(k - 1) as int] as int);
        }
    }
}

/// Main theorem: when bits are extracted from a 32-byte array in little-endian order
/// (bit `i` is bit `i%8` of byte `i/8`), then `bits_as_nat` equals `u8_32_as_nat`.
///
/// TODO: Step 3 bridges `bytes_as_nat_prefix` to `u8_32_as_nat` via `u8_32_as_nat_rec`.
/// This indirection exists because `u8_32_as_nat` is an explicit 32-term sum while
/// `bytes_as_nat_prefix` is recursive. Consolidating to a single canonical byte-to-nat
/// representation would eliminate this bridge layer.
pub proof fn lemma_bits_from_bytes_eq_u8_32_as_nat(bits: [bool; 256], bytes: [u8; 32])
    requires
        forall|i: int|
            0 <= i < 256 ==> bits[i] == (((bytes[(i / 8) as int] >> ((i % 8) as u8)) & 1u8) == 1u8),
    ensures
        bits_as_nat(bits) == u8_32_as_nat(&bytes),
{
    // Step 1: bits_as_nat == bits_from_index_to_nat(bits, 0, 256)
    assert(bits_as_nat(bits) == bits_from_index_to_nat(bits, 0, 256)) by {
        lemma_bits_as_nat_eq_bits_from_index(bits);
    }

    // Step 2: bits_from_index_to_nat(bits, 0, 256) == bytes_as_nat_prefix(bytes@, 32)
    assert(bits_from_index_to_nat(bits, 0, 256) == bytes_as_nat_prefix(bytes@, 32)) by {
        lemma_bits_chunks_eq_bytes_prefix(bits, bytes, 32);
    }

    // Step 3: bytes_as_nat_prefix(bytes@, 32) == u8_32_as_nat(bytes)
    assert(bytes_as_nat_prefix(bytes@, 32) == u8_32_as_nat(&bytes)) by {
        assert(u8_32_as_nat(&bytes) == u8_32_as_nat_rec(&bytes, 0)) by {
            lemma_u8_32_as_nat_equals_rec(&bytes);
        }
        assert(u8_32_as_nat_rec(&bytes, 0) == bytes_as_nat_prefix(bytes@, 32) + u8_32_as_nat_rec(
            &bytes,
            32,
        )) by {
            lemma_decomposition_prefix_rec(&bytes, 32);
        }
        assert(u8_32_as_nat_rec(&bytes, 32) == 0);
    }
}

} // verus!
