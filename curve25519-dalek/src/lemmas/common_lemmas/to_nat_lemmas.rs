//! Lemmas for byte-to-nat and word-to-nat conversion operations.
//!
//! This module contains lemmas for:
//! - `bytes_as_nat_prefix`: the prefix sum of bytes in little-endian
//! - Connecting Horner form (`bytes_seq_as_nat`) to direct sum form (`bytes_as_nat_prefix`)
//! - Byte extraction and injectivity of `u8_32_as_nat`
//! - Word-to-nat conversions for 64-bit words
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::specs::core_specs::*;

verus! {

// ============================================================================
// PART 1: BYTE-TO-NAT LEMMAS
// ============================================================================
// ============================================================================
// Properties of bytes_as_nat_prefix
// ============================================================================
/// Helper: Bound bytes_as_nat_prefix - geometric series bound
/// Each byte contributes at most 255 * pow2(j*8) < pow2((j+1)*8)
pub proof fn lemma_bytes_as_nat_prefix_bounded(bytes: Seq<u8>, n: nat)
    requires
        n <= bytes.len(),
    ensures
        bytes_as_nat_prefix(bytes, n) < pow2((n * 8) as nat),
    decreases n,
{
    let goal = bytes_as_nat_prefix(bytes, n) < pow2((n * 8) as nat);

    assert(goal) by {
        lemma2_to64();

        if n == 0 {
            // Base case: bytes_as_nat_prefix(bytes, 0) == 0 < 1 == pow2(0)
            assert(bytes_as_nat_prefix(bytes, 0) == 0);
            assert(pow2(0) == 1);
        } else {
            // Subgoal 1: IH - prefix(n-1) < pow2((n-1)*8)
            let prev = bytes_as_nat_prefix(bytes, (n - 1) as nat);
            let p1 = pow2(((n - 1) * 8) as nat);
            assert(prev < p1) by {
                lemma_bytes_as_nat_prefix_bounded(bytes, (n - 1) as nat);
            }

            // Subgoal 2: byte value < 256
            let byte_val = bytes[(n - 1) as int] as nat;
            let p2 = pow2(8);
            assert(byte_val < p2) by {
                lemma_u8_lt_pow2_8(bytes[(n - 1) as int]);
            }

            // Subgoal 3: pow2(n*8) == pow2((n-1)*8) * pow2(8)
            assert(pow2((n * 8) as nat) == p1 * p2) by {
                assert(n * 8 == (n - 1) * 8 + 8) by {
                    lemma_mul_is_distributive_sub(8, n as int, 1);
                }
                lemma_pow2_adds(((n - 1) * 8) as nat, 8);
            }

            // Subgoal 4: Combine with nonlinear arithmetic
            assert(prev + byte_val * p1 < p1 * p2) by (nonlinear_arith)
                requires
                    prev < p1,
                    byte_val < p2,
                    p2 == 256,
            {}
        }
    }
}

/// Bound a 32-byte little-endian nat by `2^255` when the top byte fits in 7 bits.
///
/// This is the standard Curve25519 "scalar invariant #1" style bound: if the most
/// significant bit is clear (`bytes[31] <= 127`), then the represented integer is
/// strictly less than `2^255`.
pub proof fn lemma_u8_32_as_nat_lt_pow2_255(bytes: &[u8; 32])
    requires
        bytes[31] <= 127,
    ensures
        u8_32_as_nat(bytes) < pow2(255),
{
    let prefix31 = bytes_as_nat_prefix(bytes@, 31);

    // u8_32_as_nat(bytes) == prefix31 + bytes[31] * 2^248
    lemma_u8_32_as_nat_equals_rec(bytes);
    lemma_decomposition_prefix_rec(bytes, 31);
    assert(u8_32_as_nat(bytes) == u8_32_as_nat_rec(bytes, 0));
    assert(u8_32_as_nat_rec(bytes, 0) == prefix31 + u8_32_as_nat_rec(bytes, 31));
    assert(u8_32_as_nat_rec(bytes, 31) == bytes[31] as nat * pow2(248) + u8_32_as_nat_rec(
        bytes,
        32,
    ));
    assert(u8_32_as_nat_rec(bytes, 32) == 0);
    assert(u8_32_as_nat_rec(bytes, 31) == bytes[31] as nat * pow2(248));
    assert(u8_32_as_nat(bytes) == prefix31 + bytes[31] as nat * pow2(248));

    // prefix31 < 2^248
    lemma_bytes_as_nat_prefix_bounded(bytes@, 31);

    // 2^255 == 2^248 * 128
    assert(pow2(7) == 128) by {
        lemma2_to64();
    }
    assert(pow2(255) == pow2(248) * 128nat) by {
        assert(pow2(255) == pow2(248) * pow2(7)) by {
            assert(248 + 7 == 255);
            lemma_pow2_adds(248, 7);
        }
        assert(pow2(7) == 128);
    }

    assert(u8_32_as_nat(bytes) < pow2(255)) by (nonlinear_arith)
        requires
            prefix31 < pow2(248),
            bytes[31] <= 127,
            u8_32_as_nat(bytes) == prefix31 + bytes[31] as nat * pow2(248),
            pow2(255) == pow2(248) * 128nat,
    {}
}

// ============================================================================
// Bridge Lemmas: Connecting bytes_seq_as_nat to bytes_as_nat_prefix
//
// The key insight is that bytes_seq_as_nat (Horner form) and bytes_as_nat_prefix
// (direct sum form) compute the same value.
// ============================================================================
/// Lemma: Horner form equals direct sum form for any sequence.
///
/// This is the key lemma that connects the two recursion patterns:
/// - bytes_seq_as_nat uses Horner's method: b[0] + 256*(b[1] + 256*(...))
/// - bytes_as_nat_prefix uses direct sums: b[0]*2^0 + b[1]*2^8 + ...
///
/// Both compute the same polynomial value.
pub proof fn lemma_bytes_seq_as_nat_equals_prefix(seq: Seq<u8>)
    ensures
        bytes_seq_as_nat(seq) == bytes_as_nat_prefix(seq, seq.len() as nat),
    decreases seq.len(),
{
    let goal = bytes_seq_as_nat(seq) == bytes_as_nat_prefix(seq, seq.len() as nat);

    assert(goal) by {
        if seq.len() == 0 {
            // Base case: both are 0
        } else {
            let tail = seq.skip(1);

            // IH: bytes_seq_as_nat(tail) == bytes_as_nat_prefix(tail, tail.len())
            assert(bytes_seq_as_nat(tail) == bytes_as_nat_prefix(tail, tail.len() as nat)) by {
                lemma_bytes_seq_as_nat_equals_prefix(tail);
            }

            // bytes_seq_as_nat(seq) = seq[0] + 256 * bytes_seq_as_nat(tail)
            //                       = seq[0] + 256 * prefix(tail, n-1)
            //                       = prefix(seq, n)
            assert(seq[0] as nat + pow2(8) * bytes_as_nat_prefix(tail, (seq.len() - 1) as nat)
                == bytes_as_nat_prefix(seq, seq.len() as nat)) by {
                // lemma_horner_to_prefix_step gives:
                //   seq[0] * pow2(0) + pow2(8) * prefix(tail, n-1) == prefix(seq, n)
                lemma_horner_to_prefix_step(seq, (seq.len() - 1) as nat);
                // Since pow2(0) == 1, seq[0] * pow2(0) == seq[0]
                lemma2_to64();
            }
        }
    }
}

/// Shows one step of the Horner-to-prefix conversion.
///
/// Proves: seq[0] + 256 * prefix(tail, k) == prefix(seq, k+1)
///
/// This is the key inductive step showing how Horner's method
/// (multiply by 256, add first byte) relates to the prefix sum form.
proof fn lemma_horner_to_prefix_step(seq: Seq<u8>, k: nat)
    requires
        seq.len() > 0,
        k <= seq.len() - 1,
    ensures
        seq[0] as nat * pow2(0) + pow2(8) * bytes_as_nat_prefix(seq.skip(1), k)
            == bytes_as_nat_prefix(seq, (k + 1) as nat),
    decreases k,
{
    let tail = seq.skip(1);
    let goal = seq[0] as nat * pow2(0) + pow2(8) * bytes_as_nat_prefix(tail, k)
        == bytes_as_nat_prefix(seq, (k + 1) as nat);

    assert(goal) by {
        reveal_with_fuel(bytes_as_nat_prefix, 2);
        lemma2_to64();

        if k == 0 {
            // Base case: seq[0] * 1 + 256 * 0 == prefix(seq, 1)
            assert(seq[0] as nat * pow2(0) == pow2(0) * seq[0] as nat) by {
                lemma_mul_is_commutative(seq[0] as int, pow2(0) as int);
            }
        } else {
            let k1 = (k - 1) as nat;
            let tail_prev = bytes_as_nat_prefix(tail, k1);
            let tail_term = pow2((k1 * 8) as nat) * tail[k1 as int] as nat;

            // Subgoal 1: IH - holds for k-1
            assert(seq[0] as nat * pow2(0) + pow2(8) * tail_prev == bytes_as_nat_prefix(seq, k))
                by {
                lemma_horner_to_prefix_step(seq, k1);
            }

            // Subgoal 2: pow2(8) * pow2((k-1)*8) == pow2(k*8)
            assert(pow2(8) * pow2((k1 * 8) as nat) == pow2((k * 8) as nat)) by {
                lemma_pow2_adds(8, (k1 * 8) as nat);
                assert(8 + k1 * 8 == k * 8) by {
                    lemma_mul_is_distributive_sub(8, k as int, 1);
                }
            }

            // Subgoal 3: tail[k-1] == seq[k]
            assert(tail[k1 as int] == seq[k as int]);

            // Subgoal 4: Distribute 256 over prefix(tail, k)
            assert(pow2(8) * bytes_as_nat_prefix(tail, k) == pow2(8) * tail_prev + pow2(8)
                * tail_term) by {
                lemma_mul_is_distributive_add(pow2(8) as int, tail_prev as int, tail_term as int);
            }

            // Subgoal 5: 256 * tail_term == pow2(k*8) * seq[k]
            assert(pow2(8) * tail_term == pow2((k * 8) as nat) * seq[k as int] as nat) by {
                lemma_mul_is_associative(
                    pow2(8) as int,
                    pow2((k1 * 8) as nat) as int,
                    tail[k1 as int] as int,
                );
            }
        }
    }
}

// ============================================================================
// Key Structural Lemmas using u8_32_as_nat_rec
// ============================================================================
/// Lemma: Decomposition of u8_32_as_nat_rec into prefix and suffix
/// This is the key structural insight: the recursive sum can be split at any point
pub proof fn lemma_decomposition_prefix_rec(bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
    ensures
        u8_32_as_nat_rec(bytes, 0) == bytes_as_nat_prefix(bytes@, n) + u8_32_as_nat_rec(bytes, n),
    decreases n,
{
    let goal = u8_32_as_nat_rec(bytes, 0) == bytes_as_nat_prefix(bytes@, n) + u8_32_as_nat_rec(
        bytes,
        n,
    );

    assert(goal) by {
        if n == 0 {
            // Base case: prefix(0) == 0
            assert(bytes_as_nat_prefix(bytes@, 0) == 0);
        } else {
            // Subgoal 1: IH - decomposition holds for n-1
            assert(u8_32_as_nat_rec(bytes, 0) == bytes_as_nat_prefix(bytes@, (n - 1) as nat)
                + u8_32_as_nat_rec(bytes, (n - 1) as nat)) by {
                lemma_decomposition_prefix_rec(bytes, (n - 1) as nat);
            }

            // Subgoal 2: Unfold u8_32_as_nat_rec at n-1
            assert(u8_32_as_nat_rec(bytes, (n - 1) as nat) == bytes[(n - 1) as int] as nat * pow2(
                ((n - 1) * 8) as nat,
            ) + u8_32_as_nat_rec(bytes, n));

            // Subgoal 3: Unfold bytes_as_nat_prefix at n
            assert(bytes_as_nat_prefix(bytes@, n) == bytes_as_nat_prefix(bytes@, (n - 1) as nat)
                + pow2(((n - 1) * 8) as nat) * bytes[(n - 1) as int] as nat);

            // Subgoal 4: Commutativity to match term orderings
            assert(bytes[(n - 1) as int] as nat * pow2(((n - 1) * 8) as nat) == pow2(
                ((n - 1) * 8) as nat,
            ) * bytes[(n - 1) as int] as nat) by {
                lemma_mul_is_commutative(
                    bytes[(n - 1) as int] as int,
                    pow2(((n - 1) * 8) as nat) as int,
                );
            }
        }
    }
}

/// Lemma: The suffix u8_32_as_nat_rec(bytes, n) is divisible by pow2(n*8)
/// Every term in the sum has a factor of pow2(j*8) where j >= n, so the whole sum is divisible by pow2(n*8)
pub proof fn lemma_rec_suffix_divisible(bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
    ensures
        u8_32_as_nat_rec(bytes, n) % pow2((n * 8) as nat) == 0,
    decreases (32 - n),
{
    let d = pow2((n * 8) as nat);
    let goal = u8_32_as_nat_rec(bytes, n) % d == 0;

    assert(goal) by {
        lemma2_to64();

        if n >= 32 {
            // Base case: u8_32_as_nat_rec(bytes, 32) == 0, and 0 % d == 0
            assert(u8_32_as_nat_rec(bytes, 32) == 0);
            lemma_pow2_pos((n * 8) as nat);
            assert(0nat % d == 0) by {
                lemma_small_mod(0nat, d);
            }
        } else {
            let term1 = bytes[n as int] as nat * d;
            let term2 = u8_32_as_nat_rec(bytes, (n + 1) as nat);
            lemma_pow2_pos((n * 8) as nat);

            // Subgoal 1: term1 % d == 0 (since term1 = bytes[n] * d)
            assert(term1 % d == 0) by {
                lemma_mod_multiples_basic(bytes[n as int] as int, d as int);
            }

            // Subgoal 2: IH - suffix at n+1 is divisible by pow2((n+1)*8)
            assert(term2 % pow2(((n + 1) * 8) as nat) == 0) by {
                lemma_rec_suffix_divisible(bytes, (n + 1) as nat);
            }

            // Subgoal 3: pow2((n+1)*8) == d * pow2(8), so term2 % d == 0
            assert(term2 % d == 0) by {
                assert(pow2(((n + 1) * 8) as nat) == d * pow2(8)) by {
                    lemma_pow2_adds((n * 8) as nat, 8);
                }
                lemma_mod_breakdown(term2 as int, d as int, pow2(8) as int);
            }

            // Subgoal 4: Sum of two numbers divisible by d is divisible by d
            assert((term1 + term2) % d == 0) by {
                lemma_mod_sum_both_divisible(term1, term2, d);
            }

            // Subgoal 5: u8_32_as_nat_rec(bytes, n) == term1 + term2
            assert(u8_32_as_nat_rec(bytes, n) == term1 + term2);
        }
    }
}

// ============================================================================
// Main Theorems: Byte Extraction and Injectivity
// ============================================================================
/// Lemma 1: Modulo truncates u8_32_as_nat to the first n bytes
///
/// This is the KEY lemma: taking modulo pow2(n*8) naturally truncates all bytes
/// beyond index n-1, leaving only the contribution of the first n bytes.
pub proof fn lemma_u8_32_as_nat_mod_truncates(bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
    ensures
        u8_32_as_nat(bytes) % pow2(n * 8) == bytes_as_nat_prefix(bytes@, n),
{
    let d = pow2((n * 8) as nat);
    let goal = u8_32_as_nat(bytes) % d == bytes_as_nat_prefix(bytes@, n);

    assert(goal) by {
        lemma2_to64();

        if n == 0 {
            // Base case: u8_32_as_nat % 1 == 0 == prefix(0)
            assert(pow2(0) == 1);
            assert(u8_32_as_nat(bytes) % 1 == 0);
            assert(bytes_as_nat_prefix(bytes@, 0) == 0);
        } else {
            let prefix = bytes_as_nat_prefix(bytes@, n);
            let suffix = u8_32_as_nat_rec(bytes, n);
            lemma_pow2_pos((n * 8) as nat);

            // Subgoal 1: u8_32_as_nat == u8_32_as_nat_rec(bytes, 0)
            assert(u8_32_as_nat(bytes) == u8_32_as_nat_rec(bytes, 0)) by {
                lemma_u8_32_as_nat_equals_rec(bytes);
            }

            // Subgoal 2: Decompose into prefix + suffix
            assert(u8_32_as_nat_rec(bytes, 0) == prefix + suffix) by {
                lemma_decomposition_prefix_rec(bytes, n);
            }

            // Subgoal 3: prefix < d (so prefix % d == prefix)
            assert(prefix < d) by {
                lemma_bytes_as_nat_prefix_bounded(bytes@, n);
            }
            assert(prefix % d == prefix) by {
                lemma_small_mod(prefix, d);
            }

            // Subgoal 4: suffix % d == 0
            assert(suffix % d == 0) by {
                lemma_rec_suffix_divisible(bytes, n);
            }

            // Subgoal 5: Express suffix as d * k
            lemma_fundamental_div_mod(suffix as int, d as int);
            let k = suffix / d;
            assert(suffix == d * k);

            // Subgoal 6: (prefix + suffix) % d == prefix
            assert((prefix + suffix) % d == prefix) by {
                assert(d * k == k * d) by {
                    lemma_mul_is_commutative(d as int, k as int);
                }
                assert(prefix + suffix == k * d + prefix);
                lemma_mod_sum_factor(k as int, prefix as int, d as int);
            }
        }
    }
}

/// Lemma 2: Division extracts a specific byte from a prefix
///
/// Once we have the first i+1 bytes via modulo, dividing by pow2(i*8)
/// shifts right by i bytes, leaving byte i in the lowest position.
pub proof fn lemma_prefix_div_extracts_byte(bytes: &[u8; 32], i: nat)
    requires
        i < 32,
    ensures
        (bytes_as_nat_prefix(bytes@, i + 1) / pow2(i * 8)) % pow2(8) == bytes[i as int] as nat,
{
    let low = bytes_as_nat_prefix(bytes@, i);
    let d = pow2((i * 8) as nat);
    let byte_val = bytes[i as int] as nat;
    let goal = (bytes_as_nat_prefix(bytes@, i + 1) / d) % pow2(8) == byte_val;

    assert(goal) by {
        lemma2_to64();
        lemma_pow2_pos((i * 8) as nat);

        // Subgoal 1: Expand prefix(i+1) = low + d * byte_val
        assert(bytes_as_nat_prefix(bytes@, i + 1) == low + d * byte_val);

        // Subgoal 2: low < d
        assert(low < d) by {
            lemma_bytes_as_nat_prefix_bounded(bytes@, i);
        }

        // Subgoal 3: low / d == 0 (since low < d)
        assert(low / d == 0) by {
            lemma_basic_div(low as int, d as int);
        }

        // Subgoal 4: (low + d * byte_val) / d == byte_val
        assert((low + d * byte_val) / d == byte_val) by {
            // Rewrite as (d * byte_val + low) / d
            assert(low + d * byte_val == d * byte_val + low);
            lemma_div_multiples_vanish_fancy(byte_val as int, low as int, d as int);
        }

        // Subgoal 5: byte_val % pow2(8) == byte_val (since byte_val < 256)
        assert(byte_val % pow2(8) == byte_val) by {
            lemma_u8_lt_pow2_8(bytes[i as int]);
            lemma_small_mod(byte_val, pow2(8));
        }
    }
}

/// Main Theorem: Extract byte i using modulo approach
///
/// Using lemma_pow2_div_mod and the modulo truncation approach,
/// we can extract any byte from u8_32_as_nat via division and modulo.
pub proof fn lemma_extract_byte_at_index(bytes: &[u8; 32], i: nat)
    requires
        i < 32,
    ensures
        bytes[i as int] as nat == (u8_32_as_nat(bytes) / pow2(i * 8)) % pow2(8),
{
    let goal = bytes[i as int] as nat == (u8_32_as_nat(bytes) / pow2(i * 8)) % pow2(8);

    assert(goal) by {
        lemma2_to64();

        // Subgoal 1: Transform (x / pow2(a)) % pow2(b) == (x % pow2(a+b)) / pow2(a)
        assert((u8_32_as_nat(bytes) / pow2(i * 8)) % pow2(8) == (u8_32_as_nat(bytes) % pow2(
            8 + i * 8,
        )) / pow2(i * 8)) by {
            lemma_pow2_div_mod(u8_32_as_nat(bytes), i * 8, 8);
        }

        // Subgoal 2: 8 + i*8 == (i+1)*8
        assert(8 + i * 8 == (i + 1) * 8) by {
            lemma_mul_is_distributive_add(8, 1, i as int);
        }

        // Subgoal 3: u8_32_as_nat % pow2((i+1)*8) == prefix(i+1)
        assert(u8_32_as_nat(bytes) % pow2((i + 1) * 8) == bytes_as_nat_prefix(bytes@, i + 1)) by {
            lemma_u8_32_as_nat_mod_truncates(bytes, i + 1);
        }

        // Subgoal 4: (prefix(i+1) / pow2(i*8)) % pow2(8) == bytes[i]
        assert((bytes_as_nat_prefix(bytes@, i + 1) / pow2(i * 8)) % pow2(8)
            == bytes[i as int] as nat) by {
            lemma_prefix_div_extracts_byte(bytes, i);
        }
    }
}

// ============================================================================
// Main Theorem: Injectivity
// ============================================================================
/// Main theorem: u8_32_as_nat is injective
///
/// If two 32-byte arrays have the same u8_32_as_nat value, then they are
/// equal byte-by-byte. This is proven by extracting each byte using
/// lemma_extract_byte_at_index and showing they must be equal.
pub proof fn lemma_canonical_bytes_equal(bytes1: &[u8; 32], bytes2: &[u8; 32])
    requires
        u8_32_as_nat(bytes1) == u8_32_as_nat(bytes2),
    ensures
        forall|i: int| 0 <= i < 32 ==> bytes1[i] == bytes2[i],
{
    assert forall|i: int| 0 <= i < 32 implies #[trigger] bytes1[i] == bytes2[i] by {
        // Extract byte i from both arrays
        lemma_extract_byte_at_index(bytes1, i as nat);
        lemma_extract_byte_at_index(bytes2, i as nat);

        // Since u8_32_as_nat(bytes1) == u8_32_as_nat(bytes2), the extracted bytes must be equal
        assert(bytes1[i] as nat == (u8_32_as_nat(bytes1) / pow2((i as nat) * 8)) % pow2(8));
        assert(bytes2[i] as nat == (u8_32_as_nat(bytes2) / pow2((i as nat) * 8)) % pow2(8));
        assert(bytes1[i] == bytes2[i]);
    }
}

// ============================================================================
// Trailing Zeros and Prefix Lemmas
// ============================================================================
/// Lemma: u8_32_as_nat_rec from index n is 0 when all bytes from n onwards are zero.
///
/// This is the key insight: the "suffix" part of the sum vanishes when trailing bytes are zero.
pub proof fn lemma_suffix_zero_when_bytes_zero(bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
        forall|i: int| n <= i < 32 ==> bytes[i] == 0,
    ensures
        u8_32_as_nat_rec(bytes, n) == 0,
    decreases 32 - n,
{
    let goal = u8_32_as_nat_rec(bytes, n) == 0;

    assert(goal) by {
        if n >= 32 {
            // Base case: u8_32_as_nat_rec(bytes, 32) == 0 by definition
        } else {
            // Subgoal 1: IH - suffix at n+1 is 0
            assert(u8_32_as_nat_rec(bytes, (n + 1) as nat) == 0) by {
                lemma_suffix_zero_when_bytes_zero(bytes, (n + 1) as nat);
            }

            // Subgoal 2: bytes[n] == 0, so bytes[n] * pow2(n*8) == 0
            assert(bytes[n as int] as nat * pow2((n * 8) as nat) == 0) by {
                lemma_mul_basics(pow2((n * 8) as nat) as int);
            }
        }
    }
}

/// Lemma: u8_32_as_nat equals bytes_as_nat_prefix when trailing bytes are zero.
///
/// Mathematical proof:
///   u8_32_as_nat = prefix(n) + suffix(n)    [by lemma_decomposition_prefix_rec]
///   suffix(n) = 0                           [by lemma_suffix_zero_when_bytes_zero]
///   Therefore: u8_32_as_nat = prefix(n)
pub proof fn lemma_u8_32_as_nat_with_trailing_zeros(bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
        forall|i: int| n <= i < 32 ==> bytes[i] == 0,
    ensures
        u8_32_as_nat(bytes) == bytes_as_nat_prefix(bytes@, n),
{
    let goal = u8_32_as_nat(bytes) == bytes_as_nat_prefix(bytes@, n);

    assert(goal) by {
        // Subgoal 1: u8_32_as_nat == u8_32_as_nat_rec(bytes, 0)
        assert(u8_32_as_nat(bytes) == u8_32_as_nat_rec(bytes, 0)) by {
            lemma_u8_32_as_nat_equals_rec(bytes);
        }

        // Subgoal 2: Decompose into prefix + suffix
        assert(u8_32_as_nat_rec(bytes, 0) == bytes_as_nat_prefix(bytes@, n) + u8_32_as_nat_rec(
            bytes,
            n,
        )) by {
            lemma_decomposition_prefix_rec(bytes, n);
        }

        // Subgoal 3: suffix is 0
        assert(u8_32_as_nat_rec(bytes, n) == 0) by {
            lemma_suffix_zero_when_bytes_zero(bytes, n);
        }
    }
}

/// Lemma: u8_32_as_nat of a 32-byte array with only the first byte set equals that byte.
///
/// This is a special case of lemma_u8_32_as_nat_with_trailing_zeros for n=1.
pub proof fn lemma_u8_32_as_nat_first_byte_only(bytes: &[u8; 32])
    requires
        forall|i: int| 1 <= i < 32 ==> bytes[i] == 0,
    ensures
        u8_32_as_nat(bytes) == bytes[0] as nat,
{
    let goal = u8_32_as_nat(bytes) == bytes[0] as nat;

    assert(goal) by {
        // Subgoal 1: u8_32_as_nat == prefix(1)
        lemma_u8_32_as_nat_with_trailing_zeros(bytes, 1);

        // Subgoal 2: prefix(1) == bytes[0]
        reveal_with_fuel(bytes_as_nat_prefix, 2);
        lemma2_to64();

        assert(bytes_as_nat_prefix(bytes@, 0) == 0);
        assert(bytes_as_nat_prefix(bytes@, 1) == bytes_as_nat_prefix(bytes@, 0) + pow2(0)
            * bytes[0] as nat);
        assert(pow2(0) == 1);
        assert(pow2(0) * bytes[0] as nat == bytes[0] as nat);
    }
}

/// Helper: bytes_as_nat_prefix values are equal when the sequences agree on first n bytes.
pub proof fn lemma_prefix_equal_when_bytes_match(seq1: Seq<u8>, seq2: Seq<u8>, n: nat)
    requires
        seq1.len() >= n,
        seq2.len() >= n,
        forall|i: int| #![auto] 0 <= i < n ==> seq1[i] == seq2[i],
    ensures
        bytes_as_nat_prefix(seq1, n) == bytes_as_nat_prefix(seq2, n),
    decreases n,
{
    let goal = bytes_as_nat_prefix(seq1, n) == bytes_as_nat_prefix(seq2, n);

    assert(goal) by {
        if n == 0 {
            // Both are 0
        } else {
            // IH: prefixes match for n-1
            assert(bytes_as_nat_prefix(seq1, (n - 1) as nat) == bytes_as_nat_prefix(
                seq2,
                (n - 1) as nat,
            )) by {
                lemma_prefix_equal_when_bytes_match(seq1, seq2, (n - 1) as nat);
            }
            // The n-th term is the same since seq1[n-1] == seq2[n-1]
        }
    }
}

/// Given a sequence of n bytes and a 32-byte array where:
/// - The first n bytes of the array match the sequence
/// - The remaining bytes (n..31) are zero
///
/// Proves that u8_32_as_nat of the array equals bytes_as_nat_prefix of the sequence.
///
/// (This lemma captures the common proof pattern for From<u16>, From<u32>,
/// From<u64>, and From<u128>.)
pub proof fn lemma_from_le_bytes(le_seq: Seq<u8>, bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
        le_seq.len() == n,
        forall|i: int| #![auto] 0 <= i < n ==> le_seq[i] == bytes[i],
        forall|i: int| n <= i < 32 ==> bytes[i] == 0,
    ensures
        u8_32_as_nat(bytes) == bytes_as_nat_prefix(le_seq, n),
{
    // Step 1: u8_32_as_nat(bytes) == prefix(bytes@, n)  [trailing zeros]
    lemma_u8_32_as_nat_with_trailing_zeros(bytes, n);

    // Step 2: prefix(bytes@, n) == prefix(le_seq, n)  [first n bytes match]
    lemma_prefix_equal_when_bytes_match(bytes@, le_seq, n);
}

// ============================================================================
// Lower bound lemmas for u8_32_as_nat
// ============================================================================
/// Proves that u8_32_as_nat is at least as large as any individual term in its sum.
/// Useful for showing that if bytes[i] is non-zero, then u8_32_as_nat >= 2^(i*8).
pub proof fn lemma_u8_32_as_nat_lower_bound(bytes: &[u8; 32], index: usize)
    requires
        index < 32,
    ensures
        u8_32_as_nat(bytes) >= (bytes[index as int] as nat) * pow2((index * 8) as nat),
{
    // u8_32_as_nat is defined recursively as a sum of non-negative terms
    // Therefore the sum is >= any individual term
    lemma_u8_32_as_nat_equals_rec(bytes);
    lemma_u8_32_as_nat_rec_bound(bytes, 0, index);
}

/// Helper lemma showing that u8_32_as_nat_rec is >= a specific term
proof fn lemma_u8_32_as_nat_rec_bound(bytes: &[u8; 32], start: usize, target: usize)
    requires
        start <= target < 32,
    ensures
        u8_32_as_nat_rec(bytes, start as nat) >= (bytes[target as int] as nat) * pow2(
            (target * 8) as nat,
        ),
    decreases 32 - start,
{
    if start == target {
        // Base case: the current term is exactly what we're looking for
        // u8_32_as_nat_rec(bytes, target) = bytes[target] * pow2(target*8) + (rest >= 0)
    } else {
        // Inductive case: recurse to the next position
        lemma_u8_32_as_nat_rec_bound(bytes, (start + 1) as usize, target);
    }
}

// ============================================================================
// Bridge lemmas: connecting different byte-to-nat representations
// ============================================================================
/// Lemma: u8_32_as_nat (32-byte) equals u8_32_as_nat_rec starting at index 0
pub proof fn lemma_u8_32_as_nat_equals_rec(bytes: &[u8; 32])
    ensures
        u8_32_as_nat(bytes) == u8_32_as_nat_rec(bytes, 0),
{
    reveal_with_fuel(u8_32_as_nat_rec, 33);
    assert(u8_32_as_nat_rec(bytes, 32) == 0);
}

/// Bridge: u8_32_as_nat on a [u8; 32] array equals bytes_seq_as_nat on its view.
///
/// Connects the fixed-size `u8_32_as_nat(&arr)` with the sequence-based
/// `bytes_seq_as_nat(arr@)` by going through `bytes_as_nat_prefix`.
pub proof fn lemma_u8_32_as_nat_eq_bytes_seq_as_nat(bytes: &[u8; 32])
    ensures
        u8_32_as_nat(bytes) == bytes_seq_as_nat(bytes@),
{
    // Step 1: u8_32_as_nat == u8_32_as_nat_rec(bytes, 0)
    lemma_u8_32_as_nat_equals_rec(bytes);

    // Step 2: u8_32_as_nat_rec(bytes, 0) == bytes_as_nat_prefix(bytes@, 32)
    //         because u8_32_as_nat_rec(bytes, 32) == 0
    lemma_decomposition_prefix_rec(bytes, 32);
    reveal_with_fuel(u8_32_as_nat_rec, 33);
    assert(u8_32_as_nat_rec(bytes, 32) == 0);

    // Step 3: bytes_seq_as_nat(bytes@) == bytes_as_nat_prefix(bytes@, 32)
    lemma_bytes_seq_as_nat_equals_prefix(bytes@);
}

/// Helper: bytes_as_nat_prefix equals bytes_to_nat_suffix for matching ranges
///
/// For a fixed-size array, prefix(bytes@, k) equals the sum of suffix terms from 0 to k-1.
/// This is proven by induction: at each step, prefix adds the same term as suffix would include.
proof fn lemma_prefix_equals_suffix_partial<const N: usize>(bytes: &[u8; N], k: nat)
    requires
        k <= N,
    ensures
        bytes_as_nat_prefix(bytes@, k) == bytes_as_nat_suffix(bytes, 0) - bytes_as_nat_suffix(
            bytes,
            k as int,
        ),
    decreases k,
{
    if k == 0 {
        // Base: prefix(0) == 0, and suffix(0) - suffix(0) == 0
    } else {
        // IH: prefix(k-1) == suffix(0) - suffix(k-1)
        lemma_prefix_equals_suffix_partial(bytes, (k - 1) as nat);

        // prefix(k) = prefix(k-1) + bytes[k-1] * pow2((k-1)*8)
        // suffix(k-1) = bytes[k-1] * pow2((k-1)*8) + suffix(k)
        // So: suffix(0) - suffix(k) = (suffix(0) - suffix(k-1)) + bytes[k-1] * pow2((k-1)*8)
        //                           = prefix(k-1) + bytes[k-1] * pow2((k-1)*8)
        //                           = prefix(k)
    }
}

/// Helper: For a full array, prefix(N) equals suffix(0)
proof fn lemma_prefix_equals_suffix_full<const N: usize>(bytes: &[u8; N])
    ensures
        bytes_as_nat_prefix(bytes@, N as nat) == bytes_as_nat_suffix(bytes, 0),
{
    // suffix(N) == 0 by definition (start >= N)
    assert(bytes_as_nat_suffix(bytes, N as int) == 0);

    // By lemma_prefix_equals_suffix_partial:
    // prefix(N) == suffix(0) - suffix(N) == suffix(0) - 0 == suffix(0)
    lemma_prefix_equals_suffix_partial(bytes, N as nat);
}

/// Lemma: For 64-byte arrays, bytes_seq_as_nat equals bytes_as_nat_suffix starting at 0
pub proof fn lemma_u8_32_as_nat_equals_suffix_64(bytes: &[u8; 64])
    ensures
        bytes_seq_as_nat(bytes@) == bytes_as_nat_suffix(bytes, 0),
{
    // Step 1: bytes_seq_as_nat(bytes@) == bytes_as_nat_prefix(bytes@, 64)
    lemma_bytes_seq_as_nat_equals_prefix(bytes@);

    // Step 2: bytes_as_nat_prefix(bytes@, 64) == bytes_as_nat_suffix(bytes, 0)
    lemma_prefix_equals_suffix_full(bytes);
}

// ============================================================================
// Identity bytes lemma (for CompressedEdwardsY::identity)
// ============================================================================
/// Lemma: u8_32_as_nat([1, 0, 0, ..., 0]) == 1
///
/// This proves that the little-endian interpretation of a 32-byte array
/// with byte[0] = 1 and all other bytes = 0 equals the natural number 1.
/// Used in CompressedEdwardsY::identity() verification.
pub proof fn lemma_u8_32_as_nat_identity(bytes: &[u8; 32])
    requires
        bytes[0] == 1,
        forall|i: int| 1 <= i < 32 ==> bytes[i] == 0,
    ensures
        u8_32_as_nat(bytes) == 1,
{
    // bytes[0] * pow2(0) = 1 * 1 = 1
    assert(bytes[0] as nat * pow2(0) == 1) by {
        lemma2_to64();
    }

    // All other terms are 0 * pow2(k*8) = 0
    assert forall|i: nat| 1 <= i < 32 implies (bytes[i as int] as nat) * #[trigger] pow2(i * 8)
        == 0 by {
        lemma_mul_basics(pow2(i * 8) as int);
    }
}

// ============================================================================
// PART 2: WORD-TO-NAT LEMMAS
// ============================================================================
//
// NOTE: These lemmas are currently specialized for 8-word (64-byte) inputs,
// matching the from_bytes_wide use case. They could be made generic over
// array size if other use cases emerge (e.g., for 32-byte or 128-byte inputs).
/// Upper bound: result ≤ 2^(count×64) - 1
/// Note: Currently specialized for &[u64; 8]. Could be made generic over size N.
pub proof fn lemma_words_as_nat_upper_bound(words: &[u64; 8], count: int)
    requires
        0 <= count <= 8,
        forall|k: int| 0 <= k < 8 ==> words[k] < pow2(64),
    ensures
        words_as_nat_u64(words, count, 64) <= pow2((count * 64) as nat) - 1,
    decreases count,
{
    reveal_with_fuel(words_as_nat_gen, 9);

    if count == 0 {
        lemma2_to64();
    } else {
        let idx = count - 1;
        lemma_words_as_nat_upper_bound(words, idx);
        let word_val = words[idx] as nat;

        lemma_mul_upper_bound(
            word_val as int,
            (pow2(64) - 1) as int,
            pow2((idx * 64) as nat) as int,
            pow2((idx * 64) as nat) as int,
        );

        assert(words_as_nat_u64(words, count, 64) <= pow2((count * 64) as nat) - 1) by {
            let pow_prefix = pow2((idx * 64) as nat) as int;
            let pow64 = pow2(64) as int;
            let word_i = word_val as int;
            let prefix_i = words_as_nat_u64(words, idx, 64) as int;

            lemma_pow2_adds((idx * 64) as nat, 64);
            lemma_mul_is_distributive_sub(pow_prefix, pow64, word_i);
            lemma_mul_is_distributive_add(pow_prefix, pow64 - 1 - word_i, 1 as int);
        };
    }
}

/// Equivalence: words_as_nat on word array == words_from_bytes on underlying bytes
/// Note: Currently specialized for &[u64; 8] and &[u8; 64]. Could be made generic over size N.
pub proof fn lemma_words_as_nat_equals_bytes(words: &[u64; 8], bytes: &[u8; 64], count: int)
    requires
        0 <= count <= 8,
        forall|k: int| #![auto] 0 <= k < 8 ==> words@[k] as nat == word64_from_bytes(bytes@, k),
    ensures
        words_as_nat_u64(words, count, 64) == words64_from_bytes_to_nat(bytes@, count),
    decreases count,
{
    reveal_with_fuel(words_as_nat_gen, 9);
    reveal_with_fuel(words64_from_bytes_to_nat, 9);
}

/// Expands to explicit 8-term sum (used for from_bytes_wide verification)
/// Note: This is inherently size-specific (explicit 8-term expansion).
/// For other sizes, similar expansion lemmas could be added as needed.
pub proof fn lemma_words64_from_bytes_to_nat_wide(bytes: &[u8; 64])
    ensures
        words64_from_bytes_to_nat(bytes@, 8) == word64_from_bytes(bytes@, 0) + pow2(64)
            * word64_from_bytes(bytes@, 1) + pow2(128) * word64_from_bytes(bytes@, 2) + pow2(192)
            * word64_from_bytes(bytes@, 3) + pow2(256) * word64_from_bytes(bytes@, 4) + pow2(320)
            * word64_from_bytes(bytes@, 5) + pow2(384) * word64_from_bytes(bytes@, 6) + pow2(448)
            * word64_from_bytes(bytes@, 7),
{
    reveal_with_fuel(words64_from_bytes_to_nat, 9);
    lemma2_to64();
    assert(words64_from_bytes_to_nat(bytes@, 1) == words64_from_bytes_to_nat(bytes@, 0)
        + word64_from_bytes(bytes@, 0) * pow2((0 * 64) as nat));
    // Reorder multiplications using commutativity
    assert(words64_from_bytes_to_nat(bytes@, 8) == word64_from_bytes(bytes@, 0) + pow2(64)
        * word64_from_bytes(bytes@, 1) + pow2(128) * word64_from_bytes(bytes@, 2) + pow2(192)
        * word64_from_bytes(bytes@, 3) + pow2(256) * word64_from_bytes(bytes@, 4) + pow2(320)
        * word64_from_bytes(bytes@, 5) + pow2(384) * word64_from_bytes(bytes@, 6) + pow2(448)
        * word64_from_bytes(bytes@, 7)) by {
        broadcast use lemma_mul_is_commutative;

    };
}

// ============================================================================
// Prefix chunk decomposition: splitting bytes_as_nat_prefix at 8-byte boundaries
// ============================================================================
/// bytes_as_nat_prefix of (k*8 + remaining) bytes equals bytes_as_nat_prefix of k*8 bytes
/// plus the chunk's prefix value scaled by pow2(k*64).
///
/// Recursive on `remaining` (call with remaining=8 for the full 8-byte chunk):
///   bytes_as_nat_prefix(bytes, k*8 + remaining) ==
///     bytes_as_nat_prefix(bytes, k*8) + bytes_as_nat_prefix(chunk, remaining) * pow2(k*64)
/// where chunk = bytes[k*8..(k+1)*8].
///
/// This is the "prefix additivity at 8-byte boundaries" property.
pub proof fn lemma_bytes_as_nat_prefix_chunk(bytes: Seq<u8>, chunk: Seq<u8>, k: nat, remaining: nat)
    requires
        remaining <= 8,
        bytes.len() >= k * 8 + 8,
        chunk.len() == 8,
        forall|j: int| 0 <= j < 8 ==> chunk[j] == bytes[k * 8 + j],
    ensures
        bytes_as_nat_prefix(bytes, (k * 8 + remaining) as nat) == bytes_as_nat_prefix(
            bytes,
            (k * 8) as nat,
        ) + bytes_as_nat_prefix(chunk, remaining) * pow2((k * 64) as nat),
    decreases remaining,
{
    if remaining == 0 {
        assert(bytes_as_nat_prefix(chunk, 0) == 0);
        assert(0 * pow2((k * 64) as nat) == 0) by {
            lemma_mul_basics(pow2((k * 64) as nat) as int);
        }
    } else {
        let rm1 = (remaining - 1) as nat;
        // IH: prefix(bytes, k*8+rm1) == prefix(bytes, k*8) + prefix(chunk, rm1) * pow2(k*64)
        // Kept bare: wrapping in assert-by disrupts downstream solver context
        lemma_bytes_as_nat_prefix_chunk(bytes, chunk, k, rm1);

        // Unfold bytes_as_nat_prefix at (k*8 + remaining)
        let idx = (k * 8 + rm1) as nat;
        assert(bytes_as_nat_prefix(bytes, (k * 8 + remaining) as nat) == bytes_as_nat_prefix(
            bytes,
            idx,
        ) + pow2((idx * 8) as nat) * bytes[idx as int] as nat);

        // Unfold bytes_as_nat_prefix(chunk, remaining)
        assert(bytes_as_nat_prefix(chunk, remaining) == bytes_as_nat_prefix(chunk, rm1) + pow2(
            (rm1 * 8) as nat,
        ) * chunk[rm1 as int] as nat);

        // chunk[remaining-1] == bytes[k*8 + remaining - 1]
        assert(chunk[rm1 as int] == bytes[(k * 8 + rm1) as int]);

        // Key: pow2(idx * 8) == pow2(rm1 * 8) * pow2(k * 64)
        // since idx * 8 = (k*8 + rm1) * 8 = k*64 + rm1*8
        assert((k * 8 + rm1) * 8 == k * 64 + rm1 * 8) by {
            lemma_mul_is_distributive_add(8, (k * 8) as int, rm1 as int);
            lemma_mul_is_associative(8, k as int, 8);
        }
        assert(pow2(((k * 8 + rm1) * 8) as nat) == pow2((rm1 * 8) as nat) * pow2((k * 64) as nat))
            by {
            lemma_pow2_adds((rm1 * 8) as nat, (k * 64) as nat);
        }

        // Distribute: (prefix + byte_val * pow2(rm1*8)) * pow2(k*64)
        let p = bytes_as_nat_prefix(chunk, rm1) as int;
        let bv = chunk[rm1 as int] as nat as int;
        let pw_rm1 = pow2((rm1 * 8) as nat) as int;
        let pw_k = pow2((k * 64) as nat) as int;

        assert((p + pw_rm1 * bv) * pw_k == p * pw_k + pw_rm1 * bv * pw_k) by {
            lemma_mul_is_distributive_add(pw_k, p, pw_rm1 * bv);
        }
        assert(pw_rm1 * bv * pw_k == pw_rm1 * pw_k * bv) by {
            lemma_mul_is_associative(pw_rm1, bv, pw_k);
            lemma_mul_is_commutative(bv, pw_k);
            lemma_mul_is_associative(pw_rm1, pw_k, bv);
        }
    }
}

// ============================================================================
// Lemma: 4 little-endian u64 chunks reconstruct u8_32_as_nat
// ============================================================================
/// When a 32-byte array is split into four 8-byte chunks, the weighted sum
/// of their prefix values equals u8_32_as_nat.
pub proof fn lemma_u64x4_from_le_bytes(
    bytes: [u8; 32],
    chunk0: [u8; 8],
    chunk1: [u8; 8],
    chunk2: [u8; 8],
    chunk3: [u8; 8],
)
    requires
        forall|j: int| 0 <= j < 8 ==> chunk0[j] == bytes[j],
        forall|j: int| 0 <= j < 8 ==> chunk1[j] == bytes[8 + j],
        forall|j: int| 0 <= j < 8 ==> chunk2[j] == bytes[16 + j],
        forall|j: int| 0 <= j < 8 ==> chunk3[j] == bytes[24 + j],
    ensures
        bytes_as_nat_prefix(chunk0@, 8) + bytes_as_nat_prefix(chunk1@, 8) * pow2(64)
            + bytes_as_nat_prefix(chunk2@, 8) * pow2(128) + bytes_as_nat_prefix(chunk3@, 8) * pow2(
            192,
        ) == u8_32_as_nat(&bytes),
{
    // Step 1: chunk0's prefix value equals the first 8 bytes' prefix value
    assert(bytes_as_nat_prefix(chunk0@, 8) == bytes_as_nat_prefix(bytes@, 8)) by {
        lemma_prefix_equal_when_bytes_match(chunk0@, bytes@, 8);
    }

    // Step 2: Telescoping — each chunk adds its value * pow2(k*64) to the prefix
    assert(bytes_as_nat_prefix(bytes@, 8) == bytes_as_nat_prefix(bytes@, 0) + bytes_as_nat_prefix(
        chunk0@,
        8,
    ) * pow2(0)) by {
        lemma_bytes_as_nat_prefix_chunk(bytes@, chunk0@, 0, 8);
    }
    assert(bytes_as_nat_prefix(bytes@, 0) == 0);
    assert(pow2(0) == 1) by {
        lemma2_to64();
    }

    assert forall|j: int| 0 <= j < 8 implies chunk1@[j] == bytes@[1 * 8 + j] by {
        assert(chunk1@[j] == chunk1[j]);
        assert(bytes@[8 + j] == bytes[8 + j]);
    }
    assert(bytes_as_nat_prefix(bytes@, 16) == bytes_as_nat_prefix(bytes@, 8) + bytes_as_nat_prefix(
        chunk1@,
        8,
    ) * pow2(64)) by {
        lemma_bytes_as_nat_prefix_chunk(bytes@, chunk1@, 1, 8);
    }

    assert forall|j: int| 0 <= j < 8 implies chunk2@[j] == bytes@[2 * 8 + j] by {
        assert(chunk2@[j] == chunk2[j]);
        assert(bytes@[16 + j] == bytes[16 + j]);
    }
    assert(bytes_as_nat_prefix(bytes@, 24) == bytes_as_nat_prefix(bytes@, 16) + bytes_as_nat_prefix(
        chunk2@,
        8,
    ) * pow2(128)) by {
        lemma_bytes_as_nat_prefix_chunk(bytes@, chunk2@, 2, 8);
    }

    assert forall|j: int| 0 <= j < 8 implies chunk3@[j] == bytes@[3 * 8 + j] by {
        assert(chunk3@[j] == chunk3[j]);
        assert(bytes@[24 + j] == bytes[24 + j]);
    }
    assert(bytes_as_nat_prefix(bytes@, 32) == bytes_as_nat_prefix(bytes@, 24) + bytes_as_nat_prefix(
        chunk3@,
        8,
    ) * pow2(192)) by {
        lemma_bytes_as_nat_prefix_chunk(bytes@, chunk3@, 3, 8);
    }

    // Step 3: u8_32_as_nat equals the full 32-byte prefix
    assert(u8_32_as_nat(&bytes) == bytes_as_nat_prefix(bytes@, 32)) by {
        lemma_u8_32_as_nat_equals_rec(&bytes);
        lemma_decomposition_prefix_rec(&bytes, 32);
    }
}

} // verus!
