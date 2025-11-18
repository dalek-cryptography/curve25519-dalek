#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::specs::core_specs::*;

verus! {

/// Helper spec: Sum of the first n bytes of a 32-byte array in little-endian
/// This represents: bytes[0] + bytes[1]*2^8 + ... + bytes[n-1]*2^((n-1)*8)
pub open spec fn as_nat_prefix(bytes: &[u8; 32], n: nat) -> nat
    recommends
        n <= 32,
    decreases n,
{
    if n == 0 {
        0
    } else {
        as_nat_prefix(bytes, (n - 1) as nat) + bytes[(n - 1) as int] as nat * pow2(
            ((n - 1) * 8) as nat,
        )
    }
}

// ============================================================================
// Properties of as_nat_prefix
// ============================================================================
/// Helper: Bound as_nat_prefix - geometric series bound
/// Each byte contributes at most 255 * pow2(j*8) < pow2((j+1)*8)
pub proof fn lemma_as_nat_prefix_bounded(bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
    ensures
        as_nat_prefix(bytes, n) < pow2((n * 8) as nat),
    decreases n,
{
    lemma2_to64();

    if n == 0 {
        // Base case: as_nat_prefix(bytes, 0) == 0 < 1 == pow2(0)
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(as_nat_prefix(bytes, 0) == 0);
    } else {
        // Inductive case
        lemma_as_nat_prefix_bounded(bytes, (n - 1) as nat);
        lemma_u8_lt_pow2_8(bytes[(n - 1) as int]);

        // Key identity: pow2(n*8) = pow2((n-1)*8 + 8) = pow2((n-1)*8) * pow2(8)
        assert(n * 8 == (n - 1) * 8 + 8) by {
            lemma_mul_is_distributive_sub(8, n as int, 1);
        }
        lemma_pow2_adds(((n - 1) * 8) as nat, 8);
        assert(pow2((n * 8) as nat) == pow2(((n - 1) * 8) as nat) * pow2(8));

        // Now use nonlinear arithmetic to combine
        let prev = as_nat_prefix(bytes, (n - 1) as nat);
        let byte_val = bytes[(n - 1) as int] as nat;
        let p1 = pow2(((n - 1) * 8) as nat);
        let p2 = pow2(8);

        assert(prev + byte_val * p1 < p1 * p2) by (nonlinear_arith)
            requires
                prev < p1,
                byte_val < p2,
                p2 == 256,
        {}
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
        u8_32_as_nat_rec(bytes, 0) == as_nat_prefix(bytes, n) + u8_32_as_nat_rec(bytes, n),
    decreases n,
{
    if n == 0 {
        // Base case: u8_32_as_nat_rec(bytes, 0) == 0 + u8_32_as_nat_rec(bytes, 0)
        assert(as_nat_prefix(bytes, 0) == 0);
    } else {
        // Inductive step: assume true for n-1, prove for n
        lemma_decomposition_prefix_rec(bytes, (n - 1) as nat);

        // Unfold u8_32_as_nat_rec(bytes, n-1):
        assert(u8_32_as_nat_rec(bytes, (n - 1) as nat) == bytes[(n - 1) as int] as nat * pow2(
            ((n - 1) * 8) as nat,
        ) + u8_32_as_nat_rec(bytes, n));

        // Unfold as_nat_prefix(bytes, n):
        assert(as_nat_prefix(bytes, n) == as_nat_prefix(bytes, (n - 1) as nat) + bytes[(n
            - 1) as int] as nat * pow2(((n - 1) * 8) as nat));
    }
}

/// Lemma: The suffix u8_32_as_nat_rec(bytes, n) is divisible by pow2(n*8)
/// Every term in the sum has a factor of pow2(j*8) where j >= n, so the whole sum is divisible by pow2(n*8)
///
/// NOTE: Uses lemma_mod_breakdown and lemma_mod_sum_both_divisible from vstd/common_lemmas
pub proof fn lemma_rec_suffix_divisible(bytes: &[u8; 32], n: nat)
    requires
        n <= 32,
    ensures
        u8_32_as_nat_rec(bytes, n) % pow2((n * 8) as nat) == 0,
    decreases (32 - n),
{
    lemma2_to64();

    if n >= 32 {
        // Base case: u8_32_as_nat_rec(bytes, 32) == 0
        assert(u8_32_as_nat_rec(bytes, 32) == 0);
        lemma_pow2_pos((32 * 8) as nat);
        assert(0nat % pow2((32 * 8) as nat) == 0);
    } else {
        // Inductive step: show u8_32_as_nat_rec(bytes, n) is divisible by pow2(n*8)
        let term1 = bytes[n as int] as nat * pow2((n * 8) as nat);
        let d = pow2((n * 8) as nat);
        lemma_pow2_pos((n * 8) as nat);

        // Part 1: term1 = bytes[n] * d, so term1 % d = 0
        assert((bytes[n as int] as nat * d) % d == 0) by {
            lemma_mod_multiples_basic(bytes[n as int] as int, d as int);
        }
        assert(term1 % d == 0);

        // Part 2: u8_32_as_nat_rec(bytes, n+1) is divisible by pow2((n+1)*8) by IH
        assert(u8_32_as_nat_rec(bytes, (n + 1) as nat) % pow2(((n + 1) * 8) as nat) == 0) by {
            lemma_rec_suffix_divisible(bytes, (n + 1) as nat);
        }

        // Since pow2((n+1)*8) == pow2(n*8) * pow2(8), it's also divisible by pow2(n*8)
        assert(pow2(((n + 1) * 8) as nat) == pow2((n * 8) as nat) * pow2(8)) by {
            lemma_pow2_adds((n * 8) as nat, 8);
        }

        // If x % (d * k) == 0, then x % d == 0 (follows from lemma_mod_breakdown)
        let term2 = u8_32_as_nat_rec(bytes, (n + 1) as nat);
        assert(term2 % d == 0) by {
            lemma_mod_breakdown(term2 as int, d as int, pow2(8) as int);
        }

        // Part 3: Sum of two numbers divisible by d is divisible by d
        assert((term1 + term2) % d == 0) by {
            lemma_mod_sum_both_divisible(term1, term2, d);
        }

        // Conclusion: u8_32_as_nat_rec(bytes, n) == term1 + term2, so it's divisible by d
        assert(u8_32_as_nat_rec(bytes, n) == term1 + term2);
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
        u8_32_as_nat(bytes) % pow2(n * 8) == as_nat_prefix(bytes, n),
{
    lemma2_to64();

    if n == 0 {
        // Base case: u8_32_as_nat(bytes) % pow2(0) == 0 == as_nat_prefix(bytes, 0)
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(u8_32_as_nat(bytes) % 1 == 0);
        assert(as_nat_prefix(bytes, 0) == 0);
    } else {
        // Use the recursive representation
        assert(u8_32_as_nat(bytes) == u8_32_as_nat_rec(bytes, 0)) by {
            lemma_u8_32_as_nat_equals_rec(bytes);
        }

        // Decompose u8_32_as_nat_rec(bytes, 0) into prefix + suffix
        assert(u8_32_as_nat_rec(bytes, 0) == as_nat_prefix(bytes, n) + u8_32_as_nat_rec(bytes, n))
            by {
            lemma_decomposition_prefix_rec(bytes, n);
        }

        // Show that as_nat_prefix(bytes, n) < pow2(n*8)
        assert(as_nat_prefix(bytes, n) < pow2((n * 8) as nat)) by {
            lemma_as_nat_prefix_bounded(bytes, n);
        }

        // Show that u8_32_as_nat_rec(bytes, n) is divisible by pow2(n*8)
        assert(u8_32_as_nat_rec(bytes, n) % pow2((n * 8) as nat) == 0) by {
            lemma_rec_suffix_divisible(bytes, n);
        }

        // Apply modular arithmetic: (a + b) % m == a % m when b % m == 0 and a < m
        let prefix = as_nat_prefix(bytes, n);
        let suffix = u8_32_as_nat_rec(bytes, n);
        let d = pow2((n * 8) as nat);

        lemma_pow2_pos((n * 8) as nat);
        assert(prefix % d == prefix) by {
            lemma_small_mod(prefix, d);
        }

        // REFACTORED: Inline the proof instead of using lemma_mod_sum_factor_specific
        // Since suffix % d == 0, we have suffix = (suffix/d) * d
        lemma_fundamental_div_mod(suffix as int, d as int);
        let k = suffix / d;
        assert(suffix == d * k + 0);
        assert(suffix == d * k);

        // Now use lemma_mod_sum_factor: (k * d + prefix) % d == prefix % d
        lemma_mod_sum_factor(k as int, prefix as int, d as int);
        assert((k * d + prefix) % d == prefix % d);

        // We need to show (prefix + suffix) % d == prefix
        // We have suffix == d * k, so prefix + suffix == prefix + d * k
        assert(prefix + suffix == prefix + d * k);
        // And d * k == k * d
        assert(d * k == k * d) by {
            lemma_mul_is_commutative(d as int, k as int);
        }
        // Therefore prefix + suffix == prefix + k * d == k * d + prefix
        assert(prefix + suffix == k * d + prefix);
        // And we know (k * d + prefix) % d == prefix % d == prefix
        assert((prefix + suffix) % d == prefix);

        // Therefore: u8_32_as_nat(bytes) % pow2(n*8) == as_nat_prefix(bytes, n)
        assert(u8_32_as_nat(bytes) % pow2((n * 8) as nat) == prefix);
    }
}

/// Lemma 2: Division extracts a specific byte from a prefix
///
/// Once we have the first i+1 bytes via modulo, dividing by pow2(i*8)
/// shifts right by i bytes, leaving byte i in the lowest position.
pub proof fn lemma_as_nat_prefix_div_extracts_byte(bytes: &[u8; 32], i: nat)
    requires
        i < 32,
    ensures
        (as_nat_prefix(bytes, i + 1) / pow2(i * 8)) % pow2(8) == bytes[i as int] as nat,
{
    lemma2_to64();

    // Step 1: Expand as_nat_prefix(bytes, i+1)
    assert(as_nat_prefix(bytes, i + 1) == as_nat_prefix(bytes, i) + bytes[i as int] as nat * pow2(
        (i * 8) as nat,
    ));

    // Step 2: Show that as_nat_prefix(bytes, i) < pow2(i*8)
    assert(as_nat_prefix(bytes, i) < pow2((i * 8) as nat)) by {
        lemma_as_nat_prefix_bounded(bytes, i);
    }

    // Step 3: Division of (LOW + bytes[i] * d) / d == bytes[i] when LOW < d
    let low = as_nat_prefix(bytes, i);
    let d = pow2((i * 8) as nat);
    let byte_val = bytes[i as int] as nat;

    // Since low < d, we have low / d == 0
    assert(low / d == 0) by {
        lemma_basic_div(low as int, d as int);
    }

    // Therefore: (low + byte_val * d) / d == byte_val
    lemma_pow2_pos((i * 8) as nat);
    assert(d > 0);

    // Use division algebra: (d * x + b) / d == x when 0 < d and 0 <= b < d
    // We have: 0 < d, 0 <= low < d, so we can apply the lemma
    lemma_div_multiples_vanish_fancy(byte_val as int, low as int, d as int);
    // This gives us: (d * byte_val + low) / d == byte_val

    // Show that (low + byte_val * d) = (d * byte_val + low) by commutativity
    assert(low + byte_val * d == d * byte_val + low) by {
        lemma_mul_is_commutative(byte_val as int, d as int);
    }
    assert((low + byte_val * d) / d == byte_val);

    // Step 4: bytes[i] < pow2(8), so bytes[i] % pow2(8) == bytes[i]
    assert(byte_val % pow2(8) == byte_val) by {
        lemma_u8_lt_pow2_8(bytes[i as int]);
        lemma_small_mod(byte_val, pow2(8));
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
    lemma2_to64();

    // Step 1: Apply lemma_pow2_div_mod to transform the expression
    assert((u8_32_as_nat(bytes) / pow2(i * 8)) % pow2(8) == (u8_32_as_nat(bytes) % pow2(8 + i * 8))
        / pow2(i * 8)) by {
        lemma_pow2_div_mod(u8_32_as_nat(bytes), i * 8, 8);
    }

    // Step 2: Simplify 8 + i*8 = (i+1)*8
    assert(8 + i * 8 == (i + 1) * 8) by {
        lemma_mul_is_distributive_add(8, 1, i as int);
    }

    // Step 3: Apply modulo truncation lemma
    assert(u8_32_as_nat(bytes) % pow2((i + 1) * 8) == as_nat_prefix(bytes, i + 1)) by {
        lemma_u8_32_as_nat_mod_truncates(bytes, i + 1);
    }

    // Step 4: Apply division extraction lemma
    assert((as_nat_prefix(bytes, i + 1) / pow2(i * 8)) % pow2(8) == bytes[i as int] as nat) by {
        lemma_as_nat_prefix_div_extracts_byte(bytes, i);
    }

    // Step 5: Combine all steps
    assert(bytes[i as int] as nat == (u8_32_as_nat(bytes) / pow2(i * 8)) % pow2(8));
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

} // verus!
