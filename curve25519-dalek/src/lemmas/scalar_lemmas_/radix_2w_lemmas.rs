//! Lemmas for proving correctness of `as_radix_2w` in scalar.rs.
//!
//! Key lemmas:
//! - `lemma_reconstruct_radix_2w_split`: Split reconstruction at arbitrary position k
//! - `lemma_u64x4_bit_extraction`: Bit extraction from u64x4
//! - `lemma_radix_2w_digit_bounds`: Digit bounds via carry/recentering
//! - `lemma_as_radix_2w_postconditions`: Final postconditions from loop invariant
//! - `lemma_last_iter_carry_zero`: Carry is zero at last iteration for w < 8
//! - `lemma_digits_count_radix_bounds`: Digit count and radix bounds for w in 5..=8
//!
#![allow(unused_imports)]

use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::lemmas::common_lemmas::bit_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::mask_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::shift_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;

verus! {

// =============================================================================
// Shared helpers for u64x4 word-level decomposition
// =============================================================================
/// Strip upper u64 words from u64_4_as_nat under a modular reduction.
///
/// For a boundary b in (0, 256], the words whose 64-bit base offset >= b do not
/// affect `u64_4_as_nat(&words) % pow2(b)`.  This lemma factors them out,
/// leaving only the partial sum of words below the boundary.
proof fn lemma_u64x4_mod_strip_above(words: [u64; 4], boundary: nat)
    requires
        0 < boundary <= 256,
    ensures
        u64_4_as_nat(&words) % pow2(boundary) == (if boundary <= 64 {
            words[0] as nat
        } else if boundary <= 128 {
            words[0] as nat + words[1] as nat * pow2(64)
        } else if boundary <= 192 {
            words[0] as nat + words[1] as nat * pow2(64) + words[2] as nat * pow2(128)
        } else {
            u64_4_as_nat(&words)
        }) % pow2(boundary),
{
    let val = u64_4_as_nat(&words);
    let pb = pow2(boundary) as int;
    lemma_pow2_pos(boundary);

    if boundary <= 64 {
        // Strip words[1..3]: each has base >= 64 >= boundary
        let partial = words[0] as nat;
        lemma_pow2_adds((64 - boundary) as nat, boundary);
        lemma_pow2_adds((128 - boundary) as nat, boundary);
        lemma_pow2_adds((192 - boundary) as nat, boundary);
        let r64 = pow2((64 - boundary) as nat) as int;
        let r128 = pow2((128 - boundary) as nat) as int;
        let r192 = pow2((192 - boundary) as nat) as int;
        let w1i = words[1] as nat as int;
        let w2i = words[2] as nat as int;
        let w3i = words[3] as nat as int;
        assert(w1i * pow2(64) as int == (w1i * r64) * pb) by {
            lemma_mul_is_commutative(pb, r64);
            lemma_mul_is_associative(w1i, r64, pb);
        }
        assert(w2i * pow2(128) as int == (w2i * r128) * pb) by {
            lemma_mul_is_commutative(pb, r128);
            lemma_mul_is_associative(w2i, r128, pb);
        }
        assert(w3i * pow2(192) as int == (w3i * r192) * pb) by {
            lemma_mul_is_commutative(pb, r192);
            lemma_mul_is_associative(w3i, r192, pb);
        }
        let upper = w1i * r64 + w2i * r128 + w3i * r192;
        assert((w1i * r64) * pb + (w2i * r128) * pb + (w3i * r192) * pb == upper * pb) by {
            lemma_mul_is_distributive_add_other_way(pb, w1i * r64, w2i * r128 + w3i * r192);
            lemma_mul_is_distributive_add_other_way(pb, w2i * r128, w3i * r192);
        }
        lemma_mod_sum_factor(upper, partial as int, pb);
    } else if boundary <= 128 {
        // Strip words[2..3]
        let partial = words[0] as nat + words[1] as nat * pow2(64);
        lemma_pow2_adds((128 - boundary) as nat, boundary);
        lemma_pow2_adds((192 - boundary) as nat, boundary);
        let r128 = pow2((128 - boundary) as nat) as int;
        let r192 = pow2((192 - boundary) as nat) as int;
        let w2i = words[2] as nat as int;
        let w3i = words[3] as nat as int;
        assert(w2i * pow2(128) as int == (w2i * r128) * pb) by {
            lemma_mul_is_commutative(pb, r128);
            lemma_mul_is_associative(w2i, r128, pb);
        }
        assert(w3i * pow2(192) as int == (w3i * r192) * pb) by {
            lemma_mul_is_commutative(pb, r192);
            lemma_mul_is_associative(w3i, r192, pb);
        }
        let upper = w2i * r128 + w3i * r192;
        assert((w2i * r128) * pb + (w3i * r192) * pb == upper * pb) by {
            lemma_mul_is_distributive_add_other_way(pb, w2i * r128, w3i * r192);
        }
        lemma_mod_sum_factor(upper, partial as int, pb);
    } else if boundary <= 192 {
        // Strip words[3]
        let partial = words[0] as nat + words[1] as nat * pow2(64) + words[2] as nat * pow2(128);
        lemma_pow2_adds((192 - boundary) as nat, boundary);
        let r192 = pow2((192 - boundary) as nat) as int;
        let w3i = words[3] as nat as int;
        assert(w3i * pow2(192) as int == (w3i * r192) * pb) by {
            lemma_mul_is_commutative(pb, r192);
            lemma_mul_is_associative(w3i, r192, pb);
        }
        lemma_mod_sum_factor(w3i * r192, partial as int, pb);
    }
    // boundary > 192: nothing to strip; the ensures is trivially val % pb == val % pb

}

/// Proves the sum of the first `base_idx` words is strictly less than pow2(base_idx * 64).
/// This is the bound needed for `lemma_fundamental_div_mod_converse_div` when
/// extracting word `base_idx` from a partial sum by dividing by pow2(base_idx * 64).
proof fn lemma_u64x4_lower_words_bounded(words: [u64; 4], base_idx: usize)
    requires
        1 <= base_idx <= 3,
    ensures
        ({
            let lower: nat = if base_idx == 1 {
                words[0] as nat
            } else if base_idx == 2 {
                words[0] as nat + words[1] as nat * pow2(64)
            } else {
                words[0] as nat + words[1] as nat * pow2(64) + words[2] as nat * pow2(128)
            };
            lower < pow2((base_idx as nat) * 64)
        }),
{
    lemma_u64_lt_pow2_64(words[0]);
    if base_idx >= 2 {
        lemma_u64_lt_pow2_64(words[1]);
        lemma_pow2_adds(64, 64);
        let p64 = pow2(64) as int;
        let p128 = pow2(128) as int;
        assert(words[1] as nat as int * p64 <= (p64 - 1) * p64) by {
            lemma_mul_inequality(words[1] as nat as int, p64 - 1, p64);
        }
        assert((p64 - 1) * p64 == p128 - p64) by {
            lemma_mul_is_distributive_sub_other_way(p64, p64, 1);
            lemma_mul_basics(p64);
        }
    }
    if base_idx == 3 {
        lemma_u64_lt_pow2_64(words[2]);
        lemma_pow2_adds(128, 64);
        let p64 = pow2(64) as int;
        let p128 = pow2(128) as int;
        let p192 = pow2(192) as int;
        assert(words[2] as nat as int * p128 <= (p64 - 1) * p128) by {
            lemma_mul_inequality(words[2] as nat as int, p64 - 1, p128);
        }
        assert((p64 - 1) * p128 == p192 - p128) by {
            lemma_mul_is_distributive_sub_other_way(p128, p64, 1);
            lemma_mul_basics(p128);
            lemma_mul_is_commutative(p64, p128);
        }
    }
}

// =============================================================================
// Lemma: Split reconstruct_radix_2w at position k
// =============================================================================
/// Split a radix-2^w reconstruction at an arbitrary position k.
///
/// Proves: reconstruct_radix_2w(digits, w) ==
///     reconstruct_radix_2w(digits.take(k), w) + pow2(w * k) * reconstruct_radix_2w(digits.skip(k), w)
pub proof fn lemma_reconstruct_radix_2w_split(digits: Seq<i8>, k: nat, w: nat)
    requires
        k <= digits.len(),
        w > 0,
    ensures
        reconstruct_radix_2w(digits, w) == reconstruct_radix_2w(digits.take(k as int), w) + pow2(
            w * k,
        ) * reconstruct_radix_2w(digits.skip(k as int), w),
    decreases k,
{
    if k == 0 {
        assert(digits.take(0).len() == 0);
        assert(reconstruct_radix_2w(digits.take(0), w) == 0);
        assert(digits.skip(0) =~= digits);
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        lemma_mul_basics(reconstruct_radix_2w(digits, w));
    } else {
        assert(digits.len() > 0);

        let km1 = (k - 1) as nat;
        let tail = digits.skip(1);
        assert(km1 <= tail.len());

        // IH: tail splits at km1
        lemma_reconstruct_radix_2w_split(tail, km1, w);

        // Key sequence equalities
        assert(digits.take(k as int).skip(1) =~= tail.take(km1 as int));
        assert(digits.skip(k as int) =~= tail.skip(km1 as int));

        let prefix = digits.take(k as int);
        assert(prefix.len() == k);
        assert(prefix[0] == digits[0]);

        let r_prefix_tail = reconstruct_radix_2w(tail.take(km1 as int), w);
        let r_suffix = reconstruct_radix_2w(tail.skip(km1 as int), w);
        let pw = pow2(w) as int;

        // Subgoal 1: pow2(w * km1 + w) == pow2(w * k)
        assert(w * km1 + w == w * k) by {
            lemma_mul_is_distributive_add(w as int, km1 as int, 1);
        }
        assert(pow2(w) * pow2(w * km1) == pow2(w * k)) by {
            lemma_pow2_adds(w, w * km1);
        }

        // Subgoal 2: distribute pow2(w) over the IH sum
        assert(pw * (r_prefix_tail + (pow2(w * km1) as int) * r_suffix) == pw * r_prefix_tail + pw
            * ((pow2(w * km1) as int) * r_suffix)) by {
            lemma_mul_is_distributive_add(pw, r_prefix_tail, (pow2(w * km1) as int) * r_suffix);
        }

        // Subgoal 3: reassociate to get pow2(w*k) * r_suffix
        assert(pw * ((pow2(w * km1) as int) * r_suffix) == (pow2(w * k) as int) * r_suffix) by {
            lemma_mul_is_associative(pw, pow2(w * km1) as int, r_suffix);
        }
    }
}

// =============================================================================
// Bit-vector helper lemmas for as_radix_2w loop body
// =============================================================================
// These lemmas wrap `by(bit_vector)` proofs in standalone proof functions
// with explicitly typed parameters. This is necessary because mutable loop
// variables (like `carry`) get promoted to `int` in proof contexts inside
// Verus for-loops, which breaks bitwise shift operators (`>>`, `<<`) that
// are only defined on fixed-width types.
/// Proves that extracting w bits at position bit_offset from a u64x4 array
/// via shift-and-mask equals (u64_4_as_nat / pow2(bit_offset)) % pow2(w).
pub proof fn lemma_u64x4_bit_extraction(
    words: [u64; 4],
    bit_buf: u64,
    window_mask: u64,
    w: usize,
    bit_offset: usize,
    u64_idx: usize,
    bit_idx: usize,
)
    requires
        w >= 5 && w <= 8,
        bit_offset <= 255,
        u64_idx == bit_offset / 64,
        bit_idx == bit_offset % 64,
        window_mask == (1u64 << (w as u64)) - 1,
        (bit_idx < 64 - w || u64_idx == 3) ==> bit_buf == words[u64_idx as int] >> (bit_idx as u64),
        !(bit_idx < 64 - w || u64_idx == 3) ==> bit_buf == (words[u64_idx as int] >> (
        bit_idx as u64)) | (words[(1 + u64_idx) as int] << ((64 - bit_idx) as u64)),
    ensures
        (bit_buf & window_mask) as nat == (u64_4_as_nat(&words) / pow2(bit_offset as nat)) % pow2(
            w as nat,
        ),
{
    if bit_idx < 64 - w || u64_idx == 3 {
        // Single-word case: window fits entirely within one u64 word
        let val = u64_4_as_nat(&words);
        let bit_off_nat = bit_offset as nat;
        let w_nat = w as nat;
        let bit_idx_nat = bit_idx as nat;

        lemma_pow2_div_mod(val, bit_off_nat, w_nat);

        // bit_buf == words[u64_idx] / pow2(bit_idx)
        lemma_u64_shift_is_pow2(bit_idx_nat);
        lemma_u64_shr_is_div(words[u64_idx as int], bit_idx as u64);
        assert(bit_buf as nat == (words[u64_idx as int] as nat) / pow2(bit_idx_nat));

        // (bit_buf & window_mask) as nat == (bit_buf as nat) % pow2(w)
        lemma_u64_shift_is_pow2(w_nat);
        assert(low_bits_mask(w_nat) == pow2(w_nat) - 1) by {
            reveal(low_bits_mask);
        }
        lemma_u64_low_bits_masks_fit(w_nat);
        lemma_u64_low_bits_mask_is_mod(bit_buf, w_nat);

        lemma_u64x4_single_word_decompose_generic(words, u64_idx, bit_off_nat, w_nat, bit_idx_nat);
    } else {
        lemma_u64x4_cross_word_extraction(
            words,
            bit_buf,
            window_mask,
            w,
            bit_offset,
            u64_idx,
            bit_idx,
        );
    }
}

/// Generic single-word decomposition: unifies the four idx-specific lemmas.
///
/// The proof follows a common 3-step pattern for each idx:
///   1. **Strip**: remove upper words via `lemma_u64x4_mod_strip_above`
///   2. **Divide**: extract `words[u64_idx]` from the partial sum via
///      `lemma_u64x4_lower_words_bounded` + `lemma_fundamental_div_mod_converse_div`
///   3. **Chain**: connect with `lemma_pow2_div_mod` and `lemma_div_denominator`
proof fn lemma_u64x4_single_word_decompose_generic(
    words: [u64; 4],
    u64_idx: usize,
    bit_off_nat: nat,
    w_nat: nat,
    bit_idx_nat: nat,
)
    requires
        u64_idx == bit_off_nat / 64,
        bit_idx_nat == bit_off_nat % 64,
        bit_idx_nat + w_nat <= 64 || u64_idx == 3,
        w_nat >= 5 && w_nat <= 8,
        bit_off_nat <= 255,
    ensures
        (u64_4_as_nat(&words) % pow2(bit_off_nat + w_nat)) / pow2(bit_off_nat) == ((
        words[u64_idx as int] as nat) / pow2(bit_idx_nat)) % pow2(w_nat),
{
    let val = u64_4_as_nat(&words);
    let biw = bit_idx_nat + w_nat;
    let biw_total = bit_off_nat + w_nat;

    if u64_idx == 0 {
        // Strip words[1..3]; partial = words[0]
        lemma_u64x4_mod_strip_above(words, biw);
        lemma_pow2_div_mod(words[0] as nat, bit_idx_nat, w_nat);
    } else if u64_idx == 1 {
        // Strip words[2..3]; partial = words[0] + words[1]*p64
        let lower: nat = words[0] as nat + words[1] as nat * pow2(64);
        lemma_u64x4_mod_strip_above(words, biw_total);
        // Divide partial by p64 to extract words[1]
        lemma_u64x4_lower_words_bounded(words, 1);
        lemma_pow2_pos(64);
        lemma_fundamental_div_mod_converse_div(
            lower as int,
            pow2(64) as int,
            words[1] as nat as int,
            words[0] as nat as int,
        );
        // Chain: pow2(bit_off) = pow2(64) * pow2(bit_idx)
        lemma_pow2_pos(bit_idx_nat);
        lemma_pow2_adds(64, bit_idx_nat);
        lemma_pow2_pos(biw_total);
        lemma_mod_bound(lower as int, pow2(biw_total) as int);
        lemma_div_denominator(
            (lower % pow2(biw_total)) as int,
            pow2(64) as int,
            pow2(bit_idx_nat) as int,
        );
        lemma_pow2_div_mod(lower, 64, biw);
        lemma_pow2_div_mod(words[1] as nat, bit_idx_nat, w_nat);
    } else if u64_idx == 2 {
        // Strip words[3]; partial = words[0] + words[1]*p64 + words[2]*p128
        let lower: nat = words[0] as nat + words[1] as nat * pow2(64) + words[2] as nat * pow2(128);
        lemma_u64x4_mod_strip_above(words, biw_total);
        // Divide partial by p128 to extract words[2]
        lemma_u64x4_lower_words_bounded(words, 2);
        lemma_pow2_pos(128);
        lemma_fundamental_div_mod_converse_div(
            lower as int,
            pow2(128) as int,
            words[2] as nat as int,
            (words[0] as nat + words[1] as nat * pow2(64)) as int,
        );
        // Chain: pow2(bit_off) = pow2(128) * pow2(bit_idx)
        lemma_pow2_pos(bit_idx_nat);
        lemma_pow2_adds(128, bit_idx_nat);
        lemma_pow2_pos(biw_total);
        lemma_mod_bound(lower as int, pow2(biw_total) as int);
        lemma_div_denominator(
            (lower % pow2(biw_total)) as int,
            pow2(128) as int,
            pow2(bit_idx_nat) as int,
        );
        lemma_pow2_div_mod(lower, 128, biw);
        lemma_pow2_div_mod(words[2] as nat, bit_idx_nat, w_nat);
    } else {
        // idx=3: no stripping needed; divide val by p192 to extract words[3]
        lemma_u64x4_lower_words_bounded(words, 3);
        lemma_pow2_pos(192);
        lemma_fundamental_div_mod_converse_div(
            val as int,
            pow2(192) as int,
            words[3] as nat as int,
            (words[0] as nat + words[1] as nat * pow2(64) + words[2] as nat * pow2(128)) as int,
        );
        // Chain: pow2(bit_off) = pow2(192) * pow2(bit_idx)
        lemma_pow2_pos(bit_idx_nat);
        lemma_pow2_adds(192, bit_idx_nat);
        lemma_div_denominator(val as int, pow2(192) as int, pow2(bit_idx_nat) as int);
        lemma_pow2_div_mod(val, bit_off_nat, w_nat);
        lemma_pow2_div_mod(words[3] as nat, bit_idx_nat, w_nat);
    }
}

/// Helper: the low `w` bits of `(b << k)` equal `(b % pow2(w-k)) << k`.
/// Since w <= 8, all masks fit trivially in u64; the proof needs only a
/// single bit-vector step plus the mask-to-mod connection.
proof fn lemma_u64_shl_low_bits(b: u64, k: u64, w: u64)
    requires
        k > 0,
        k < 64,
        w > k,
        w <= 8,
    ensures
        ({
            let cross = (w - k) as nat;
            let mask = low_bits_mask(w as nat) as u64;
            let b_lo: u64 = (b as nat % pow2(cross)) as u64;
            (b << k) & mask == b_lo << k
        }),
{
    let cross: nat = (w - k) as nat;
    let cross_u: u64 = cross as u64;

    // With w <= 8, both masks fit in u64 trivially
    let w_mask: u64 = sub(1u64 << w, 1);
    let c_mask: u64 = sub(1u64 << cross_u, 1);

    // Connect c_mask to mod: b & c_mask == b_lo
    reveal(low_bits_mask);
    lemma_u64_shift_is_pow2(cross);
    lemma_pow2_pos(cross);
    lemma_u64_low_bits_mask_is_mod(b, cross);
    lemma_mod_bound(b as int, pow2(cross) as int);

    // Connect w_mask to low_bits_mask(w)
    lemma_u64_low_bits_masks_fit(w as nat);
    lemma_u64_shift_is_pow2(w as nat);
    assert(w_mask == low_bits_mask(w as nat) as u64) by {
        lemma_pow2_pos(w as nat);
        assert(1u64 << w == pow2(w as nat) as u64);
        assert(low_bits_mask(w as nat) == pow2(w as nat) - 1);
    };

    // Core bit-vector identity
    assert((b << k) & w_mask == (b & c_mask) << k) by (bit_vector)
        requires
            k > 0u64,
            k < 64u64,
            w > k,
            w <= 8u64,
            cross_u == (sub(w, k)) as u64,
            w_mask == (sub(1u64 << w, 1)) as u64,
            c_mask == (sub(1u64 << cross_u, 1)) as u64,
    ;
}

/// Helper: reduce the u64x4 window extraction to a two-word extraction.
/// Shows: (val % pow2(bit_off + w)) / pow2(bit_off) == (two_val / pow2(bit_idx)) % pow2(w)
/// where two_val = words[u64_idx] + words[u64_idx+1] * pow2(64).
///
/// The proof uses `lemma_u64x4_mod_strip_above` to remove irrelevant upper words,
/// then divides by pow2(base) to extract the two relevant words.
proof fn lemma_u64x4_cross_word_reduce_to_two(
    words: [u64; 4],
    bit_idx_nat: nat,
    w_nat: nat,
    u64_idx: usize,
)
    requires
        bit_idx_nat == ((u64_idx as nat) * 64 + bit_idx_nat) % 64,  // bit_idx < 64
        bit_idx_nat + w_nat > 64,
        u64_idx < 3,
        w_nat >= 5 && w_nat <= 8,
        (u64_idx as nat) * 64 + bit_idx_nat <= 255,
        bit_idx_nat < 64,
    ensures
        ({
            let val = u64_4_as_nat(&words);
            let two_val: nat = words[u64_idx as int] as nat + words[(1 + u64_idx) as int] as nat
                * pow2(64);
            let bit_off_nat = (u64_idx as nat) * 64 + bit_idx_nat;
            (val % pow2(bit_off_nat + w_nat)) / pow2(bit_off_nat) == (two_val / pow2(bit_idx_nat))
                % pow2(w_nat)
        }),
{
    let val = u64_4_as_nat(&words);
    let base: nat = (u64_idx as nat) * 64;
    let two_val: nat = words[u64_idx as int] as nat + words[(1 + u64_idx) as int] as nat * pow2(64);
    let bit_off_nat = base + bit_idx_nat;
    let biw_total = bit_off_nat + w_nat;

    lemma_pow2_div_mod(val, bit_off_nat, w_nat);
    lemma_pow2_pos(bit_idx_nat);

    if u64_idx == 0 {
        // Strip words[2..3]; partial = w0+w1*p64 = two_val.  biw_total in (64,72]
        lemma_u64x4_mod_strip_above(words, biw_total);
        // val % pow2(biw_total) == two_val % pow2(biw_total), and base = 0
        lemma_pow2_div_mod(two_val, bit_idx_nat, w_nat);
    } else if u64_idx == 1 {
        // Strip words[2..3] from (val / pow2(64)), i.e. from shifted_val.
        // First divide val by pow2(64): val = shifted_val * p64 + words[0]
        lemma_u64x4_lower_words_bounded(words, 1);
        lemma_pow2_pos(64);
        lemma_pow2_adds(64, 64);
        lemma_pow2_adds(128, 64);
        let shifted_val: nat = words[1] as nat + words[2] as nat * pow2(64) + words[3] as nat
            * pow2(128);
        assert(val as int == shifted_val as int * pow2(64) as int + words[0] as nat as int) by {
            let p64 = pow2(64) as int;
            let w1i = words[1] as nat as int;
            let w2i = words[2] as nat as int;
            let w3i = words[3] as nat as int;
            assert(w2i * pow2(128) as int == (w2i * p64) * p64) by {
                lemma_mul_is_associative(w2i, p64, p64);
            }
            assert(w3i * pow2(192) as int == (w3i * pow2(128) as int) * p64) by {
                lemma_mul_is_associative(w3i, pow2(128) as int, p64);
                lemma_mul_is_commutative(pow2(128) as int, p64);
            }
            lemma_mul_is_distributive_add_other_way(p64, w1i, w2i * p64 + w3i * pow2(128) as int);
            lemma_mul_is_distributive_add_other_way(p64, w2i * p64, w3i * pow2(128) as int);
        }
        lemma_fundamental_div_mod_converse_div(
            val as int,
            pow2(64) as int,
            shifted_val as int,
            words[0] as nat as int,
        );
        // Now strip words[3] from shifted_val: biw_total - 64 = bit_idx + w, in (0, 72]
        let biw_local = bit_idx_nat + w_nat;
        lemma_pow2_pos(biw_local);
        lemma_pow2_adds(biw_local, (128 - biw_local) as nat);
        let r128 = pow2((128 - biw_local) as nat) as int;
        let w3i = words[3] as nat as int;
        assert(w3i * pow2(128) as int == (w3i * r128) * pow2(biw_local) as int) by {
            lemma_mul_is_commutative(pow2(biw_local) as int, r128);
            lemma_mul_is_associative(w3i, r128, pow2(biw_local) as int);
        }
        lemma_mod_sum_factor(w3i * r128, two_val as int, pow2(biw_local) as int);
        // Chain via div_denominator
        lemma_pow2_adds(64, bit_idx_nat);
        lemma_div_denominator(val as int, pow2(64) as int, pow2(bit_idx_nat) as int);
        lemma_pow2_div_mod(two_val, bit_idx_nat, w_nat);
        lemma_pow2_div_mod(shifted_val, bit_idx_nat, w_nat);
    } else {
        // u64_idx == 2, base = 128: divide val by pow2(128) to get two_val
        lemma_u64x4_lower_words_bounded(words, 2);
        lemma_pow2_pos(128);
        lemma_pow2_adds(64, 128);
        // val = two_val * pow2(128) + (w0 + w1*p64)
        assert(val as int == two_val as int * pow2(128) as int + (words[0] as nat + words[1] as nat
            * pow2(64)) as int) by {
            let p128 = pow2(128) as int;
            let w2i = words[2] as nat as int;
            let w3i = words[3] as nat as int;
            assert(w3i * pow2(192) as int == (w3i * pow2(64) as int) * p128) by {
                lemma_mul_is_associative(w3i, pow2(64) as int, p128);
            }
            lemma_mul_is_distributive_add_other_way(p128, w2i, w3i * pow2(64) as int);
        }
        lemma_fundamental_div_mod_converse_div(
            val as int,
            pow2(128) as int,
            two_val as int,
            (words[0] as nat + words[1] as nat * pow2(64)) as int,
        );
        // two_val has no upper words to strip; trivial mod identity
        lemma_pow2_pos(bit_idx_nat + w_nat);
        lemma_mod_sum_factor(0, two_val as int, pow2(bit_idx_nat + w_nat) as int);
        // Chain via div_denominator
        lemma_pow2_adds(128, bit_idx_nat);
        lemma_div_denominator(val as int, pow2(128) as int, pow2(bit_idx_nat) as int);
        lemma_pow2_div_mod(two_val, bit_idx_nat, w_nat);
        lemma_pow2_div_mod(val / pow2(128), bit_idx_nat, w_nat);
    }
}

/// Helper: cross-word decomposition - bits [bit_offset, bit_offset+w) span two words.
proof fn lemma_u64x4_cross_word_decompose(
    words: [u64; 4],
    bit_off_nat: nat,
    w_nat: nat,
    bit_idx_nat: nat,
    u64_idx: usize,
    bit_buf: u64,
)
    requires
        u64_idx == bit_off_nat / 64,
        bit_idx_nat == bit_off_nat % 64,
        bit_idx_nat + w_nat > 64,
        u64_idx < 3,
        w_nat >= 5 && w_nat <= 8,
        bit_off_nat <= 255,
        bit_buf == (words[u64_idx as int] >> (bit_idx_nat as u64)) | (words[(1 + u64_idx) as int]
            << ((64 - bit_idx_nat) as u64)),
    ensures
        (u64_4_as_nat(&words) % pow2(bit_off_nat + w_nat)) / pow2(bit_off_nat) == (bit_buf as nat)
            % pow2(w_nat),
{
    let val = u64_4_as_nat(&words);
    let remain: nat = (64 - bit_idx_nat) as nat;  // bits from low word
    let cross: nat = (bit_idx_nat + w_nat - 64) as nat;  // bits from high word
    assert(remain + cross == w_nat);
    assert(remain > 0 && remain < w_nat);
    assert(cross > 0 && cross <= 8);

    let a = words[u64_idx as int];
    let b = words[(1 + u64_idx) as int];
    let base: nat = (u64_idx as nat) * 64;
    assert(bit_off_nat == base + bit_idx_nat);

    // === Step 1: Reduce val to two relevant words ===
    let two_val: nat = a as nat + b as nat * pow2(64);

    lemma_pow2_div_mod(val, bit_off_nat, w_nat);

    lemma_u64x4_cross_word_reduce_to_two(words, bit_idx_nat, w_nat, u64_idx);

    // === Step 2: Decompose two_val / pow2(bit_idx) ===
    let lo: nat = a as nat % pow2(bit_idx_nat);
    let hi: nat = a as nat / pow2(bit_idx_nat);
    lemma_pow2_pos(bit_idx_nat);
    lemma_fundamental_div_mod(a as int, pow2(bit_idx_nat) as int);

    lemma_u64_lt_pow2_64(a);
    lemma_pow2_adds(bit_idx_nat, remain);
    lemma_div_strictly_bounded(a as int, pow2(bit_idx_nat) as int, pow2(remain) as int);

    assert(two_val as int == lo as int + pow2(bit_idx_nat) as int * (hi as int + b as nat as int
        * pow2(remain) as int)) by {
        let pbi = pow2(bit_idx_nat) as int;
        let pr = pow2(remain) as int;
        let bi = b as nat as int;
        // b * pow2(64) == b * (pbi * pr); commute inner: b * (pr * pbi) == (b * pr) * pbi == pbi * (b * pr)
        assert(bi * pow2(64) as int == pbi * (bi * pr)) by {
            lemma_mul_is_commutative(pbi, pr);
            lemma_mul_is_associative(bi, pr, pbi);
            lemma_mul_is_commutative(bi * pr, pbi);
        }
        // pbi * hi + pbi * (b * pr) == pbi * (hi + b * pr)
        lemma_mul_is_distributive_add(pbi, hi as int, bi * pr);
    }

    let q: nat = (hi + b as nat * pow2(remain));
    assert(two_val as int == q as int * pow2(bit_idx_nat) as int + lo as int) by {
        lemma_mul_is_commutative(pow2(bit_idx_nat) as int, q as int);
    }
    lemma_fundamental_div_mod_converse_div(
        two_val as int,
        pow2(bit_idx_nat) as int,
        q as int,
        lo as int,
    );
    assert(two_val / pow2(bit_idx_nat) == q);

    // === Step 3: (q % pow2(w)) = hi + (b % pow2(cross)) * pow2(remain) ===
    lemma_pow2_adds(remain, cross);
    lemma_pow2_pos(cross);
    lemma_fundamental_div_mod(b as int, pow2(cross) as int);
    let b_lo: nat = b as nat % pow2(cross);
    let b_hi: nat = b as nat / pow2(cross);

    // b*pr == (pc*b_hi + b_lo)*pr == pc*b_hi*pr + b_lo*pr == pr*pc*b_hi + b_lo*pr == pw*b_hi + b_lo*pr
    assert(b as nat as int * pow2(remain) as int == pow2(w_nat) as int * b_hi as int + b_lo as int
        * pow2(remain) as int) by {
        let pr = pow2(remain) as int;
        let pc = pow2(cross) as int;
        let pw = pow2(w_nat) as int;
        // (pc*b_hi + b_lo) * pr == pc*b_hi*pr + b_lo*pr
        // (pc*b_hi + b_lo)*pr == (pc*b_hi)*pr + b_lo*pr by distributivity
        lemma_mul_is_distributive_add_other_way(pr, pc * b_hi as int, b_lo as int);
        // (pc*b_hi)*pr == pr*(pc*b_hi) == (pr*pc)*b_hi == pw*b_hi
        lemma_mul_is_commutative(pc * b_hi as int, pr);
        lemma_mul_is_associative(pr, pc, b_hi as int);
    }

    // Substitution: q == hi + b*pow2(remain) and b*pow2(remain) == pow2(w)*b_hi + b_lo*pow2(remain)
    assert(q as int == pow2(w_nat) as int * b_hi as int + (hi as int + b_lo as int * pow2(
        remain,
    ) as int));

    let window_val: nat = (hi + b_lo * pow2(remain));
    lemma_mod_bound(b as int, pow2(cross) as int);
    // b_lo * pow2(remain) <= (pow2(cross)-1) * pow2(remain) = pow2(w) - pow2(remain)
    assert(b_lo as int * pow2(remain) as int <= (pow2(cross) as int - 1) * pow2(remain) as int) by {
        lemma_mul_inequality(b_lo as int, pow2(cross) as int - 1, pow2(remain) as int);
    }
    assert((pow2(cross) as int - 1) * pow2(remain) as int == pow2(w_nat) as int - pow2(
        remain,
    ) as int) by {
        lemma_mul_is_distributive_sub_other_way(pow2(remain) as int, pow2(cross) as int, 1);
        lemma_mul_basics(pow2(remain) as int);
        lemma_mul_is_commutative(pow2(remain) as int, pow2(cross) as int);
    }

    lemma_pow2_pos(w_nat);
    assert(q as int == b_hi as int * pow2(w_nat) as int + window_val as int) by {
        lemma_mul_is_commutative(pow2(w_nat) as int, b_hi as int);
    }
    lemma_mod_sum_factor(b_hi as int, window_val as int, pow2(w_nat) as int);
    lemma_small_mod(window_val, pow2(w_nat));
    assert(q % pow2(w_nat) == window_val);

    // === Step 4: Show (bit_buf as nat) % pow2(w) == window_val ===
    lemma_u64_shr_is_div(a, bit_idx_nat as u64);
    assert((a >> (bit_idx_nat as u64)) as nat == hi);

    let shr_a: u64 = a >> (bit_idx_nat as u64);
    let shl_b: u64 = b << (remain as u64);
    assert(bit_buf == shr_a | shl_b);

    assert((shr_a | shl_b) as nat % pow2(w_nat) == shr_a as nat + (b as nat % pow2(cross)) * pow2(
        remain,
    )) by {
        lemma_u64_low_bits_masks_fit(w_nat);
        let mask = low_bits_mask(w_nat) as u64;
        let b_lo_u64: u64 = (b as nat % pow2(cross)) as u64;
        let remain_u64: u64 = remain as u64;

        lemma_u64_distribute_over_bit_or(shr_a, shl_b, w_nat as u64);

        if remain < w_nat {
            lemma_pow2_strictly_increases(remain, w_nat);
        }
        lemma_u64_low_bits_mask_is_mod(shr_a, w_nat);
        lemma_u64_pow2_le_max(w_nat);
        lemma_small_mod(shr_a as nat, pow2(w_nat));
        assert(shr_a & mask == shr_a);

        lemma_u64_shl_low_bits(b, remain_u64, w_nat as u64);

        lemma_mod_bound(b as int, pow2(cross) as int);
        if cross < 8 {
            lemma_pow2_strictly_increases(cross, 8);
        }
        assert(pow2(8) == 256) by {
            lemma_u64_shift_is_pow2(8);
            assert((1u64 << 8u64) == 256u64) by (bit_vector);
        };

        lemma_u64_shift_is_pow2(remain);
        assert(b_lo_u64 <= u64::MAX >> remain_u64) by (bit_vector)
            requires
                remain_u64 > 0u64,
                remain_u64 <= 7u64,
                b_lo_u64 <= 255u64,
        ;
        lemma_u64_bit_or_is_plus(shr_a, b_lo_u64, remain_u64);

        assert(shl_b & mask == b_lo_u64 << remain_u64);
        assert(shr_a & mask == shr_a);
        assert((shr_a | shl_b) & mask == shr_a + (b_lo_u64 << remain_u64));

        lemma_u64_low_bits_mask_is_mod(shr_a | shl_b, w_nat);
        lemma_u64_pow2_le_max(w_nat);
        lemma_u64_shl_is_mul(b_lo_u64, remain_u64);
        assert((shr_a + (b_lo_u64 << remain_u64)) as nat == shr_a as nat + (b_lo_u64
            << remain_u64) as nat);
        assert((shr_a | shl_b) as nat % pow2(w_nat) == shr_a as nat + b_lo * pow2(remain));
    };

    assert((bit_buf as nat) % pow2(w_nat) == window_val);
}

/// Sub-lemma: cross-word bit extraction from u64x4.
/// Handles both the boundary case (bit_idx + w == 64) and the true cross-word case.
proof fn lemma_u64x4_cross_word_extraction(
    words: [u64; 4],
    bit_buf: u64,
    window_mask: u64,
    w: usize,
    bit_offset: usize,
    u64_idx: usize,
    bit_idx: usize,
)
    requires
        w >= 5 && w <= 8,
        bit_offset <= 255,
        u64_idx == bit_offset / 64,
        bit_idx == bit_offset % 64,
        !(bit_idx < 64 - w || u64_idx == 3),
        window_mask == (1u64 << (w as u64)) - 1,
        bit_buf == (words[u64_idx as int] >> (bit_idx as u64)) | (words[(1 + u64_idx) as int] << ((
        64 - bit_idx) as u64)),
    ensures
        (bit_buf & window_mask) as nat == (u64_4_as_nat(&words) / pow2(bit_offset as nat)) % pow2(
            w as nat,
        ),
{
    let val = u64_4_as_nat(&words);
    let bit_off_nat = bit_offset as nat;
    let w_nat = w as nat;
    let bit_idx_nat = bit_idx as nat;

    if bit_idx_nat + w_nat == 64 {
        // Boundary case: window fits in a single word even though the exec code
        // used the cross-word formula (low | high). Masking removes the OR'd high bits.
        lemma_u64_shift_is_pow2(w_nat);
        assert(low_bits_mask(w_nat) == pow2(w_nat) - 1) by {
            reveal(low_bits_mask);
        }
        lemma_u64_low_bits_masks_fit(w_nat);
        lemma_u64_low_bits_mask_is_mod(bit_buf, w_nat);
        lemma_pow2_div_mod(val, bit_off_nat, w_nat);

        lemma_u64x4_single_word_decompose_generic(words, u64_idx, bit_off_nat, w_nat, bit_idx_nat);

        // word >> bit_idx < pow2(w) since bit_idx + w == 64, so mod is identity
        let low_w = words[u64_idx as int] >> (bit_idx as u64);
        lemma_u64_shr_is_div(words[u64_idx as int], bit_idx as u64);
        lemma_u64_lt_pow2_64(words[u64_idx as int]);
        lemma_pow2_adds(bit_idx_nat, w_nat);
        lemma_div_strictly_bounded(
            words[u64_idx as int] as int,
            pow2(bit_idx_nat) as int,
            pow2(w_nat) as int,
        );
        lemma_small_mod((words[u64_idx as int] >> (bit_idx as u64)) as nat, pow2(w_nat));

        // bit_vector: masking (low_w | (b << w)) gives low_w
        let w_u64: u64 = w as u64;
        let b = words[(1 + u64_idx) as int];
        assert(low_w < (1u64 << w_u64)) by {
            lemma_u64_shift_is_pow2(w_nat);
        };
        assert((64 - bit_idx) as u64 == w_u64);
        let mask_u64: u64 = ((1u64 << w_u64) - 1) as u64;
        assert((bit_buf & mask_u64) == low_w) by (bit_vector)
            requires
                bit_buf == low_w | (b << w_u64),
                mask_u64 == ((1u64 << w_u64) - 1) as u64,
                low_w < (1u64 << w_u64),
                w_u64 >= 5u64,
                w_u64 <= 8u64,
        ;
    } else {
        // True cross-word case: window spans two words
        lemma_u64_shift_is_pow2(w_nat);
        assert(low_bits_mask(w_nat) == pow2(w_nat) - 1) by {
            reveal(low_bits_mask);
        }
        lemma_u64_low_bits_masks_fit(w_nat);
        lemma_u64_low_bits_mask_is_mod(bit_buf, w_nat);
        lemma_pow2_div_mod(val, bit_off_nat, w_nat);
        lemma_u64x4_cross_word_decompose(words, bit_off_nat, w_nat, bit_idx_nat, u64_idx, bit_buf);
    }
}

/// Helper: establishes concrete digits_count values and product bounds for w in 5..=8.
///
/// Factored out because three lemmas (lemma_digits_count_radix_bounds,
/// lemma_last_iter_carry_zero, lemma_as_radix_2w_postconditions) all repeat
/// the same w-case-analysis to derive these facts.
proof fn lemma_w_digits_count_concrete(w: usize, digits_count: usize)
    requires
        5 <= w <= 8,
        digits_count as int == (256 + w as int - 1) / w as int,
    ensures
        w == 5 ==> digits_count == 52,
        w == 6 ==> digits_count == 43,
        w == 7 ==> digits_count == 37,
        w == 8 ==> digits_count == 32,
        digits_count > 0,
        digits_count <= 52,
        digits_count * w >= 256,
        digits_count * w <= 256 + w - 1,
{
    if w == 5 {
        assert((256 + 4) / 5 == 52);
        assert(52 * 5 >= 256);
        assert(52 * 5 <= 260);
    } else if w == 6 {
        assert((256 + 5) / 6 == 43);
        assert(43 * 6 >= 256);
        assert(43 * 6 <= 261);
    } else if w == 7 {
        assert((256 + 6) / 7 == 37);
        assert(37 * 7 >= 256);
        assert(37 * 7 <= 262);
    } else {
        assert(w == 8);
        assert((256 + 7) / 8 == 32);
        assert(32 * 8 >= 256);
        assert(32 * 8 <= 263);
    }
}

/// Helper lemma: proves the postconditions of as_radix_2w from the loop invariant state.
/// Isolated from the main function to avoid solver interference.
pub proof fn lemma_as_radix_2w_postconditions(
    digits: [i8; 64],
    w: usize,
    digits_count: usize,
    carry: u64,
    scalar_val: nat,
)
    requires
        w >= 5,
        w <= 8,
        carry <= 1,
        digits_count as int == (256 + w as int - 1) / w as int,
        // Core loop invariant at i == digits_count
        reconstruct_radix_2w(digits@.take(digits_count as int), w as nat) + (carry as int) * (pow2(
            (w * digits_count) as nat,
        ) as int) == (scalar_val as int) % (pow2((w * digits_count) as nat) as int),
        // Digit bounds from loop
        forall|j: int|
            0 <= j < digits_count ==> {
                let bound = pow2((w - 1) as nat) as int;
                -bound <= (#[trigger] digits[j]) && digits[j] < bound
            },
        // Scalar bound
        scalar_val < pow2(256),
        // w=8 case: digit at digits_count was set to carry
        w == 8 ==> digits[digits_count as int] as int == carry as int,
        // w<8 case: carry is 0 (no adjustment needed)
        w < 8 ==> carry == 0,
    ensures
        ({
            let final_digits_count = if w < 8 {
                (256 + (w as int) - 1) / (w as int)
            } else {
                (256 + (w as int) - 1) / (w as int) + 1
            };
            is_valid_radix_2w(&digits, w as nat, final_digits_count as nat) && reconstruct_radix_2w(
                digits@.take(final_digits_count),
                w as nat,
            ) == scalar_val as int
        }),
{
    // Concrete digits_count values and bounds for each w in {5,6,7,8}
    // Kept bare: results needed as side-effect context throughout the proof
    lemma_w_digits_count_concrete(w, digits_count);

    let final_digits_count: int = if w < 8 {
        digits_count as int
    } else {
        digits_count as int + 1  // w==8: extra digit for carry

    };

    // scalar_val % pow2(w*digits_count) == scalar_val (since w*digits_count >= 256)
    assert((scalar_val as int) % (pow2((w * digits_count) as nat) as int) == scalar_val as int) by {
        if w * digits_count > 256 {
            lemma_pow2_strictly_increases(256, (w * digits_count) as nat);
        }
        lemma_small_mod(scalar_val, pow2((w * digits_count) as nat));
    }

    // Reconstruction: extend loop invariant to include carry digit
    if w == 8 {
        // Split reconstruction at position 32
        assert(reconstruct_radix_2w(digits@.take(33), w as nat) == reconstruct_radix_2w(
            digits@.take(33).take(32),
            w as nat,
        ) + pow2((w * 32) as nat) * reconstruct_radix_2w(digits@.take(33).skip(32), w as nat)) by {
            lemma_reconstruct_radix_2w_split(digits@.take(33), 32, w as nat);
        }
        assert(digits@.take(33).take(32) =~= digits@.take(32));
        // Prove single-element tail reconstructs to its value
        let tail = digits@.take(33).skip(32);
        assert(reconstruct_radix_2w(tail, w as nat) == digits[32] as int) by {
            assert(tail.len() == 1 && tail[0] == digits[32]);
            assert(reconstruct_radix_2w(tail.skip(1), w as nat) == 0);
            lemma_mul_basics(pow2(w as nat) as int);
        }
        assert(pow2((w * 32) as nat) as int * (carry as int) == (carry as int) * (pow2(
            (w * 32) as nat,
        ) as int)) by {
            lemma_mul_is_commutative(pow2((w * 32) as nat) as int, carry as int);
        }
    }
    // Digit bounds for is_valid_radix_2w

    assert forall|j: int| 0 <= j < final_digits_count implies {
        let bound = pow2((w - 1) as nat) as int;
        -bound <= (#[trigger] digits[j]) && (#[trigger] digits[j]) < bound
    } by {
        let bound = pow2((w - 1) as nat) as int;
        if j >= digits_count as int {
            // w==8 carry digit: carry <= 1 < 128 = pow2(7)
            assert(digits[j] as int == carry as int);
            assert(bound == 128) by {
                assert(pow2(7) == 128) by {
                    lemma2_to64();
                }
            }
        }
    }
}

// =============================================================================
// Setup and bounds lemmas for as_radix_2w
// =============================================================================
/// Proves digits_count * w >= 256, digits_count * w <= 256 + w - 1, radix == pow2(w)
/// for w in 5..=8 when digits_count == (256 + w - 1) / w.
pub proof fn lemma_digits_count_radix_bounds(w: usize, digits_count: usize)
    requires
        5 <= w <= 8,
        digits_count as int == (256 + w as int - 1) / w as int,
    ensures
        digits_count <= 52,
        digits_count > 0,
        digits_count * w >= 256,
        digits_count * w <= 256 + w - 1,
        (1u64 << (w as u64)) <= 256u64,
        (1u64 << (w as u64)) as nat == pow2(w as nat),
{
    // Concrete bounds for digits_count given w in {5,6,7,8}
    lemma_w_digits_count_concrete(w, digits_count);
    let radix: u64 = 1u64 << (w as u64);
    assert(radix <= 256u64) by (bit_vector)
        requires
            radix == 1u64 << (w as u64),
            5u64 <= (w as u64),
            (w as u64) <= 8u64,
    ;
    // radix as nat == pow2(w as nat): bridge from bit-shift to pow2
    assert(radix as nat == pow2(w as nat)) by {
        lemma2_to64();
        lemma_u64_shift_is_pow2(w as nat);
    }
}

/// Helper lemma: at the last iteration of the radix-2^w extraction loop (w < 8),
/// the carry is 0 because there are too few remaining bits to produce a carry.
pub proof fn lemma_last_iter_carry_zero(
    scalar_val: nat,
    old_carry: u64,
    extracted: u64,
    w: usize,
    i: usize,
)
    requires
        w >= 5 && w < 8,
        (i + 1) as int == (256 + w as int - 1) / w as int,
        scalar_val < pow2(256),
        old_carry <= 1,
        extracted as nat == (scalar_val / pow2((w * i) as nat)) % pow2(w as nat),
    ensures
        old_carry + extracted < (1u64 << (w as u64)) / 2,
{
    let digits_count: usize = (i + 1) as usize;

    assert(pow2(w as nat) as int == (1u64 << (w as u64)) as int) by {
        lemma2_to64();
        lemma_u64_shift_is_pow2(w as nat);
    }

    // Step 1: Establish remaining_bits and prove remaining_bits <= w - 2 by case analysis
    let wi: nat = (w * i) as nat;
    let remaining_bits: nat = (256 - w * i) as nat;

    // Establish concrete digits_count, then derive concrete remaining_bits
    lemma_w_digits_count_concrete(w, digits_count);
    // The solver needs concrete product w*i to compute remaining_bits.
    // After the helper, digits_count is concrete, and i == digits_count - 1.
    if w == 5 {
        assert(remaining_bits == 1nat);
    } else if w == 6 {
        assert(remaining_bits == 4nat);
    } else {
        assert(remaining_bits == 4nat);
    }

    // Step 2: scalar_val / pow2(wi) < pow2(remaining_bits)
    let quotient: nat = scalar_val / pow2(wi);
    assert(quotient < pow2(remaining_bits)) by {
        assert(pow2(256) == pow2(remaining_bits) * pow2(wi)) by {
            lemma_pow2_adds(remaining_bits, wi);
        }
        assert(pow2(256) == pow2(wi) * pow2(remaining_bits)) by {
            lemma_mul_is_commutative(pow2(remaining_bits) as int, pow2(wi) as int);
        }
        assert(pow2(wi) >= 1) by {
            lemma_pow2_pos(wi);
        }
        lemma_div_strictly_bounded(scalar_val as int, pow2(wi) as int, pow2(remaining_bits) as int);
    }

    // Step 3: Since remaining_bits <= w - 2 < w, quotient % pow2(w) == quotient
    let extracted_nat: nat = extracted as nat;
    assert(extracted_nat == quotient) by {
        if remaining_bits < w as nat {
            lemma_pow2_strictly_increases(remaining_bits, w as nat);
        }
        assert(quotient < pow2(w as nat));
        lemma_small_mod(quotient as nat, pow2(w as nat) as nat);
    }

    // Step 4: coef = old_carry + extracted <= 1 + pow2(remaining_bits) - 1 = pow2(remaining_bits)
    // Since pow2(remaining_bits) < pow2(w) and old_carry <= 1, no overflow

    // Step 5: remaining_bits <= w-2 implies old_carry + extracted < pow2(w-1) == half_radix
    assert(pow2(remaining_bits) <= pow2((w - 2) as nat)) by {
        if remaining_bits < (w - 2) as nat {
            lemma_pow2_strictly_increases(remaining_bits, (w - 2) as nat);
        }
    }

    assert(pow2((w - 1) as nat) == 2 * pow2((w - 2) as nat)) by {
        lemma_pow2_adds(1, (w - 2) as nat);
        lemma2_to64();
    }

    // old_carry + extracted <= 1 + (pow2(remaining_bits) - 1) <= pow2(w-2) < 2*pow2(w-2) = pow2(w-1)
    // and (1u64 << w) / 2 == pow2(w-1)
    assert(((1u64 << (w as u64)) / 2) as nat == pow2((w - 1) as nat)) by {
        assert(pow2(w as nat) == pow2((w - 1) as nat) * 2) by {
            lemma_pow2_adds((w - 1) as nat, 1);
            lemma2_to64();
        }
        assert(pow2(w as nat) / 2 == pow2((w - 1) as nat));
    }
}

// =============================================================================
// Digit bounds via recentering
// =============================================================================
/// Proves that the recentered digit value is within [-pow2(w-1), pow2(w-1)).
///
/// Given digit_val = coef - new_carry * pow2(w), and new_carry in {0,1}:
/// - If new_carry == 0: coef < half_radix, so digit_val == coef in [0, bound)
/// - If new_carry == 1: coef >= half_radix, so digit_val == coef - radix in [-bound, 0]
pub proof fn lemma_radix_2w_digit_bounds(coef: u64, w: usize, new_carry: u64)
    requires
        coef <= (1u64 << (w as u64)),
        5 <= w <= 8,
        new_carry <= 1,
        new_carry == ((coef + (1u64 << (w as u64)) / 2) as u64) >> (w as u64),
    ensures
        ({
            let digit_val = coef as int - new_carry as int * pow2(w as nat) as int;
            &&& -pow2((w - 1) as nat) as int <= digit_val
            &&& digit_val < pow2((w - 1) as nat) as int
        }),
{
    let radix: u64 = 1u64 << (w as u64);
    let half_radix: u64 = radix / 2;
    let digit_val: int = coef as int - new_carry as int * pow2(w as nat) as int;

    let bound = pow2((w - 1) as nat) as int;
    let pw = pow2(w as nat) as int;

    assert(radix as nat == pow2(w as nat)) by {
        lemma2_to64();
        lemma_u64_shift_is_pow2(w as nat);
    }
    assert(pw == radix as int);

    // half_radix == pow2(w-1)
    assert(pow2((w - 1) as nat) == radix as nat / 2) by {
        lemma_pow2_adds((w - 1) as nat, 1);
        assert(pow2(1) == 2) by {
            lemma2_to64();
        }
    }
    assert(bound == half_radix as int);

    // Carry determines coef vs half_radix
    assert(new_carry <= 1u64 && (new_carry == 0u64 ==> coef < half_radix) && (new_carry == 1u64
        ==> coef >= half_radix)) by (bit_vector)
        requires
            5u64 <= (w as u64) && (w as u64) <= 8u64,
            radix == 1u64 << (w as u64),
            half_radix == radix / 2u64,
            coef <= radix,
            new_carry == ((coef + half_radix) as u64) >> (w as u64),
    ;

    if new_carry == 0 {
        assert(new_carry as int * pw == 0) by {
            lemma_mul_basics(pw);
        }
        assert(digit_val == coef as int);
        assert((coef as int) < half_radix as int);
    } else {
        assert(new_carry == 1);
        assert(new_carry as int * pw == pw) by {
            lemma_mul_basics(pw);
        }
        assert(digit_val == coef as int - pw);
        assert(pw == radix as int);
        assert(coef as int >= half_radix as int);
        assert(coef as int <= radix as int);
        assert(radix == 2 * half_radix) by (bit_vector)
            requires
                half_radix == radix / 2u64,
                radix == 1u64 << (w as u64),
                5u64 <= (w as u64) && (w as u64) <= 8u64,
        ;
        assert(digit_val <= 0);
        assert(bound >= 1) by {
            lemma_pow2_pos((w - 1) as nat);
        }
    }
}

/// Proves the reconstruction invariant step for the as_radix_2w loop.
///
/// Given the old invariant:
///   reconstruct(digits_old, w) + old_carry * pow2(w*i) == scalar_val % pow2(w*i)
///
/// And the key relationships from the loop iteration, proves the new invariant:
///   reconstruct(digits_new, w) + carry * pow2(w*(i+1)) == scalar_val % pow2(w*(i+1))
///
/// where digits_new extends digits_old by one digit at position i.
pub proof fn lemma_radix_2w_loop_reconstruction_step(
    digits_new: Seq<i8>,
    i: usize,
    w: usize,
    scalar_val: nat,
    old_carry: u64,
    new_carry: u64,
    extracted: nat,
)
    requires
        5 <= w <= 8,
        i < 64,
        digits_new.len() == (i + 1) as int,
        // Old loop invariant
        reconstruct_radix_2w(digits_new.take(i as int), w as nat) + (old_carry as int) * pow2(
            (w * i) as nat,
        ) as int == (scalar_val as int) % pow2((w * i) as nat) as int,
        // Key relationships from the loop iteration
        digits_new[i as int] as int == (old_carry as int + extracted as int) - new_carry as int
            * pow2(w as nat) as int,
        extracted == (scalar_val / pow2((w * i) as nat)) % pow2(w as nat),
        new_carry <= 1,
    ensures
        reconstruct_radix_2w(digits_new, w as nat) + (new_carry as int) * pow2(
            (w * (i + 1)) as nat,
        ) as int == (scalar_val as int) % pow2((w * (i + 1)) as nat) as int,
{
    let digit_val = digits_new[i as int] as int;
    let coef_int = old_carry as int + extracted as int;
    let digits_old = digits_new.take(i as int);

    let pw = pow2(w as nat) as int;
    let pwi = pow2((w * i) as nat) as int;
    let pwi1 = pow2((w * (i + 1)) as nat) as int;

    // Step 1: Split reconstruction at position i
    assert(reconstruct_radix_2w(digits_new, w as nat) == reconstruct_radix_2w(
        digits_new.take(i as int),
        w as nat,
    ) + pow2(w as nat * i as nat) * reconstruct_radix_2w(digits_new.skip(i as int), w as nat)) by {
        lemma_reconstruct_radix_2w_split(digits_new, i as nat, w as nat);
    }

    // tail has exactly one element: digits_new[i]
    let tail = digits_new.skip(i as int);
    assert(reconstruct_radix_2w(tail, w as nat) == digit_val) by {
        assert(reconstruct_radix_2w(tail.skip(1), w as nat) == 0);
        lemma_mul_basics(pw);
    }

    let recon_old = reconstruct_radix_2w(digits_old, w as nat);

    // Step 2: Establish pwi1 = pw * pwi
    assert(pw * pwi == pwi1) by {
        assert(w + w * i == w * (i + 1)) by {
            lemma_mul_is_distributive_add(w as int, i as int, 1);
        }
        lemma_pow2_adds(w as nat, (w * i) as nat);
    }

    // Step 3: digit_val * pwi + nc * pwi1 = coef_int * pwi
    let nc = new_carry as int;
    let nc_pw = nc * pw;

    assert(digit_val == coef_int - nc_pw);
    assert(digit_val * pwi + nc * pwi1 == coef_int * pwi) by {
        lemma_mul_is_distributive_sub_other_way(pwi, coef_int, nc_pw);
        lemma_mul_is_associative(nc, pw, pwi);
    }

    // Step 4: mod_breakdown: S % (pwi*pw) == pwi * ((S/pwi) % pw) + S % pwi
    assert(scalar_val as int % (pwi * pw) == pwi * ((scalar_val as int / pwi) % pw)
        + scalar_val as int % pwi) by {
        assert(pwi > 0) by {
            lemma_pow2_pos((w * i) as nat);
        }
        assert(pw > 0) by {
            lemma_pow2_pos(w as nat);
        }
        lemma_mod_breakdown(scalar_val as int, pwi, pw);
    }
    assert(scalar_val as int / pwi == (scalar_val / pow2((w * i) as nat)) as int);
    assert(pwi * (extracted as int) == extracted as int * pwi) by {
        lemma_mul_is_commutative(pwi, extracted as int);
    }

    // Step 5: Combine everything
    assert((old_carry as int + extracted as int) * pwi == old_carry as int * pwi + extracted as int
        * pwi) by {
        lemma_mul_is_distributive_add_other_way(pwi, old_carry as int, extracted as int);
    }
    assert(recon_old + old_carry as int * pwi + extracted as int * pwi == scalar_val as int % pwi
        + extracted as int * pwi);

    // Step 6: Close the chain
    let recon_new = reconstruct_radix_2w(digits_new, w as nat);

    assert(digit_val * pwi == pwi * digit_val) by {
        lemma_mul_is_commutative(digit_val, pwi);
    }
    assert(recon_new + nc * pwi1 == scalar_val as int % pwi + extracted as int * pwi);

    assert(scalar_val as int % (pwi * pw) == scalar_val as int % pwi + extracted as int * pwi);
    assert(pwi * pw == pwi1) by {
        lemma_mul_is_commutative(pwi, pw);
    }
    assert(scalar_val as int % pwi1 == scalar_val as int % pwi + extracted as int * pwi);

}

} // verus!
