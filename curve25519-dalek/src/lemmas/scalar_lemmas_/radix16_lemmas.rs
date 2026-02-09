//! Lemmas for proving correctness of `as_radix_16` in scalar.rs.
//!
//! Key lemmas:
//! - `lemma_reconstruct_radix_2w_split`: Split reconstruction at arbitrary position k
//! - `lemma_carry_preserves_reconstruction`: Carry operation preserves radix-16 sum
//! - `lemma_bytes32_to_radix16_nibbles`: Nibble extraction reconstructs the scalar value
#![allow(unused_imports)]

use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;

verus! {

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
// Lemma: Carry operation preserves reconstruction
// =============================================================================
/// The carry operation at position i preserves the radix-2^w reconstruction.
pub proof fn lemma_carry_preserves_reconstruction(
    old_digits: Seq<i8>,
    new_digits: Seq<i8>,
    i: nat,
    carry: int,
    w: nat,
)
    requires
        w > 0,
        old_digits.len() == new_digits.len(),
        i + 1 < old_digits.len(),
        new_digits[i as int] == old_digits[i as int] - carry * (pow2(w) as int),
        new_digits[(i + 1) as int] == old_digits[(i + 1) as int] + carry,
        forall|j: int|
            0 <= j < old_digits.len() && j != i && j != i + 1 ==> old_digits[j] == new_digits[j],
    ensures
        reconstruct_radix_2w(new_digits, w) == reconstruct_radix_2w(old_digits, w),
{
    // Split both at position i
    lemma_reconstruct_radix_2w_split(old_digits, i, w);
    lemma_reconstruct_radix_2w_split(new_digits, i, w);

    // Prefixes are identical
    assert(old_digits.take(i as int) =~= new_digits.take(i as int));

    let old_suffix = old_digits.skip(i as int);
    let new_suffix = new_digits.skip(i as int);
    assert(old_suffix.len() >= 2);

    // Split suffixes to isolate positions i and i+1
    lemma_reconstruct_radix_2w_split(old_suffix, 1, w);
    lemma_reconstruct_radix_2w_split(new_suffix, 1, w);

    // Reconstruct of single-element prefix == digit value
    assert(reconstruct_radix_2w(old_suffix.take(1), w) == old_digits[i as int] as int) by {
        assert(old_suffix.take(1)[0] == old_digits[i as int]);
        assert(old_suffix.take(1).skip(1).len() == 0);
    }
    assert(reconstruct_radix_2w(new_suffix.take(1), w) == new_digits[i as int] as int) by {
        assert(new_suffix.take(1)[0] == new_digits[i as int]);
        assert(new_suffix.take(1).skip(1).len() == 0);
    }

    let old_rest = old_suffix.skip(1);
    let new_rest = new_suffix.skip(1);

    // Split rest to isolate position i+1
    lemma_reconstruct_radix_2w_split(old_rest, 1, w);
    lemma_reconstruct_radix_2w_split(new_rest, 1, w);

    assert(reconstruct_radix_2w(old_rest.take(1), w) == old_digits[(i + 1) as int] as int) by {
        assert(old_rest.take(1)[0] == old_digits[(i + 1) as int]);
        assert(old_rest.take(1).skip(1).len() == 0);
    }
    assert(reconstruct_radix_2w(new_rest.take(1), w) == new_digits[(i + 1) as int] as int) by {
        assert(new_rest.take(1)[0] == new_digits[(i + 1) as int]);
        assert(new_rest.take(1).skip(1).len() == 0);
    }

    // Tail after position i+1 is identical
    assert(old_rest.skip(1) =~= new_rest.skip(1));

    // Core algebraic identity: carry preserves d[i] + pw * d[i+1]
    let old_di = old_digits[i as int] as int;
    let old_di1 = old_digits[(i + 1) as int] as int;
    let new_di = new_digits[i as int] as int;
    let new_di1 = new_digits[(i + 1) as int] as int;
    let pw = pow2(w) as int;
    let tail_recon = reconstruct_radix_2w(old_rest.skip(1), w);

    assert(new_di + pw * new_di1 == old_di + pw * old_di1) by {
        lemma_mul_is_distributive_add(pw, old_di1, carry);
        lemma_mul_is_commutative(carry, pw);
    }

    assert(new_di + pw * (new_di1 + pw * tail_recon) == old_di + pw * (old_di1 + pw * tail_recon))
        by {
        lemma_mul_is_distributive_add(pw, new_di1, pw * tail_recon);
        lemma_mul_is_distributive_add(pw, old_di1, pw * tail_recon);
    }

    assert(w * 1 == w) by {
        lemma_mul_basics(w as int);
    }
}

// =============================================================================
// Lemma: Bytes to nibbles reconstruction
// =============================================================================
/// After extracting nibbles from each byte, reconstruct_radix_16 of the
/// nibble array equals bytes32_to_nat of the original bytes.
///
/// Uses the algebraic identity: output[2*i] + 16 * output[2*i+1] == bytes[i]
/// which holds because bot_half gives byte % 16 and top_half gives byte / 16.
pub proof fn lemma_bytes32_to_radix16_nibbles(output: [i8; 64], bytes: [u8; 32])
    requires
        forall|i: int|
            #![trigger output[2 * i], output[2 * i + 1]]
            0 <= i < 32 ==> output[2 * i] as int + 16 * (output[2 * i + 1] as int)
                == bytes[i] as int,
        forall|i: int| 0 <= i < 64 ==> output[i] >= 0,
    ensures
        reconstruct_radix_16(output@) == bytes32_to_nat(&bytes) as int,
{
    let out_seq = output@;
    let byte_seq = bytes@;

    // Bridge array indexing to Seq indexing for quantifier triggers
    assert forall|i: int|
        #![trigger out_seq[2 * i], out_seq[2 * i + 1]]
        0 <= i < 32 implies out_seq[2 * i] as int + 16 * (out_seq[2 * i + 1] as int)
        == byte_seq[i] as int by {
        assert(out_seq[2 * i] == output[2 * i]);
        assert(out_seq[2 * i + 1] == output[2 * i + 1]);
        assert(byte_seq[i] == bytes[i]);
    }
    assert forall|i: int| 0 <= i < 64 implies out_seq[i] >= 0 by {
        assert(out_seq[i] == output[i]);
    }

    // Subgoal 1: nibbles reconstruct to bytes_to_nat_prefix
    lemma_nibbles_equal_bytes_prefix(out_seq, byte_seq, 32);
    assert(out_seq.take(64) =~= out_seq);

    // Subgoal 2: bytes_to_nat_prefix(bytes@, 32) == bytes32_to_nat(&bytes)
    lemma_decomposition_prefix_rec(&bytes, 32);
    lemma_bytes32_to_nat_equals_rec(&bytes);
}

/// Helper: reconstruct_radix_2w of first 2*k nibbles equals bytes_to_nat_prefix of first k bytes
proof fn lemma_nibbles_equal_bytes_prefix(output: Seq<i8>, bytes: Seq<u8>, k: nat)
    requires
        output.len() == 64,
        bytes.len() == 32,
        k <= 32,
        forall|i: int|
            #![trigger output[2 * i], output[2 * i + 1]]
            0 <= i < 32 ==> output[2 * i] as int + 16 * (output[2 * i + 1] as int)
                == bytes[i] as int,
        forall|i: int| 0 <= i < 64 ==> output[i] >= 0,
    ensures
        reconstruct_radix_2w(output.take((2 * k) as int), 4) == bytes_to_nat_prefix(
            bytes,
            k,
        ) as int,
    decreases k,
{
    if k == 0 {
        assert(output.take(0).len() == 0);
        assert(reconstruct_radix_2w(output.take(0), 4) == 0);
    } else {
        let km1 = (k - 1) as nat;

        // IH: first 2*km1 nibbles reconstruct to first km1 bytes
        lemma_nibbles_equal_bytes_prefix(output, bytes, km1);

        let prefix = output.take((2 * k) as int);
        assert(prefix.len() == 2 * k);

        // Split prefix at position 2*km1: known part + last two nibbles
        lemma_reconstruct_radix_2w_split(prefix, 2 * km1, 4);
        assert(prefix.take((2 * km1) as int) =~= output.take((2 * km1) as int));

        // The last two elements are the nibbles for byte km1
        let tail = prefix.skip((2 * km1) as int);
        assert(tail.len() == 2);
        assert(tail[0] == output[(2 * km1) as int]);
        assert(tail[1] == output[(2 * km1 + 1) as int]);

        // Unroll reconstruction of the 2-element tail
        let tail_skip1 = tail.skip(1);
        let tail_skip2 = tail_skip1.skip(1);
        assert(tail_skip1.len() == 1);
        assert(tail_skip1[0] == tail[1]);
        assert(tail_skip2.len() == 0);
        assert(reconstruct_radix_2w(tail_skip2, 4) == 0);
        assert(reconstruct_radix_2w(tail_skip1, 4) == (tail[1] as int) + pow2(4) * 0);
        assert(reconstruct_radix_2w(tail_skip1, 4) == tail[1] as int) by {
            lemma_mul_basics(pow2(4) as int);
        }
        assert(reconstruct_radix_2w(tail, 4) == (tail[0] as int) + pow2(4) * (tail[1] as int));

        // pow2(4) == 16, so tail reconstructs to the nibble identity
        assert(pow2(4) == 16) by {
            lemma2_to64();
        }
        assert(output[(2 * km1) as int] as int + 16 * (output[(2 * km1 + 1) as int] as int)
            == bytes[km1 as int] as int);
        assert(reconstruct_radix_2w(tail, 4) == bytes[km1 as int] as int);

        // pow2(4 * 2*km1) == pow2(8*km1)
        assert(4 * (2 * km1) == 8 * km1) by {
            lemma_mul_is_associative(4, 2, km1 as int);
        }
    }
}

// =============================================================================
// Lemma: Valid radix-16 implies bounded digits
// =============================================================================
/// Lemma: is_valid_radix_16 implies radix_16_all_bounded
///
/// is_valid_radix_16 gives tighter bounds (-8 <= d < 8 for non-last, -8 <= d <= 8 for last)
/// but radix_16_all_bounded (-8 <= d <= 8 for all) is still implied.
pub proof fn lemma_valid_radix_16_implies_all_bounded(digits: [i8; 64])
    requires
        is_valid_radix_16(&digits),
    ensures
        radix_16_all_bounded(&digits),
{
    // Expand the definitions:
    //
    // - is_valid_radix_16(digits) = is_valid_radix_2w(digits, 4, 64)
    // - is_valid_radix_2w gives, for each i in [0, 64):
    //     -8 <= digits[i] and (digits[i] < 8) for i < 63, while (digits[63] <= 8)
    // This implies the simpler predicate radix_16_all_bounded(digits):
    //     forall i in [0, 64): -8 <= digits[i] <= 8
    // `is_valid_radix_16(digits)` is `is_valid_radix_2w(digits, 4, 64)`.
    assert(is_valid_radix_2w(&digits, 4, 64));

    // Prove the pointwise bound `-8 <= digits[i] <= 8` for all i in [0, 64).
    assert forall|i: int| 0 <= i < 64 implies radix_16_digit_bounded(#[trigger] digits[i]) by {
        // From `is_valid_radix_2w(digits, 4, 64)` we get:
        // - for i < 63: -8 <= digits[i] < 8
        // - for i = 63: -8 <= digits[i] <= 8
        //
        // because bound = pow2(w-1) = pow2(3) = 8.
        assert(pow2(3) == 8) by {
            vstd::arithmetic::power2::lemma2_to64();
        }
        if i < 63 {
            assert(-8 <= digits[i] && digits[i] < 8);
            // Strengthen `< 8` to `<= 8`.
            assert(digits[i] <= 8);
        } else {
            assert(i == 63);
            assert(-8 <= digits[i] && digits[i] <= 8);
        }
    }

    assert(radix_16_all_bounded(&digits));
}

} // verus!
