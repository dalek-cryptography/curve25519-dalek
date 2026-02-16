//! Lemmas for proving correctness of `non_adjacent_form` in scalar.rs.
//!
//! Key lemmas:
//! - `lemma_reconstruct_split`: Split base-2 reconstruction at arbitrary position k
//! - `lemma_reconstruct_zero_extend`: Trailing zeros don't change reconstruction
//! - `lemma_naf_even_step`: Invariant preservation for even window (pos += 1)
//! - `lemma_naf_odd_step`: Invariant preservation for odd window (pos += w)
//! - `lemma_naf_digit_bounds`: NAF digit bounds from recentering
//! - `lemma_naf_terminal_carry`: carry = 0 at loop exit when scalar_val < 2^255
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

// Reuse shared u64x4 helpers from radix_2w_lemmas
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::radix_2w_lemmas::*;

verus! {

// =============================================================================
// Reconstruction lemmas for base-2 (NAF) representation
// =============================================================================
/// Split a base-2 reconstruction at an arbitrary position k.
///
/// Proves: reconstruct(naf) ==
///     reconstruct(naf.take(k)) + pow2(k) * reconstruct(naf.skip(k))
proof fn lemma_reconstruct_split(naf: Seq<i8>, k: nat)
    requires
        k <= naf.len(),
    ensures
        reconstruct(naf) == reconstruct(naf.take(k as int)) + pow2(k) * reconstruct(
            naf.skip(k as int),
        ),
    decreases k,
{
    if k == 0 {
        assert(naf.take(0).len() == 0);
        assert(reconstruct(naf.take(0)) == 0);
        assert(naf.skip(0) =~= naf);
        assert(pow2(0) * reconstruct(naf) == reconstruct(naf)) by {
            assert(pow2(0) == 1) by {
                lemma2_to64();
            };
            lemma_mul_basics(reconstruct(naf));
        };
    } else {
        assert(naf.len() > 0);
        let km1 = (k - 1) as nat;
        let tail = naf.skip(1);
        assert(km1 <= tail.len());

        // IH: tail splits at km1
        lemma_reconstruct_split(tail, km1);

        // Key sequence equalities
        assert(naf.take(k as int).skip(1) =~= tail.take(km1 as int));
        assert(naf.skip(k as int) =~= tail.skip(km1 as int));

        let prefix = naf.take(k as int);
        assert(prefix.len() == k);
        assert(prefix[0] == naf[0]);

        let r_prefix_tail = reconstruct(tail.take(km1 as int));
        let r_suffix = reconstruct(tail.skip(km1 as int));

        // Subgoal 1: pow2(km1 + 1) == pow2(k)
        assert(pow2(km1) * pow2(1) == pow2(k)) by {
            lemma_pow2_adds(km1, 1);
            assert(km1 + 1 == k);
        }
        assert(pow2(1) == 2) by {
            lemma2_to64();
        }

        // Subgoal 2: distribute 2 over the IH sum
        let p2 = 2 as int;
        assert(p2 * (r_prefix_tail + (pow2(km1) as int) * r_suffix) == p2 * r_prefix_tail + p2 * ((
        pow2(km1) as int) * r_suffix)) by {
            lemma_mul_is_distributive_add(p2, r_prefix_tail, (pow2(km1) as int) * r_suffix);
        }

        // Subgoal 3: reassociate to get pow2(k) * r_suffix
        assert(p2 * ((pow2(km1) as int) * r_suffix) == (pow2(k) as int) * r_suffix) by {
            lemma_mul_is_associative(p2, pow2(km1) as int, r_suffix);
        }

        // Reconstruct(prefix) unfolds to prefix[0] + 2 * reconstruct(prefix.skip(1))
        // = naf[0] + 2 * r_prefix_tail
        // Reconstruct(naf) = naf[0] + 2 * reconstruct(tail)
        // = naf[0] + 2 * (r_prefix_tail + pow2(km1) * r_suffix)   [by IH]
        // = naf[0] + 2 * r_prefix_tail + 2 * pow2(km1) * r_suffix
        // = reconstruct(prefix) + pow2(k) * r_suffix
    }
}

/// Trailing zeros don't change the reconstruction value.
///
/// If all entries in naf from position k to n-1 are zero,
/// then reconstruct(naf.take(n)) == reconstruct(naf.take(k)).
proof fn lemma_reconstruct_zero_extend(naf: Seq<i8>, k: nat, n: nat)
    requires
        k <= n,
        n <= naf.len(),
        forall|j: int| k <= j < n ==> naf[j] == 0i8,
    ensures
        reconstruct(naf.take(n as int)) == reconstruct(naf.take(k as int)),
    decreases (n - k),
{
    if k == n {
        // trivial
    } else {
        // Show reconstruct(naf.take(n)) == reconstruct(naf.take(n-1))
        // by splitting at n-1 and showing the tail has one zero element.
        let nm1 = (n - 1) as nat;
        let suffix = naf.take(n as int).skip(nm1 as int);

        assert(reconstruct(suffix) == 0) by {
            assert(suffix.len() == 1);
            assert(suffix[0] == naf[nm1 as int]);
            assert(naf[nm1 as int] == 0i8);
            assert(suffix.skip(1).len() == 0);
            assert(reconstruct(suffix.skip(1)) == 0);
        };

        // reconstruct(naf.take(n)) == reconstruct(naf.take(nm1)) + pow2(nm1) * 0
        //                           == reconstruct(naf.take(nm1))
        assert(reconstruct(naf.take(n as int)) == reconstruct(naf.take(nm1 as int))) by {
            lemma_reconstruct_split(naf.take(n as int), nm1);
            assert(naf.take(n as int).take(nm1 as int) =~= naf.take(nm1 as int));
            assert(pow2(nm1) * reconstruct(suffix) == 0) by {
                lemma_mul_basics(pow2(nm1) as int);
            };
        };

        // Recurse for k..nm1
        lemma_reconstruct_zero_extend(naf, k, nm1);
    }
}

// The NAF-specific bit-extraction wrappers have been removed. The call site
// in non_adjacent_form now calls lemma_u64x4_bit_extraction directly
// (from radix_2w_lemmas, generalized to w >= 2).
// =============================================================================
// Even step: invariant preservation when window is even (pos += 1)
// =============================================================================
/// Proves the invariant holds at pos+1 when the window is even.
///
/// When window = carry + extracted is even and naf[pos] = 0:
///   reconstruct(naf.take(pos+1)) + carry * pow2(pos+1) == scalar_val % pow2(pos+1)
///
/// Key insight: window even means carry == bit_at(pos), so the parity argument works.
pub proof fn lemma_naf_even_step(
    naf: Seq<i8>,
    pos: nat,
    carry: nat,
    scalar_val: nat,
    w: nat,
    extracted: nat,
)
    requires
        pos < 256,
        naf.len() == 256,
        carry <= 1,
        w >= 2,
        // Old invariant
        reconstruct(naf.take(pos as int)) + (carry as int) * pow2(pos) as int == (scalar_val as int)
            % pow2(pos) as int,
        // naf[pos] is zero
        naf[pos as int] == 0i8,
        // extracted is the w-bit window at pos
        extracted == (scalar_val / pow2(pos)) % pow2(w),
        // Window is even
        (carry + extracted) % 2 == 0,
    ensures
        reconstruct(naf.take((pos + 1) as int)) + (carry as int) * pow2((pos + 1) as nat) as int
            == (scalar_val as int) % pow2((pos + 1) as nat) as int,
{
    let p_pos = pow2(pos) as int;
    let c = carry as int;
    let sv_mod_pos = (scalar_val as int) % pow2(pos) as int;
    let bit_at_pos: nat = (scalar_val / pow2(pos)) % 2;

    // Step 1: reconstruct(naf.take(pos+1)) == reconstruct(naf.take(pos)) since naf[pos] == 0
    assert(reconstruct(naf.take((pos + 1) as int)) == reconstruct(naf.take(pos as int))) by {
        lemma_reconstruct_zero_extend(naf, pos, (pos + 1) as nat);
    };

    // Step 2: extracted % 2 == bit_at_pos (mod-of-mod)
    assert(extracted % 2 == bit_at_pos) by {
        let sv_shifted = (scalar_val / pow2(pos)) as int;
        assert(pow2(w) == 2 * pow2((w - 1) as nat)) by {
            assert(pow2(1) == 2) by {
                lemma2_to64();
            };
            lemma_pow2_adds(1, (w - 1) as nat);
        };
        lemma_pow2_pos((w - 1) as nat);
        lemma_mod_mod(sv_shifted, 2, pow2((w - 1) as nat) as int);
    };

    // Step 3: carry == bit_at_pos (parity argument)
    assert(carry == bit_at_pos) by {
        if carry != bit_at_pos {
            assert((carry + extracted) % 2 != 0);
        }
    };

    // Step 4: scalar_val % pow2(pos+1) == carry * pow2(pos) + scalar_val % pow2(pos)
    assert((scalar_val as int) % pow2((pos + 1) as nat) as int == c * p_pos + sv_mod_pos) by {
        lemma_pow2_pos(pos);
        assert(pow2(pos) * 2 == pow2(pos + 1)) by {
            assert(pow2(1) == 2) by {
                lemma2_to64();
            };
            lemma_pow2_adds(pos, 1);
        };
        lemma_mod_breakdown(scalar_val as int, pow2(pos) as int, 2);
        lemma_mul_is_commutative(p_pos, bit_at_pos as int);
    };

    // Step 5: Combine — recon(pos+1) + c*pow2(pos+1)
    //       = recon(pos) + c*2*pow2(pos)
    //       = (sv_mod_pos - c*p_pos) + 2*c*p_pos
    //       = sv_mod_pos + c*p_pos = sv % pow2(pos+1)
    assert(pow2((pos + 1) as nat) == 2 * pow2(pos)) by {
        assert(pow2(1) == 2) by {
            lemma2_to64();
        };
        lemma_pow2_adds(1, pos);
        lemma_mul_is_commutative(pow2(1) as int, pow2(pos) as int);
    };
    assert(c * pow2((pos + 1) as nat) as int == c * 2 * p_pos) by {
        lemma_mul_is_associative(c, 2, p_pos);
    };
}

// =============================================================================
// Odd step: invariant preservation when window is odd (pos += w)
// =============================================================================
/// Proves the invariant holds at pos+w when the window is odd (digit emitted).
///
/// After emitting a digit and advancing by w:
///   reconstruct(naf.take(pos+w)) + new_carry * pow2(pos+w) == scalar_val % pow2(pos+w)
pub proof fn lemma_naf_odd_step(
    naf: Seq<i8>,
    pos: nat,
    w: nat,
    scalar_val: nat,
    old_carry: nat,
    new_carry: nat,
    extracted: nat,
)
    requires
        2 <= w <= 8,
        pos < 256,
        pos + w <= 256 + w,  // pos + w can be up to ~264
        naf.len() == 256,
        old_carry <= 1,
        new_carry <= 1,
        // Old invariant
        reconstruct(naf.take(pos as int)) + (old_carry as int) * pow2(pos) as int == (
        scalar_val as int) % pow2(pos) as int,
        // Digit relationship: naf[pos] = window - new_carry * 2^w
        naf[pos as int] as int == (old_carry as int + extracted as int) - new_carry as int * pow2(
            w,
        ) as int,
        // Intermediate positions are zero
        forall|j: int| pos < j < pos + w && j < 256 ==> naf[j] == 0i8,
        // extracted is the w-bit window value
        extracted == (scalar_val / pow2(pos)) % pow2(w),
        extracted < pow2(w),
    ensures
        ({
            let end_pos = if pos + w <= 256 {
                (pos + w) as nat
            } else {
                256nat
            };
            reconstruct(naf.take(end_pos as int)) + (new_carry as int) * pow2(
                (pos + w) as nat,
            ) as int == (scalar_val as int) % pow2((pos + w) as nat) as int
        }),
{
    let pw = pow2(w) as int;
    let p_pos = pow2(pos) as int;
    let nc = new_carry as int;
    let digit_val = naf[pos as int] as int;
    let coef_int = old_carry as int + extracted as int;
    let recon_old = reconstruct(naf.take(pos as int));

    let end_pos: nat = if pos + w <= 256 {
        (pos + w) as nat
    } else {
        256nat
    };
    let suffix = naf.take(end_pos as int).skip(pos as int);
    let suffix_len: nat = (end_pos - pos) as nat;

    // Step 1: reconstruct(suffix) == naf[pos] (digit is first element, rest are zero)
    assert(reconstruct(suffix) == digit_val) by {
        assert(suffix[0] == naf[pos as int]);
        // suffix[1..] are all zeros (vacuously true if suffix_len == 1)
        assert(forall|j: int| 1 <= j < suffix.len() ==> suffix[j] == 0i8) by {
            assert forall|j: int| 1 <= j < suffix.len() implies suffix[j] == 0i8 by {
                let idx = pos + j;
                assert(suffix[j] == naf[idx as int]);
            }
        };
        // Zero-extend collapses suffix to its first element
        lemma_reconstruct_zero_extend(suffix, 1, suffix_len);
        assert(suffix.take(suffix_len as int) =~= suffix);
        assert(reconstruct(suffix.take(1)) == digit_val) by {
            let s1 = suffix.take(1);
            assert(s1.skip(1).len() == 0);
            assert(reconstruct(s1.skip(1)) == 0);
        };
    };

    // Step 2: reconstruct(naf.take(end_pos)) == recon_old + p_pos * digit_val
    assert(reconstruct(naf.take(end_pos as int)) == recon_old + p_pos * digit_val) by {
        lemma_reconstruct_split(naf.take(end_pos as int), pos);
        assert(naf.take(end_pos as int).take(pos as int) =~= naf.take(pos as int));
        lemma_mul_is_commutative(p_pos, reconstruct(suffix));
    };

    // Step 3: digit_val * p_pos + nc * pow2(pos+w) == coef_int * p_pos
    assert(pow2((pos + w) as nat) as int == pw * p_pos) by {
        lemma_pow2_adds(w, pos);
        lemma_mul_is_commutative(pw, p_pos);
    };
    assert(digit_val * p_pos + nc * pow2((pos + w) as nat) as int == coef_int * p_pos) by {
        assert(digit_val == coef_int - nc * pw);
        lemma_mul_is_distributive_sub_other_way(p_pos, coef_int, nc * pw);
        lemma_mul_is_associative(nc, pw, p_pos);
    };

    // Step 4: mod_breakdown: sv % pow2(pos+w) == p_pos * extracted + sv % pow2(pos)
    assert((scalar_val as int) % pow2((pos + w) as nat) as int == extracted as int * p_pos + (
    scalar_val as int) % p_pos) by {
        lemma_pow2_pos(pos);
        lemma_pow2_pos(w);
        lemma_mod_breakdown(scalar_val as int, p_pos, pw);
        lemma_mul_is_commutative(p_pos, extracted as int);
    };

    // Step 5: Combine
    // recon_old + p_pos*digit_val + nc*pow2(pos+w)
    //   = recon_old + coef_int * p_pos                      [by step 3]
    //   = (sv%p_pos - old_carry*p_pos) + (old_carry + extracted)*p_pos  [by IH]
    //   = sv%p_pos + extracted*p_pos                          [algebra]
    //   = sv % pow2(pos+w)                                    [by step 4]
    assert(coef_int * p_pos == old_carry as int * p_pos + extracted as int * p_pos) by {
        lemma_mul_is_distributive_add_other_way(p_pos, old_carry as int, extracted as int);
    };
    assert(digit_val * p_pos == p_pos * digit_val) by {
        lemma_mul_is_commutative(digit_val, p_pos);
    };
}

// =============================================================================
// Digit bounds for NAF recentering (w >= 2)
// =============================================================================
/// Proves that the NAF digit after recentering is in (-pow2(w-1), pow2(w-1)).
///
/// The digit is also odd (since window is odd and width is even).
///
/// Given: window = carry + extracted, window is odd, window in [1, 2^w]
/// - If window < width/2: digit = window (positive, odd)
/// - If window >= width/2: digit = window - width (negative, odd)
pub proof fn lemma_naf_digit_bounds(window: u64, w: usize, width: u64)
    requires
        2 <= w <= 8,
        width == 1u64 << (w as u64),
        window >= 1,
        window <= width,
        window % 2 == 1,  // window is odd

    ensures
// Positive case bounds

        window < width / 2 ==> window as int >= 1,
        window < width / 2 ==> (window as int) < pow2((w - 1) as nat) as int,
        // Negative case bounds
        window >= width / 2 ==> (window as int - width as int) > -pow2((w - 1) as nat) as int,
        window >= width / 2 ==> (window as int - width as int) < 0,
        // Digit is always odd and nonzero
        window < width / 2 ==> window as int % 2 != 0,
        window >= width / 2 ==> (window as int - width as int) % 2 != 0,
{
    let half: u64 = width / 2;
    let bound = pow2((w - 1) as nat) as int;

    assert(width as nat == pow2(w as nat)) by {
        lemma2_to64();
        lemma_u64_shift_is_pow2(w as nat);
    };

    assert(bound == half as int) by {
        assert(pow2((w - 1) as nat) == width as nat / 2) by {
            lemma_pow2_adds((w - 1) as nat, 1);
            assert(pow2(1) == 2) by {
                lemma2_to64();
            };
        };
    };

    let window_int = window as int;
    let half_int = half as int;
    let width_int = width as int;

    if window < half {
        // digit = window, which is in [1, half) = [1, 2^(w-1))
    } else {
        // digit = window - width
        // width is even (bit_vector), so window (odd) != width, and window > half (also even)
        assert(width % 2 == 0) by (bit_vector)
            requires
                width == 1u64 << (w as u64),
                2u64 <= (w as u64) && (w as u64) <= 8u64,
        ;
        assert(window > half) by {
            assert(half % 2 == 0) by (bit_vector)
                requires
                    half == width / 2u64,
                    width == 1u64 << (w as u64),
                    2u64 <= (w as u64) && (w as u64) <= 8u64,
            ;
        };

        // window > half and width = 2*half, so window - width > -half = -bound
        assert(window_int - width_int > -half_int && window_int - width_int < 0) by {
            assert(width_int == 2 * half_int) by {
                assert(width == 2 * half) by (bit_vector)
                    requires
                        half == width / 2u64,
                        width == 1u64 << (w as u64),
                        2u64 <= (w as u64) && (w as u64) <= 8u64,
                ;
            };
        };

        // digit is odd: window odd - width even = odd
        assert((window_int - width_int) % 2 != 0) by {
            lemma_fundamental_div_mod(window_int, 2);
            lemma_fundamental_div_mod(width_int, 2);
            let q_w = window_int / 2;
            let q_d = width_int / 2;
            let diff = window_int - width_int;
            assert(diff == 2 * (q_w - q_d) + 1) by {
                lemma_mul_is_distributive_sub(2int, q_w, q_d);
            };
            lemma_fundamental_div_mod_converse(diff, 2, q_w - q_d, 1);
        };
    }
}

// =============================================================================
// Terminal carry: carry = 0 at loop exit
// =============================================================================
/// Proves that carry = 0 when the loop exits, given scalar_val < pow2(255).
///
/// When pos >= 255 and scalar_val < pow2(255), all remaining bits are 0.
/// If carry = 1, window = 1 (odd, < half), so it gets emitted and carry → 0.
/// Therefore carry = 0 at loop exit (pos >= 256).
/// Proves that when scalar_val < pow2(255) and pos >= 255,
/// the extracted bits are 0, so carry gets consumed.
pub proof fn lemma_naf_high_bits_zero(scalar_val: nat, pos: nat)
    requires
        scalar_val < pow2(255),
        pos >= 255,
    ensures
        scalar_val / pow2(pos) == 0,
{
    // scalar_val < pow2(255) <= pow2(pos), so division yields 0
    assert(scalar_val < pow2(pos)) by {
        if pos > 255 {
            lemma_pow2_strictly_increases(255, pos);
        }
    };
    assert(scalar_val / pow2(pos) == 0) by {
        lemma_pow2_pos(pos);
        lemma_fundamental_div_mod_converse(
            scalar_val as int,
            pow2(pos) as int,
            0int,
            scalar_val as int,
        );
    };
}

// =============================================================================
// Overflow helpers
// =============================================================================
/// Proves that window = carry + (bit_buf & window_mask) fits in u64 without overflow.
pub proof fn lemma_naf_window_no_overflow(carry: u64, bit_buf: u64, window_mask: u64, w: usize)
    requires
        carry <= 1,
        w >= 2 && w <= 8,
        window_mask == (1u64 << (w as u64)) - 1,
    ensures
        (bit_buf & window_mask) <= window_mask,
        carry + (bit_buf & window_mask) <= (1u64 << (w as u64)),
        carry + (bit_buf & window_mask) < u64::MAX,
{
    assert((bit_buf & window_mask) <= window_mask) by (bit_vector)
        requires
            window_mask == (1u64 << (w as u64)) - 1,
            2u64 <= (w as u64) && (w as u64) <= 8u64,
    ;
    assert(carry + (bit_buf & window_mask) <= (1u64 << (w as u64))) by {
        assert(1u64 + window_mask == (1u64 << (w as u64))) by (bit_vector)
            requires
                window_mask == (1u64 << (w as u64)) - 1,
                2u64 <= (w as u64) && (w as u64) <= 8u64,
        ;
    };
    assert(carry + (bit_buf & window_mask) < u64::MAX) by {
        assert((1u64 << (w as u64)) <= 256u64) by (bit_vector)
            requires
                2u64 <= (w as u64) && (w as u64) <= 8u64,
        ;
    };
}

/// Proves that the wrapping_sub used for negative digits gives the correct i8 value.
pub proof fn lemma_naf_wrapping_sub_correct(window: u64, width: u64, w: usize)
    requires
        2 <= w <= 8,
        width == 1u64 << (w as u64),
        window >= width / 2,
        window <= width,
        window % 2 == 1,
    ensures
        ({
            let result = (window as i8).wrapping_sub(width as i8);
            result as int == window as int - width as int
        }),
{
    assert(width <= 256u64 && width >= 4u64) by (bit_vector)
        requires
            width == 1u64 << (w as u64),
            2u64 <= (w as u64) && (w as u64) <= 8u64,
    ;
    assert(window <= 255u64);  // odd and <= even width

    // Use u8 intermediaries to avoid mixing u64 and i8 in bit_vector blocks
    let w_u8: u8 = #[verifier::truncate]
    (window as u8);
    let d_u8: u8 = #[verifier::truncate]
    (width as u8);
    assert((window as i8) == (w_u8 as i8)) by (bit_vector)
        requires
            w_u8 == window as u8,
    ;
    assert((width as i8) == (d_u8 as i8)) by (bit_vector)
        requires
            d_u8 == width as u8,
    ;

    if w <= 7 {
        assert(width <= 128u64) by (bit_vector)
            requires
                width == 1u64 << (w as u64),
                2u64 <= (w as u64) && (w as u64) <= 7u64,
        ;
        assert(window <= 127u64);  // odd and <= even width <= 128
        assert((w_u8 as i8).wrapping_sub(d_u8 as i8) as int == w_u8 as int - d_u8 as int)
            by (bit_vector)
            requires
                w_u8 <= 127u8,
                d_u8 <= 128u8,
                d_u8 >= 4u8,
                w_u8 >= d_u8 / 2u8,
        ;
        assert(w_u8 as int == window as int) by (bit_vector)
            requires
                w_u8 == window as u8,
                window <= 255u64,
        ;
        assert(d_u8 as int == width as int) by (bit_vector)
            requires
                d_u8 == width as u8,
                width <= 255u64,
        ;
    } else {
        // w == 8: width = 256, width as u8 = 0, window in [128, 255]
        assert(width == 256u64) by (bit_vector)
            requires
                width == 1u64 << (w as u64),
                (w as u64) == 8u64,
        ;
        assert((w_u8 as i8).wrapping_sub(d_u8 as i8) as int == w_u8 as int - 256) by {
            assert(d_u8 == 0u8) by (bit_vector)
                requires
                    d_u8 == width as u8,
                    width == 256u64,
            ;
            assert((w_u8 as i8).wrapping_sub(0i8) == (w_u8 as i8)) by (bit_vector);
            assert((w_u8 as i8) as int == w_u8 as int - 256) by (bit_vector)
                requires
                    w_u8 >= 128u8,
            ;
        };
        assert(w_u8 as int == window as int) by (bit_vector)
            requires
                w_u8 == window as u8,
                window <= 255u64,
        ;
    }
}

/// Proves properties about the `width` and `window_mask` computation.
pub proof fn lemma_naf_width_properties(w: usize)
    requires
        2 <= w <= 8,
    ensures
        (1u64 << (w as u64)) as nat == pow2(w as nat),
        (1u64 << (w as u64)) >= 4,
        (1u64 << (w as u64)) <= 256,
{
    assert(1u64 << (w as u64) >= 4u64 && 1u64 << (w as u64) <= 256u64) by (bit_vector)
        requires
            2u64 <= (w as u64) && (w as u64) <= 8u64,
    ;
    assert((1u64 << (w as u64)) as nat == pow2(w as nat)) by {
        lemma2_to64();
        lemma_u64_shift_is_pow2(w as nat);
    };
}

} // verus!
