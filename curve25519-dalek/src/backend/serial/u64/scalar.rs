//! Arithmetic mod \\(2\^{252} + 27742317777372353535851937790883648493\\)
//! with five \\(52\\)-bit unsigned limbs.
//!
//! \\(51\\)-bit limbs would cover the desired bit range (\\(253\\)
//! bits), but isn't large enough to reduce a \\(512\\)-bit number with
//! Montgomery multiplication, so \\(52\\) bits is used instead.  To see
//! that this is safe for intermediate results, note that the largest
//! limb in a \\(5\times 5\\) product of \\(52\\)-bit limbs will be
//!
//! ```text
//! (0xfffffffffffff^2) * 5 = 0x4ffffffffffff60000000000005 (107 bits).
//! ```
use super::field::load8_at;
#[allow(unused_imports)]
use super::subtle_assumes::select;
use core::fmt::Debug;
use core::ops::{Index, IndexMut};
#[allow(unused_imports)]
use subtle::Choice;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

#[allow(unused_imports)]
use crate::constants;

#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::bit_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::mul_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::shift_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::load8_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::montgomery_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_byte_lemmas::bytes_to_scalar_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_byte_lemmas::scalar_to_bytes_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::montgomery_reduce_lemmas::*; // TODO: see https://github.com/Beneficial-AI-Foundation/dalek-lite/issues/386
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::montgomery_reduce_part1_chain_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::montgomery_reduce_part2_chain_lemmas::*;
#[allow(unused_imports)]
use crate::specs::montgomery_reduce_specs::*;
use crate::specs::scalar52_specs::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::lemmas::common_lemmas::to_nat_lemmas::lemma_u8_32_as_nat_equals_suffix_64;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_extra::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::scalar_montgomery_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::bytes_as_nat_prefix;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::bytes_as_nat_suffix;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::bytes_seq_as_nat;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::spec_load8_at;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::u8_32_as_nat;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::word64_from_bytes;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::words64_from_bytes_to_nat;

verus! {

/// The `Scalar52` struct represents an element in
/// \\(\mathbb Z / \ell \mathbb Z\\) as 5 \\(52\\)-bit limbs.
#[derive(Copy, Clone)]
pub struct Scalar52 {
    pub limbs: [u64; 5],
}

} // verus!
impl Debug for Scalar52 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Scalar52: {:?}", self.limbs)
    }
}

verus! {

#[cfg(feature = "zeroize")]
impl Zeroize for Scalar52 {
    /* <VERIFICATION NOTE>
    Using wrapper function for Verus compatibility instead of direct call to zeroize
    </VERIFICATION NOTE> */
    fn zeroize(&mut self)
        ensures
            forall|i: int| 0 <= i < 5 ==> self.limbs[i] == 0,
    {
        /* ORIGINAL CODE: self.limbs.zeroize(); */
        crate::core_assumes::zeroize_limbs5(&mut self.limbs);
    }
}

impl Index<usize> for Scalar52 {
    type Output = u64;

    fn index(&self, _index: usize) -> (result: &u64)
        requires
            _index < 5,
        ensures
            result == &(self.limbs[_index as int]),
    {
        &(self.limbs[_index])
    }
}

} // verus!
// VERIFICATION EXCLUDED: mutable returns unsupported by Verus
impl IndexMut<usize> for Scalar52 {
    fn index_mut(&mut self, _index: usize) -> &mut u64 {
        &mut (self.limbs[_index])
    }
}

verus! {

/// u64 * u64 = u128 multiply helper
#[inline(always)]
fn m(x: u64, y: u64) -> (z: u128)
    ensures
        (z as nat) == (x as nat) * (y as nat),
{
    proof {
        lemma_mul_le(x as nat, u64::MAX as nat, y as nat, u64::MAX as nat);
    }
    (x as u128) * (y as u128)
}

impl Scalar52 {
    /// The scalar \\( 0 \\).
    pub const ZERO: Scalar52 = Scalar52 { limbs: [0, 0, 0, 0, 0] };

    /// Unpack a 32 byte / 256 bit scalar into 5 52-bit limbs.
    #[rustfmt::skip]  // keep alignment of s[*] calculations
    pub fn from_bytes(bytes: &[u8; 32]) -> (s: Scalar52)
        ensures
            u8_32_as_nat(bytes) == scalar52_to_nat(&s),
            limbs_bounded(&s),
            limb_prod_bounded_u128(s.limbs, s.limbs, 5),
    {
        let mut words = [0u64;4];
        for i in 0..4
            invariant
                0 <= i <= 4,
                forall|i2: int| i <= i2 < 4 ==> words[i2] == 0,
                forall|i2: int|
                    0 <= i2 < i ==> (words[i2] == bytes_as_nat_prefix(
                        Seq::new(8, |j: int| bytes[i2 * 8 + j]),
                        8,
                    )),
        {
            proof {
                assert(words[i as int] == 0);
                lemma_pow2_pos(0)
            }

            for j in 0..8
                invariant
                    0 <= j <= 8 && 0 <= i < 4,
                    words[i as int] < pow2(j as nat * 8),
                    forall|i2: int| i + 1 <= i2 < 4 ==> words[i2] == 0,
                    words[i as int] == bytes_as_nat_prefix(
                        Seq::new(8, |j2: int| bytes[i as int * 8 + j2]),
                        j as nat,
                    ),
                    forall|i2: int|
                        0 <= i2 < i ==> ((words[i2] as nat) == bytes_as_nat_prefix(
                            Seq::new(8, |j: int| bytes[i2 * 8 + j]),
                            8,
                        )),
            {
                proof {
                    lemma_byte_to_word_step(*bytes, words, i, j);
                }
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
            }
        }

        proof {
            lemma_bytes_to_word_equivalence(bytes, words);
            assert(1u64 << 52 > 0) by (bit_vector);
            assert(1u64 << 48 > 0) by (bit_vector);
        }

        let mask = (1u64 << 52) - 1;
        let top_mask = (1u64 << 48) - 1;
        let mut s = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        //test workflow graphs
        s.limbs[0] = words[0] & mask;
        s.limbs[1] = ((words[0] >> 52) | (words[1] << 12)) & mask;
        s.limbs[2] = ((words[1] >> 40) | (words[2] << 24)) & mask;
        s.limbs[3] = ((words[2] >> 28) | (words[3] << 36)) & mask;
        s.limbs[4] = (words[3] >> 16) & top_mask;

        proof {
            lemma_words_to_scalar(words, s, mask, top_mask);
            assert(u8_32_as_nat(bytes) == scalar52_to_nat(&s));
            lemma_limbs_bounded_implies_prod_bounded(&s, &s);
        }

        s
    }

    /// Reduce a 64 byte / 512 bit scalar mod l
    #[rustfmt::skip]  // keep alignment of lo[*] and hi[*] calculations
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> (s: Scalar52)
        ensures
    // VERIFICATION NOTE: Result is canonical

            is_canonical_scalar52(&s),
            scalar52_to_nat(&s) == bytes_seq_as_nat(bytes@) % group_order(),
    {
        let ghost wide_input = bytes_seq_as_nat(bytes@);

        proof {
            // Bridge bytes_seq_as_nat with the suffix sum for loop invariant
            lemma_u8_32_as_nat_equals_suffix_64(bytes);
        }

        // Stage 1 assumption: the byte-to-word packing yields the expected little-endian value.
        let mut words = [0u64;8];
        for i in 0..8
            invariant
                forall|k: int|
                    #![auto]
                    0 <= k < i ==> words@[k] as nat == word64_from_bytes(bytes@, k),
                words64_from_bytes_to_nat(bytes@, i as int) + bytes_as_nat_suffix(
                    bytes,
                    (i as int) * 8,
                ) == bytes_seq_as_nat(bytes@),
                forall|k: int| i <= k < 8 ==> words@[k] == 0,
        {
            let offset = i * 8;
            let _offset_end = offset + 7usize;
            proof {
                // offset + 7 = i*8 + 7 <= 7*8 + 7 = 63 < 64 = bytes.len()
                assert(_offset_end < 64);
            }
            let chunk = load8_at(bytes, offset);
            words[i] = chunk;

            proof {
                let i_int = i as int;
                // spec_load8_at uses pow2(k*8) * byte, word64_from_bytes uses byte * pow2(k*8)
                assert(spec_load8_at(bytes, (i_int * 8) as usize) == word64_from_bytes(
                    bytes@,
                    i_int,
                )) by {
                    broadcast use lemma_mul_is_commutative;

                };
                assert forall|k: int| i + 1 <= k < 8 implies words@[k] == 0 by {
                    assert(words@[#[trigger] k] == 0);
                };
                reveal_with_fuel(words64_from_bytes_to_nat, 9);
                assert(bytes_as_nat_suffix(bytes, i_int * 8) == word64_from_bytes(bytes@, i_int)
                    * pow2((i_int * 64) as nat) + bytes_as_nat_suffix(bytes, (i_int + 1) * 8)) by {
                    lemma_bytes_suffix_matches_word_partial(bytes, i_int, 8);
                    broadcast use lemma_mul_is_commutative;

                };
            }
        }

        proof {
            lemma_words_as_nat_equals_bytes(&words, bytes, 8);
        }

        // Stage 2 word bounds: every assembled chunk fits in 64 bits.
        assert forall|k: int| 0 <= k < 8 implies words[k] < pow2(64) by {
            let idx = (k * 8) as usize;
            lemma_spec_load8_at_fits_u64(bytes, idx);
            // spec_load8_at uses pow2(k*8) * byte, word64_from_bytes uses byte * pow2(k*8)
            assert(spec_load8_at(bytes, idx) == word64_from_bytes(bytes@, k)) by {
                broadcast use lemma_mul_is_commutative;

            };
            lemma2_to64_rest();  // u64::MAX == pow2(64) - 1
        };

        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;
        let mut lo = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        let mut hi = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };

        lo.limbs[0] = words[0] & mask;
        lo.limbs[1] = ((words[0] >> 52) | (words[1] << 12)) & mask;
        lo.limbs[2] = ((words[1] >> 40) | (words[2] << 24)) & mask;
        lo.limbs[3] = ((words[2] >> 28) | (words[3] << 36)) & mask;
        lo.limbs[4] = ((words[3] >> 16) | (words[4] << 48)) & mask;
        hi.limbs[0] = (words[4] >> 4) & mask;
        hi.limbs[1] = ((words[4] >> 56) | (words[5] << 8)) & mask;
        hi.limbs[2] = ((words[5] >> 44) | (words[6] << 20)) & mask;
        hi.limbs[3] = ((words[6] >> 32) | (words[7] << 32)) & mask;
        hi.limbs[4] = words[7] >> 20;

        // Stage 3: the masked limbs contributed by each 64-bit word remain below 2^52.
        let ghost lo_raw = lo;
        let ghost hi_raw = hi;

        proof {
            lemma_lo_limbs_bounded(&lo_raw, &words, mask);
            lemma_hi_limbs_bounded(&hi_raw, &words, mask);
        }

        let ghost pow2_260 = pow2(260);
        let ghost low_expr = (words[0] as nat) + pow2(64) * (words[1] as nat) + pow2(128) * (
        words[2] as nat) + pow2(192) * (words[3] as nat) + pow2(256) * ((words[4] & 0xf) as nat);

        let ghost high_expr = (words[4] >> 4) as nat + pow2(60) * (words[5] as nat) + pow2(124) * (
        words[6] as nat) + pow2(188) * (words[7] as nat);

        let ghost wide_sum = (words[0] as nat) + pow2(64) * (words[1] as nat) + pow2(128) * (
        words[2] as nat) + pow2(192) * (words[3] as nat) + pow2(256) * (words[4] as nat) + pow2(320)
            * (words[5] as nat) + pow2(384) * (words[6] as nat) + pow2(448) * (words[7] as nat);

        proof {
            // Reading the five 52-bit limbs in radix 2^52 reproduces the low chunk reconstructed from the 64-bit words.
            lemma_low_limbs_encode_low_expr(&lo_raw.limbs, &words, mask);
            lemma_five_limbs_equals_to_nat(&lo_raw.limbs);
            // Reading the five 52-bit limbs in radix 2^52 reproduces the high chunk reconstructed from the 64-bit words.
            lemma_high_limbs_encode_high_expr(&hi_raw.limbs, &words, mask);
            lemma_five_limbs_equals_to_nat(&hi_raw.limbs);
        }
        assert(scalar52_to_nat(&hi_raw) == high_expr);

        // Assumption [L2]: The 512-bit input splits as `pow2(260) * high_expr + low_expr`.
        // WideSum-Expansion: converting the eight 64-bit words back into a natural number matches the explicit little-endian sum of their weighted contributions.
        proof {
            lemma_words64_from_bytes_to_nat_wide(bytes);
        }

        // HighLow-Recombine: Combining the high and low chunks at the 2^260 boundary reproduces the weighted word sum.
        // Bridge bit operations to arithmetic operations for word4
        let ghost word4 = words[4];
        let ghost word4_high_nat = (word4 >> 4) as nat;
        let ghost word4_low_nat = (word4 & 0xf) as nat;
        // word4 >> 4 == word4 / 16 and word4 & 0xf == word4 % 16 (for u64)
        assert(word4_high_nat == (word4 as nat) / 16 && word4_low_nat == (word4 as nat) % 16) by {
            assert(word4 >> 4 == word4 / 16 && word4 & 0xf == word4 % 16) by (bit_vector)
                requires
                    word4 == word4,
            ;
        };
        proof {
            lemma_high_low_recombine(
                words[0] as nat,
                words[1] as nat,
                words[2] as nat,
                words[3] as nat,
                word4 as nat,
                words[5] as nat,
                words[6] as nat,
                words[7] as nat,
                word4_low_nat,
                word4_high_nat,
            );
        }

        assert(wide_input == pow2_260 * high_expr + low_expr);
        // L3: The lower chunk has value strictly below 2^260.
        proof {
            lemma_bound_scalar(&lo_raw);
        }
        assert(low_expr < pow2_260);

        // Assumption: The lower bits of the wide input, modulo 2^260, match the natural value encoded by `lo_raw`.
        assert(scalar52_to_nat(&lo_raw) == wide_input % pow2(260)) by {
            lemma_mod_multiples_vanish(high_expr as int, low_expr as int, pow2_260 as int);
            lemma_small_mod(low_expr, pow2_260);
        };
        // Assumption: The upper bits of the wide input, divided by 2^260, match the natural value encoded by `hi_raw`.
        assert(scalar52_to_nat(&hi_raw) == wide_input / pow2(260)) by {
            lemma_mul_is_commutative(pow2_260 as int, high_expr as int);
            lemma_fundamental_div_mod_converse(
                wide_input as int,
                pow2_260 as int,
                high_expr as int,
                low_expr as int,
            );
        };
        // Recombining quotient and remainder at the 2^260 radix recreates the original wide input.
        assert(high_expr < pow2(252)) by {
            lemma_words_as_nat_upper_bound(&words, 8);
            lemma_pow2_adds(260, 252);
            assert(pow2_260 * pow2(252) == pow2(512));
            lemma_multiply_divide_lt(wide_input as int, pow2_260 as int, pow2(252) as int);
        };

        // Stage 4 assumption: Montgomery reductions behave as expected for these operands.
        proof {
            lemma_r_limbs_bounded();  // had to write this one manually due to crashes
            lemma_rr_limbs_bounded();
            lemma_limbs_bounded_implies_prod_bounded(&lo, &constants::R);
            lemma_limbs_bounded_implies_prod_bounded(&hi, &constants::RR);
        }

        /* ORIGINAL CODE:
        lo = Scalar52::montgomery_reduce(&Scalar52::mul_internal(&lo, &constants::R));
        */
        let lo_product = Scalar52::mul_internal(&lo, &constants::R);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(&lo, &constants::R, &lo_product);
            // R is canonical (< L), so the product satisfies canonical_bound
            lemma_r_equals_spec(constants::R);  // gives scalar52_to_nat(&R) < group_order()
            lemma_canonical_product_satisfies_canonical_bound(&lo, &constants::R, &lo_product);
        }
        lo = Scalar52::montgomery_reduce(&lo_product);  // (lo * R) / R = lo
        // is_canonical_scalar52(&lo) follows from montgomery_reduce postcondition

        /* ORIGINAL CODE:
        hi = Scalar52::montgomery_reduce(&Scalar52::mul_internal(&hi, &constants::RR));
        */
        let hi_product = Scalar52::mul_internal(&hi, &constants::RR);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(&hi, &constants::RR, &hi_product);
            // RR is canonical (< L), so the product satisfies canonical_bound
            lemma_rr_equals_spec();  // gives scalar52_to_nat(&RR) < group_order()
            lemma_canonical_product_satisfies_canonical_bound(&hi, &constants::RR, &hi_product);
        }
        hi = Scalar52::montgomery_reduce(&hi_product);  // (hi * R^2) / R = hi * R
        // is_canonical_scalar52(&hi) follows from montgomery_reduce postcondition

        proof {
            let ghost lo_before_nat = scalar52_to_nat(&lo_raw);
            let ghost lo_after_nat = scalar52_to_nat(&lo);
            let ghost r_nat = scalar52_to_nat(&constants::R);
            lemma_r_equals_spec(constants::R);
            // lo: multiply by R, reduce => extra_factor = 1
            lemma_montgomery_reduce_cancels_r(lo_after_nat, lo_before_nat, r_nat, 1);

            let ghost hi_before_nat = scalar52_to_nat(&hi_raw);
            let ghost hi_after_nat = scalar52_to_nat(&hi);
            let ghost rr_nat = scalar52_to_nat(&constants::RR);
            lemma_rr_equals_spec();
            // hi: multiply by R², reduce => extra_factor = R
            lemma_montgomery_reduce_cancels_r(
                hi_after_nat,
                hi_before_nat,
                rr_nat,
                montgomery_radix(),
            );
        }

        let result = Scalar52::add(&hi, &lo);

        // Stage 5 assumption: combining the reduced pieces matches the wide scalar modulo L.
        proof {
            lemma_montgomery_reduced_sum_congruent(
                scalar52_to_nat(&result),
                scalar52_to_nat(&hi),
                scalar52_to_nat(&lo),
                scalar52_to_nat(&hi_raw),
                scalar52_to_nat(&lo_raw),
                wide_input,
            );

            lemma_cancel_mul_pow2_mod(scalar52_to_nat(&result), wide_input, montgomery_radix());

            // Since result < group_order() (from add's postcondition),
            // we have scalar52_to_nat(&result) % group_order() == scalar52_to_nat(&result)
            lemma_small_mod(scalar52_to_nat(&result), group_order());
        }

        result
    }

    /// Pack the limbs of this `Scalar52` into 32 bytes
    #[rustfmt::skip]  // keep alignment of s[*] calculations
    #[allow(clippy::identity_op)]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_bytes(self) -> (s: [u8; 32])
        requires
            limbs_bounded(&self),
        ensures
            u8_32_as_nat(&s) == scalar52_to_nat(&self) % pow2(256),
    {
        let mut s = [0u8;32];

        s[0] = (self.limbs[0] >> 0) as u8;
        s[1] = (self.limbs[0] >> 8) as u8;
        s[2] = (self.limbs[0] >> 16) as u8;
        s[3] = (self.limbs[0] >> 24) as u8;
        s[4] = (self.limbs[0] >> 32) as u8;
        s[5] = (self.limbs[0] >> 40) as u8;
        s[6] = ((self.limbs[0] >> 48) | (self.limbs[1] << 4)) as u8;
        s[7] = (self.limbs[1] >> 4) as u8;
        s[8] = (self.limbs[1] >> 12) as u8;
        s[9] = (self.limbs[1] >> 20) as u8;
        s[10] = (self.limbs[1] >> 28) as u8;
        s[11] = (self.limbs[1] >> 36) as u8;
        s[12] = (self.limbs[1] >> 44) as u8;
        s[13] = (self.limbs[2] >> 0) as u8;
        s[14] = (self.limbs[2] >> 8) as u8;
        s[15] = (self.limbs[2] >> 16) as u8;
        s[16] = (self.limbs[2] >> 24) as u8;
        s[17] = (self.limbs[2] >> 32) as u8;
        s[18] = (self.limbs[2] >> 40) as u8;
        s[19] = ((self.limbs[2] >> 48) | (self.limbs[3] << 4)) as u8;
        s[20] = (self.limbs[3] >> 4) as u8;
        s[21] = (self.limbs[3] >> 12) as u8;
        s[22] = (self.limbs[3] >> 20) as u8;
        s[23] = (self.limbs[3] >> 28) as u8;
        s[24] = (self.limbs[3] >> 36) as u8;
        s[25] = (self.limbs[3] >> 44) as u8;
        s[26] = (self.limbs[4] >> 0) as u8;
        s[27] = (self.limbs[4] >> 8) as u8;
        s[28] = (self.limbs[4] >> 16) as u8;
        s[29] = (self.limbs[4] >> 24) as u8;
        s[30] = (self.limbs[4] >> 32) as u8;
        s[31] = (self.limbs[4] >> 40) as u8;

        proof {
            // The main lemma proves the property using the non-recursive (_aux) versions
            lemma_as_bytes_52(self.limbs, s);
            lemma_five_limbs_equals_to_nat(&self.limbs);
        }

        s
    }

    /// Compute `a + b` (mod l)
    pub fn add(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            scalar52_to_nat(&a) < group_order(),
            scalar52_to_nat(&b) < group_order(),
        ensures
            scalar52_to_nat(&s) == (scalar52_to_nat(&a) + scalar52_to_nat(&b)) % group_order(),
            // VERIFICATION NOTE: Result is canonical
            scalar52_to_nat(&s) < group_order(),
            // VERIFICATION NOTE: Result has bounded limbs (from sub)
            limbs_bounded(&s),
    {
        let mut sum = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;

        // a + b
        let mut carry: u64 = 0;
        proof {
            // Base case: empty subrange has value 0
            assert(seq_u64_to_nat(a.limbs@.subrange(0, 0 as int)) == 0);
            assert(seq_u64_to_nat(b.limbs@.subrange(0, 0 as int)) == 0);
            assert(seq_u64_to_nat(sum.limbs@.subrange(0, 0 as int)) == 0);
            assert((carry >> 52) == 0) by (bit_vector)
                requires
                    carry == 0,
            ;
            lemma2_to64();
            assert(pow2(0) == 1);
        }
        for i in 0..5
            invariant
                forall|j: int| 0 <= j < i ==> sum.limbs[j] < 1u64 << 52,
                limbs_bounded(a),
                limbs_bounded(b),
                mask == (1u64 << 52) - 1,
                i == 0 ==> carry == 0,
                i >= 1 ==> (carry >> 52) < 2,
                seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + seq_u64_to_nat(
                    b.limbs@.subrange(0, i as int),
                ) == seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) + (carry >> 52) * pow2(
                    (52 * (i) as nat),
                ),
        {
            proof {
                lemma_add_loop_bounds(i as int, carry, a.limbs[i as int], b.limbs[i as int]);
            }
            let ghost old_carry = carry;
            carry = a.limbs[i] + b.limbs[i] + (carry >> 52);
            let ghost sum_loop_start = sum;
            sum.limbs[i] = carry & mask;
            assert(sum_loop_start.limbs@.subrange(0, i as int) == sum.limbs@.subrange(0, i as int));
            proof {
                lemma_add_loop_invariant(sum, carry, i, a, b, old_carry, mask, sum_loop_start);
            }
            proof {
                lemma_add_carry_and_sum_bounds(carry, mask);
            }
        }

        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(sum.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(
            (52 * (5) as nat),
        ));

        proof {
            lemma_add_sum_simplify(a, b, &sum, carry);
        }

        // subtract l if the sum is >= l
        proof {
            lemma_l_value_properties(&constants::L, &sum);
        }
        assert(group_order() > scalar52_to_nat(&sum) - group_order() >= -group_order());
        proof {
            lemma_l_equals_group_order();
        }
        proof {
            lemma_mod_sub_multiples_vanish(scalar52_to_nat(&sum) as int, group_order() as int);
        }
        Scalar52::sub(&sum, &constants::L)
    }

    // VERIFICATION NOTE: refactored sub function from Dalek upstream
    #[allow(dead_code)]
    pub fn sub_new(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            -group_order() <= scalar52_to_nat(&a) - scalar52_to_nat(&b) < group_order(),
        ensures
            scalar52_to_nat(&s) == (scalar52_to_nat(&a) - scalar52_to_nat(&b)) % (
            group_order() as int),
    {
        assume(false);  // TODO: complete the proof
        let mut difference = Scalar52::ZERO;
        let mask = (1u64 << 52) - 1;

        // a - b
        let mut borrow: u64 = 0;
        for i in 0..5 {
            assume(false);
            borrow = a.limbs[i].wrapping_sub(b.limbs[i] + (borrow >> 63));
            difference[i] = borrow & mask;
        }

        // conditionally add l if the difference is negative
        difference.conditional_add_l(Choice::from((borrow >> 63) as u8));
        difference
    }

    // VERIFICATION NOTE: conditional_add_l function only used in sub_new function
    #[allow(dead_code)]
    pub(crate) fn conditional_add_l(&mut self, condition: Choice) -> (carry: u64)
        requires
            limbs_bounded(&old(self)),
            scalar52_to_nat(old(self)) + group_order() < pow2(260),
        ensures
    // The mathematical value modulo group_order doesn't change (since L = group_order)

            scalar52_to_nat(self) % group_order() == scalar52_to_nat(old(self)) % group_order(),
            // VERIFICATION NOTE: expression below unsupported by Verus
            //limbs_bounded(&self),
            // Meaning of conditional addition
            choice_is_true(condition) ==> scalar52_to_nat(self) == scalar52_to_nat(old(self))
                + group_order(),
            !choice_is_true(condition) ==> scalar52_to_nat(self) == scalar52_to_nat(old(self)),
    {
        let mut carry: u64 = 0;

        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;

        for i in 0..5
            invariant
                mask == (1u64 << 52) - 1,
                forall|j: int| 0 <= j < i ==> self.limbs[j] < (1u64 << 52),
                forall|j: int| i <= j < 5 ==> self.limbs[j] == old(self).limbs[j],
                forall|j: int| i <= j < 5 ==> self.limbs[j] < (1u64 << 52),
                i == 0 ==> carry == 0,
                i >= 1 ==> (carry >> 52) < 2,
        {
            /* <VERIFICATION NOTE> Using wrapper function for Verus compatibility instead of direct call to conditional_select */
            let addend = select(&0, &constants::L.limbs[i], condition);
            /* <ORIGINAL CODE>
             let addend = u64::conditional_select(&0, &constants::L[i], condition);
             <ORIGINAL CODE>*/

            // Prove no overflow using the same lemma as in sub()
            proof {
                lemma_scalar_subtract_no_overflow(
                    carry,
                    self.limbs[i as int],
                    addend,
                    i as u32,
                    &constants::L,
                );
            }

            carry = (carry >> 52) + self.limbs[i] + addend;
            self.limbs[i] = carry & mask;

            proof {
                lemma_carry_bounded_after_mask(carry, mask);
            }
        }

        proof {
            // TODO: Prove the postconditions
            assume(scalar52_to_nat(self) % group_order() == scalar52_to_nat(old(self))
                % group_order());
            //   assume(limbs_bounded(&self));
            assume(choice_is_true(condition) ==> scalar52_to_nat(self) == scalar52_to_nat(old(self))
                + group_order());
            assume(!choice_is_true(condition) ==> scalar52_to_nat(self) == scalar52_to_nat(
                old(self),
            ));
        }

        carry
    }

    /// Compute `a - b` (mod l)
    ///
    /// PRECONDITION RELAXATION: `a` doesn't need to be fully bounded.
    /// Limbs 0-3 must be < 2^52, but limb 4 can be up to 2^52 + b[4].
    /// This is needed for montgomery_reduce where the intermediate has r4 > 2^52.
    pub fn sub(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
    // Relaxed bound: limbs 0-3 bounded, limb 4 can exceed 2^52 by up to b[4]

            limbs_bounded_for_sub(a, b),
            limbs_bounded(b),
        ensures
    // UNCONDITIONAL: limbs are always bounded due to masking in both loops

            limbs_bounded(&s),
            // CONDITIONAL: modular correctness and canonicity only when value constraint holds
            // -L <= (a - b) < L
            ({
                let diff = scalar52_to_nat(&a) as int - scalar52_to_nat(&b) as int;
                let l = group_order() as int;
                -l <= diff && diff < l
            }) ==> (scalar52_to_nat(&s) == (scalar52_to_nat(&a) as int - scalar52_to_nat(&b) as int)
                % (group_order() as int)),
            ({
                let diff = scalar52_to_nat(&a) as int - scalar52_to_nat(&b) as int;
                let l = group_order() as int;
                -l <= diff && diff < l
            }) ==> is_canonical_scalar52(&s),
    {
        let mut difference = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;

        // a - b
        let mut borrow: u64 = 0;
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 0 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 0 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 0 as int)));
        assert((borrow >> 63) == 0) by (bit_vector)
            requires
                borrow == 0,
        ;
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 0 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 0 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 0 as int)) - (borrow >> 63) * pow2(
            (52 * (0) as nat),
        ));
        for i in 0..5
            invariant
                limbs_bounded(b),
                limbs_bounded_for_sub(a, b),
                forall|j: int| 0 <= j < i ==> difference.limbs[j] < (1u64 << 52),
                mask == (1u64 << 52) - 1,
                seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(
                    b.limbs@.subrange(0, i as int),
                ) == seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) - (borrow >> 63)
                    * pow2((52 * (i) as nat)),
        {
            proof {
                assert((borrow >> 63) < 2) by (bit_vector);
            }
            let ghost old_borrow = borrow;
            borrow = a.limbs[i].wrapping_sub(b.limbs[i] + (borrow >> 63));
            let ghost difference_loop1_start = difference;
            difference.limbs[i] = borrow & mask;
            assert(difference_loop1_start.limbs@.subrange(0, i as int)
                == difference.limbs@.subrange(0, i as int));
            assert(seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(
                b.limbs@.subrange(0, i as int),
            ) == seq_u64_to_nat(difference_loop1_start.limbs@.subrange(0, i as int)) - (old_borrow
                >> 63) * pow2((52 * (i) as nat)));
            proof {
                lemma_sub_loop1_invariant(
                    difference,
                    borrow,
                    i,
                    a,
                    b,
                    old_borrow,
                    mask,
                    difference_loop1_start,
                );
            }
            proof {
                lemma_borrow_and_mask_bounded(borrow, mask);
            }
        }

        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) - (borrow >> 63) * pow2(
            (52 * (5) as nat),
        ));
        // conditionally add l if the difference is negative
        assert(borrow >> 63 == 1 || borrow >> 63 == 0) by (bit_vector);
        let mut carry: u64 = 0;
        let ghost difference_after_loop1 = difference;
        assert(seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 0 as int)) == 0);
        assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 0 as int)) == 0);
        assert(seq_u64_to_nat(difference.limbs@.subrange(0, 0 as int)) == 0);
        assert(carry >> 52 == 0) by (bit_vector)
            requires
                carry == 0,
        ;
        for i in 0..5
            invariant
                forall|j: int| 0 <= j < 5 ==> difference.limbs[j] < (1u64 << 52),  // from first loop
                forall|j: int|
                    i <= j < 5 ==> difference.limbs[j] == difference_after_loop1.limbs[j],
                mask == (1u64 << 52) - 1,
                i == 0 ==> carry == 0,
                i >= 1 ==> (carry >> 52) < 2,
                (i >= 1 && borrow >> 63 == 0) ==> carry == difference.limbs[i - 1],
                borrow >> 63 == 0 ==> difference_after_loop1 == difference,
                borrow >> 63 == 1 ==> seq_u64_to_nat(
                    difference_after_loop1.limbs@.subrange(0, i as int),
                ) + seq_u64_to_nat(constants::L.limbs@.subrange(0, i as int)) == seq_u64_to_nat(
                    difference.limbs@.subrange(0, i as int),
                ) + (carry >> 52) * pow2(52 * i as nat),
        {
            let ghost old_carry = carry;
            let underflow = Choice::from((borrow >> 63) as u8);
            let addend = select(&0, &constants::L.limbs[i], underflow);
            if borrow >> 63 == 0 {
                assert(addend == 0);
            }
            if borrow >> 63 == 1 {
                assert(addend == constants::L.limbs[i as int]);
            }
            proof {
                lemma_scalar_subtract_no_overflow(
                    carry,
                    difference.limbs[i as int],
                    addend,
                    i as u32,
                    &constants::L,
                );
            }
            carry = (carry >> 52) + difference.limbs[i] + addend;
            let ghost difference_loop2_start = difference;
            difference.limbs[i] = carry & mask;
            proof {
                lemma_carry_bounded_after_mask(carry, mask);
                assert(difference_loop2_start.limbs@.subrange(0, i as int)
                    == difference.limbs@.subrange(0, i as int));
                lemma_sub_loop2_invariant(
                    difference,
                    i,
                    a,
                    b,
                    mask,
                    difference_after_loop1,
                    difference_loop2_start,
                    carry,
                    old_carry,
                    addend,
                    borrow,
                );
            }
        }
        proof {
            // UNCONDITIONAL: Prove limbs_bounded from loop invariant
            // After loop 2, each limb is masked with (2^52 - 1), so < 2^52
            // The loop 2 invariant maintains: forall|j: int| 0 <= j < 5 ==> difference.limbs[j] < (1u64 << 52)
            assert(limbs_bounded(&difference)) by {
                assert(forall|j: int| 0 <= j < 5 ==> difference.limbs[j] < (1u64 << 52));
                // limbs_bounded requires each limb < pow2(52)
                // (1u64 << 52) == pow2(52)
                assert((1u64 << 52) == pow2(52)) by {
                    lemma_u64_shift_is_pow2(52);
                }
            }

            // CONDITIONAL: Modular correctness and canonicity only when value constraint holds
            let a_val = scalar52_to_nat(&a) as int;
            let b_val = scalar52_to_nat(&b) as int;
            let l_val = group_order() as int;
            if -l_val <= a_val - b_val && a_val - b_val < l_val {
                lemma_sub_correct_after_loops(
                    difference,
                    carry,
                    a,
                    b,
                    difference_after_loop1,
                    borrow,
                );
            }
        }
        difference
    }

    /// Compute `a * b`
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of z[*] calculations
    pub(crate) fn mul_internal(a: &Scalar52, b: &Scalar52) -> (z: [u128; 9])
        requires
            limb_prod_bounded_u128(a.limbs, b.limbs, 5),
        ensures
            slice128_to_nat(&z) == scalar52_to_nat(&a) * scalar52_to_nat(&b),
            spec_mul_internal(a, b) == z,
    {
        proof { lemma_mul_internal_no_overflow() }

        let mut z = [0u128;9];

        z[0] = m(a.limbs[0], b.limbs[0]);
        z[1] = m(a.limbs[0], b.limbs[1]) + m(a.limbs[1], b.limbs[0]);
        z[2] = m(a.limbs[0], b.limbs[2]) + m(a.limbs[1], b.limbs[1]) + m(a.limbs[2], b.limbs[0]);
        z[3] = m(a.limbs[0], b.limbs[3]) + m(a.limbs[1], b.limbs[2]) + m(a.limbs[2], b.limbs[1])
            + m(a.limbs[3], b.limbs[0]);
        z[4] = m(a.limbs[0], b.limbs[4]) + m(a.limbs[1], b.limbs[3]) + m(a.limbs[2], b.limbs[2])
            + m(a.limbs[3], b.limbs[1]) + m(a.limbs[4], b.limbs[0]);
        z[5] = m(a.limbs[1], b.limbs[4]) + m(a.limbs[2], b.limbs[3]) + m(a.limbs[3], b.limbs[2])
            + m(a.limbs[4], b.limbs[1]);
        z[6] = m(a.limbs[2], b.limbs[4]) + m(a.limbs[3], b.limbs[3]) + m(a.limbs[4], b.limbs[2]);
        z[7] = m(a.limbs[3], b.limbs[4]) + m(a.limbs[4], b.limbs[3]);
        z[8] = m(a.limbs[4], b.limbs[4]);

        proof {
            lemma_mul_internal_correct(&a.limbs, &b.limbs, &z);
        }

        z
    }

    /* <ORIGINAL CODE>
    fn square_internal(a: &Scalar52) -> [u128; 9] {
        let aa = [
            a[0] * 2,
            a[1] * 2,
            a[2] * 2,
            a[3] * 2,
        ];

        [
            m( a[0], a[0]),
            m(aa[0], a[1]),
            m(aa[0], a[2]) + m( a[1], a[1]),
            m(aa[0], a[3]) + m(aa[1], a[2]),
            m(aa[0], a[4]) + m(aa[1], a[3]) + m( a[2], a[2]),
                             m(aa[1], a[4]) + m(aa[2], a[3]),
                                              m(aa[2], a[4]) + m( a[3], a[3]),
                                                               m(aa[3], a[4]),
                                                                                m(a[4], a[4])
        ]
    }
    </ORIGINAL CODE> */
    /* <VERIFICATION NOTE>
    -  refactored verified version of square_internal
    - slightly slower ?
    </VERIFICATION NOTE> */
    /// Compute `a^2`
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of calculations
    pub(crate) fn square_internal(a: &Scalar52) -> (z: [u128; 9])
        requires
            limb_prod_bounded_u128(a.limbs, a.limbs, 5),
        ensures
            slice128_to_nat(&z) == scalar52_to_nat(&a) * scalar52_to_nat(&a),
            spec_mul_internal(a, a) == z,
            limbs_bounded(&a) ==> forall|i: int| 0 <= i < 9 ==> z[i] < 5 * (1u128 << 104),
    {
        proof { lemma_square_internal_no_overflow() }

        let mut z = [0u128;9];
        z[0] = m(a.limbs[0], a.limbs[0]);
        z[1] = m(a.limbs[0], a.limbs[1]) * 2;
        z[2] = m(a.limbs[0], a.limbs[2]) * 2 + m(a.limbs[1], a.limbs[1]);
        z[3] = m(a.limbs[0], a.limbs[3]) * 2 + m(a.limbs[1], a.limbs[2]) * 2;
        z[4] = m(a.limbs[0], a.limbs[4]) * 2 + m(a.limbs[1], a.limbs[3]) * 2 + m(
            a.limbs[2],
            a.limbs[2],
        );
        z[5] = m(a.limbs[1], a.limbs[4]) * 2 + m(a.limbs[2], a.limbs[3]) * 2;
        z[6] = m(a.limbs[2], a.limbs[4]) * 2 + m(a.limbs[3], a.limbs[3]);
        z[7] = m(a.limbs[3], a.limbs[4]) * 2;
        z[8] = m(a.limbs[4], a.limbs[4]);

        proof {
            lemma_square_internal_correct(&a.limbs, &z);

            if (limbs_bounded(&a)) {
                assert((1u64 << 52) * (1u64 << 52) == 1u128 << 104) by (bit_vector);
                assert(5 * (1u128 << 104) <= u128::MAX) by (bit_vector);
                let bound = 1u64 << 52;
                let b2 = 1u128 << 104;
                assert forall|i: int| 0 <= i < 9 implies z[i] < 5 * b2 by {
                    assert forall|j: int, k: int| 0 <= j < 5 && 0 <= k < 5 implies (
                    a.limbs[j] as u128) * (a.limbs[k] as u128) < b2 by {
                        // trigger foralls in limbs_bounded:
                        assert(a.limbs[j] < bound);
                        assert(a.limbs[k] < bound);
                        lemma_mul_lt(
                            a.limbs[j] as nat,
                            bound as nat,
                            a.limbs[k] as nat,
                            bound as nat,
                        );
                    }
                    assert(z[i] < b2 * 2 + b2 * 2 + b2);
                    assert(b2 * 2 + b2 * 2 + b2 == 5 * b2) by {
                        assert(b2 * 2 + b2 * 2 == b2 * 4) by {
                            lemma_mul_is_distributive_add(b2 as int, 2, 2);
                        }
                        assert(b2 == b2 * 1) by {
                            lemma_mul_basics_3(b2 as int);
                        }
                        assert(b2 * 4 + b2 * 1 == 5 * b2) by {
                            lemma_mul_is_distributive_add(b2 as int, 4, 1);
                            lemma_mul_is_commutative(b2 as int, 5);
                        }
                    }
                }
            }
        }

        z
    }

    /* ORIGINAL CODE for montgomery_reduce - from dalek-cryptography/curve25519-dalek @ 61533d75
    /// pub (crate) fn montgomery_reduce(limbs: &[u128; 9]) -> Scalar52 {
    ///     #[inline(always)]
    ///     fn part1(sum: u128) -> (u128, u64) {
    ///         let p = (sum as u64).wrapping_mul(constants::LFACTOR) & ((1u64 << 52) - 1);
    ///         ((sum + m(p, constants::L[0])) >> 52, p)
    ///     }
    ///     #[inline(always)]
    ///     fn part2(sum: u128) -> (u128, u64) {
    ///         let w = (sum as u64) & ((1u64 << 52) - 1);
    ///         (sum >> 52, w)
    ///     }
    ///     // note: l[3] is zero, so its multiples can be skipped
    ///     let l = &constants::L;
    ///     // the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R
    ///     let (carry, n0) = part1(        limbs[0]);
    ///     let (carry, n1) = part1(carry + limbs[1] + m(n0, l[1]));
    ///     let (carry, n2) = part1(carry + limbs[2] + m(n0, l[2]) + m(n1, l[1]));
    ///     let (carry, n3) = part1(carry + limbs[3]               + m(n1, l[2]) + m(n2, l[1]));
    ///     let (carry, n4) = part1(carry + limbs[4] + m(n0, l[4])               + m(n2, l[2]) + m(n3, l[1]));
    ///     // limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result
    ///     let (carry, r0) = part2(carry + limbs[5]               + m(n1, l[4])               + m(n3, l[2])   + m(n4, l[1]));
    ///     let (carry, r1) = part2(carry + limbs[6]                             + m(n2,l[4])                  + m(n4, l[2]));
    ///     let (carry, r2) = part2(carry + limbs[7]                                           + m(n3, l[4])                );
    ///     let (carry, r3) = part2(carry + limbs[8]                                                           + m(n4, l[4]));
    ///     let         r4 = carry as u64;
    ///     // result may be >= l, so attempt to subtract l
    ///     Scalar52::sub(&Scalar52([r0, r1, r2, r3, r4]), l)
    /// }
    </ORIGINAL CODE> */
    /// Compute `limbs/R` (mod l), where R is the Montgomery modulus 2^260
    ///
    /// # Preconditions
    /// - `montgomery_reduce_input_bounds(limbs)`: Per-limb bounds for overflow-safe computation
    /// - `montgomery_reduce_canonical_bound(limbs)`: T < R×L (HAC 14.32's value constraint)
    ///
    /// # Postconditions (all unconditional given preconditions)
    /// - `limbs_bounded(&result)`: Result limbs are bounded (< 2^52)
    /// - `montgomery_congruent(&result, limbs)`: (result × R) ≡ T (mod L)
    /// - `is_canonical_scalar52(&result)`: result < L
    ///
    /// # Note
    /// The `canonical_bound` precondition corresponds to HAC Algorithm 14.32's requirement
    /// that T < m×R for correct Montgomery reduction. This ensures intermediate < 2L,
    /// which is needed for sub's correctness and the r4 < 2^52 + L[4] bound.
    /// HAC is at https://cacr.uwaterloo.ca/hac/about/chap14.pdf
    /// The `input_bounds` precondition ensures no overflow in u128 arithmetic.
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of n* and r* calculations
    pub(crate) fn montgomery_reduce(limbs: &[u128; 9]) -> (result: Scalar52)
        requires
    // Per-limb bounds for overflow-safe u128 arithmetic

            montgomery_reduce_input_bounds(limbs),
            // HAC 14.32's value constraint: T < R×L ensures intermediate < 2L
            montgomery_reduce_canonical_bound(limbs),
        ensures
    // All postconditions are now unconditional (given preconditions)

            limbs_bounded(&result),
            montgomery_congruent(&result, limbs),
            is_canonical_scalar52(&result),
    {
        // note: l[3] is zero, so its multiples can be skipped
        let l = &constants::L;

        // =====================================================================
        // PHASE 1: First half - compute Montgomery adjustment factors n0..n4
        // Each part1 call requires sum < 2^108
        // =====================================================================

        // Establish L is limbs_bounded once for all lemma_m calls
        proof {
            lemma_l_limbs_bounded();
        }

        // Establish once: product bound, overflow safety, and shift-to-pow2 conversions
        proof {
            assert(((1u64 << 52) as u128) * ((1u64 << 52) as u128) == (1u128 << 104))
                by (bit_vector);
            assert((1u128 << 108) < u128::MAX) by (bit_vector);
            // Convert pow2(N) to (1u128 << N) for all limb bounds used below
            lemma_u128_shift_is_pow2(104);
            lemma_u128_shift_is_pow2(105);
            lemma_u128_shift_is_pow2(106);
            lemma_u128_shift_is_pow2(107);
            lemma_u128_shift_is_pow2(108);
        }

        proof {
            assert(limbs[0] < (1u128 << 108)) by {
                lemma_pow2_strictly_increases(104, 108);
            };
        }
        let (carry, n0) = Self::part1(limbs[0]);
        let ghost carry0 = carry;

        let m_n0_l1 = m(n0, l.limbs[1]);
        proof {
            assert(carry + limbs[1] + m_n0_l1 < (1u128 << 108)) by {
                lemma_m(n0, l.limbs[1], (1u64 << 52), (1u64 << 52));
                assert((1u128 << 57) + (1u128 << 105) + (1u128 << 104) <= (1u128 << 108))
                    by (bit_vector);
            };
        }
        let sum1 = carry + limbs[1] + m_n0_l1;
        /* ORIGINAL CODE:
         let (carry, n1) = Self::part1(carry + limbs[1] + m(n0, l.limbs[1])); */
        let (carry, n1) = Self::part1(sum1);
        let ghost carry1 = carry;

        let m_n0_l2 = m(n0, l.limbs[2]);
        let m_n1_l1 = m(n1, l.limbs[1]);
        proof {
            assert(carry + limbs[2] + m_n0_l2 + m_n1_l1 < (1u128 << 108)) by {
                lemma_m(n0, l.limbs[2], (1u64 << 52), (1u64 << 52));
                lemma_m(n1, l.limbs[1], (1u64 << 52), (1u64 << 52));
                assert((1u128 << 57) + (1u128 << 106) + 2 * (1u128 << 104) <= (1u128 << 108))
                    by (bit_vector);
            };
        }
        let sum2 = carry + limbs[2] + m_n0_l2 + m_n1_l1;
        /* ORIGINAL CODE:
        let (carry, n2) = Self::part1(carry + limbs[2] + m(n0, l.limbs[2]) + m(n1, l.limbs[1])); */
        let (carry, n2) = Self::part1(sum2);
        let ghost carry2 = carry;

        let m_n1_l2 = m(n1, l.limbs[2]);
        let m_n2_l1 = m(n2, l.limbs[1]);
        proof {
            assert(carry + limbs[3] + m_n1_l2 + m_n2_l1 < (1u128 << 108)) by {
                lemma_m(n1, l.limbs[2], (1u64 << 52), (1u64 << 52));
                lemma_m(n2, l.limbs[1], (1u64 << 52), (1u64 << 52));
                assert((1u128 << 57) + (1u128 << 107) + 2 * (1u128 << 104) <= (1u128 << 108))
                    by (bit_vector);
            };
        }
        let sum3 = carry + limbs[3] + m_n1_l2 + m_n2_l1;
        /* ORIGINAL CODE:
        let (carry, n3) = Self::part1(carry + limbs[3] + m(n1, l.limbs[2]) + m(n2, l.limbs[1])); */
        let (carry, n3) = Self::part1(sum3);
        let ghost carry3 = carry;

        let m_n0_l4 = m(n0, l.limbs[4]);
        let m_n2_l2 = m(n2, l.limbs[2]);
        let m_n3_l1 = m(n3, l.limbs[1]);
        proof {
            assert(carry + limbs[4] + m_n0_l4 + m_n2_l2 + m_n3_l1 < (1u128 << 108)) by {
                lemma_m(n0, l.limbs[4], (1u64 << 52), (1u64 << 52));
                lemma_m(n2, l.limbs[2], (1u64 << 52), (1u64 << 52));
                lemma_m(n3, l.limbs[1], (1u64 << 52), (1u64 << 52));
                assert((1u128 << 57) + (1u128 << 107) + 3 * (1u128 << 104) <= (1u128 << 108))
                    by (bit_vector);
            };
        }
        let sum4 = carry + limbs[4] + m_n0_l4 + m_n2_l2 + m_n3_l1;
        /* ORIGINAL CODE:
        let (carry, n4) = Self::part1(carry + limbs[4] + m(n0, l.limbs[4]) + m(n2, l.limbs[2]) + m(n3, l.limbs[1])); */
        let (carry, n4) = Self::part1(sum4);
        let ghost carry4 = carry;

        // =====================================================================
        // PHASE 2: Divide by R (take upper half) - part2 calls
        // part2 has no precondition, only need overflow safety
        // Note: After part1, carry < 2^57. After part2, carry < 2^56.
        // =====================================================================

        let m_n1_l4 = m(n1, l.limbs[4]);
        let m_n3_l2 = m(n3, l.limbs[2]);
        let m_n4_l1 = m(n4, l.limbs[1]);
        proof {
            assert(carry + limbs[5] + m_n1_l4 + m_n3_l2 + m_n4_l1 < (1u128 << 108)) by {
                lemma_m(n1, l.limbs[4], (1u64 << 52), (1u64 << 52));
                lemma_m(n3, l.limbs[2], (1u64 << 52), (1u64 << 52));
                lemma_m(n4, l.limbs[1], (1u64 << 52), (1u64 << 52));
                assert((1u128 << 57) + (1u128 << 107) + 3 * (1u128 << 104) <= (1u128 << 108))
                    by (bit_vector);
            };
        }
        let sum5 = carry + limbs[5] + m_n1_l4 + m_n3_l2 + m_n4_l1;
        let (carry, r0) = Self::part2(sum5);
        /* ORIGINAL CODE: let (carry, r0) = Self::part2(carry + limbs[5] + m(n1, l.limbs[4]) + m(n3, l.limbs[2]) + m(n4, l.limbs[1]),); */
        let ghost carry5 = carry;
        assert(r0 < (1u64 << 52));  // from part2 postcondition

        let m_n2_l4 = m(n2, l.limbs[4]);
        let m_n4_l2 = m(n4, l.limbs[2]);
        proof {
            assert(carry + limbs[6] + m_n2_l4 + m_n4_l2 < (1u128 << 108)) by {
                lemma_m(n2, l.limbs[4], (1u64 << 52), (1u64 << 52));
                lemma_m(n4, l.limbs[2], (1u64 << 52), (1u64 << 52));
                assert((1u128 << 56) + (1u128 << 106) + 2 * (1u128 << 104) <= (1u128 << 108))
                    by (bit_vector);
            };
        }
        let sum6 = carry + limbs[6] + m_n2_l4 + m_n4_l2;
        let (carry, r1) = Self::part2(sum6);
        /* ORIGINAL CODE: let (carry, r1) = Self::part2(carry + limbs[6] + m(n2, l.limbs[4]) + m(n4, l.limbs[2])); */
        let ghost carry6 = carry;
        assert(r1 < (1u64 << 52));  // from part2 postcondition

        let m_n3_l4 = m(n3, l.limbs[4]);
        proof {
            assert(carry + limbs[7] + m_n3_l4 < (1u128 << 108)) by {
                lemma_m(n3, l.limbs[4], (1u64 << 52), (1u64 << 52));
                assert((1u128 << 56) + (1u128 << 105) + (1u128 << 104) <= (1u128 << 108))
                    by (bit_vector);
            };
        }
        let sum7 = carry + limbs[7] + m_n3_l4;
        let (carry, r2) = Self::part2(sum7);
        /* ORIGINAL CODE: let (carry, r2) = Self::part2(carry + limbs[7] + m(n3, l.limbs[4])); */
        let ghost carry7 = carry;
        assert(r2 < (1u64 << 52));  // from part2 postcondition

        let m_n4_l4 = m(n4, l.limbs[4]);
        proof {
            assert(carry + limbs[8] + m_n4_l4 < (1u128 << 108)) by {
                lemma_m(n4, l.limbs[4], (1u64 << 52), (1u64 << 52));
                assert((1u128 << 56) + 2 * (1u128 << 104) <= (1u128 << 108)) by (bit_vector);
            };
        }
        let sum8 = carry + limbs[8] + m_n4_l4;
        let (carry, r3) = Self::part2(sum8);
        /* ORIGINAL CODE: let (carry, r3) = Self::part2(carry + limbs[8] + m(n4, l.limbs[4])); */
        let ghost carry8 = carry;  // Ghost: save for algorithm correctness proof (this becomes r4)
        assert(r3 < (1u64 << 52));  // from part2 postcondition

        /* ORIGINAL CODE: let r4 = carry as u64; */
        // Unlike r0-r3 (which are masked to 52 bits by part2), r4 is the raw final carry
        // and can exceed 2^52. Two separate bounds are needed:
        //
        //   1. CAST SAFETY: carry8 < 2^53
        //      Proven here by lemma_carry8_bound from the computation structure:
        //      sum8 = carry7 + limb8 + n4*L[4] < 2^105, so carry8 = sum8 >> 52 < 2^53.
        //      This allows the safe u128 -> u64 cast.
        //
        //   2. SUB PRECONDITION: r4 < 2^52 + L[4]
        //      Proven later by lemma_r4_bound_from_canonical, using the REDC value
        //      constraint (T < R*L) to show intermediate < 2L, which bounds r4.
        //      This satisfies sub's relaxed limbs_bounded_for_sub precondition.
        //
        // We must prove (1) before the cast since lemma_montgomery_reduce_pre_sub
        // takes r4: u64 as input, creating a chicken-and-egg dependency.
        proof {
            let limb8 = limbs[8];
            let l4 = l.limbs[4];

            assert(limb8 < (1u128 << 104)) by {
                lemma_u128_shift_is_pow2(104);
            }

            assert(l4 == (1u64 << 44)) by {
                lemma_l_limb4_is_pow2_44();
                assert(pow2(44) == (1u64 << 44) as nat) by {
                    lemma_u64_shift_is_pow2(44);
                }
            }

            assert(carry8 == sum8 >> 52) by (bit_vector)
                requires
                    sum8 == (r3 as u128) + (carry8 << 52),
                    r3 < (1u64 << 52),
                    carry8 < (1u128 << 56),
            ;

            assert(carry8 < pow2(53)) by {
                assert(m_n4_l4 == (n4 as u128) * (l4 as u128));
                lemma_carry8_bound(limb8, n4, l4, carry7, sum8, carry8);
            }

            assert(carry < (1u128 << 53)) by {
                lemma_u128_shift_is_pow2(53);
            }
        }
        // Safe cast: carry < 2^53 proven by lemma_carry8_bound
        let r4 = carry as u64;

        // =====================================================================
        // PHASE 3: Conditional subtraction
        // =====================================================================
        // The intermediate result may be >= L, so attempt to subtract L.
        // sub() handles this with constant-time conditional subtraction.
        // =====================================================================
        let intermediate = Scalar52 { limbs: [r0, r1, r2, r3, r4] };

        // =====================================================================
        // Proof: Establish sub() preconditions
        // =====================================================================
        // 1. Part 1 chain proves: (T + N×L) ≡ 0 (mod R) and N < R
        // 2. Part 2 chain proves: intermediate × R = T + N×L
        // 3. Direct REDC bound: T < R×L ∧ N < R → intermediate < 2L → r4 bounded
        // =====================================================================

        proof {
            // =========================================================================
            // SECTION 1: Result limb bounds (r0-r3 from part2 postconditions)
            // =========================================================================
            // Establish pow2(52) == (1u64 << 52) once — needed throughout (n_i bounds, etc.)
            assert(pow2(52) == (1u64 << 52) as nat) by {
                lemma_u64_shift_is_pow2(52);
            }
            assert(r0 < pow2(52) as u64 && r1 < pow2(52) as u64 && r2 < pow2(52) as u64 && r3
                < pow2(52) as u64);

            // =========================================================================
            // SECTION 2: Part 1 - Convert u128 shift operations to nat arithmetic
            // =========================================================================
            // Part1 postconditions use u128: sum + p*L[0] == carry << 52
            // Divisibility lemma needs nat: sum + p*l0() == carry * pow2(52)
            // Each stage equation pairs with lemma_carry_shift_to_nat for its carry.

            assert((1u128 << 57) as nat == pow2(57)) by {
                lemma_u128_shift_is_pow2(57);
            }
            assert(limbs[0] as nat + (n0 as nat) * l0() == (carry0 as nat) * pow2(52)) by {
                lemma_carry_shift_to_nat(carry0, 57);
            }
            assert((carry0 as nat + limbs[1] as nat + (n0 as nat) * (constants::L.limbs[1] as nat))
                + (n1 as nat) * l0() == (carry1 as nat) * pow2(52)) by {
                lemma_carry_shift_to_nat(carry1, 57);
            }
            assert((carry1 as nat + limbs[2] as nat + (n0 as nat) * (constants::L.limbs[2] as nat)
                + (n1 as nat) * (constants::L.limbs[1] as nat)) + (n2 as nat) * l0() == (
            carry2 as nat) * pow2(52)) by {
                lemma_carry_shift_to_nat(carry2, 57);
            }
            assert((carry2 as nat + limbs[3] as nat + (n1 as nat) * (constants::L.limbs[2] as nat)
                + (n2 as nat) * (constants::L.limbs[1] as nat)) + (n3 as nat) * l0() == (
            carry3 as nat) * pow2(52)) by {
                lemma_carry_shift_to_nat(carry3, 57);
            }
            assert((carry3 as nat + limbs[4] as nat + (n0 as nat) * (constants::L.limbs[4] as nat)
                + (n2 as nat) * (constants::L.limbs[2] as nat) + (n3 as nat) * (
            constants::L.limbs[1] as nat)) + (n4 as nat) * l0() == (carry4 as nat) * pow2(52)) by {
                lemma_carry_shift_to_nat(carry4, 57);
            }

            // =========================================================================
            // SECTION 3: Call divisibility lemma and establish N < 2^260
            // =========================================================================
            let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
            let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
                + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
            let l_low = constants::L.limbs[0] as nat + constants::L.limbs[1] as nat * pow2(52)
                + constants::L.limbs[2] as nat * pow2(104) + constants::L.limbs[3] as nat * pow2(
                156,
            ) + constants::L.limbs[4] as nat * pow2(208);

            // Quotient relationship: t_low + nl_low_coeffs == carry4 × 2^260
            let l0_val = constants::L.limbs[0] as nat;
            let l1_val = constants::L.limbs[1] as nat;
            let l2_val = constants::L.limbs[2] as nat;
            let l4_val = constants::L.limbs[4] as nat;
            let coeff0 = (n0 as nat) * l0_val;
            let coeff1 = (n0 as nat) * l1_val + (n1 as nat) * l0_val;
            let coeff2 = (n0 as nat) * l2_val + (n1 as nat) * l1_val + (n2 as nat) * l0_val;
            let coeff3 = (n1 as nat) * l2_val + (n2 as nat) * l1_val + (n3 as nat) * l0_val;
            let coeff4 = (n0 as nat) * l4_val + (n2 as nat) * l2_val + (n3 as nat) * l1_val + (
            n4 as nat) * l0_val;
            let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156)
                + coeff4 * pow2(208);

            assert((t_low + n * l_low) % pow2(260) == 0 && t_low + nl_low_coeffs == (carry4 as nat)
                * pow2(260)) by {
                lemma_part1_chain_divisibility(
                    limbs,
                    n0,
                    n1,
                    n2,
                    n3,
                    n4,
                    carry0,
                    carry1,
                    carry2,
                    carry3,
                    carry4,
                );
            }

            assert(n < pow2(260)) by {
                let n_arr: [u64; 5] = [n0, n1, n2, n3, n4];
                lemma_five_limbs_equals_to_nat(&n_arr);

                // Connect five_limbs_to_nat_aux to five_u64_limbs_to_nat
                assert(five_limbs_to_nat_aux(n_arr) == n) by {
                    lemma_mul_is_commutative(pow2(52) as int, n1 as nat as int);
                    lemma_mul_is_commutative(pow2(104) as int, n2 as nat as int);
                    lemma_mul_is_commutative(pow2(156) as int, n3 as nat as int);
                    lemma_mul_is_commutative(pow2(208) as int, n4 as nat as int);
                }

                // Each n_i < 2^52, so limbs52_to_nat < 2^260
                assert(forall|i: int| 0 <= i < 5 ==> n_arr@[i] < (1u64 << 52));
                lemma_general_bound(n_arr@);
                assert(52 * 5 == 260nat) by (compute_only);
            }

            // =========================================================================
            // SECTION 4: Part 2 - Convert part2 postconditions to nat
            // =========================================================================
            // Sum definitions (from how sums are computed in code)
            assert(sum5 as nat == carry4 as nat + limbs[5] as nat + (n1 as nat) * (
            constants::L.limbs[4] as nat) + (n3 as nat) * (constants::L.limbs[2] as nat) + (
            n4 as nat) * (constants::L.limbs[1] as nat));
            assert(sum6 as nat == carry5 as nat + limbs[6] as nat + (n2 as nat) * (
            constants::L.limbs[4] as nat) + (n4 as nat) * (constants::L.limbs[2] as nat));
            assert(sum7 as nat == carry6 as nat + limbs[7] as nat + (n3 as nat) * (
            constants::L.limbs[4] as nat));
            assert(sum8 as nat == carry7 as nat + limbs[8] as nat + (n4 as nat) * (
            constants::L.limbs[4] as nat));

            // Convert part2 carries (< 2^56) and stage equations: sum == r + carry * pow2(52)
            assert((1u128 << 56) as nat == pow2(56)) by {
                lemma_u128_shift_is_pow2(56);
            }
            assert(sum5 as nat == (r0 as nat) + (carry5 as nat) * pow2(52)) by {
                lemma_carry_shift_to_nat(carry5, 56);
            }
            assert(sum6 as nat == (r1 as nat) + (carry6 as nat) * pow2(52)) by {
                lemma_carry_shift_to_nat(carry6, 56);
            }
            assert(sum7 as nat == (r2 as nat) + (carry7 as nat) * pow2(52)) by {
                lemma_carry_shift_to_nat(carry7, 56);
            }

            // carry8 becomes r4: prove r4 == carry8 (truncation preserves value)
            assert((r4 as nat) == (carry8 as nat)) by {
                lemma_pow2_strictly_increases(56, 64);
                lemma_u128_cast_64_is_mod(carry8);
                assert(pow2(64) == (1u128 << 64) as nat) by {
                    lemma_u128_shift_is_pow2(64);
                }
                assert((1u128 << 64) == 0x10000000000000000u128) by (bit_vector);
                lemma_small_mod(carry8 as nat, 0x10000000000000000nat);
            }
            assert(sum8 as nat == (r3 as nat) + (r4 as nat) * pow2(52)) by {
                lemma_carry_shift_to_nat(carry8, 56);
            }

            // =========================================================================
            // SECTION 5: Call pre_sub lemma for quotient relationship
            // =========================================================================
            assert(scalar52_to_nat(&intermediate) * montgomery_radix() == slice128_to_nat(limbs) + n
                * group_order()) by {
                lemma_montgomery_reduce_pre_sub(
                    limbs,
                    n0,
                    n1,
                    n2,
                    n3,
                    n4,
                    n,
                    carry4,
                    sum5,
                    sum6,
                    sum7,
                    sum8,
                    carry5,
                    carry6,
                    carry7,
                    r0,
                    r1,
                    r2,
                    r3,
                    r4,
                    &intermediate,
                );
            }

            // =========================================================================
            // SECTION 6: Establish sub() preconditions via direct REDC bound
            // =========================================================================
            let inter_val = scalar52_to_nat(&intermediate);
            let l_val = group_order();

            assert(scalar52_to_nat(l) == group_order()) by {
                lemma_l_equals_group_order();
            }

            // Direct REDC bound: connect scalar52_to_nat to explicit limb sum,
            // then apply lemma_r4_bound_from_canonical for r4 < 2^52 + L[4] and inter < 2L.
            // Call shared lemmas once — both facts follow from lemma_r4_bound_from_canonical.
            lemma_l_equals_group_order();
            lemma_five_limbs_equals_to_nat(&intermediate.limbs);
            lemma_mul_is_commutative(pow2(52) as int, r1 as int);
            lemma_mul_is_commutative(pow2(104) as int, r2 as int);
            lemma_mul_is_commutative(pow2(156) as int, r3 as int);
            lemma_mul_is_commutative(pow2(208) as int, r4 as int);
            lemma_r4_bound_from_canonical(limbs, r0, r1, r2, r3, r4, n);
            assert(limbs_bounded_for_sub(&intermediate, l));
            assert(inter_val < 2 * l_val);
            // diff bounds follow from 0 <= inter_val < 2*l_val
            assert((inter_val as int) - (l_val as int) >= -(l_val as int));
            assert((inter_val as int) - (l_val as int) < (l_val as int));
        }
        // Now sub's precondition is satisfied

        let result = Scalar52::sub(&intermediate, l);

        // =====================================================================
        // POSTCONDITION PROOFS
        // =====================================================================
        // All postconditions are derived from:
        // 1. lemma_montgomery_reduce_pre_sub - establishes quotient relationship
        // 2. sub - computes result = (intermediate - L) mod L, canonical output
        // 3. lemma_montgomery_reduce_post_sub - derives montgomery_congruent
        // =====================================================================
        proof {
            // Postcondition 1: limbs_bounded(result) - directly from sub postcondition
            assert(limbs_bounded(&result));

            // Postcondition 2: montgomery_congruent(&result, limbs)
            assert(montgomery_congruent(&result, limbs)) by {
                let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);

                // Subgoal: L constant equals group order
                assert(scalar52_to_nat(l) == group_order()) by {
                    lemma_l_equals_group_order();
                }

                // From pre_sub lemma: quotient relationship
                // intermediate × R = T + N×L
                assert(scalar52_to_nat(&intermediate) * montgomery_radix() == slice128_to_nat(limbs)
                    + n * group_order());

                // From sub postcondition: result = (intermediate - L) mod L
                assert(scalar52_to_nat(&result) == (scalar52_to_nat(&intermediate) as int
                    - group_order() as int) % (group_order() as int));

                // Derive montgomery_congruent from the above
                lemma_montgomery_reduce_post_sub(limbs, &intermediate, &result, n);
            }

            // Postcondition 3: is_canonical_scalar52(result) - directly from sub postcondition
            assert(is_canonical_scalar52(&result));
        }

        result
    }

    /// Helper function for Montgomery reduction
    /// Computes p such that sum + p*L[0] is divisible by 2^52, returns (carry, p).
    /// VER NOTE: spec validation needed concurrent with proof for montgomery_reduce
    #[inline(always)]
    fn part1(sum: u128) -> (res: (u128, u64))
        requires
    // Bound needed to ensure no overflow and carry bounds

            sum < (1u128 << 108),
        ensures
            ({
                let carry = res.0;
                let p = res.1;
                &&& p < (1u64 << 52)  // p is bounded by 52 bits
                &&& sum + (p as u128) * (constants::L.limbs[0] as u128) == carry
                    << 52
                // Carry bound: sum + p*L[0] < 2^108 + 2^102 < 2^109, so carry < 2^57
                &&& carry < (1u128 << 57)
            }),
    {
        /* ORIGINAL CODE:
         #[inline(always)]
        fn part1(sum: u128) -> (u128, u64) {
            let p = (sum as u64).wrapping_mul(constants::LFACTOR) & ((1u64 << 52) - 1);
            ((sum + m(p, constants::L.limbs[0])) >> 52, p)
        }
         */
        //
        // Verus's `by (bit_vector)` mode cannot reason about wrapping_mul.
        //
        // EQUIVALENT REFACTORING: Extract low 52 bits first, then multiply in u128.
        // This avoids wrapping_mul and is mathematically equivalent because:
        //   (a.wrapping_mul(b)) & MASK52 = (a * b) mod 2^52 = ((a mod 2^52) * b) mod 2^52
        // The tests test_part1_wrapping_mul_equivalence and
        // test_wrapping_mul_mask_equals_mod test this equivalence.
        let mask52: u64 = 0xFFFFFFFFFFFFFu64;  // (1 << 52) - 1
        let sum_low52: u64 = (sum as u64) & mask52;
        let product: u128 = (sum_low52 as u128) * (constants::LFACTOR as u128);
        let p: u64 = (product as u64) & mask52;

        // Bounds for m() precondition - must be outside proof block for exec code
        assert(p < 0x10000000000000u64) by (bit_vector)
            requires
                p == (product as u64) & mask52,
                mask52 == 0xFFFFFFFFFFFFFu64,
        ;
        assert(0x10000000000000u64 == (1u64 << 52)) by (bit_vector);
        assert(p < (1u64 << 52));

        assert(constants::L.limbs[0] < (1u64 << 52));

        let pL0: u128 = m(p, constants::L.limbs[0]);

        proof {
            assert((p as u128) * (constants::L.limbs[0] as u128) < (1u128 << 102)) by (bit_vector)
                requires
                    p < 0x10000000000000u64,
                    constants::L.limbs[0] < 0x4000000000000u64,
            ;
            assert((1u128 << 108) + (1u128 << 102) < (1u128 << 110)) by (bit_vector);
        }

        let total: u128 = sum + pL0;
        let carry: u128 = total >> 52;

        // =====================================================================
        // PROOF (encapsulated in lemma_part1_correctness)
        // =====================================================================
        proof {
            lemma_part1_correctness(sum);

            // Prove carry < 2^57:
            // total = sum + pL0 < 2^108 + 2^102 < 2^109
            // carry = total >> 52 < 2^109 / 2^52 = 2^57
            assert(total < (1u128 << 109)) by {
                assert(sum < (1u128 << 108));
                assert(pL0 < (1u128 << 102));
                assert((1u128 << 108) + (1u128 << 102) < (1u128 << 109)) by (bit_vector);
            }
            assert(carry < (1u128 << 57)) by {
                // total >> 52 < 2^109 / 2^52 = 2^57
                assert(total >> 52 < (1u128 << 57)) by (bit_vector)
                    requires
                        total < (1u128 << 109),
                ;
            }
        }

        (carry, p)
    }

    /// Helper function for Montgomery reduction
    /// VER NOTE: spec validation needed concurrent with proof for montgomery_reduce
    #[inline(always)]
    fn part2(sum: u128) -> (res: (u128, u64))
        requires
            sum < (1u128 << 108),
        ensures
            ({
                let carry = res.0;
                let w = res.1;
                &&& w < (1u64 << 52)  // w is bounded by 52 bits (lower limb)
                &&& sum == (w as u128) + (carry << 52)
                &&& carry < (1u128 << 56)  // carry bound from sum < 2^108

            }),
    {
        proof { lemma_part2_bounds(sum) }
        let w = (sum as u64) & ((1u64 << 52) - 1);
        let carry = sum >> 52;
        (carry, w)
    }

    /// Compute `a * b` (mod l)
    ///
    /// # Preconditions
    /// - Both inputs must be bounded (limbs < 2^52)
    /// - At least one input must be canonical (< L) for verified first reduction
    #[inline(never)]
    pub fn mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            // At least one input must be canonical for montgomery_reduce's canonical_bound
            is_canonical_scalar52(a) || is_canonical_scalar52(b),
        ensures
            scalar52_to_nat(&result) % group_order() == (scalar52_to_nat(&a) * scalar52_to_nat(&b))
                % group_order(),
            is_canonical_scalar52(&result),
    {
        proof {
            lemma_rr_limbs_bounded();
            lemma_limbs_bounded_implies_prod_bounded(a, b);
        }

        // First montgomery_reduce: ab*R ≡ a*b (mod L)
        /* ORIGINAL CODE:
        let ab = Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b));
        */
        let z1 = Scalar52::mul_internal(a, b);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(a, b, &z1);
            // At least one input is canonical, so product satisfies canonical_bound
            if is_canonical_scalar52(b) {
                lemma_canonical_product_satisfies_canonical_bound(a, b, &z1);
            } else {
                // a must be canonical since one of them is
                lemma_spec_mul_internal_commutative(a, b);
                lemma_canonical_product_satisfies_canonical_bound(b, a, &z1);
            }
        }
        let ab = Scalar52::montgomery_reduce(&z1);

        assert((scalar52_to_nat(&ab) * montgomery_radix()) % group_order() == (scalar52_to_nat(&a)
            * scalar52_to_nat(&b)) % group_order());

        // ab has limbs_bounded from montgomery_reduce's postcondition
        proof {
            lemma_limbs_bounded_implies_prod_bounded(&ab, &constants::RR);
        }

        // Second montgomery_reduce: result*R ≡ ab*RR (mod L)
        // RR is canonical (< L), so product satisfies canonical_bound
        /* ORIGINAL CODE:
        let result = Scalar52::montgomery_reduce(&Scalar52::mul_internal(&ab, &constants::RR));
        */
        let z2 = Scalar52::mul_internal(&ab, &constants::RR);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(&ab, &constants::RR, &z2);
            lemma_rr_equals_spec();
            lemma_canonical_product_satisfies_canonical_bound(&ab, &constants::RR, &z2);
        }
        let result = Scalar52::montgomery_reduce(&z2);
        // is_canonical_scalar52(&result) follows from montgomery_reduce postcondition

        assert((scalar52_to_nat(&result) * montgomery_radix()) % group_order() == (scalar52_to_nat(
            &ab,
        ) * scalar52_to_nat(&constants::RR)) % group_order());

        proof {
            // 1. Prove RR ≡ R² (mod L)
            lemma_rr_equals_spec();

            // 2. Apply cancellation lemma to get: result ≡ ab*R (mod L)
            //    Combined with ab*R ≡ a*b (mod L), we get result ≡ a*b (mod L)
            lemma_cancel_mul_montgomery_mod(
                scalar52_to_nat(&result),
                scalar52_to_nat(&ab),
                scalar52_to_nat(&constants::RR),
            );

            // 3. Since result < group_order (from montgomery_reduce), result % L == result
            lemma_small_mod(scalar52_to_nat(&result), group_order());
        }

        result
    }

    /// Compute `a^2` (mod l)
    ///
    /// # Preconditions
    /// - Input must be canonical (bounded and < L) for verified first reduction
    #[inline(never)]
    #[allow(dead_code)]  // XXX we don't expose square() via the Scalar API
    pub fn square(&self) -> (result: Scalar52)
        requires
    // Must be canonical for montgomery_reduce's canonical_bound

            is_canonical_scalar52(self),
        ensures
            scalar52_to_nat(&result) == (scalar52_to_nat(self) * scalar52_to_nat(self))
                % group_order(),
    {
        proof {
            lemma_rr_limbs_bounded();
            // Derive limb_prod_bounded_u128 for square_internal's precondition
            lemma_limbs_bounded_implies_prod_bounded(self, self);
        }

        /* ORIGINAL CODE:
        let aa = Scalar52::montgomery_reduce(&Scalar52::square_internal(self));
        */
        let z1 = Scalar52::square_internal(self);
        proof {
            // Establish montgomery_reduce's preconditions for first call
            lemma_bounded_product_satisfies_input_bounds(self, self, &z1);
            // self is canonical, so product satisfies canonical_bound
            lemma_canonical_product_satisfies_canonical_bound(self, self, &z1);
        }
        let aa = Scalar52::montgomery_reduce(&z1);

        assert((scalar52_to_nat(&aa) * montgomery_radix()) % group_order() == (scalar52_to_nat(self)
            * scalar52_to_nat(self)) % group_order());

        // aa has limbs_bounded from montgomery_reduce's postcondition
        proof {
            lemma_limbs_bounded_implies_prod_bounded(&aa, &constants::RR);
        }

        /* ORIGINAL CODE:
        let result = Scalar52::montgomery_reduce(&Scalar52::mul_internal(&aa, &constants::RR));
        */
        let z2 = Scalar52::mul_internal(&aa, &constants::RR);
        proof {
            // Establish montgomery_reduce's preconditions for second call
            lemma_bounded_product_satisfies_input_bounds(&aa, &constants::RR, &z2);
            // RR is canonical (< L), so product satisfies canonical_bound
            lemma_rr_equals_spec();
            lemma_canonical_product_satisfies_canonical_bound(&aa, &constants::RR, &z2);
        }
        let result = Scalar52::montgomery_reduce(&z2);
        // is_canonical_scalar52(&result) follows from montgomery_reduce postcondition

        assert((scalar52_to_nat(&result) * montgomery_radix()) % group_order() == (scalar52_to_nat(
            &aa,
        ) * scalar52_to_nat(&constants::RR)) % group_order());

        proof {
            // 1. prove (scalar52_to_nat(&constants::RR) % group_order() == (montgomery_radix()*montgomery_radix()) % group_order()
            lemma_rr_equals_spec();

            // 2. Reduce to (scalar52_to_nat(&result)) % group_order() == (scalar52_to_nat(self) * scalar52_to_nat(self)) % group_order()
            lemma_cancel_mul_montgomery_mod(
                scalar52_to_nat(&result),
                scalar52_to_nat(&aa),
                scalar52_to_nat(&constants::RR),
            );

            // 3. allows us to assert (scalar52_to_nat(&result)) % group_order() == (scalar52_to_nat(&result))
            //  true from montgomery_reduce postcondition
            lemma_small_mod((scalar52_to_nat(&result)), group_order())
        }

        assert((scalar52_to_nat(&result)) % group_order() == (scalar52_to_nat(&aa)
            * montgomery_radix()) % group_order());

        result
    }

    /// Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^260
    ///
    /// # Preconditions
    /// - Both inputs must have `limbs_bounded` (ensures `input_bounds` for the product)
    /// - At least one input must be canonical for `montgomery_reduce`'s `canonical_bound`
    #[inline(never)]
    pub fn montgomery_mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            // At least one input must be canonical for montgomery_reduce's canonical_bound
            is_canonical_scalar52(a) || is_canonical_scalar52(b),
        ensures
            limb_prod_bounded_u128(result.limbs, result.limbs, 5),
            (scalar52_to_nat(&result) * montgomery_radix()) % group_order() == (scalar52_to_nat(&a)
                * scalar52_to_nat(&b)) % group_order(),
            // Result is canonical from montgomery_reduce
            is_canonical_scalar52(&result),
    {
        proof {
            // Derive limb_prod_bounded_u128 for mul_internal's precondition
            lemma_limbs_bounded_implies_prod_bounded(a, b);
        }
        /* ORIGINAL CODE:
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b))
        */
        let z = Scalar52::mul_internal(a, b);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(a, b, &z);
            // At least one input is canonical, establish canonical_bound
            if is_canonical_scalar52(b) {
                lemma_canonical_product_satisfies_canonical_bound(a, b, &z);
            } else {
                // a must be canonical since one of them is
                lemma_spec_mul_internal_commutative(a, b);
                lemma_canonical_product_satisfies_canonical_bound(b, a, &z);
            }
        }
        let result = Scalar52::montgomery_reduce(&z);
        proof {
            // Derive limb_prod_bounded_u128 from limbs_bounded
            lemma_limbs_bounded_implies_prod_bounded(&result, &result);
        }
        result
    }

    /// Compute `(a^2) / R` (mod l) in Montgomery form, where R is the Montgomery modulus 2^260
    ///
    /// # Preconditions
    /// - Input must be canonical for `montgomery_reduce`'s `canonical_bound`
    ///
    /// Why `limbs_bounded` (part of canonical): `square_internal(self)[0] = self.limbs[0]²`,
    /// and we need `self.limbs[0]² < 2^104`, so `self.limbs[0] < 2^52`.
    #[inline(never)]
    pub fn montgomery_square(&self) -> (result: Scalar52)
        requires
    // Must be canonical for montgomery_reduce's canonical_bound

            is_canonical_scalar52(self),
        ensures
            limb_prod_bounded_u128(result.limbs, result.limbs, 5),
            (scalar52_to_nat(&result) * montgomery_radix()) % group_order() == (scalar52_to_nat(
                self,
            ) * scalar52_to_nat(self)) % group_order(),
            // Result is canonical from montgomery_reduce
            is_canonical_scalar52(&result),
    {
        proof {
            // Derive limb_prod_bounded_u128 for square_internal's precondition
            lemma_limbs_bounded_implies_prod_bounded(self, self);
        }
        /* ORIGINAL CODE:
        Scalar52::montgomery_reduce(&Scalar52::square_internal(self))
        */
        let z = Scalar52::square_internal(self);
        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(self, self, &z);
            // self is canonical, so product satisfies canonical_bound
            lemma_canonical_product_satisfies_canonical_bound(self, self, &z);
        }
        let result = Scalar52::montgomery_reduce(&z);
        proof {
            // Derive limb_prod_bounded_u128 from limbs_bounded
            lemma_limbs_bounded_implies_prod_bounded(&result, &result);
        }
        result
    }

    /// Puts a Scalar52 in to Montgomery form, i.e. computes `a*R (mod l)`
    ///
    /// # Precondition
    /// Requires `limbs_bounded(self)` because `montgomery_mul` (called internally) now
    /// requires both inputs to have `limbs_bounded`. This is safe because all `Scalar52`
    /// values in practice have `limbs_bounded` (from `unpack()` or other Montgomery ops).
    #[inline(never)]
    pub fn as_montgomery(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            limb_prod_bounded_u128(result.limbs, result.limbs, 5),
            #[trigger] (scalar52_to_nat(&result) % group_order()) == #[trigger] ((scalar52_to_nat(
                self,
            ) * montgomery_radix()) % group_order()),
            // Result is canonical because RR is canonical
            is_canonical_scalar52(&result),
    {
        proof {
            lemma_rr_limbs_bounded();
            // RR is canonical (< group_order), so montgomery_mul's canonicity postcondition applies
            lemma_rr_equals_spec();
            assert(group_order() > 0);
        }
        let result = Scalar52::montgomery_mul(self, &constants::RR);
        proof {
            // From montgomery_mul's ensures clause:
            // (scalar52_to_nat(&result) * montgomery_radix()) % group_order() ==
            // (scalar52_to_nat(self) * scalar52_to_nat(&constants::RR)) % group_order()
            // Prove that RR = R² mod L
            lemma_rr_equals_radix_squared();

            // Now we can apply the cancellation lemma
            lemma_cancel_mul_montgomery_mod(
                scalar52_to_nat(&result),
                scalar52_to_nat(self),
                scalar52_to_nat(&constants::RR),
            );
        }
        result
    }

    /// Takes a Scalar52 out of Montgomery form, i.e. computes `a/R (mod l)`
    ///
    #[allow(clippy::wrong_self_convention)]
    #[inline(never)]
    pub fn from_montgomery(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            (scalar52_to_nat(&result) * montgomery_radix()) % group_order() == scalar52_to_nat(self)
                % group_order(),
            // Result is canonical (< group_order). This follows from montgomery_reduce's postcondition
            is_canonical_scalar52(&result),
    {
        let mut limbs = [0u128;9];
        #[allow(clippy::needless_range_loop)]
        for i in 0..5
            invariant
                forall|j: int| #![auto] 0 <= j < i ==> limbs[j] == self.limbs[j] as u128,
                forall|j: int| #![auto] i <= j < 9 ==> limbs[j] == 0,
        {
            limbs[i] = self.limbs[i] as u128;
        }
        proof {
            // Derive limb_prod_bounded_u128 for lemma_from_montgomery_is_product_with_one's precondition
            lemma_limbs_bounded_implies_prod_bounded(self, self);
            lemma_from_montgomery_is_product_with_one(self, &limbs);
            // Establish montgomery_reduce's preconditions
            lemma_identity_array_satisfies_input_bounds(self, &limbs);
            lemma_identity_array_satisfies_canonical_bound(self, &limbs);
        }
        let result = Scalar52::montgomery_reduce(&limbs);
        // is_canonical_scalar52(&result) follows from montgomery_reduce postcondition
        // (canonical_bound holds, so postcondition gives is_canonical_scalar52)
        proof {
            lemma_from_montgomery_limbs_conversion(&limbs, &self.limbs);
        }
        result
    }
}

} // verus!
#[cfg(test)]
pub mod test {
    use super::*;
    use num_bigint::BigUint;
    use num_traits::{One, Zero};
    use proptest::prelude::*;

    // Executable versions of spec functions to match the spec as closely as possible

    /// Convert 5 limbs (52-bit each) to a BigUint
    /// Matches the spec: scalar52_to_nat(&[u64; 5])
    pub fn to_nat_exec(limbs: &[u64; 5]) -> BigUint {
        let mut result = BigUint::zero();
        let radix = BigUint::from(1u128 << 52);
        for i in (0..5).rev() {
            result = result * &radix + BigUint::from(limbs[i]);
        }
        result
    }

    /// The group order L
    /// Matches the spec: group_order()
    pub fn group_order_exec() -> BigUint {
        // L = 2^252 + 27742317777372353535851937790883648493
        let base = BigUint::one() << 252;
        let offset = BigUint::parse_bytes(b"27742317777372353535851937790883648493", 10).unwrap();
        base + offset
    }

    /// Check if all limbs are bounded by 2^52
    /// Matches the spec: limbs_bounded(&Scalar52)
    pub fn limbs_bounded_exec(s: &Scalar52) -> bool {
        s.limbs.iter().all(|&limb| limb < (1u64 << 52))
    }

    /// Convert a 32-byte array to a BigUint
    /// Matches the spec: u8_32_as_nat(&[u8; 32])
    pub fn u8_32_as_nat_exec(bytes: &[u8; 32]) -> BigUint {
        let mut result = BigUint::zero();
        let radix = BigUint::from(256u32);
        for i in (0..32).rev() {
            result = result * &radix + BigUint::from(bytes[i]);
        }
        result
    }

    /// Test case demonstrating that from_bytes does NOT ensure canonicality.
    /// i.e. the postcondition `scalar52_to_nat(&s) < group_order()` may not hold
    ///
    /// The minimal failing case found by proptest: bytes[31] = 17 (all others 0)
    /// represents 17 * 2^248, which is >= L, so the result is not canonical.
    #[test]
    fn from_bytes_non_canonical_example() {
        let bytes: [u8; 32] = [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 17,
        ];

        let s = Scalar52::from_bytes(&bytes);

        let result_nat = to_nat_exec(&s.limbs);
        let l = group_order_exec();

        // OLD Postcondition 3: scalar52_to_nat(&s) < group_order() - DOES NOT HOLD
        assert!(
            &result_nat >= &l,
            "This example demonstrates result >= L: {} >= {}",
            result_nat,
            l
        );
    }

    proptest! {
        #![proptest_config(proptest::test_runner::Config::with_cases(1000000))]

        /// Test from_bytes spec: for any 32-byte array, verify both postconditions
        /// 1. u8_32_as_nat(bytes) == scalar52_to_nat(&s)
        /// 2. limbs_bounded(&s)
        #[test]
        fn prop_from_bytes(bytes in prop::array::uniform32(any::<u8>())) {
            // Call from_bytes
            let s = Scalar52::from_bytes(&bytes);

            // Convert to BigUint using executable spec functions
            let bytes_nat = u8_32_as_nat_exec(&bytes);
            let result_nat = to_nat_exec(&s.limbs);

            // Postcondition 1: u8_32_as_nat(bytes) == scalar52_to_nat(&s)
            prop_assert_eq!(bytes_nat, result_nat,
                "from_bytes spec violated: u8_32_as_nat(bytes) != scalar52_to_nat(&s)");

            // Postcondition 2: limbs_bounded(&s)
            prop_assert!(limbs_bounded_exec(&s),
                "from_bytes spec violated: result limbs not bounded by 2^52");
        }
    }

    /// Test that our refactoring of part1 is equivalent to the original wrapping_mul version.
    ///
    /// ORIGINAL CODE:
    ///   let p = (sum as u64).wrapping_mul(LFACTOR) & MASK52;
    ///
    /// REFACTORED CODE (to avoid Verus wrapping_mul limitation):
    ///   let sum_low52 = (sum as u64) & MASK52;
    ///   let product = (sum_low52 as u128) * (LFACTOR as u128);
    ///   let p = (product as u64) & MASK52;
    ///
    /// This test verifies:
    ///   (a.wrapping_mul(b)) & MASK52 == ((a & MASK52) * b) & MASK52
    ///
    /// for all relevant values of `sum` that part1 might receive.
    #[test]
    fn test_part1_wrapping_mul_equivalence() {
        use proptest::prelude::*;
        use proptest::test_runner::{Config, TestRunner};

        let mask52: u64 = (1u64 << 52) - 1;
        let lfactor: u64 = 0x51da312547e1b;

        let mut runner = TestRunner::new(Config {
            cases: 10000,
            ..Config::default()
        });

        runner
            .run(
                &(0u128..(1u128 << 108)), // sum < 2^108 (part1's precondition)
                |sum| {
                    // ORIGINAL: using wrapping_mul
                    let p_original = (sum as u64).wrapping_mul(lfactor) & mask52;

                    // REFACTORED: extract low 52 bits first, multiply in u128
                    let sum_low52 = (sum as u64) & mask52;
                    let product = (sum_low52 as u128) * (lfactor as u128);
                    let p_refactored = (product as u64) & mask52;

                    // They must be equal
                    prop_assert_eq!(
                        p_original,
                        p_refactored,
                        "Mismatch for sum = {}: original = {}, refactored = {}",
                        sum,
                        p_original,
                        p_refactored
                    );

                    Ok(())
                },
            )
            .expect("Property test failed");
    }

    /// Test that wrapping_mul followed by masking equals mod 2^52
    ///
    /// This verifies: (a.wrapping_mul(b)) & MASK52 == (a * b) mod 2^52
    #[test]
    fn test_wrapping_mul_mask_equals_mod() {
        use proptest::prelude::*;
        use proptest::test_runner::{Config, TestRunner};

        let mask52: u64 = (1u64 << 52) - 1;
        let mod_52: u128 = 1u128 << 52;

        let mut runner = TestRunner::new(Config {
            cases: 10000,
            ..Config::default()
        });

        runner
            .run(&(any::<u64>(), any::<u64>()), |(a, b)| {
                // Using wrapping_mul and mask
                let result_wrapping = a.wrapping_mul(b) & mask52;

                // Using full multiplication and mod
                let product_full = (a as u128) * (b as u128);
                let result_mod = (product_full % mod_52) as u64;

                prop_assert_eq!(
                    result_wrapping,
                    result_mod,
                    "wrapping_mul & mask != mod for a={}, b={}: {} != {}",
                    a,
                    b,
                    result_wrapping,
                    result_mod
                );

                Ok(())
            })
            .expect("Property test failed");
    }
}
// #[cfg(test)]
// mod test {
//     use super::*;
//     /// Note: x is 2^253-1 which is slightly larger than the largest scalar produced by
//     /// this implementation (l-1), and should show there are no overflows for valid scalars
//     ///
//     /// x = 14474011154664524427946373126085988481658748083205070504932198000989141204991
//     /// x = 7237005577332262213973186563042994240801631723825162898930247062703686954002 mod l
//     /// x = 3057150787695215392275360544382990118917283750546154083604586903220563173085*R mod l in Montgomery form
//     pub static X: Scalar52 = Scalar52 {
//         limbs: [
//             0x000fffffffffffff,
//             0x000fffffffffffff,
//             0x000fffffffffffff,
//             0x000fffffffffffff,
//             0x00001fffffffffff,
//         ],
//     };
//     /// x^2 = 3078544782642840487852506753550082162405942681916160040940637093560259278169 mod l
//     pub static XX: Scalar52 = Scalar52 {
//         limbs: [
//             0x0001668020217559,
//             0x000531640ffd0ec0,
//             0x00085fd6f9f38a31,
//             0x000c268f73bb1cf4,
//             0x000006ce65046df0,
//         ],
//     };
//     /// x^2 = 4413052134910308800482070043710297189082115023966588301924965890668401540959*R mod l in Montgomery form
//     pub static XX_MONT: Scalar52 = Scalar52 {
//         limbs: [
//             0x000c754eea569a5c,
//             0x00063b6ed36cb215,
//             0x0008ffa36bf25886,
//             0x000e9183614e7543,
//             0x0000061db6c6f26f,
//         ],
//     };
//     /// y = 6145104759870991071742105800796537629880401874866217824609283457819451087098
//     pub static Y: Scalar52 = Scalar52 {
//         limbs: [
//             0x000b75071e1458fa,
//             0x000bf9d75e1ecdac,
//             0x000433d2baf0672b,
//             0x0005fffcc11fad13,
//             0x00000d96018bb825,
//         ],
//     };
//     /// x*y = 36752150652102274958925982391442301741 mod l
//     pub static XY: Scalar52 = Scalar52 {
//         limbs: [
//             0x000ee6d76ba7632d,
//             0x000ed50d71d84e02,
//             0x00000000001ba634,
//             0x0000000000000000,
//             0x0000000000000000,
//         ],
//     };
//     /// x*y = 658448296334113745583381664921721413881518248721417041768778176391714104386*R mod l in Montgomery form
//     pub static XY_MONT: Scalar52 = Scalar52 {
//         limbs: [
//             0x0006d52bf200cfd5,
//             0x00033fb1d7021570,
//             0x000f201bc07139d8,
//             0x0001267e3e49169e,
//             0x000007b839c00268,
//         ],
//     };
//     /// a = 2351415481556538453565687241199399922945659411799870114962672658845158063753
//     pub static A: Scalar52 = Scalar52 {
//         limbs: [
//             0x0005236c07b3be89,
//             0x0001bc3d2a67c0c4,
//             0x000a4aa782aae3ee,
//             0x0006b3f6e4fec4c4,
//             0x00000532da9fab8c,
//         ],
//     };
//     /// b = 4885590095775723760407499321843594317911456947580037491039278279440296187236
//     pub static B: Scalar52 = Scalar52 {
//         limbs: [
//             0x000d3fae55421564,
//             0x000c2df24f65a4bc,
//             0x0005b5587d69fb0b,
//             0x00094c091b013b3b,
//             0x00000acd25605473,
//         ],
//     };
//     /// a+b = 0
//     /// a-b = 4702830963113076907131374482398799845891318823599740229925345317690316127506
//     pub static AB: Scalar52 = Scalar52 {
//         limbs: [
//             0x000a46d80f677d12,
//             0x0003787a54cf8188,
//             0x0004954f0555c7dc,
//             0x000d67edc9fd8989,
//             0x00000a65b53f5718,
//         ],
//     };
//     // c = (2^512 - 1) % l = 1627715501170711445284395025044413883736156588369414752970002579683115011840
//     pub static C: Scalar52 = Scalar52 {
//         limbs: [
//             0x000611e3449c0f00,
//             0x000a768859347a40,
//             0x0007f5be65d00e1b,
//             0x0009a3dceec73d21,
//             0x00000399411b7c30,
//         ],
//     };
//     #[test]
//     fn mul_max() {
//         let res = Scalar52::mul(&X, &X);
//         for i in 0..5 {
//             assert!(res[i] == XX[i]);
//         }
//     }
//     #[test]
//     fn square_max() {
//         let res = X.square();
//         for i in 0..5 {
//             assert!(res[i] == XX[i]);
//         }
//     }
//     #[test]
//     fn montgomery_mul_max() {
//         let res = Scalar52::montgomery_mul(&X, &X);
//         for i in 0..5 {
//             assert!(res[i] == XX_MONT[i]);
//         }
//     }
//     #[test]
//     fn montgomery_square_max() {
//         let res = X.montgomery_square();
//         for i in 0..5 {
//             assert!(res[i] == XX_MONT[i]);
//         }
//     }
//     #[test]
//     fn mul() {
//         let res = Scalar52::mul(&X, &Y);
//         for i in 0..5 {
//             assert!(res[i] == XY[i]);
//         }
//     }
//     #[test]
//     fn montgomery_mul() {
//         let res = Scalar52::montgomery_mul(&X, &Y);
//         for i in 0..5 {
//             assert!(res[i] == XY_MONT[i]);
//         }
//     }
//     #[test]
//     fn add() {
//         let res = Scalar52::add(&A, &B);
//         let zero = Scalar52::ZERO;
//         for i in 0..5 {
//             assert!(res[i] == zero[i]);
//         }
//     }
//     #[test]
//     fn sub() {
//         let res = Scalar52::sub(&A, &B);
//         for i in 0..5 {
//             assert!(res[i] == AB[i]);
//         }
//     }
//     #[test]
//     fn from_bytes_wide() {
//         let bignum = [255u8; 64]; // 2^512 - 1
//         let reduced = Scalar52::from_bytes_wide(&bignum);
//         for i in 0..5 {
//             assert!(reduced[i] == C[i]);
//         }
//     }
// }
