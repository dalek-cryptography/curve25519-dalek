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
use crate::lemmas::common_lemmas::bit_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::shift_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::core_lemmas::*;
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
#[cfg(verus_keep_ghost)]
use crate::lemmas::scalar_montgomery_lemmas::lemma_from_montgomery_is_product_with_one;
#[allow(unused_imports)]
use crate::specs::scalar_specs_u64::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_extra::*;
#[cfg(verus_keep_ghost)]
use crate::specs::core_specs::spec_load8_at;

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
    requires
        x < (1u64 << 52),
        y < (1u64 << 52),
    ensures
        z < (1u128 << 104),
        z == x * y,
{
    proof {
        lemma_52_52(x, y);
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
            bytes_to_nat(bytes) == to_nat(&s.limbs),
            limbs_bounded(&s),
    {
        let mut words = [0u64;4];
        for i in 0..4
            invariant
                0 <= i <= 4,
                forall|i2: int| i <= i2 < 4 ==> words[i2] == 0,
                forall|i2: int|
                    0 <= i2 < i ==> (words[i2] == bytes_seq_to_nat_clear_aux(
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
                    words[i as int] == bytes_seq_to_nat_clear_aux(
                        Seq::new(8, |j2: int| bytes[i as int * 8 + j2]),
                        j as nat,
                    ),
                    forall|i2: int|
                        0 <= i2 < i ==> ((words[i2] as nat) == bytes_seq_to_nat_clear_aux(
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
            assert(bytes_to_nat(bytes) == to_nat(&s.limbs));
        }

        s
    }

    /// Reduce a 64 byte / 512 bit scalar mod l
    #[rustfmt::skip]  // keep alignment of lo[*] and hi[*] calculations
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> (s: Scalar52)
        ensures
            limbs_bounded(&s),
            to_nat(&s.limbs) % group_order() == bytes_wide_to_nat(bytes) % group_order(),
            // VERIFICATION NOTE: Result is canonical
            to_nat(&s.limbs) < group_order(),
    {
        let ghost wide_input = bytes_wide_to_nat(bytes);

        // Stage 1 assumption: the byte-to-word packing yields the expected little-endian value.
        let mut words = [0u64;8];
        for i in 0..8
            invariant
                forall|k: int|
                    #![auto]
                    0 <= k < i ==> words@[k] as nat == word_from_bytes(bytes, k),
                words_from_bytes_to_nat(bytes, i as int) + bytes_wide_to_nat_rec(
                    bytes,
                    (i as int) * 8,
                ) == bytes_wide_to_nat(bytes),
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
                // spec_load8_at uses pow2(k*8) * byte, word_from_bytes uses byte * pow2(k*8)
                assert(spec_load8_at(bytes, (i_int * 8) as usize) == word_from_bytes(bytes, i_int))
                    by {
                    broadcast use lemma_mul_is_commutative;

                };
                assert forall|k: int| i + 1 <= k < 8 implies words@[k] == 0 by {
                    assert(words@[#[trigger] k] == 0);
                };
                reveal_with_fuel(words_from_bytes_to_nat, 9);
                assert(bytes_wide_to_nat_rec(bytes, i_int * 8) == word_from_bytes(bytes, i_int)
                    * pow2((i_int * 64) as nat) + bytes_wide_to_nat_rec(bytes, (i_int + 1) * 8))
                    by {
                    lemma_bytes_wide_to_nat_rec_matches_word_partial(bytes, i_int, 8);
                    broadcast use lemma_mul_is_commutative;

                };
            }
        }

        proof {
            lemma_words_to_nat_gen_u64_prefix_matches_bytes(&words, bytes, 8);
        }

        // Stage 2 word bounds: every assembled chunk fits in 64 bits.
        assert forall|k: int| 0 <= k < 8 implies words[k] < pow2(64) by {
            let idx = (k * 8) as usize;
            lemma_spec_load8_at_fits_u64(bytes, idx);
            // spec_load8_at uses pow2(k*8) * byte, word_from_bytes uses byte * pow2(k*8)
            assert(spec_load8_at(bytes, idx) == word_from_bytes(bytes, k)) by {
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
        assert(to_nat(&hi_raw.limbs) == high_expr);

        // Assumption [L2]: The 512-bit input splits as `pow2(260) * high_expr + low_expr`.
        // WideSum-Expansion: converting the eight 64-bit words back into a natural number matches the explicit little-endian sum of their weighted contributions.
        proof {
            lemma_words_from_bytes_to_nat_wide(bytes);
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
        assert(to_nat(&lo_raw.limbs) == wide_input % pow2(260)) by {
            lemma_mod_multiples_vanish(high_expr as int, low_expr as int, pow2_260 as int);
            lemma_small_mod(low_expr, pow2_260);
        };
        // Assumption: The upper bits of the wide input, divided by 2^260, match the natural value encoded by `hi_raw`.
        assert(to_nat(&hi_raw.limbs) == wide_input / pow2(260)) by {
            lemma_fundamental_div_mod_converse(
                wide_input as int,
                pow2_260 as int,
                high_expr as int,
                low_expr as int,
            );
        };
        // Recombining quotient and remainder at the 2^260 radix recreates the original wide input.
        assert(high_expr < pow2(252)) by {
            lemma_words_to_nat_gen_u64_bound_le(&words, 8);
            lemma_pow2_adds(260, 252);
            assert(pow2_260 * pow2(252) == pow2(512));
            lemma_multiply_divide_lt(wide_input as int, pow2_260 as int, pow2(252) as int);
        };

        // Stage 4 assumption: Montgomery reductions behave as expected for these operands.
        proof {
            lemma_r_limbs_bounded();  // had to write this one manually due to crashes
            lemma_rr_limbs_bounded();
        }

        let lo_product = Scalar52::mul_internal(&lo, &constants::R);
        lo = Scalar52::montgomery_reduce(&lo_product);  // (lo * R) / R = lo
        let hi_product = Scalar52::mul_internal(&hi, &constants::RR);
        hi = Scalar52::montgomery_reduce(&hi_product);  // (hi * R^2) / R = hi * R

        proof {
            let ghost lo_before_nat = to_nat(&lo_raw.limbs);
            let ghost lo_after_nat = to_nat(&lo.limbs);
            let ghost r_nat = to_nat(&constants::R.limbs);
            lemma_r_equals_spec(constants::R);
            // lo: multiply by R, reduce => extra_factor = 1
            lemma_montgomery_reduce_cancels_r(lo_after_nat, lo_before_nat, r_nat, 1);

            let ghost hi_before_nat = to_nat(&hi_raw.limbs);
            let ghost hi_after_nat = to_nat(&hi.limbs);
            let ghost rr_nat = to_nat(&constants::RR.limbs);
            lemma_rr_equals_spec(constants::RR);
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
                to_nat(&result.limbs),
                to_nat(&hi.limbs),
                to_nat(&lo.limbs),
                to_nat(&hi_raw.limbs),
                to_nat(&lo_raw.limbs),
                wide_input,
            );

            lemma_cancel_mul_pow2_mod(to_nat(&result.limbs), wide_input, montgomery_radix());
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
            bytes_to_nat(&s) == to_nat(&self.limbs) % pow2(256),
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
            to_nat(&a.limbs) < group_order(),
            to_nat(&b.limbs) < group_order(),
        ensures
            to_nat(&s.limbs) == (to_nat(&a.limbs) + to_nat(&b.limbs)) % group_order(),
            // VERIFICATION NOTE: Result is canonical
            to_nat(&s.limbs) < group_order(),
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
        assert(group_order() > to_nat(&sum.limbs) - group_order() >= -group_order());
        proof {
            lemma_l_equals_group_order();
        }
        proof {
            lemma_mod_sub_multiples_vanish(to_nat(&sum.limbs) as int, group_order() as int);
        }
        Scalar52::sub(&sum, &constants::L)
    }

    // VERIFICATION NOTE: refactored sub function from Dalek upstream
    #[allow(dead_code)]
    pub fn sub_new(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            -group_order() <= to_nat(&a.limbs) - to_nat(&b.limbs) < group_order(),
        ensures
            to_nat(&s.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int),
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
            to_nat(&old(self).limbs) + group_order() < pow2(260),
        ensures
    // The mathematical value modulo group_order doesn't change (since L = group_order)

            to_nat(&self.limbs) % group_order() == to_nat(&old(self).limbs) % group_order(),
            // VERIFICATION NOTE: expression below unsupported by Verus
            //limbs_bounded(&self),
            // Meaning of conditional addition
            super::subtle_assumes::choice_is_true(condition) ==> to_nat(&self.limbs) == to_nat(
                &old(self).limbs,
            ) + group_order(),
            !super::subtle_assumes::choice_is_true(condition) ==> to_nat(&self.limbs) == to_nat(
                &old(self).limbs,
            ),
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
            assume(to_nat(&self.limbs) % group_order() == to_nat(&old(self).limbs) % group_order());
            //   assume(limbs_bounded(&self));
            assume(super::subtle_assumes::choice_is_true(condition) ==> to_nat(&self.limbs)
                == to_nat(&old(self).limbs) + group_order());
            assume(!super::subtle_assumes::choice_is_true(condition) ==> to_nat(&self.limbs)
                == to_nat(&old(self).limbs));
        }

        carry
    }

    /// Compute `a - b` (mod l)
    pub fn sub(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
            // Without the following condition, all we can prove is something like:
            // to_nat(&a.limbs) >= to_nat(&b.limbs) ==> to_nat(&s.limbs) == to_nat(&a.limbs) - to_nat(&b.limbs),
            // to_nat(&a.limbs) < to_nat(&b.limbs) ==> to_nat(&s.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs) + pow2(260) + group_order()) % (pow2(260) as int),
            // In the 2nd case, `sub` doesn't always do subtraction mod group_order
            -group_order() <= to_nat(&a.limbs) - to_nat(&b.limbs) < group_order(),
        ensures
            to_nat(&s.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int),
            limbs_bounded(&s),
            // VERIFICATION NOTE: Result is in canonical form
            to_nat(&s.limbs) < group_order(),
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
                limbs_bounded(a),
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
            lemma_sub_correct_after_loops(difference, carry, a, b, difference_after_loop1, borrow);
        }
        difference
    }

    /// Compute `a * b`
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of z[*] calculations
    pub(crate) fn mul_internal(a: &Scalar52, b: &Scalar52) -> (z: [u128; 9])
        requires
            limbs_bounded(a),
            limbs_bounded(b),
        ensures
            slice128_to_nat(&z) == to_nat(&a.limbs) * to_nat(&b.limbs),
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
            limbs_bounded(a),
        ensures
            slice128_to_nat(&z) == to_nat(&a.limbs) * to_nat(&a.limbs),
            spec_mul_internal(a, a) == z,
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
        }

        z
    }

    /// Compute `limbs/R` (mod l), where R is the Montgomery modulus 2^260
    #[inline(always)]
    #[rustfmt::skip]  // keep alignment of n* and r* calculations
    pub(crate) fn montgomery_reduce(limbs: &[u128; 9]) -> (result:
        Scalar52)
    // If the input is the product of 2 bounded scalars, we get 2 postconditions.
    // If the 2nd scalar is also canonical, we unlock a 3rd postcondition.
    // Not all calling code needs the 3rd postcondition.
    // Note: This spec is not yet confirmed because the function is unproved.
    // The spec is checked by prop_montgomery_reduce_two_bounded and prop_montgomery_reduce_one_canonical.
    // If you edit this spec, please update the proptests.
    // Once this function and all deps are proved, you can remove those proptests,
    // and montgomery_reduce_non_canonical_product_fails_postcondition,
    // and test_canonical_scalar_generator (if it's then unused)

        ensures
            (exists|bounded1: &Scalar52, bounded2: &Scalar52|
                limbs_bounded(bounded1) && limbs_bounded(bounded2) && spec_mul_internal(
                    bounded1,
                    bounded2,
                ) == limbs) ==> ((to_nat(&result.limbs) * montgomery_radix()) % group_order()
                == slice128_to_nat(limbs) % group_order() && limbs_bounded(&result)),
            (exists|bounded: &Scalar52, canonical: &Scalar52|
                limbs_bounded(bounded) && limbs_bounded(canonical) && to_nat(&canonical.limbs)
                    < group_order() && spec_mul_internal(bounded, canonical) == limbs) ==> to_nat(
                &result.limbs,
            ) < group_order(),
    {
        assume(false);  // TODO: Add proofs

        // note: l[3] is zero, so its multiples can be skipped
        let l = &constants::L;

        // the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R
        let (carry, n0) = Self::part1(limbs[0]);
        let (carry, n1) = Self::part1(carry + limbs[1] + m(n0, l.limbs[1]));
        let (carry, n2) = Self::part1(carry + limbs[2] + m(n0, l.limbs[2]) + m(n1, l.limbs[1]));
        let (carry, n3) = Self::part1(carry + limbs[3] + m(n1, l.limbs[2]) + m(n2, l.limbs[1]));
        let (carry, n4) = Self::part1(
            carry + limbs[4] + m(n0, l.limbs[4]) + m(n2, l.limbs[2]) + m(n3, l.limbs[1]),
        );

        // limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result
        let (carry, r0) = Self::part2(
            carry + limbs[5] + m(n1, l.limbs[4]) + m(n3, l.limbs[2]) + m(n4, l.limbs[1]),
        );
        let (carry, r1) = Self::part2(carry + limbs[6] + m(n2, l.limbs[4]) + m(n4, l.limbs[2]));
        let (carry, r2) = Self::part2(carry + limbs[7] + m(n3, l.limbs[4]));
        let (carry, r3) = Self::part2(carry + limbs[8] + m(n4, l.limbs[4]));
        let r4 = carry as u64;

        // result may be >= l, so attempt to subtract l
        Scalar52::sub(&Scalar52 { limbs: [r0, r1, r2, r3, r4] }, l)
    }

    /// Helper function for Montgomery reduction
    /// VER NOTE: spec validation needed concurrent with proof for montgomery_reduce
    #[inline(always)]
    fn part1(sum: u128) -> (res: (u128, u64))
        ensures
            ({
                let carry = res.0;
                let p = res.1;
                &&& p < (1u64 << 52)  // VER NOTE: p is bounded by 52 bits
                // VER NOTE: The sum plus p*L[0] equals carry shifted left by 52 bits (i.e., divisible by 2^52)
                &&& sum + (p as u128) * (constants::L.limbs[0] as u128) == carry << 52
            }),
    {
        assert((1u64 << 52) > 1) by (bit_vector);
        assert((1u64 << 52) - 1 > 0);
        let p = (sum as u64).wrapping_mul(constants::LFACTOR) & ((1u64 << 52) - 1);
        proof {
            let piece1 = (sum as u64).wrapping_mul(constants::LFACTOR) as u64;
            let piece2 = ((1u64 << 52) - 1) as u64;
            assert(p == piece1 & piece2);
            assert(piece1 & piece2 < (1u64 << 52)) by (bit_vector)
                requires
                    piece2 == ((1u64 << 52) - 1),
            ;
        }
        assert(p < (1u64 << 52));
        assert(constants::L.limbs[0] == 0x0002631a5cf5d3ed);
        assert(0x0002631a5cf5d3ed < (1u64 << 52)) by (bit_vector);
        assert(constants::L.limbs[0] < (1u64 << 52));
        // Going to need a precondition on sum to ensure it's small enough
        // This bound may not be the right bound
        assume(sum + p * constants::L.limbs[0] < ((2 as u64) << 63));
        let carry = (sum + m(p, constants::L.limbs[0])) >> 52;
        // Is this actually true? Not sure that the right shift and left shift cancel.
        assume(sum + (p as u128) * (constants::L.limbs[0] as u128) == carry << 52);
        (carry, p)
    }

    /// Helper function for Montgomery reduction
    /// VER NOTE: spec validation needed concurrent with proof for montgomery_reduce
    #[inline(always)]
    fn part2(sum: u128) -> (res: (u128, u64))
        ensures
            ({
                let carry = res.0;
                let w = res.1;
                &&& w < (1u64
                    << 52)  // VER NOTE: w is bounded by 52 bits (lower limb)
                // VER NOTE: The sum equals w plus carry shifted left by 52 bits
                &&& sum == (w as u128) + (carry << 52)
            }),
    {
        proof { lemma_part2_bounds(sum) }
        let w = (sum as u64) & ((1u64 << 52) - 1);
        let carry = sum >> 52;
        (carry, w)
    }

    /// Compute `a * b` (mod l)
    #[inline(never)]
    pub fn mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
        ensures
            to_nat(&result.limbs) % group_order() == (to_nat(&a.limbs) * to_nat(&b.limbs))
                % group_order(),
            // VER NOTE: Result has bounded limbs from montgomery_reduce
            limbs_bounded(&result),
            // VER NOTE: Result is canonical from montgomery_reduce
            to_nat(&result.limbs) < group_order(),
    {
        proof {
            lemma_rr_limbs_bounded();
        }

        // First montgomery_reduce: ab*R ≡ a*b (mod L)
        let ab = Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b));

        assert((to_nat(&ab.limbs) * montgomery_radix()) % group_order() == (to_nat(&a.limbs)
            * to_nat(&b.limbs)) % group_order());

        // Second montgomery_reduce: result*R ≡ ab*RR (mod L)
        // Since RR < group_order, this triggers the stronger postcondition
        let result = Scalar52::montgomery_reduce(&Scalar52::mul_internal(&ab, &constants::RR));

        assert((to_nat(&result.limbs) * montgomery_radix()) % group_order() == (to_nat(&ab.limbs)
            * to_nat(&constants::RR.limbs)) % group_order());

        proof {
            // 1. Prove RR ≡ R² (mod L)
            lemma_rr_equals_spec(constants::RR);

            // 2. Apply cancellation lemma to get: result ≡ ab*R (mod L)
            //    Combined with ab*R ≡ a*b (mod L), we get result ≡ a*b (mod L)
            lemma_cancel_mul_montgomery_mod(
                to_nat(&result.limbs),
                to_nat(&ab.limbs),
                to_nat(&constants::RR.limbs),
            );

            // 3. Since result < group_order (from montgomery_reduce), result % L == result
            lemma_small_mod(to_nat(&result.limbs), group_order());
        }

        result
    }

    /// Compute `a^2` (mod l)
    #[inline(never)]
    #[allow(dead_code)]  // XXX we don't expose square() via the Scalar API
    pub fn square(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            to_nat(&result.limbs) == (to_nat(&self.limbs) * to_nat(&self.limbs)) % group_order(),
    {
        proof {
            lemma_rr_limbs_bounded();
        }

        // We only know limbs_bounded, so this triggers the weaker part of the
        // montgomery_reduce spec
        let aa = Scalar52::montgomery_reduce(&Scalar52::square_internal(self));

        assert((to_nat(&aa.limbs) * montgomery_radix()) % group_order() == (to_nat(&self.limbs)
            * to_nat(&self.limbs)) % group_order());

        // square_internal ensures
        // ensures
        //     slice128_to_nat(&z) == to_nat(&a.limbs) * to_nat(&a.limbs),

        // We know RR < group_order, so this triggers the stronger part of the
        // montgomery_reduce spec, which is what this function's postcondition wants
        let result = Scalar52::montgomery_reduce(&Scalar52::mul_internal(&aa, &constants::RR));

        assert((to_nat(&result.limbs) * montgomery_radix()) % group_order() == (to_nat(&aa.limbs)
            * to_nat(&constants::RR.limbs)) % group_order());

        proof {
            // 1. prove (to_nat(&constants::RR.limbs) % group_order() == (montgomery_radix()*montgomery_radix()) % group_order()
            lemma_rr_equals_spec(constants::RR);

            // 2. Reduce to (to_nat(&result.limbs)) % group_order() == (to_nat(&self.limbs) * to_nat(&self.limbs)) % group_order()
            lemma_cancel_mul_montgomery_mod(
                to_nat(&result.limbs),
                to_nat(&aa.limbs),
                to_nat(&constants::RR.limbs),
            );

            // 3. allows us to assert (to_nat(&result.limbs)) % group_order() == (to_nat(&result.limbs))
            //  true from montgomery_reduce postcondition
            lemma_small_mod((to_nat(&result.limbs)), group_order())
        }

        assert((to_nat(&result.limbs)) % group_order() == (to_nat(&aa.limbs) * montgomery_radix())
            % group_order());

        result
    }

    /// Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^260
    #[inline(never)]
    pub fn montgomery_mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
        requires
            limbs_bounded(a),
            limbs_bounded(b),
        ensures
            limbs_bounded(&result),
            (to_nat(&result.limbs) * montgomery_radix()) % group_order() == (to_nat(&a.limbs)
                * to_nat(&b.limbs)) % group_order(),
    {
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b))
    }

    /// Compute `(a^2) / R` (mod l) in Montgomery form, where R is the Montgomery modulus 2^260
    #[inline(never)]
    pub fn montgomery_square(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            limbs_bounded(&result),
            (to_nat(&result.limbs) * montgomery_radix()) % group_order() == (to_nat(&self.limbs)
                * to_nat(&self.limbs)) % group_order(),
    {
        Scalar52::montgomery_reduce(&Scalar52::square_internal(self))
    }

    /// Puts a Scalar52 in to Montgomery form, i.e. computes `a*R (mod l)`
    #[inline(never)]
    pub fn as_montgomery(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            limbs_bounded(&result),
            #[trigger] (to_nat(&result.limbs) % group_order()) == #[trigger] ((to_nat(&self.limbs)
                * montgomery_radix()) % group_order()),
    {
        proof {
            lemma_rr_limbs_bounded();
            assert(group_order() > 0);
        }
        let result = Scalar52::montgomery_mul(self, &constants::RR);
        proof {
            // From montgomery_mul's ensures clause:
            // (to_nat(&result.limbs) * montgomery_radix()) % group_order() ==
            // (to_nat(&self.limbs) * to_nat(&constants::RR.limbs)) % group_order()
            // Prove that RR = R² mod L
            lemma_rr_equals_radix_squared();

            // Now we can apply the cancellation lemma
            lemma_cancel_mul_montgomery_mod(
                to_nat(&result.limbs),
                to_nat(&self.limbs),
                to_nat(&constants::RR.limbs),
            );
        }
        result
    }

    /// Takes a Scalar52 out of Montgomery form, i.e. computes `a/R (mod l)`
    #[allow(clippy::wrong_self_convention)]
    #[inline(never)]
    pub fn from_montgomery(&self) -> (result: Scalar52)
        requires
            limbs_bounded(self),
        ensures
            limbs_bounded(&result),
            (to_nat(&result.limbs) * montgomery_radix()) % group_order() == to_nat(&self.limbs)
                % group_order(),
            // Result is canonical (< group_order). This follows from montgomery_reduce's postcondition
            to_nat(&result.limbs) < group_order(),
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
            lemma_from_montgomery_is_product_with_one(self, &limbs);
        }
        let result = Scalar52::montgomery_reduce(&limbs);
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
    /// Matches the spec: to_nat(&[u64; 5])
    pub fn to_nat_exec(limbs: &[u64; 5]) -> BigUint {
        let mut result = BigUint::zero();
        let radix = BigUint::from(1u128 << 52);
        for i in (0..5).rev() {
            result = result * &radix + BigUint::from(limbs[i]);
        }
        result
    }

    /// Convert 9 u128 limbs (52-bit each) to a BigUint
    /// Matches the spec: slice128_to_nat(&[u128; 9])
    pub fn slice128_to_nat_exec(limbs: &[u128; 9]) -> BigUint {
        let mut result = BigUint::zero();
        let radix = BigUint::from(1u128 << 52);
        for i in (0..9).rev() {
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

    /// Montgomery radix R = 2^260
    /// Matches the spec: montgomery_radix()
    pub fn montgomery_radix_exec() -> BigUint {
        BigUint::one() << 260
    }

    /// Check if all limbs are bounded by 2^52
    /// Matches the spec: limbs_bounded(&Scalar52)
    pub fn limbs_bounded_exec(s: &Scalar52) -> bool {
        s.limbs.iter().all(|&limb| limb < (1u64 << 52))
    }

    // Property-based test generators

    /// Generate a valid Scalar52 with bounded limbs (each limb < 2^52)
    fn arb_bounded_scalar52() -> impl Strategy<Value = Scalar52> {
        prop::array::uniform5(0u64..(1u64 << 52)).prop_map(|limbs| Scalar52 { limbs })
    }

    /// Generate a canonical scalar: limbs_bounded AND value < L
    /// This generates a random BigUint in [0, L) and converts it to Scalar52
    fn arb_canonical_scalar52() -> impl Strategy<Value = Scalar52> {
        // Generate random bytes and interpret as BigUint, then reduce mod L
        proptest::collection::vec(any::<u8>(), 32..=64).prop_map(|bytes| {
            let l = group_order_exec();
            let value = BigUint::from_bytes_le(&bytes) % &l;

            // Convert BigUint to limbs in base 2^52
            let mut limbs = [0u64; 5];
            let mask = (1u64 << 52) - 1;
            let mut remaining = value;

            for i in 0..5 {
                let limb_big = &remaining & BigUint::from(mask);
                limbs[i] = limb_big.to_u64_digits().first().copied().unwrap_or(0);
                remaining >>= 52;
            }

            Scalar52 { limbs }
        })
    }

    /// Test case demonstrating that montgomery_reduce fails its canonicality postcondition
    /// when given input that is the product of two bounded-but-non-canonical scalars.
    ///
    /// This specific case was found by proptest and demonstrates why the precondition
    /// requires BOTH scalars to be canonical (< L), not just bounded.
    #[test]
    #[should_panic(expected = "Result not in canonical form")]
    fn montgomery_reduce_non_canonical_product_fails_postcondition() {
        // This is the minimal failing case found by proptest
        let limbs: [u128; 9] = [
            0,
            0,
            0,
            0,
            43234767039827164816921,
            0,
            0,
            0,
            130605075492091607448940168551,
        ];

        // Verify the input limbs are relatively small (much smaller than 2^104 which is the
        // theoretical max for products of 52-bit limbs)
        assert!(limbs[0] < (1u128 << 1), "limbs[0] should be < 2^1");
        assert!(limbs[1] < (1u128 << 1), "limbs[1] should be < 2^1");
        assert!(limbs[2] < (1u128 << 1), "limbs[2] should be < 2^1");
        assert!(limbs[3] < (1u128 << 1), "limbs[3] should be < 2^1");
        assert!(limbs[4] < (1u128 << 76), "limbs[4] should be < 2^76");
        assert!(limbs[5] < (1u128 << 1), "limbs[5] should be < 2^1");
        assert!(limbs[6] < (1u128 << 1), "limbs[6] should be < 2^1");
        assert!(limbs[7] < (1u128 << 1), "limbs[7] should be < 2^1");
        assert!(limbs[8] < (1u128 << 97), "limbs[8] should be < 2^97");

        let result = Scalar52::montgomery_reduce(&limbs);

        let result_nat = to_nat_exec(&result.limbs);
        let limbs_nat = slice128_to_nat_exec(&limbs);
        let l = group_order_exec();
        let r = montgomery_radix_exec();

        // The Montgomery property should still hold
        assert_eq!(
            (&result_nat * &r) % &l,
            &limbs_nat % &l,
            "Montgomery property violated"
        );

        // The result should be limbs_bounded
        assert!(
            limbs_bounded_exec(&result),
            "Result limbs not bounded by 2^52"
        );

        // But the canonicality postcondition FAILS
        assert!(
            &result_nat < &l,
            "Result not in canonical form (>= L): {} >= {}",
            result_nat,
            l
        );
    }

    /// Test that the canonical scalar generator round-trips correctly
    #[test]
    fn test_canonical_scalar_generator() {
        use proptest::prelude::*;
        use proptest::strategy::ValueTree;
        use proptest::test_runner::{Config, TestRunner};

        let mut runner = TestRunner::new(Config::default());
        let l = group_order_exec();

        println!("Testing canonical scalar generator round-trip:");
        for i in 0..10 {
            let scalar = arb_canonical_scalar52()
                .new_tree(&mut runner)
                .unwrap()
                .current();

            // Convert to nat
            let value = to_nat_exec(&scalar.limbs);

            // Check it's canonical
            assert!(value < l, "Generated value should be < L");

            // Check limbs are bounded
            for (j, &limb) in scalar.limbs.iter().enumerate() {
                assert!(
                    limb < (1u64 << 52),
                    "Limb {} should be < 2^52, got {}",
                    j,
                    limb
                );
            }

            // Convert back to Scalar52 manually and check it matches
            let mut limbs_check = [0u64; 5];
            let mask = (1u64 << 52) - 1;
            let mut remaining = value.clone();

            for j in 0..5 {
                let limb_big = &remaining & BigUint::from(mask);
                limbs_check[j] = limb_big.to_u64_digits().first().copied().unwrap_or(0);
                remaining >>= 52;
            }

            // Check round-trip
            assert_eq!(
                scalar.limbs,
                limbs_check,
                "Round-trip failed for test {}",
                i + 1
            );

            // Convert back to nat and verify
            let value_check = to_nat_exec(&limbs_check);
            assert_eq!(
                value,
                value_check,
                "Value mismatch after round-trip for test {}",
                i + 1
            );

            println!(
                "Test {}: value = {}, limbs = {:?} ✓",
                i + 1,
                value,
                scalar.limbs
            );
        }
    }

    /// Generate random 9-limb array from product of one bounded scalar and one canonical scalar
    fn arb_nine_limbs_one_canonical() -> impl Strategy<Value = [u128; 9]> {
        (arb_bounded_scalar52(), arb_canonical_scalar52())
            .prop_map(|(a, b)| Scalar52::mul_internal(&a, &b))
    }

    /// Generate 9-limb arrays from product of TWO bounded scalars
    fn arb_nine_limbs_two_bounded() -> impl Strategy<Value = [u128; 9]> {
        (arb_bounded_scalar52(), arb_bounded_scalar52())
            .prop_map(|(a, b)| Scalar52::mul_internal(&a, &b))
    }

    /// Convert a 32-byte array to a BigUint
    /// Matches the spec: bytes_to_nat(&[u8; 32])
    pub fn bytes_to_nat_exec(bytes: &[u8; 32]) -> BigUint {
        let mut result = BigUint::zero();
        let radix = BigUint::from(256u32);
        for i in (0..32).rev() {
            result = result * &radix + BigUint::from(bytes[i]);
        }
        result
    }

    /// Test case demonstrating that from_bytes does NOT ensure canonicality.
    /// i.e. the postcondition `to_nat(&s.limbs) < group_order()` may not hold
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

        // OLD Postcondition 3: to_nat(&s.limbs) < group_order() - DOES NOT HOLD
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
        /// 1. bytes_to_nat(bytes) == to_nat(&s.limbs)
        /// 2. limbs_bounded(&s)
        #[test]
        fn prop_from_bytes(bytes in prop::array::uniform32(any::<u8>())) {
            // Call from_bytes
            let s = Scalar52::from_bytes(&bytes);

            // Convert to BigUint using executable spec functions
            let bytes_nat = bytes_to_nat_exec(&bytes);
            let result_nat = to_nat_exec(&s.limbs);

            // Postcondition 1: bytes_to_nat(bytes) == to_nat(&s.limbs)
            prop_assert_eq!(bytes_nat, result_nat,
                "from_bytes spec violated: bytes_to_nat(bytes) != to_nat(&s.limbs)");

            // Postcondition 2: limbs_bounded(&s)
            prop_assert!(limbs_bounded_exec(&s),
                "from_bytes spec violated: result limbs not bounded by 2^52");
        }

        /// Test 1: Input is product of TWO bounded scalars (both may be non-canonical)
        /// Spec says: if input = mul(bounded1, bounded2) then Montgomery property and limbs_bounded hold
        /// (but canonicality is NOT guaranteed)
        #[test]
        fn prop_montgomery_reduce_two_bounded(limbs in arb_nine_limbs_two_bounded()) {
            // Call montgomery_reduce
            let result = Scalar52::montgomery_reduce(&limbs);

            // Convert to BigUint using executable spec functions
            let result_nat = to_nat_exec(&result.limbs);
            let limbs_nat = slice128_to_nat_exec(&limbs);
            let l = group_order_exec();
            let r = montgomery_radix_exec();

            // Postcondition 1: Montgomery property (should hold for product of two bounded)
            let lhs = (&result_nat * &r) % &l;
            let rhs = &limbs_nat % &l;
            prop_assert_eq!(lhs, rhs,
                "Montgomery reduce spec violated: (result * R) mod L != limbs mod L");

            // Postcondition 2: limbs_bounded (should hold for product of two bounded)
            prop_assert!(limbs_bounded_exec(&result),
                "Result limbs not bounded by 2^52");

            // Postcondition 3: Canonicality is NOT guaranteed for product of two bounded scalars
            // (only guaranteed when one is canonical)
        }

        /// Test 2: Input is product of one bounded scalar and one canonical scalar
        /// Spec says: if input = mul(bounded, canonical) then result < L
        #[test]
        fn prop_montgomery_reduce_one_canonical(limbs in arb_nine_limbs_one_canonical()) {
            // Call montgomery_reduce
            let result = Scalar52::montgomery_reduce(&limbs);

            // Convert to BigUint using executable spec functions
            let result_nat = to_nat_exec(&result.limbs);
            let limbs_nat = slice128_to_nat_exec(&limbs);
            let l = group_order_exec();
            let r = montgomery_radix_exec();

            // Postcondition 1: Montgomery property (holds by first part of spec)
            let lhs = (&result_nat * &r) % &l;
            let rhs = &limbs_nat % &l;
            prop_assert_eq!(lhs, rhs,
                "Montgomery reduce spec violated: (result * R) mod L != limbs mod L");

            // Postcondition 2: limbs_bounded (holds by first part of spec)
            prop_assert!(limbs_bounded_exec(&result),
                "Result limbs not bounded by 2^52");

            // Postcondition 3: Canonicality - SHOULD hold by second part of spec
            // (exists bounded, canonical such that limbs = mul(bounded, canonical)) ==> result < L
            prop_assert!(&result_nat < &l,
                "Result not in canonical form (>= L), but input was product of bounded × canonical");
        }
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
