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

use super::subtle_assumes::select;
use core::fmt::Debug;
use core::ops::{Index, IndexMut};
use subtle::Choice;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::constants;

#[allow(unused_imports)]
use super::scalar_lemmas::*;
#[allow(unused_imports)]
use super::scalar_specs::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

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

#[cfg(feature = "zeroize")]
impl Zeroize for Scalar52 {
    fn zeroize(&mut self) {
        self.limbs.zeroize();
    }
}

verus! {
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
    z == x * y
{
    proof {lemma_52_52(x, y);}
    (x as u128) * (y as u128)
}

impl Scalar52 {
    /// The scalar \\( 0 \\).
    pub const ZERO: Scalar52 = Scalar52 { limbs: [0, 0, 0, 0, 0] };

    /// Unpack a 32 byte / 256 bit scalar into 5 52-bit limbs.
    #[rustfmt::skip] // keep alignment of s[*] calculations
    pub fn from_bytes(bytes: &[u8; 32]) -> (s: Scalar52)
    ensures bytes_to_nat(bytes) == to_nat(&s.limbs)
    {
        let mut words = [0u64; 4];
        for i in 0..4
            invariant 0 <= i <= 4 // proof
        {
            for j in 0..8
                invariant 0 <= j <= 8 && i < 4
            {
                proof {
                    assert(i < 4 && j < 8);
                    assert((i as u64)*8u64 < 32u64);
                    let idx = (i as u64) * 8 + (j as u64);
                    assert(idx < 32);
                }
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
            }
        }
        //TODO: prove that bytes_to_nat(bytes) == words_to_nat(&words)
        assume(bytes_to_nat(bytes) == words_to_nat(&words));
        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
            assert(1u64 << 48 > 0) by (bit_vector);
            // TODO: prove property about words array
        }

        let mask = (1u64 << 52) - 1;
        let top_mask = (1u64 << 48) - 1;
        let mut s = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        //test workflow graphs
        s.limbs[0] =   words[0]                            & mask;
        s.limbs[1] = ((words[0] >> 52) | (words[1] << 12)) & mask;
        s.limbs[2] = ((words[1] >> 40) | (words[2] << 24)) & mask;
        s.limbs[3] = ((words[2] >> 28) | (words[3] << 36)) & mask;
        s.limbs[4] =  (words[3] >> 16)                     & top_mask;

        assume(false); // TODO: complete the proof

        s
    }

    /// Reduce a 64 byte / 512 bit scalar mod l
    #[rustfmt::skip] // keep alignment of lo[*] and hi[*] calculations
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> (s: Scalar52)
    ensures
        limbs_bounded(&s),
        to_nat(&s.limbs) == bytes_wide_to_nat(bytes) % group_order(),
    {
        assume(false); // TODO: complete the proof
        let mut words = [0u64; 8];
        for i in 0..8 {
            for j in 0..8 {
                assume(false);
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
            }
        }

        let mask = (1u64 << 52) - 1;
        let mut lo = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        let mut hi = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };

        lo[0] =   words[0]                             & mask;
        lo[1] = ((words[0] >> 52) | (words[ 1] << 12)) & mask;
        lo[2] = ((words[1] >> 40) | (words[ 2] << 24)) & mask;
        lo[3] = ((words[2] >> 28) | (words[ 3] << 36)) & mask;
        lo[4] = ((words[3] >> 16) | (words[ 4] << 48)) & mask;
        hi[0] =  (words[4] >>  4)                      & mask;
        hi[1] = ((words[4] >> 56) | (words[ 5] <<  8)) & mask;
        hi[2] = ((words[5] >> 44) | (words[ 6] << 20)) & mask;
        hi[3] = ((words[6] >> 32) | (words[ 7] << 32)) & mask;
        hi[4] =   words[7] >> 20                             ;

        lo = Scalar52::montgomery_mul(&lo, &constants::R);  // (lo * R) / R = lo
        hi = Scalar52::montgomery_mul(&hi, &constants::RR); // (hi * R^2) / R = hi * R

        Scalar52::add(&hi, &lo)
    }

    /// Pack the limbs of this `Scalar52` into 32 bytes
    #[rustfmt::skip] // keep alignment of s[*] calculations
    #[allow(clippy::identity_op)]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_bytes(self) -> (s: [u8; 32])
    ensures bytes_to_nat(&s) == to_nat(&self.limbs)
    {
        let mut s = [0u8; 32];

        s[ 0] =  (self.limbs[ 0] >>  0)                      as u8;
        s[ 1] =  (self.limbs[ 0] >>  8)                      as u8;
        s[ 2] =  (self.limbs[ 0] >> 16)                      as u8;
        s[ 3] =  (self.limbs[ 0] >> 24)                      as u8;
        s[ 4] =  (self.limbs[ 0] >> 32)                      as u8;
        s[ 5] =  (self.limbs[ 0] >> 40)                      as u8;
        s[ 6] = ((self.limbs[ 0] >> 48) | (self.limbs[ 1] << 4)) as u8;
        s[ 7] =  (self.limbs[ 1] >>  4)                      as u8;
        s[ 8] =  (self.limbs[ 1] >> 12)                      as u8;
        s[ 9] =  (self.limbs[ 1] >> 20)                      as u8;
        s[10] =  (self.limbs[ 1] >> 28)                      as u8;
        s[11] =  (self.limbs[ 1] >> 36)                      as u8;
        s[12] =  (self.limbs[ 1] >> 44)                      as u8;
        s[13] =  (self.limbs[ 2] >>  0)                      as u8;
        s[14] =  (self.limbs[ 2] >>  8)                      as u8;
        s[15] =  (self.limbs[ 2] >> 16)                      as u8;
        s[16] =  (self.limbs[ 2] >> 24)                      as u8;
        s[17] =  (self.limbs[ 2] >> 32)                      as u8;
        s[18] =  (self.limbs[ 2] >> 40)                      as u8;
        s[19] = ((self.limbs[ 2] >> 48) | (self.limbs[ 3] << 4)) as u8;
        s[20] =  (self.limbs[ 3] >>  4)                      as u8;
        s[21] =  (self.limbs[ 3] >> 12)                      as u8;
        s[22] =  (self.limbs[ 3] >> 20)                      as u8;
        s[23] =  (self.limbs[ 3] >> 28)                      as u8;
        s[24] =  (self.limbs[ 3] >> 36)                      as u8;
        s[25] =  (self.limbs[ 3] >> 44)                      as u8;
        s[26] =  (self.limbs[ 4] >>  0)                      as u8;
        s[27] =  (self.limbs[ 4] >>  8)                      as u8;
        s[28] =  (self.limbs[ 4] >> 16)                      as u8;
        s[29] =  (self.limbs[ 4] >> 24)                      as u8;
        s[30] =  (self.limbs[ 4] >> 32)                      as u8;
        s[31] =  (self.limbs[ 4] >> 40)                      as u8;

        assume(false); // TODO: complete the proof

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
    {
        let mut sum = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof { assert(1u64 << 52 > 0) by (bit_vector); }
        let mask = (1u64 << 52) - 1;

        // a + b
        let mut carry: u64 = 0;
        proof {
            // Base case: empty subrange has value 0
            assert(seq_u64_to_nat(a.limbs@.subrange(0, 0 as int)) == 0);
            assert(seq_u64_to_nat(b.limbs@.subrange(0, 0 as int)) == 0);
            assert(seq_u64_to_nat(sum.limbs@.subrange(0, 0 as int)) == 0);
            assert((carry >> 52) == 0) by (bit_vector) requires carry == 0;
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
                    seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + seq_u64_to_nat(b.limbs@.subrange(0, i as int)) ==
                    seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) + (carry >> 52) * pow2((52 * (i) as nat))
        {
            proof {lemma_add_loop_bounds(i as int, carry, a.limbs[i as int], b.limbs[i as int]);}
            let ghost old_carry = carry;
            carry = a.limbs[i] + b.limbs[i] + (carry >> 52);
            let ghost sum_loop_start = sum;
            sum.limbs[i] = carry & mask;
            assert(sum_loop_start.limbs@.subrange(0, i as int) == sum.limbs@.subrange(0, i as int));
            proof {
                lemma_add_loop_invariant(sum, carry, i, a, b, old_carry, mask, sum_loop_start);
            }
            proof {lemma_add_carry_and_sum_bounds(carry, mask);}
        }

        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) ==
               seq_u64_to_nat(sum.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2((52 * (5) as nat)));

        proof {lemma_add_sum_simplify(a, b, &sum, carry);}

        // subtract l if the sum is >= l
        proof { lemma_l_value_properties(&constants::L, &sum); }
        assert(group_order() > to_nat(&sum.limbs) - group_order() >= -group_order());
        proof{lemma_l_equals_group_order();}
        proof{lemma_mod_sub_multiples_vanish(to_nat(&sum.limbs) as int, group_order() as int);}
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
        assume(false); // TODO: complete the proof
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
        to_nat(&old(self).limbs) + group_order() < pow2(260)
    ensures
        // The mathematical value modulo group_order doesn't change (since L = group_order)
        to_nat(&self.limbs) % group_order() == to_nat(&old(self).limbs) % group_order(),
        // VERIFICATION NOTE: expression below unsupported by Verus
        //limbs_bounded(&self),

        // Meaning of conditional addition
        super::subtle_assumes::choice_is_true(condition) ==>
            to_nat(&self.limbs) == to_nat(&old(self).limbs) + group_order(),
        !super::subtle_assumes::choice_is_true(condition) ==>
            to_nat(&self.limbs) == to_nat(&old(self).limbs),
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
                lemma_scalar_subtract_no_overflow(carry, self.limbs[i as int], addend, i as u32, &constants::L);
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
            assume(super::subtle_assumes::choice_is_true(condition) ==>
                to_nat(&self.limbs) == to_nat(&old(self).limbs) + group_order());
            assume(!super::subtle_assumes::choice_is_true(condition) ==>
                to_nat(&self.limbs) == to_nat(&old(self).limbs));
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
    {
        let mut difference = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof { assert(1u64 << 52 > 0) by (bit_vector);}
        let mask = (1u64 << 52) - 1;

        // a - b
        let mut borrow: u64 = 0;
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 0 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 0 as int )) ==
                seq_u64_to_nat(difference.limbs@.subrange(0, 0 as int )));
        assert( (borrow >> 63) == 0 ) by (bit_vector)
            requires borrow == 0;
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 0 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 0 as int )) ==
                seq_u64_to_nat(difference.limbs@.subrange(0, 0 as int )) - (borrow >> 63) * pow2((52 * (0) as nat)));
        for i in 0..5
            invariant
                      limbs_bounded(b),
                      limbs_bounded(a),
                      forall|j: int| 0 <= j < i ==> difference.limbs[j] < (1u64 << 52),
                      mask == (1u64 << 52) - 1,
                      seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(b.limbs@.subrange(0, i as int )) ==
                                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int )) - (borrow >> 63) * pow2((52 * (i) as nat))
        {
            proof { assert ((borrow >> 63) < 2) by (bit_vector); }
            let ghost old_borrow = borrow;
            borrow = a.limbs[i].wrapping_sub(b.limbs[i] + (borrow >> 63));
            let ghost difference_loop1_start = difference;
            difference.limbs[i] = borrow & mask;
            assert(difference_loop1_start.limbs@.subrange(0, i as int) == difference.limbs@.subrange(0, i as int));
            assert(
            seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(b.limbs@.subrange(0, i as int )) ==
                        seq_u64_to_nat(difference_loop1_start.limbs@.subrange(0, i as int )) - (old_borrow >> 63) * pow2((52 * (i) as nat)));
            proof{
                lemma_sub_loop1_invariant(difference, borrow, i, a, b, old_borrow, mask, difference_loop1_start);
            }
            proof { lemma_borrow_and_mask_bounded(borrow, mask); }
        }

        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int )) ==
                seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int )) - (borrow >> 63) * pow2((52 * (5) as nat)) );
        // conditionally add l if the difference is negative
        assert(borrow >> 63 == 1 || borrow >> 63 == 0) by (bit_vector);
        let mut carry: u64 = 0;
        let ghost difference_after_loop1 = difference;
        assert(seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 0 as int)) == 0);
        assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 0 as int)) == 0);
        assert(seq_u64_to_nat(difference.limbs@.subrange(0, 0 as int)) == 0);
        assert(carry >> 52 == 0) by (bit_vector)
            requires carry == 0;
        for i in 0..5
            invariant
                      forall|j: int| 0 <= j < 5 ==> difference.limbs[j] < (1u64 << 52),  // from first loop
                      forall|j: int| i <= j < 5 ==> difference.limbs[j] == difference_after_loop1.limbs[j],
                      mask == (1u64 << 52) - 1,
                      i == 0 ==> carry == 0,
                      i >= 1 ==> (carry >> 52) < 2,
                      (i >=1 && borrow >> 63 == 0) ==> carry == difference.limbs[i-1],
                      borrow >> 63 == 0 ==> difference_after_loop1 == difference,
                      borrow >> 63 == 1 ==>
                          seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i as int)) + seq_u64_to_nat(constants::L.limbs@.subrange(0, i as int)) ==
                          seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (carry >> 52) * pow2(52 * i as nat)

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
            proof {lemma_scalar_subtract_no_overflow(carry, difference.limbs[i as int], addend, i as u32, &constants::L);}
            carry = (carry >> 52) + difference.limbs[i] + addend;
            let ghost difference_loop2_start = difference;
            difference.limbs[i] = carry & mask;
            proof {
                lemma_carry_bounded_after_mask(carry, mask);
                assert(difference_loop2_start.limbs@.subrange(0, i as int) == difference.limbs@.subrange(0, i as int));
                lemma_sub_loop2_invariant(difference, i, a, b, mask, difference_after_loop1, difference_loop2_start, carry, old_carry, addend, borrow);
            }
        }
        proof { lemma_sub_correct_after_loops(difference, carry, a, b, difference_after_loop1, borrow);}
        difference
    }

    /// Compute `a * b`
    #[inline(always)]
    #[rustfmt::skip] // keep alignment of z[*] calculations
    pub (crate) fn mul_internal(a: &Scalar52, b: &Scalar52) -> (z: [u128; 9])
    requires
        limbs_bounded(a),
        limbs_bounded(b),
    ensures
        slice128_to_nat(&z) == to_nat(&a.limbs) * to_nat(&b.limbs),
    {
        proof {lemma_mul_internal_no_overflow()}

        let mut z = [0u128; 9];

        z[0] = m(a.limbs[0], b.limbs[0]);
        z[1] = m(a.limbs[0], b.limbs[1]) + m(a.limbs[1], b.limbs[0]);
        z[2] = m(a.limbs[0], b.limbs[2]) + m(a.limbs[1], b.limbs[1]) + m(a.limbs[2], b.limbs[0]);
        z[3] = m(a.limbs[0], b.limbs[3]) + m(a.limbs[1], b.limbs[2]) + m(a.limbs[2], b.limbs[1]) + m(a.limbs[3], b.limbs[0]);
        z[4] = m(a.limbs[0], b.limbs[4]) + m(a.limbs[1], b.limbs[3]) + m(a.limbs[2], b.limbs[2]) + m(a.limbs[3], b.limbs[1]) + m(a.limbs[4], b.limbs[0]);
        z[5] =                 m(a.limbs[1], b.limbs[4]) + m(a.limbs[2], b.limbs[3]) + m(a.limbs[3], b.limbs[2]) + m(a.limbs[4], b.limbs[1]);
        z[6] =                                 m(a.limbs[2], b.limbs[4]) + m(a.limbs[3], b.limbs[3]) + m(a.limbs[4], b.limbs[2]);
        z[7] =                                                 m(a.limbs[3], b.limbs[4]) + m(a.limbs[4], b.limbs[3]);
        z[8] =                                                                 m(a.limbs[4], b.limbs[4]);

        proof {lemma_mul_internal_correct(&a.limbs, &b.limbs, &z);}

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
    #[rustfmt::skip] // keep alignment of calculations
    pub (crate) fn square_internal(a: &Scalar52) -> (z: [u128; 9])
    requires
        limbs_bounded(a),
    ensures
        slice128_to_nat(&z) == to_nat(&a.limbs) * to_nat(&a.limbs),
    {
        proof {lemma_square_internal_no_overflow()}

        let mut z = [0u128; 9];
        z[0] = m(a.limbs[0], a.limbs[0]);
        z[1] = m(a.limbs[0], a.limbs[1]) * 2;
        z[2] = m(a.limbs[0], a.limbs[2]) * 2 + m(a.limbs[1], a.limbs[1]);
        z[3] = m(a.limbs[0], a.limbs[3]) * 2 + m(a.limbs[1], a.limbs[2]) * 2;
        z[4] = m(a.limbs[0], a.limbs[4]) * 2 + m(a.limbs[1], a.limbs[3]) * 2 + m(a.limbs[2], a.limbs[2]);
        z[5] =                 m(a.limbs[1], a.limbs[4]) * 2 + m(a.limbs[2], a.limbs[3]) * 2;
        z[6] =                                 m(a.limbs[2], a.limbs[4]) * 2 + m(a.limbs[3], a.limbs[3]);
        z[7] =                                                 m(a.limbs[3], a.limbs[4]) * 2;
        z[8] =                                                                 m(a.limbs[4], a.limbs[4]);

        proof {lemma_square_internal_correct(&a.limbs, &z);}

        z
    }

    /// Compute `limbs/R` (mod l), where R is the Montgomery modulus 2^260
    #[inline(always)]
    #[rustfmt::skip] // keep alignment of n* and r* calculations
    pub (crate) fn montgomery_reduce(limbs: &[u128; 9]) -> (result: Scalar52)
    ensures
        (to_nat(&result.limbs) * montgomery_radix()) % group_order() == slice128_to_nat(limbs) % group_order(),
        limbs_bounded(&result),
    {
        assume(false); // TODO: Add proofs


        // note: l[3] is zero, so its multiples can be skipped
        let l = &constants::L;

        // the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R
        let (carry, n0) = Self::part1(limbs[0]);
        let (carry, n1) = Self::part1(carry + limbs[1] + m(n0, l.limbs[1]));
        let (carry, n2) = Self::part1(carry + limbs[2] + m(n0, l.limbs[2]) + m(n1, l.limbs[1]));
        let (carry, n3) = Self::part1(carry + limbs[3] + m(n1, l.limbs[2]) + m(n2, l.limbs[1]));
        let (carry, n4) = Self::part1(carry + limbs[4] + m(n0, l.limbs[4]) + m(n2, l.limbs[2]) + m(n3, l.limbs[1]));

        // limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result
        let (carry, r0) = Self::part2(carry + limbs[5] + m(n1, l.limbs[4]) + m(n3, l.limbs[2]) + m(n4, l.limbs[1]));
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
        })
    {
        assume(false); // TODO: Add proofs
        let p = (sum as u64).wrapping_mul(constants::LFACTOR) & ((1u64 << 52) - 1);
        let carry = (sum + m(p, constants::L.limbs[0])) >> 52;
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
            &&& w < (1u64 << 52)  // VER NOTE: w is bounded by 52 bits (lower limb)
            // VER NOTE: The sum equals w plus carry shifted left by 52 bits
            &&& sum == (w as u128) + (carry << 52)
        })
    {
        assume(false); // TODO: Add proofs
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
        to_nat(&result.limbs) == (to_nat(&a.limbs) * to_nat(&b.limbs)) % group_order(),
    {
        assume(false); // TODO: Add proofs
        let ab = Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b));
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(&ab, &constants::RR))
    }

    /// Compute `a^2` (mod l)
    #[inline(never)]
    #[allow(dead_code)] // XXX we don't expose square() via the Scalar API
    pub fn square(&self) -> (result: Scalar52)
    requires
        limbs_bounded(self),
    ensures
        to_nat(&result.limbs) == (to_nat(&self.limbs) * to_nat(&self.limbs)) % group_order(),
    {
        assume(false); // TODO: Add proofs
        let aa = Scalar52::montgomery_reduce(&Scalar52::square_internal(self));
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(&aa, &constants::RR))
    }

    /// Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^260
    #[inline(never)]
    pub fn montgomery_mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
    ensures
        limbs_bounded(&result),
        (to_nat(&result.limbs) * montgomery_radix()) % group_order() == (to_nat(&a.limbs) * to_nat(&b.limbs)) % group_order(),
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
        (to_nat(&result.limbs) * montgomery_radix()) % group_order() == (to_nat(&self.limbs) * to_nat(&self.limbs)) % group_order(),
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
        to_nat(&result.limbs) % group_order() == (to_nat(&self.limbs) * montgomery_radix()) % group_order(),
    {
        proof {
            lemma_rr_limbs_bounded();
        }
        let result = Scalar52::montgomery_mul(self, &constants::RR);
        assume(to_nat(&result.limbs) % group_order() == (to_nat(&self.limbs) * montgomery_radix()) % group_order());
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
        (to_nat(&result.limbs) * montgomery_radix()) % group_order() == to_nat(&self.limbs) % group_order(),
    {
        let mut limbs = [0u128; 9];
        #[allow(clippy::needless_range_loop)]
        for i in 0..5
            invariant
                forall|j: int| #![auto] 0 <= j < i ==> limbs[j] == self.limbs[j] as u128,
                forall|j: int| #![auto] i <= j < 9 ==> limbs[j] == 0,
        {
            limbs[i] = self.limbs[i] as u128;
        }
        let result = Scalar52::montgomery_reduce(&limbs);
        proof {
            lemma_from_montgomery_limbs_conversion(&limbs, &self.limbs);
        }
        result
    }
}


} // verus!

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
