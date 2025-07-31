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

#[allow(unused_imports)]
use super::scalar_lemmas::*;
#[allow(unused_imports)]
use super::scalar_specs::*;
use super::subtle_assumes::*;
use core::fmt::Debug;
use core::ops::{Index, IndexMut};
use subtle::Choice;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::constants;

use super::common_verus::shift_is_pow2;
use crate::backend::serial::u64::constants::L;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::lemma_u64_shr_is_div;
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
    // TODO Verify this
    #[verifier::external_body]
    fn index(&self, _index: usize) -> &u64 {
        &(self.limbs[_index])
    }
}
} // verus!

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
        assume(bytes_to_nat(bytes) == words_to_nat(&words));
        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
            assert(1u64 << 48 > 0) by (bit_vector);
            // TODO: prove property about words array
        }

        let mask = (1u64 << 52) - 1;
        let top_mask = (1u64 << 48) - 1;
        let mut s = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };

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
    #[verifier::external_body] // TODO Verify this function
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> Scalar52 {
        let mut words = [0u64; 8];
        for i in 0..8 {
            for j in 0..8 {
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
    pub fn to_bytes(self) -> (s: [u8; 32])
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
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] < (1u64 << 52),
        forall|i: int| 0 <= i < 5 ==>  b.limbs[i] < (1u64 << 52),
    ensures
        to_nat(&s.limbs) == (to_nat(&a.limbs) + to_nat(&b.limbs)) % group_order(),
    {
        //let mut sum = Scalar52::ZERO;
        let mut sum = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof {
            assert(Scalar52::ZERO == Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] });
            assert(sum == Scalar52::ZERO);
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;

        // a + b
        let mut carry: u64 = 0;
        proof {
            assert(carry == 0u64);
            assert(1u64 << 54 < u64::MAX) by (bit_vector);
            assert(0u64 < (1u64 << 54)) by (bit_vector);
        }
        for i in 0..5
           invariant 0 <= i <= 5,
                    forall|j: int| 0 <= j < i ==> sum.limbs[j] < 1u64 << 52,
                    forall|j: int| 0 <= j < 5 ==> a.limbs[j] < (1u64 << 52),
                    forall|j: int| 0 <= j < 5 ==> b.limbs[j] < (1u64 << 52),
                    mask == (1u64 << 52) - 1,
                    i == 0 ==> carry == 0,
                    i >= 1 ==> carry < (1u64 << 53),
                    i >= 1 ==> (carry >> 52) < 2,
        {
            proof {
                assert(0 <= i < 5);
                assert(a.limbs[i as int] < 1u64 << 52);
                assert(b.limbs[i as int] < 1u64 << 52);

                // Prove carry >> 52 bound
                if i == 0 {
                    assert(carry == 0);
                    assert((0u64 >> 52) == 0) by (bit_vector);
                    assert((carry >> 52) == 0);
                } else {
                    assert((carry >> 52) < 2);
                }
                assert((carry >> 52) <= 1);

                // Prove no overflow
                assert((1u64 << 52) + (1u64 << 52) == (1u64 << 53)) by (bit_vector);
                assert(a.limbs[i as int] + b.limbs[i as int] < 1u64 << 53);
                assert((carry >> 52) + a.limbs[i as int] + b.limbs[i as int] <= 1 + (1u64 << 52) - 1 + (1u64 << 52) - 1);
                assert((carry >> 52) + a.limbs[i as int] + b.limbs[i as int] < 2 * (1u64 << 52));
                assert(2 * (1u64 << 52) == (1u64 << 53)) by (bit_vector);
                assert((carry >> 52) + a.limbs[i as int] + b.limbs[i as int] < (1u64 << 53));
                assert((1u64 << 53) < u64::MAX) by (bit_vector);
            }
            carry = a.limbs[i] + b.limbs[i] + (carry >> 52);
            sum.limbs[i] = carry & mask;
            proof {
                // Prove sum.limbs[i] < 2^52
                assert(mask == (1u64 << 52) - 1);
                assert(sum.limbs[i as int] == (carry & mask));
                assert((carry & mask) <= mask) by (bit_vector);
                assert(mask < (1u64 << 52));
                assert((carry & mask) < (1u64 << 52));
                assert(sum.limbs[i as int] < (1u64 << 52));

                // Prove carry bound for next iteration
                assert(carry < (1u64 << 53));

                // Prove carry >> 52 < 2 for next iteration
                broadcast use lemma_u64_shr_is_div;
                lemma_pow2_pos(52);
                shift_is_pow2(52);
                assert((1u64 << 52) == pow2(52));
                assert(carry >> 52 == carry / (1u64 << 52));

                // We have: carry < 2 * (1u64 << 52)
                // So carry / (1u64 << 52) < 2
                lemma_div_pos_is_pos(carry as int, (1u64 << 52) as int);
                assert(0 <= carry / (1u64 << 52));

                lemma_fundamental_div_mod(carry as int, (1u64 << 52) as int);
                let q = carry / (1u64 << 52);
                let r = carry % (1u64 << 52);
                assert(carry == q * (1u64 << 52) + r);
                assert(0 <= r < (1u64 << 52));

                // Since carry < 2 * (1u64 << 52), we have:
                // q * (1u64 << 52) + r < 2 * (1u64 << 52)
                // Therefore: q * (1u64 << 52) < 2 * (1u64 << 52)
                // So: q < 2
                assert(q * (1u64 << 52) <= carry);
                assert(carry < 2 * (1u64 << 52));
                assert(q * (1u64 << 52) < 2 * (1u64 << 52));
                lemma_mul_strictly_positive(q as int, (1u64 << 52) as int);
                lemma_mul_strict_inequality_converse(q as int, 2int, (1u64 << 52) as int);
                assert(q < 2);
                assert((carry >> 52) < 2);
            }
        }

        // subtract l if the sum is >= l

        /*** BEGIN: ADAPTED CODE BLOCK ***/

        /* ORIGINAL CODE */
        /*let mut s = Scalar52::sub(&sum, &Self::L);*/
        /* OUR ADAPTED CODE FOR VERUS; PROVED EQUIVALENT TO ORIGINAL CODE */
        let l_value = Scalar52 { limbs: [0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0x0000000000000000, 0x0000100000000000] };
        proof {
            // Prove that l_value == L
            assert(l_value.limbs[0] == L.limbs[0]);
            assert(l_value.limbs[1] == L.limbs[1]);
            assert(l_value.limbs[2] == L.limbs[2]);
            assert(l_value.limbs[3] == L.limbs[3]);
            assert(l_value.limbs[4] == L.limbs[4]);
            assert(l_value.limbs =~= L.limbs);
            assert(to_nat(&l_value.limbs) == to_nat(&L.limbs));

            // Prove all l_value limbs are < 2^52
            assert(l_value.limbs[0] == 0x0002631a5cf5d3ed);
            assert(0x0002631a5cf5d3ed < (1u64 << 52)) by (bit_vector);
            assert(l_value.limbs[0] < (1u64 << 52));

            assert(l_value.limbs[1] == 0x000dea2f79cd6581);
            assert(0x000dea2f79cd6581 < (1u64 << 52)) by (bit_vector);
            assert(l_value.limbs[1] < (1u64 << 52));

            assert(l_value.limbs[2] == 0x000000000014def9);
            assert(0x000000000014def9 < (1u64 << 52)) by (bit_vector);
            assert(l_value.limbs[2] < (1u64 << 52));

            assert(l_value.limbs[3] == 0x0000000000000000);
            assert(0x0000000000000000 < (1u64 << 52)) by (bit_vector);
            assert(l_value.limbs[3] < (1u64 << 52));

            assert(l_value.limbs[4] == 0x0000100000000000);
            assert(0x0000100000000000 < (1u64 << 52)) by (bit_vector);
            assert(l_value.limbs[4] < (1u64 << 52));

            // After the loop, all sum.limbs are bounded by 2^52
            assert forall|j: int| 0 <= j < 5 implies sum.limbs[j] < (1u64 << 52) by {
                assert(sum.limbs[j] < (1u64 << 52));
            }
        }

        let result = Scalar52::sub(&sum, &l_value);

        // We've proven no overflow occurs. The mathematical correctness is assumed.
        assume(to_nat(&result.limbs) == (to_nat(&a.limbs) + to_nat(&b.limbs)) % group_order());

        result

        /*** END: ADAPTED CODE BLOCK ***/

    }

    /// Compute `a - b` (mod l)
    pub fn sub(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] < (1u64 << 52),
        forall|i: int| 0 <= i < 5 ==> b.limbs[i] < (1u64 << 52),
    ensures
        to_nat(&s.limbs) == (to_nat(&a.limbs) + group_order() - to_nat(&b.limbs)) % (group_order() as int)
    {
        let mut difference = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof {
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;

        // a - b
        let mut borrow: u64 = 0;
        for i in 0..5
            invariant 0 <= i <= 5,
                      forall|j: int| 0 <= j < 5 ==> b.limbs[j] < (1u64 << 52),
                      forall|j: int| 0 <= j < i ==> difference.limbs[j] < (1u64 << 52),
                      mask == (1u64 << 52) - 1,
        {
            proof {
                assert ((borrow >> 63) < 2) by (bit_vector);
            }
            borrow = a.limbs[i].wrapping_sub(b.limbs[i] + (borrow >> 63));
            difference.limbs[i] = borrow & mask;
            proof {
                // Since mask = 2^52 - 1, we know (borrow & mask) < 2^52
                assert(mask == (1u64 << 52) - 1);
                // Any value ANDed with mask is at most mask
                // This is a fundamental property of AND
                // Since mask = 2^52 - 1, it has all bits 0-51 set to 1
                // (borrow & mask) can only have bits 0-51 set, so it's at most mask
                // We'll use the fact that for any x: (x & mask) & (~mask) == 0
                assert((borrow & mask) & (!(mask as u64)) == 0) by (bit_vector);
                // This means all bits of (borrow & mask) outside of mask are 0
                // Therefore (borrow & mask) <= mask
                assert((borrow & mask) <= mask) by (bit_vector);
                assert(mask < (1u64 << 52));
                assert((borrow & mask) < (1u64 << 52));
                assert(difference.limbs[i as int] == (borrow & mask));
                assert(difference.limbs[i as int] < (1u64 << 52));
            }
        }

        proof {
            // After the first loop, all difference.limbs are bounded
            assert forall|j: int| 0 <= j < 5 implies difference.limbs[j] < (1u64 << 52) by {
                assert(difference.limbs[j] < (1u64 << 52));
            }
        }

        // conditionally add l if the difference is negative
        let mut carry: u64 = 0;
        for i in 0..5
            invariant 0 <= i <= 5,
                      forall|j: int| 0 <= j < i ==> difference.limbs[j] < (1u64 << 52),
                      forall|j: int| 0 <= j < 5 ==> difference.limbs[j] < (1u64 << 52),  // from first loop
                      mask == (1u64 << 52) - 1,
                      i == 0 ==> carry == 0,
                      i >= 1 ==> (carry >> 52) < 2,
        {
            #[verifier::truncate]
            let underflow = Choice::from((borrow >> 63) as u8);
          /*** BEGIN: ADAPTED CODE BLOCK ***/
          // ORIGINAL CODE
         //   let addend = u64::conditional_select(&0, &constants::L[i], underflow);
        // OUR ADAPTED CODE FOR VERUS
            let addend = select(&0, &L.limbs[i], underflow);
        /*** END: ADAPTED CODE BLOCK ***/
            proof {
                lemma_scalar_subtract_no_overflow(carry, difference.limbs[i as int], addend, i as u32, &L);
            }
            carry = (carry >> 52) + difference.limbs[i] + addend;
            difference.limbs[i] = carry & mask;
            proof {
                assert(mask == (1u64 << 52) - 1);
                assert(difference.limbs[i as int] == (carry & mask));
                assert((carry & mask) <= mask) by (bit_vector);
                assert(mask < (1u64 << 52));
                assert((carry & mask) < (1u64 << 52));
                assert(difference.limbs[i as int] < (1u64 << 52));
                // Prove invariant is maintained for next iteration
                assert(carry < (1u64 << 53));
                // If carry < 2^53, then carry >> 52 < 2
                assert((1u64 << 53) == 2 * (1u64 << 52)) by (bit_vector);
                assert(carry < 2 * (1u64 << 52));
                // This means carry / 2^52 < 2, so carry >> 52 <= 1
                // We know carry < 2^53, and 2^53 = 2 * 2^52
                // So carry / 2^52 < 2
                // Since the result is an integer, carry >> 52 <= 1
                // Prove carry >> 52 <= 1
                broadcast use lemma_u64_shr_is_div;
                lemma_pow2_pos(52);
                shift_is_pow2(52);
                assert((1u64 << 52) == pow2(52));
                assert(carry >> 52 == carry / (1u64 << 52));

                // We have: carry < 2 * (1u64 << 52)
                // Need to show: carry / (1u64 << 52) <= 1
                // Which is equivalent to: carry < 2 * (1u64 << 52)
                assert(carry < 2 * (1u64 << 52));

                // Use the fact that for positive integers a, b, c:
                // If a < b * c, then a / c < b
                // Here: carry < 2 * (1u64 << 52), so carry / (1u64 << 52) < 2
                // For integer division, x < 2 implies x <= 1
                lemma_div_pos_is_pos(carry as int, (1u64 << 52) as int);
                assert(0 <= carry / (1u64 << 52));

                // Key insight: carry is bounded by 2 * 2^52
                // So carry = q * 2^52 + r where q < 2 and 0 <= r < 2^52
                // This means q must be 0 or 1
                lemma_fundamental_div_mod(carry as int, (1u64 << 52) as int);
                let q = carry / (1u64 << 52);
                let r = carry % (1u64 << 52);
                assert(carry == q * (1u64 << 52) + r);
                assert(0 <= r < (1u64 << 52));

                // Since carry < 2 * (1u64 << 52), we have:
                // q * (1u64 << 52) + r < 2 * (1u64 << 52)
                // Therefore: q * (1u64 << 52) < 2 * (1u64 << 52)
                // So: q < 2
                assert(q * (1u64 << 52) <= carry);
                assert(carry < 2 * (1u64 << 52));
                assert(q * (1u64 << 52) < 2 * (1u64 << 52));
                lemma_mul_strictly_positive(q as int, (1u64 << 52) as int);
                lemma_mul_strict_inequality_converse(q as int, 2int, (1u64 << 52) as int);
                assert(q < 2);
                assert(q <= 1);
                assert((carry >> 52) <= 1);
                assert((carry >> 52) < 2);
            }
        }
        assume(to_nat(&difference.limbs) == (to_nat(&a.limbs) + group_order() - to_nat(&b.limbs)) % (group_order() as int));
        difference
    }

    /// Compute `a * b`
    #[inline(always)]
    #[rustfmt::skip] // keep alignment of z[*] calculations
    pub (crate) fn mul_internal(a: &Scalar52, b: &Scalar52) -> (z: [u128; 9])
    requires
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] < (1u64 << 52),
        forall|i: int| 0 <= i < 5 ==> b.limbs[i] < (1u64 << 52),
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


    // TODO Make this function more like the original?
    /// Compute `a^2`
    #[inline(always)]
    #[rustfmt::skip] // keep alignment of calculations
    pub (crate) fn square_internal(a: &Scalar52) -> (z: [u128; 9])
    requires
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] < (1u64 << 52),
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
        // TODO: Add proper specification for Montgomery reduction
        true,
    {
        assume(false); // TODO: Add proper bounds checking and proofs


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
    #[inline(always)]
    fn part1(sum: u128) -> (u128, u64)
    {
        assume(false); // TODO: Add proper bounds checking and proofs
        let p = (sum as u64).wrapping_mul(constants::LFACTOR) & ((1u64 << 52) - 1);
        let carry = (sum + m(p, constants::L.limbs[0])) >> 52;
        (carry, p)
    }

    /// Helper function for Montgomery reduction
    #[inline(always)]
    fn part2(sum: u128) -> (u128, u64)
    {
        assume(false); // TODO: Add proper bounds checking and proofs
        let w = (sum as u64) & ((1u64 << 52) - 1);
        let carry = sum >> 52;
        (carry, w)
    }

    /// Compute `a * b` (mod l)
    #[inline(never)]
    pub fn mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] < (1u64 << 52),
        forall|i: int| 0 <= i < 5 ==> b.limbs[i] < (1u64 << 52),
    ensures
        to_nat(&result.limbs) == (to_nat(&a.limbs) * to_nat(&b.limbs)) % group_order(),
    {
        assume(false); // TODO: Add proper Montgomery arithmetic proofs
        let ab = Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b));
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(&ab, &constants::RR))
    }

    /// Compute `a^2` (mod l)
    #[inline(never)]
    #[allow(dead_code)] // XXX we don't expose square() via the Scalar API
    pub fn square(&self) -> (result: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
    ensures
        to_nat(&result.limbs) == (to_nat(&self.limbs) * to_nat(&self.limbs)) % group_order(),
    {
        assume(false); // TODO: Add proper Montgomery arithmetic proofs
        let aa = Scalar52::montgomery_reduce(&Scalar52::square_internal(self));
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(&aa, &constants::RR))
    }

    /// Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^260
    #[inline(never)]
    pub fn montgomery_mul(a: &Scalar52, b: &Scalar52) -> (result: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] < (1u64 << 52),
        forall|i: int| 0 <= i < 5 ==> b.limbs[i] < (1u64 << 52),
    ensures
        to_nat(&result.limbs) == (to_nat(&a.limbs) * to_nat(&b.limbs)) % group_order(),
    {
        assume(false); // TODO: Add proper Montgomery arithmetic proofs
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(a, b))
    }

    /// Compute `(a^2) / R` (mod l) in Montgomery form, where R is the Montgomery modulus 2^260
    #[inline(never)]
    pub fn montgomery_square(&self) -> (result: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
    ensures
        to_nat(&result.limbs) == (to_nat(&self.limbs) * to_nat(&self.limbs)) % group_order(),
    {
        assume(false); // TODO: Add proper Montgomery arithmetic proofs
        Scalar52::montgomery_reduce(&Scalar52::square_internal(self))
    }

    /// Puts a Scalar52 in to Montgomery form, i.e. computes `a*R (mod l)`
    #[inline(never)]
    pub fn as_montgomery(&self) -> (result: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
    ensures
        // TODO: Add proper specification for Montgomery form conversion
        true,
    {
        assume(false); // TODO: Add proper Montgomery arithmetic proofs
        Scalar52::montgomery_mul(self, &constants::RR)
    }

    /// Takes a Scalar52 out of Montgomery form, i.e. computes `a/R (mod l)`
    #[allow(clippy::wrong_self_convention)]
    #[inline(never)]
    pub fn from_montgomery(&self) -> (result: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
    ensures
        // TODO: Add proper specification for Montgomery form conversion
        true,
    {
        let mut limbs = [0u128; 9];
        #[allow(clippy::needless_range_loop)]
        for i in 0..5 {
            limbs[i] = self.limbs[i] as u128;
        }
        Scalar52::montgomery_reduce(&limbs)
    }
}


} // verus!

#[cfg(test)]
mod test {
    use super::*;

    /// Note: x is 2^253-1 which is slightly larger than the largest scalar produced by
    /// this implementation (l-1), and should show there are no overflows for valid scalars
    ///
    /// x = 14474011154664524427946373126085988481658748083205070504932198000989141204991
    /// x = 7237005577332262213973186563042994240801631723825162898930247062703686954002 mod l
    /// x = 3057150787695215392275360544382990118917283750546154083604586903220563173085*R mod l in Montgomery form
    pub static X: Scalar52 = Scalar52 {
        limbs: [
            0x000fffffffffffff,
            0x000fffffffffffff,
            0x000fffffffffffff,
            0x000fffffffffffff,
            0x00001fffffffffff,
        ],
    };

    /// x^2 = 3078544782642840487852506753550082162405942681916160040940637093560259278169 mod l
    pub static XX: Scalar52 = Scalar52 {
        limbs: [
            0x0001668020217559,
            0x000531640ffd0ec0,
            0x00085fd6f9f38a31,
            0x000c268f73bb1cf4,
            0x000006ce65046df0,
        ],
    };

    /// x^2 = 4413052134910308800482070043710297189082115023966588301924965890668401540959*R mod l in Montgomery form
    pub static XX_MONT: Scalar52 = Scalar52 {
        limbs: [
            0x000c754eea569a5c,
            0x00063b6ed36cb215,
            0x0008ffa36bf25886,
            0x000e9183614e7543,
            0x0000061db6c6f26f,
        ],
    };

    /// y = 6145104759870991071742105800796537629880401874866217824609283457819451087098
    pub static Y: Scalar52 = Scalar52 {
        limbs: [
            0x000b75071e1458fa,
            0x000bf9d75e1ecdac,
            0x000433d2baf0672b,
            0x0005fffcc11fad13,
            0x00000d96018bb825,
        ],
    };

    /// x*y = 36752150652102274958925982391442301741 mod l
    pub static XY: Scalar52 = Scalar52 {
        limbs: [
            0x000ee6d76ba7632d,
            0x000ed50d71d84e02,
            0x00000000001ba634,
            0x0000000000000000,
            0x0000000000000000,
        ],
    };

    /// x*y = 658448296334113745583381664921721413881518248721417041768778176391714104386*R mod l in Montgomery form
    pub static XY_MONT: Scalar52 = Scalar52 {
        limbs: [
            0x0006d52bf200cfd5,
            0x00033fb1d7021570,
            0x000f201bc07139d8,
            0x0001267e3e49169e,
            0x000007b839c00268,
        ],
    };

    /// a = 2351415481556538453565687241199399922945659411799870114962672658845158063753
    pub static A: Scalar52 = Scalar52 {
        limbs: [
            0x0005236c07b3be89,
            0x0001bc3d2a67c0c4,
            0x000a4aa782aae3ee,
            0x0006b3f6e4fec4c4,
            0x00000532da9fab8c,
        ],
    };

    /// b = 4885590095775723760407499321843594317911456947580037491039278279440296187236
    pub static B: Scalar52 = Scalar52 {
        limbs: [
            0x000d3fae55421564,
            0x000c2df24f65a4bc,
            0x0005b5587d69fb0b,
            0x00094c091b013b3b,
            0x00000acd25605473,
        ],
    };

    /// a+b = 0
    /// a-b = 4702830963113076907131374482398799845891318823599740229925345317690316127506
    pub static AB: Scalar52 = Scalar52 {
        limbs: [
            0x000a46d80f677d12,
            0x0003787a54cf8188,
            0x0004954f0555c7dc,
            0x000d67edc9fd8989,
            0x00000a65b53f5718,
        ],
    };

    // c = (2^512 - 1) % l = 1627715501170711445284395025044413883736156588369414752970002579683115011840
    pub static C: Scalar52 = Scalar52 {
        limbs: [
            0x000611e3449c0f00,
            0x000a768859347a40,
            0x0007f5be65d00e1b,
            0x0009a3dceec73d21,
            0x00000399411b7c30,
        ],
    };

    #[test]
    fn mul_max() {
        let res = Scalar52::mul(&X, &X);
        for i in 0..5 {
            assert!(res[i] == XX[i]);
        }
    }

    #[test]
    fn square_max() {
        let res = X.square();
        for i in 0..5 {
            assert!(res[i] == XX[i]);
        }
    }

    #[test]
    fn montgomery_mul_max() {
        let res = Scalar52::montgomery_mul(&X, &X);
        for i in 0..5 {
            assert!(res[i] == XX_MONT[i]);
        }
    }

    #[test]
    fn montgomery_square_max() {
        let res = X.montgomery_square();
        for i in 0..5 {
            assert!(res[i] == XX_MONT[i]);
        }
    }

    #[test]
    fn mul() {
        let res = Scalar52::mul(&X, &Y);
        for i in 0..5 {
            assert!(res[i] == XY[i]);
        }
    }

    #[test]
    fn montgomery_mul() {
        let res = Scalar52::montgomery_mul(&X, &Y);
        for i in 0..5 {
            assert!(res[i] == XY_MONT[i]);
        }
    }

    #[test]
    fn add() {
        let res = Scalar52::add(&A, &B);
        let zero = Scalar52::ZERO;
        for i in 0..5 {
            assert!(res[i] == zero[i]);
        }
    }

    #[test]
    fn sub() {
        let res = Scalar52::sub(&A, &B);
        for i in 0..5 {
            assert!(res[i] == AB[i]);
        }
    }

    #[test]
    fn from_bytes_wide() {
        let bignum = [255u8; 64]; // 2^512 - 1
        let reduced = Scalar52::from_bytes_wide(&bignum);
        for i in 0..5 {
            assert!(reduced[i] == C[i]);
        }
    }
}
