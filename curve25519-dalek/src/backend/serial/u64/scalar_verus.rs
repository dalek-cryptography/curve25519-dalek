// scalar64_verus.rs
#![allow(unused)]
use subtle::{Choice, ConditionallySelectable};
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::calc;
use vstd::prelude::*;
// use crate::constants; // We manually import needed constants

verus! {

        #[verifier::external_type_specification]
        #[verifier::external_body]
        pub struct ExChoice(Choice);

        pub uninterp spec fn boolify(c: Choice) -> bool;

        pub assume_specification [Choice::from](u: u8) -> (c: Choice)
            ensures u == 0 ==> boolify(c) == false,
                    u == 1 ==> boolify(c) == true;

        #[verifier::external_body]
        fn select(x: &u64, y: &u64, c: Choice) -> (res: u64)
            ensures boolify(c) ==> res == x,
                    ! boolify(c) ==> res == y
        {
            u64::conditional_select(x, y, c)
        }


        /* MANUALLY IMPORTED FROM curve25519-dalek/src/backend/serial/u64/constants.rs */
        /// `L` is the order of base point, i.e. 2^252 + 27742317777372353535851937790883648493
        pub const L: Scalar52 = Scalar52 { limbs: [
            0x0002631a5cf5d3ed,
            0x000dea2f79cd6581,
            0x000000000014def9,
            0x0000000000000000,
            0x0000100000000000,
        ]};

        /// `RR` = (R^2) mod L where R = 2^260
        pub const RR: Scalar52 = Scalar52 { limbs: [
            0x0009d265e952d13b,
            0x000d63c715bea69f,
            0x0005ea65f25dd3d5,
            0x000e571d6372e9c5,
            0x0000039da6b19ca7,
        ]};

        /// `LFACTOR` = (-(L^(-1))) mod 2^52
        pub const LFACTOR: u64 = 0x51da312547e1b;

        /******  SPECIFICATION FUNCTIONS ********/

        // FUTURE VERUS FEATURE: Generic function to convert array of integers to natural number
        // This is what we would like to have, but Verus doesn't support generic types yet.
        // When Verus adds generic support, this could replace the concrete u64/u32 versions below.
        /*
        pub open spec fn to_nat_gen<T>(limbs: &[T], num_limbs: int, bits_per_limb: int) -> nat
        decreases num_limbs
        {
            if num_limbs <= 0 {
                0
            } else {
                let limb_value = (limbs[num_limbs - 1] as nat) * pow2(((num_limbs - 1) * bits_per_limb) as nat);
                limb_value + to_nat_gen(limbs, num_limbs - 1, bits_per_limb)
            }
        }
        */

        // Generic function to convert array of integers to natural number
        // Takes: array of integers, number of limbs, bits per limb
        // Note: Generic types not supported in Verus yet.
        // These are specification functions that work only with the u64 and u32 types
        pub open spec fn to_nat_gen_u64(limbs: &[u64], num_limbs: int, bits_per_limb: int) -> nat
        decreases num_limbs
        {
            if num_limbs <= 0 {
                0
            } else {
                let limb_value = (limbs[num_limbs - 1] as nat) * pow2(((num_limbs - 1) * bits_per_limb) as nat);
                limb_value + to_nat_gen_u64(limbs, num_limbs - 1, bits_per_limb)
            }
        }

        pub open spec fn slice_to_nat128(limbs: &[u128]) -> nat
        {
            seq_to_nat(limbs@.map(|i, x| x as nat))
        }

        pub open spec fn slice_to_nat64(limbs: &[u64]) -> nat
        {
            seq_to_nat(limbs@.map(|i, x| x as nat))
        }

        pub open spec fn seq_to_nat(limbs: Seq<nat>) -> nat
        decreases limbs.len()
        {
            if limbs.len() == 0 {
                0
            } else {
                limbs[0] + seq_to_nat(limbs.subrange(1, limbs.len() as int)) * pow2(52)
            }
        }

        // pub open spec fn to_nat_gen<T>(limbs: &[T], num_limbs: int, bits_per_limb: int) -> nat
        // where
        //     T: core::marker::Copy + Into<nat>
        // decreases num_limbs
        // {
        //     if num_limbs <= 0 {
        //         0
        //     } else {
        //         let limb_value = (limbs[num_limbs - 1] as nat) * pow2(((num_limbs - 1) * bits_per_limb) as nat);
        //         limb_value + to_nat_gen(limbs, num_limbs - 1, bits_per_limb)
        //     }
        // }




        // TODO There should be an indirect version
        pub open spec fn nine_limbs_to_nat_direct(limbs: &[u128; 9]) -> nat {
            (limbs[0] as nat) +
            (limbs[1] as nat) * pow2(52) +
            (limbs[2] as nat) * pow2(104) +
            (limbs[3] as nat) * pow2(156) +
            (limbs[4] as nat) * pow2(208) +
            (limbs[5] as nat) * pow2(260) +
            (limbs[6] as nat) * pow2(312) +
            (limbs[7] as nat) * pow2(364) +
            (limbs[8] as nat) * pow2(416)
        }

        proof fn lemma_nine_limbs_equals_slice_to_nat128(limbs: &[u128; 9])
        ensures 
            nine_limbs_to_nat_direct(limbs) == slice_to_nat128(limbs)
        {

            let seq = limbs@.map(|i, x| x as nat);

            calc! {
                (==)
                slice_to_nat128(limbs); {
                }
                seq_to_nat(seq); {
                    reveal_with_fuel(seq_to_nat, 10);
                }
                (limbs[0] as nat) +
                ((limbs[1] as nat) + 
                 ((limbs[2] as nat) + 
                  ((limbs[3] as nat) + 
                   ((limbs[4] as nat) + 
                    ((limbs[5] as nat) + 
                     ((limbs[6] as nat) + 
                      ((limbs[7] as nat) + 
                       (limbs[8] as nat) * pow2(52)
                      ) * pow2(52)
                     ) * pow2(52)
                    ) * pow2(52)
                   ) * pow2(52)
                  ) * pow2(52)
                 ) * pow2(52)
                ) * pow2(52); {
                lemma_pow2_adds(52, 52);
                lemma_pow2_adds(104, 52);
                lemma_pow2_adds(156, 52);
                lemma_pow2_adds(208, 52);
                lemma_pow2_adds(260, 52);
                lemma_pow2_adds(312, 52);
                lemma_pow2_adds(364, 52);
                broadcast use group_mul_is_distributive;
                broadcast use lemma_mul_is_associative;
                }
                nine_limbs_to_nat_direct(limbs);
            }
        }

        proof fn lemma_five_limbs_equals_slice_to_nat64(limbs: &[u64; 5])
        ensures 
            to_nat_direct(*limbs) == slice_to_nat64(limbs)
        {
            let seq = limbs@.map(|i, x| x as nat);

            calc! {
                (==)
                slice_to_nat64(limbs); {
                }
                seq_to_nat(seq); {
                    reveal_with_fuel(seq_to_nat, 6);
                }
                (limbs[0] as nat) +
                ((limbs[1] as nat) + 
                 ((limbs[2] as nat) + 
                  ((limbs[3] as nat) + 
                   (limbs[4] as nat) * pow2(52)
                  ) * pow2(52)
                 ) * pow2(52)
                ) * pow2(52); {
                lemma_pow2_adds(52, 52);
                lemma_pow2_adds(104, 52);
                lemma_pow2_adds(156, 52);
                broadcast use group_mul_is_distributive;
                broadcast use lemma_mul_is_associative;
                }
                (limbs[0] as nat) +
                pow2(52) * (limbs[1] as nat) +
                pow2(104) * (limbs[2] as nat) +
                pow2(156) * (limbs[3] as nat) +
                pow2(208) * (limbs[4] as nat); {
                }
                to_nat_direct(*limbs);
            }
        }

        pub open spec fn to_nat_direct(limbs: [u64; 5]) -> nat {
            (limbs[0] as nat) +
            pow2(52) * (limbs[1] as nat) +
            pow2(104) * (limbs[2] as nat) +
            pow2(156) * (limbs[3] as nat) +
            pow2(208) * (limbs[4] as nat)
        }

        pub open spec fn to_nat_gen_u32(limbs: &[u32], num_limbs: int, bits_per_limb: int) -> nat
        decreases num_limbs
        {
            if num_limbs <= 0 {
                0
            } else {
                let limb_value = (limbs[num_limbs - 1] as nat) * pow2(((num_limbs - 1) * bits_per_limb) as nat);
                limb_value + to_nat_gen_u32(limbs, num_limbs - 1, bits_per_limb)
            }
        }

        // Interpret limbs as a little-endian integer with 52-bit limbs
        pub open spec fn to_nat(limbs: &[u64; 5]) -> nat {
            to_nat_gen_u64(limbs, 5, 52)
        }

        // Modular reduction of to_nat mod L
        spec fn to_scalar(limbs: &[u64; 5]) -> nat {
            to_nat(limbs) % group_order()
        }

        /// natural value of a 256 bit bitstring represented as array of 32 bytes
        pub open spec fn bytes_to_nat(bytes: &[u8; 32]) -> nat {
            // Convert bytes to nat in little-endian order using recursive helper
            bytes_to_nat_rec(bytes, 0)
        }

        pub open spec fn bytes_to_nat_rec(bytes: &[u8; 32], index: int) -> nat
        decreases 32 - index
        {
            if index >= 32 {
                0
            } else {
                (bytes[index] as nat) * pow2(index as nat) + bytes_to_nat_rec(bytes, index + 1)
            }
        }

        // Generic function to convert array of words to natural number
        // Takes: array of words, number of words, bits per word
        // Note: This is a specification function that works with concrete types
        pub open spec fn words_to_nat_gen_u64(words: &[u64], num_words: int, bits_per_word: int) -> nat
        decreases num_words
        {
            if num_words <= 0 {
                0
            } else {
                let word_value = (words[num_words - 1] as nat) * pow2(((num_words - 1) * bits_per_word) as nat);
                word_value + words_to_nat_gen_u64(words, num_words - 1, bits_per_word)
            }
        }

        pub open spec fn words_to_nat_gen_u32(words: &[u32], num_words: int, bits_per_word: int) -> nat
        decreases num_words
        {
            if num_words <= 0 {
                0
            } else {
                let word_value = (words[num_words - 1] as nat) * pow2(((num_words - 1) * bits_per_word) as nat);
                word_value + words_to_nat_gen_u32(words, num_words - 1, bits_per_word)
            }
        }

        // natural value of a 256 bit bitstring represented as an array of 4 words of 64 bits
        // Now implemented using the generic function
        pub open spec fn words_to_nat(words: &[u64; 4]) -> nat {
            words_to_nat_gen_u64(words, 4, 64)
        }

        // Group order: the value of L as a natural number
        pub open spec fn group_order() -> nat {
            (1u64 << 252) as nat + 27742317777372353535851937790883648493nat
        }

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
            proof {
                assert(1u128 << 52 == 1u64 << 52) by (bit_vector);
                calc! {
                    (<)
                    (x as u128) * (y as u128); (<=) {
                        if x > 0 {
                            lemma_mul_strict_inequality(y as int, (1u128 << 52) as int, x as int);
                        } else {
                            assert(x == 0);
                            assert((x as u128) * (y as u128) == 0);
                        }
                    }
                    (x as u128) * (1u128 << 52); (<) {
                        lemma_mul_strict_inequality(x as int, (1u128 << 52) as int, (1u128 << 52) as int);
                    }
                    (1u128 << 52) * (1u128 << 52);
                }
                assert((1u128 << 52) * (1u128 << 52) == (1u128 << 104)) by (compute);
            }
            (x as u128) * (y as u128)
        }

        pub struct Scalar52 {
            // ADAPTED CODE LINE: we give a name to the field: "limbs"
            pub limbs: [u64; 5],
        }

    impl Scalar52 {

        /****** IMPLEMENTATION CONSTANTS AND FUNCTIONS ********/
        pub const ZERO: Scalar52 = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };

        /// Unpack a 32 byte / 256 bit scalar into 5 52-bit limbs.
        #[rustfmt::skip] // keep alignment of s[*] calculations
        /* ADAPTED CODE LINE: we give a name to the output: "s" */
        pub fn from_bytes(bytes: &[u8; 32]) -> (s: Scalar52)
        // SPECIFICATION: unpacking keeps the same nat value
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
        // let mut s = Scalar52::ZERO; // ORIGINAL IMPLEMENTATION
        let mut s = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof {
            assert(Scalar52::ZERO == Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] });
            assert(s == Scalar52::ZERO); // PROVES EQUIVALENCE TO ORIGINAL IMPLEMENTATION
        }

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
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> Scalar52 {
        // TODO; just signature for now
        Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] }
    }

    /// Pack the limbs of this `Scalar52` into 32 bytes
    #[rustfmt::skip] // keep alignment of s[*] calculations
    #[allow(clippy::identity_op)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_bytes(self) -> (s: [u8; 32])
    // DIFF-SPEC-3: we give a name to the output: "s"
    // SPECIFICATION: packing keeps the same nat value
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
        to_nat(&s.limbs) == to_nat(&a.limbs) + to_nat(&b.limbs),
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
           invariant //0 <= i <= 5,
           // forall|j: int| 0 <= j < i ==> sum.limbs[j] < 1u64 << 52,
            (0 <= i < 5) ==> a.limbs[i as int] < (1u64 << 52),
            (0 <= i < 5) ==> b.limbs[i as int] < (1u64 << 52),
            carry < (1u64 << 54),
        {
            proof {
                assert(0 <= i < 5);
                assert(a.limbs[i as int] < 1u64 << 52);
                assert(b.limbs[i as int] < 1u64 << 52);
                assert((1u64 << 52) + (1u64 << 52) == (1u64 << 53)) by (bit_vector);
                assert(a.limbs[i as int] + b.limbs[i as int] < 1u64 << 53);
                assert(carry < (1u64 << 54));
                assert(carry >> 52 >= 0u64);
                assert((carry >> 52) < (1u64 << 54)) by (bit_vector);
                assert((1u64 << 53) + 3 < (1u64 << 54)) by (bit_vector);
                assert((1u64 << 53) + (1u64 << 54) <= (1u64 << 55)) by (bit_vector);
                assert((a.limbs[i as int] + b.limbs[i as int] + (carry >> 52)) < (1u64 << 55));
            }
            carry = a.limbs[i] + b.limbs[i] + (carry >> 52);
            sum.limbs[i] = carry & mask;
            assume( (0 <= i < 5) ==> a.limbs[i as int] < (1u64 << 52));
            assume( (0 <= i < 5) ==> b.limbs[i as int] < (1u64 << 52));
            assume(false);
        }

        // subtract l if the sum is >= l

        /*** BEGIN: ADAPTED CODE BLOCK ***/

        /* ORIGINAL CODE */
        /*let mut s = Scalar52::sub(&sum, &Self::L);*/
        /* OUR ADAPTED CODE FOR VERUS; PROVED EQUIVALENT TO ORIGINAL CODE */
        let l_value = Scalar52 { limbs: [0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0x0000000000000000, 0x0000100000000000] };
        assert(to_nat(&l_value.limbs) == to_nat(&L.limbs));
        assume(false); // TODO: complete the proof

        Scalar52::sub(&sum, &l_value)

        /*** END: ADAPTED CODE BLOCK ***/

    }

    /// Compute `a - b` (mod l)
    pub fn sub(a: &Scalar52, b: &Scalar52) -> (s: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] < (1u64 << 52),
        forall|i: int| 0 <= i < 5 ==> b.limbs[i] < (1u64 << 52),
    ensures
        to_nat(&s.limbs) == to_nat(&a.limbs) - to_nat(&b.limbs),
    {
        //let mut difference = Scalar52::ZERO;
         let mut difference = Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] };
        proof {
            assert(Scalar52::ZERO == Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] });
            assert(difference == Scalar52::ZERO);
            assert(1u64 << 52 > 0) by (bit_vector);
        }
        let mask = (1u64 << 52) - 1;

        // a - b
        let mut borrow: u64 = 0;
        for i in 0..5
            invariant 0 <= i <= 5,
                      forall|j: int| 0 <= j < 5 ==> b.limbs[j] < (1u64 << 52),
        {
            proof {
                assert ((borrow >> 63) < 2) by (bit_vector);
            }
            borrow = a.limbs[i].wrapping_sub(b.limbs[i] + (borrow >> 63));
            difference.limbs[i] = borrow & mask;
        }

        // conditionally add l if the difference is negative
        let mut carry: u64 = 0;
        for i in 0..5 {
            let underflow = Choice::from((borrow >> 63) as u8);
          /*** BEGIN: ADAPTED CODE BLOCK ***/
          // ORIGINAL CODE
         //   let addend = u64::conditional_select(&0, &constants::L[i], underflow);
        // OUR ADAPTED CODE FOR VERUS
            let addend = select(&0, &L.limbs[i], underflow);
        /*** END: ADAPTED CODE BLOCK ***/
            assume (carry >> 52 < 2);
            assume (difference.limbs[i as int] < 1 << 52);
            assume (L.limbs[i as int] < 1 << 52);
            carry = (carry >> 52) + difference.limbs[i] + addend;
            difference.limbs[i] = carry & mask;
        }
        assume(false); // TODO: complete the proof
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
        nine_limbs_to_nat_direct(&z) == to_nat_direct(a.limbs) * to_nat_direct(b.limbs),
    {
        let mut z = [0u128; 9];

        z[0] = m(a.limbs[0], b.limbs[0]);

        proof {
            // Each m() result is < 2^104
            // Sum: 2^104 + 2^104 = 2^105 < 2^128
            assert((1u128 << 104) + (1u128 << 104) == (1u128 << 105)) by (bit_vector);
        }
        z[1] = m(a.limbs[0], b.limbs[1]) + m(a.limbs[1], b.limbs[0]);

        proof {
            // Each m() result is < 2^104
            // Sum: 3 * 2^104 = 3 * 2^104 < 2^106 < 2^128
            assert(3u128 * (1u128 << 104) < (1u128 << 106)) by (bit_vector);
        }
        z[2] = m(a.limbs[0], b.limbs[2]) + m(a.limbs[1], b.limbs[1]) + m(a.limbs[2], b.limbs[0]);

        proof {
            // Each m() result is < 2^104
            // Sum: 4 * 2^104 = 2^2 * 2^104 = 2^106 < 2^128

            assert(4u128 * (1u128 << 104) == (1u128 << 2) * (1u128 << 104)) by (bit_vector);
            assert((1u128 << 2) * (1u128 << 104) == (1u128 << 106)) by (bit_vector);
        }
        z[3] = m(a.limbs[0], b.limbs[3]) + m(a.limbs[1], b.limbs[2]) + m(a.limbs[2], b.limbs[1]) + m(a.limbs[3], b.limbs[0]);

        proof {
            // Each m() result is < 2^104
            // Sum: 5 * 2^104 < 8 * 2^104 = 2^3 * 2^104 = 2^107 < 2^128
            assert(8u128 == (1u128 << 3)) by (bit_vector);
            assert((1u128 << 3) * (1u128 << 104) == (1u128 << 107)) by (bit_vector);
        }
        z[4] = m(a.limbs[0], b.limbs[4]) + m(a.limbs[1], b.limbs[3]) + m(a.limbs[2], b.limbs[2]) + m(a.limbs[3], b.limbs[1]) + m(a.limbs[4], b.limbs[0]);
        z[5] =                 m(a.limbs[1], b.limbs[4]) + m(a.limbs[2], b.limbs[3]) + m(a.limbs[3], b.limbs[2]) + m(a.limbs[4], b.limbs[1]);
        z[6] =                                 m(a.limbs[2], b.limbs[4]) + m(a.limbs[3], b.limbs[3]) + m(a.limbs[4], b.limbs[2]);
        z[7] =                                                 m(a.limbs[3], b.limbs[4]) + m(a.limbs[4], b.limbs[3]);
        z[8] =                                                                 m(a.limbs[4], b.limbs[4]);

        proof {
            assert(to_nat_direct(a.limbs) * to_nat_direct(b.limbs) == nine_limbs_to_nat_direct(&z)) by {
                broadcast use group_mul_is_commutative_and_distributive;
                broadcast use lemma_mul_is_associative;

                lemma_pow2_adds(52, 52);
                lemma_pow2_adds(52, 104);
                lemma_pow2_adds(52, 156);
                lemma_pow2_adds(52, 208);
                lemma_pow2_adds(104, 104);
                lemma_pow2_adds(104, 156);
                lemma_pow2_adds(104, 208);
                lemma_pow2_adds(156, 156);
                lemma_pow2_adds(156, 208);
                lemma_pow2_adds(208, 208);
            };
        }

        z
    }

    /// Compute `a^2`
    #[inline(always)]
    #[rustfmt::skip] // keep alignment of calculations
    pub (crate) fn square_internal(a: &Scalar52) -> (z: [u128; 9])
    requires
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] < (1u64 << 52),
    ensures
        nine_limbs_to_nat_direct(&z) == to_nat_direct(a.limbs) * to_nat_direct(a.limbs),
    {
        let mut z = [0u128; 9];

        z[0] = m(a.limbs[0], a.limbs[0]);

        proof {
            // m() ensures its result is < 2^104
            // Since m_result < 2^104, we have m_result * 2 < 2^105
            // and 2^105 is well within u128 bounds
            assert((1u128 << 104) * 2 == (1u128 << 105)) by (bit_vector);
        }
        z[1] = m(a.limbs[0], a.limbs[1]) * 2;

        proof {
            // Each m() result is < 2^104
            // m_term1 * 2 < 2^105

            // Sum: 2^105 + 2^104 = 3 * 2^104 < 2^106 < 2^128
            assert((1u128 << 105) + (1u128 << 104) < (1u128 << 106)) by (bit_vector);
        }
        z[2] = m(a.limbs[0], a.limbs[2]) * 2 + m(a.limbs[1], a.limbs[1]);

        proof {
            // Each m() result is < 2^104
            // Each * 2 gives < 2^105

            // Sum: 2^105 + 2^105 = 2^106 < 2^128
            assert((1u128 << 105) + (1u128 << 105) == (1u128 << 106)) by (bit_vector);
        }
        z[3] = m(a.limbs[0], a.limbs[3]) * 2 + m(a.limbs[1], a.limbs[2]) * 2;

        proof {
            // Each m() result is < 2^104
            // First two terms * 2 give < 2^105

            // Sum: 2^105 + 2^105 + 2^104 = 2^106 + 2^104 < 2^107 < 2^128
            assert((1u128 << 106) + (1u128 << 104) < (1u128 << 107)) by (bit_vector);
        }
        z[4] = m(a.limbs[0], a.limbs[4]) * 2 + m(a.limbs[1], a.limbs[3]) * 2 + m(a.limbs[2], a.limbs[2]);
        z[5] =                 m(a.limbs[1], a.limbs[4]) * 2 + m(a.limbs[2], a.limbs[3]) * 2;
        z[6] =                                 m(a.limbs[2], a.limbs[4]) * 2 + m(a.limbs[3], a.limbs[3]);
        z[7] =                                                 m(a.limbs[3], a.limbs[4]) * 2;
        z[8] =                                                                 m(a.limbs[4], a.limbs[4]);

        proof {

            assert(to_nat_direct(a.limbs) * to_nat_direct(a.limbs) == nine_limbs_to_nat_direct(&z)) by {
                broadcast use group_mul_is_commutative_and_distributive;
                broadcast use lemma_mul_is_associative;

                lemma_pow2_adds(52, 52);
                lemma_pow2_adds(52, 104);
                lemma_pow2_adds(52, 156);
                lemma_pow2_adds(52, 208);
                lemma_pow2_adds(104, 104);
                lemma_pow2_adds(104, 156);
                lemma_pow2_adds(104, 208);
                lemma_pow2_adds(156, 156);
                lemma_pow2_adds(156, 208);
                lemma_pow2_adds(208, 208);
            };

        }

        z
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
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(&ab, &RR))
    }

    /// Compute `a^2` (mod l)
    #[inline(never)]
    pub fn square(&self) -> (result: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
    ensures
        to_nat(&result.limbs) == (to_nat(&self.limbs) * to_nat(&self.limbs)) % group_order(),
    {
        assume(false); // TODO: Add proper Montgomery arithmetic proofs
        let aa = Scalar52::montgomery_reduce(&Scalar52::square_internal(self));
        Scalar52::montgomery_reduce(&Scalar52::mul_internal(&aa, &RR))
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

    /// Helper function for part1 of Montgomery reduction
    #[inline(always)]
    fn montgomery_part1(sum: u128) -> (u128, u64)
    {
        assume(false); // TODO: Add proper bounds checking and proofs
        let p = (sum as u64).wrapping_mul(LFACTOR) & ((1u64 << 52) - 1);
        let carry = (sum + m(p, L.limbs[0])) >> 52;
        (carry, p)
    }

    /// Helper function for part2 of Montgomery reduction
    #[inline(always)]
    fn montgomery_part2(sum: u128) -> (u128, u64)
    {
        assume(false); // TODO: Add proper bounds checking and proofs
        let w = (sum as u64) & ((1u64 << 52) - 1);
        let carry = sum >> 52;
        (carry, w)
    }

    /// Montgomery reduction: reduces a 9-limb number to a 5-limb scalar
    /// This is the core of Montgomery arithmetic - it computes (x / R) mod L
    /// where R = 2^260 and L is the scalar field order
    pub (crate) fn montgomery_reduce(limbs: &[u128; 9]) -> (result: Scalar52)
    ensures
        // TODO: Add proper specification for Montgomery reduction
        true,
    {
        assume(false); // TODO: Add proper bounds checking and proofs
        // First half: compute Montgomery adjustment factor n and add n*L to make limbs divisible by R
        let (carry, n0) = Scalar52::montgomery_part1(limbs[0]);
        let (carry, n1) = Scalar52::montgomery_part1(carry + limbs[1] + m(n0, L.limbs[1]));
        let (carry, n2) = Scalar52::montgomery_part1(carry + limbs[2] + m(n0, L.limbs[2]) + m(n1, L.limbs[1]));
        let (carry, n3) = Scalar52::montgomery_part1(carry + limbs[3] + m(n1, L.limbs[2]) + m(n2, L.limbs[1]));
        let (carry, n4) = Scalar52::montgomery_part1(carry + limbs[4] + m(n0, L.limbs[4]) + m(n2, L.limbs[2]) + m(n3, L.limbs[1]));

        // Second half: limbs is now divisible by R, so divide by R by taking upper half
        let (carry, r0) = Scalar52::montgomery_part2(carry + limbs[5] + m(n1, L.limbs[4]) + m(n3, L.limbs[2]) + m(n4, L.limbs[1]));
        let (carry, r1) = Scalar52::montgomery_part2(carry + limbs[6] + m(n2, L.limbs[4]) + m(n4, L.limbs[2]));
        let (carry, r2) = Scalar52::montgomery_part2(carry + limbs[7] + m(n3, L.limbs[4]));
        let (carry, r3) = Scalar52::montgomery_part2(carry + limbs[8] + m(n4, L.limbs[4]));
        let r4 = carry as u64;

        // Result may be >= L, so attempt to subtract L
        let result = Scalar52 { limbs: [r0, r1, r2, r3, r4] };
        Scalar52::sub(&result, &L)
    }

    /// Puts a Scalar52 into Montgomery form, i.e. computes `a*R (mod L)`
    #[inline(never)]
    pub fn as_montgomery(&self) -> (result: Scalar52)
    requires
        forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
    ensures
        // TODO: Add proper specification for Montgomery form conversion
        true,
    {
        assume(false); // TODO: Add proper Montgomery arithmetic proofs
        Scalar52::montgomery_mul(self, &RR)
    }

    /// Takes a Scalar52 out of Montgomery form, i.e. computes `a/R (mod L)`
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


    /// Inverts the scalar using Montgomery logic (simplified)
    pub fn invert(&self) -> Scalar52 {
        // TODO
        Scalar52 { limbs: [0u64, 0u64, 0u64, 0u64, 0u64] }
    }

    /// Verification: scalar * scalar.invert() ≡ 1 mod L
    proof fn verify_invert_correct(&self)
   //     requires to_scalar(&self.limbs) != 0
    //    ensures (to_scalar(&self.limbs) * invert_spec(&self.limbs)) % group_order() == 1
    {
        assume(false);

    }

}


fn main()
{
    // Test scalar creation from bytes
    let test_bytes: [u8; 32] = [
        42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
    ];

    let scalar = Scalar52::from_bytes(&test_bytes);
    let inv_scalar = scalar.invert();
}
}
