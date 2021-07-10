// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis agora lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Field arithmetic modulo \\(p = 2\^{255} - 19\\).
//!
//! The `curve25519_dalek::field` module provides a type alias
//! `curve25519_dalek::field::FieldElement` to a field element type
//! defined in the `backend` module; either `FieldElement51` or
//! `FieldElement2625`.
//!
//! Field operations defined in terms of machine
//! operations, such as field multiplication or squaring, are defined in
//! the backend implementation.
//!
//! Field operations defined in terms of other field operations, such as
//! field inversion or square roots, are defined here.

use core::cmp::{Eq, PartialEq};

use subtle::ConditionallySelectable;
use subtle::ConditionallyNegatable;
use subtle::Choice;
use subtle::ConstantTimeEq;

use constants;
use backend;

#[cfg(feature = "fiat_u32_backend")]
pub use backend::serial::fiat_u32::field::*;
#[cfg(feature = "fiat_u64_backend")]
pub use backend::serial::fiat_u64::field::*;
/// A `FieldElement` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// The `FieldElement` type is an alias for one of the platform-specific
/// implementations.
/// Using formally-verified field arithmetic from fiat-crypto
#[cfg(feature = "fiat_u32_backend")]
pub type FieldElement = backend::serial::fiat_u32::field::FieldElement2625;
#[cfg(feature = "fiat_u64_backend")]
pub type FieldElement = backend::serial::fiat_u64::field::FieldElement51;

#[cfg(feature = "u64_backend")]
pub use backend::serial::u64::field::*;
/// A `FieldElement` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// The `FieldElement` type is an alias for one of the platform-specific
/// implementations.
#[cfg(feature = "u64_backend")]
pub type FieldElement = backend::serial::u64::field::FieldElement51;

#[cfg(feature = "u32_backend")]
pub use backend::serial::u32::field::*;
/// A `FieldElement` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// The `FieldElement` type is an alias for one of the platform-specific
/// implementations.
#[cfg(feature = "u32_backend")]
pub type FieldElement = backend::serial::u32::field::FieldElement2625;

#[cfg(feature = "u32e_backend")]
pub use backend::serial::u32e::field::*;
/// A `FieldElement` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// The `FieldElement` type is an alias for one of the platform-specific
/// implementations.
#[cfg(feature = "u32e_backend")]
pub type FieldElement = backend::serial::u32e::field::Engine25519;

impl Eq for FieldElement {}

impl PartialEq for FieldElement {
    fn eq(&self, other: &FieldElement) -> bool {
        self.ct_eq(other).unwrap_u8() == 1u8
    }
}

impl ConstantTimeEq for FieldElement {
    /// Test equality between two `FieldElement`s.  Since the
    /// internal representation is not canonical, the field elements
    /// are normalized to wire format before comparison.
    fn ct_eq(&self, other: &FieldElement) -> Choice {
        self.to_bytes().ct_eq(&other.to_bytes())
    }
}

impl FieldElement {
    /// Determine if this `FieldElement` is negative, in the sense
    /// used in the ed25519 paper: `x` is negative if the low bit is
    /// set.
    ///
    /// # Return
    ///
    /// If negative, return `Choice(1)`.  Otherwise, return `Choice(0)`.
    pub fn is_negative(&self) -> Choice {
        let bytes = self.to_bytes();
        (bytes[0] & 1).into()
    }

    /// Determine if this `FieldElement` is zero.
    ///
    /// # Return
    ///
    /// If zero, return `Choice(1)`.  Otherwise, return `Choice(0)`.
    pub fn is_zero(&self) -> Choice {
        let zero = [0u8; 32];
        let bytes = self.to_bytes();

        bytes.ct_eq(&zero)
    }

    /// Compute (self^(2^250-1), self^11), used as a helper function
    /// within invert() and pow22523().
    fn pow22501(&self) -> (FieldElement, FieldElement) {
        // Instead of managing which temporary variables are used
        // for what, we define as many as we need and leave stack
        // allocation to the compiler
        //
        // Each temporary variable t_i is of the form (self)^e_i.
        // Squaring t_i corresponds to multiplying e_i by 2,
        // so the pow2k function shifts e_i left by k places.
        // Multiplying t_i and t_j corresponds to adding e_i + e_j.
        //
        // Temporary t_i                      Nonzero bits of e_i
        //
        let t0  = self.square();           // 1         e_0 = 2^1
        let t1  = t0.square().square();    // 3         e_1 = 2^3
        let t2  = self * &t1;              // 3,0       e_2 = 2^3 + 2^0
        let t3  = &t0 * &t2;               // 3,1,0
        let t4  = t3.square();             // 4,2,1
        let t5  = &t2 * &t4;               // 4,3,2,1,0
        let t6  = t5.pow2k(5);             // 9,8,7,6,5
        let t7  = &t6 * &t5;               // 9,8,7,6,5,4,3,2,1,0
        let t8  = t7.pow2k(10);            // 19..10
        let t9  = &t8 * &t7;               // 19..0
        let t10 = t9.pow2k(20);            // 39..20
        let t11 = &t10 * &t9;              // 39..0
        let t12 = t11.pow2k(10);           // 49..10
        let t13 = &t12 * &t7;              // 49..0
        let t14 = t13.pow2k(50);           // 99..50
        let t15 = &t14 * &t13;             // 99..0
        let t16 = t15.pow2k(100);          // 199..100
        let t17 = &t16 * &t15;             // 199..0
        let t18 = t17.pow2k(50);           // 249..50
        let t19 = &t18 * &t13;             // 249..0

        (t19, t3)
    }

    /// Given a slice of public `FieldElements`, replace each with its inverse.
    ///
    /// All input `FieldElements` **MUST** be nonzero.
    #[cfg(feature = "alloc")]
    pub fn batch_invert(inputs: &mut [FieldElement]) {
        // Montgomery’s Trick and Fast Implementation of Masked AES
        // Genelle, Prouff and Quisquater
        // Section 3.2

        let n = inputs.len();
        let mut scratch = vec![FieldElement::one(); n];

        // Keep an accumulator of all of the previous products
        let mut acc = FieldElement::one();

        // Pass through the input vector, recording the previous
        // products in the scratch space
        for (input, scratch) in inputs.iter().zip(scratch.iter_mut()) {
            *scratch = acc;
            acc = &acc * input;
        }

	// acc is nonzero iff all inputs are nonzero
        assert_eq!(acc.is_zero().unwrap_u8(), 0);

        // Compute the inverse of all products
        acc = acc.invert();

        // Pass through the vector backwards to compute the inverses
        // in place
        for (input, scratch) in inputs.iter_mut().rev().zip(scratch.into_iter().rev()) {
            let tmp = &acc * input;
            *input = &acc * &scratch;
            acc = tmp;
        }
    }

    /// Given a nonzero field element, compute its inverse.
    ///
    /// The inverse is computed as self^(p-2), since
    /// x^(p-2)x = x^(p-1) = 1 (mod p).
    ///
    /// This function returns zero on input zero.
    pub fn invert(&self) -> FieldElement {
        // The bits of p-2 = 2^255 -19 -2 are 11010111111...11.
        //
        //                                 nonzero bits of exponent
        let (t19, t3) = self.pow22501();   // t19: 249..0 ; t3: 3,1,0
        let t20 = t19.pow2k(5);            // 254..5
        let t21 = &t20 * &t3;              // 254..5,3,1,0

        t21
    }

    /// Raise this field element to the power (p-5)/8 = 2^252 -3.
    fn pow_p58(&self) -> FieldElement {
        // The bits of (p-5)/8 are 101111.....11.
        //
        //                                 nonzero bits of exponent
        let (t19, _) = self.pow22501();    // 249..0
        let t20 = t19.pow2k(2);            // 251..2
        let t21 = self * &t20;             // 251..2,0

        t21
    }

    /// Given `FieldElements` `u` and `v`, compute either `sqrt(u/v)`
    /// or `sqrt(i*u/v)` in constant time.
    ///
    /// This function always returns the nonnegative square root.
    ///
    /// # Return
    ///
    /// - `(Choice(1), +sqrt(u/v))  ` if `v` is nonzero and `u/v` is square;
    /// - `(Choice(1), zero)        ` if `u` is zero;
    /// - `(Choice(0), zero)        ` if `v` is zero and `u` is nonzero;
    /// - `(Choice(0), +sqrt(i*u/v))` if `u/v` is nonsquare (so `i*u/v` is square).
    ///
    pub fn sqrt_ratio_i(u: &FieldElement, v: &FieldElement) -> (Choice, FieldElement) {
        // Using the same trick as in ed25519 decoding, we merge the
        // inversion, the square root, and the square test as follows.
        //
        // To compute sqrt(α), we can compute β = α^((p+3)/8).
        // Then β^2 = ±α, so multiplying β by sqrt(-1) if necessary
        // gives sqrt(α).
        //
        // To compute 1/sqrt(α), we observe that
        //    1/β = α^(p-1 - (p+3)/8) = α^((7p-11)/8)
        //                            = α^3 * (α^7)^((p-5)/8).
        //
        // We can therefore compute sqrt(u/v) = sqrt(u)/sqrt(v)
        // by first computing
        //    r = u^((p+3)/8) v^(p-1-(p+3)/8)
        //      = u u^((p-5)/8) v^3 (v^7)^((p-5)/8)
        //      = (uv^3) (uv^7)^((p-5)/8).
        //
        // If v is nonzero and u/v is square, then r^2 = ±u/v,
        //                                     so vr^2 = ±u.
        // If vr^2 =  u, then sqrt(u/v) = r.
        // If vr^2 = -u, then sqrt(u/v) = r*sqrt(-1).
        //
        // If v is zero, r is also zero.

        let v3 = &v.square()  * v;
        let v7 = &v3.square() * v;
        let mut r = &(u * &v3) * &(u * &v7).pow_p58();
        let check = v * &r.square();

        let i = &constants::SQRT_M1;

        let correct_sign_sqrt   = check.ct_eq(        u);
        let flipped_sign_sqrt   = check.ct_eq(     &(-u));
        let flipped_sign_sqrt_i = check.ct_eq(&(&(-u)*i));

        let r_prime = &constants::SQRT_M1 * &r;
        r.conditional_assign(&r_prime, flipped_sign_sqrt | flipped_sign_sqrt_i);

        // Choose the nonnegative square root.
        let r_is_negative = r.is_negative();
        r.conditional_negate(r_is_negative);

        let was_nonzero_square = correct_sign_sqrt | flipped_sign_sqrt;

        (was_nonzero_square, r)
    }

    /// Attempt to compute `sqrt(1/self)` in constant time.
    ///
    /// Convenience wrapper around `sqrt_ratio_i`.
    ///
    /// This function always returns the nonnegative square root.
    ///
    /// # Return
    ///
    /// - `(Choice(1), +sqrt(1/self))  ` if `self` is a nonzero square;
    /// - `(Choice(0), zero)           ` if `self` is zero;
    /// - `(Choice(0), +sqrt(i/self))  ` if `self` is a nonzero nonsquare;
    ///
    pub fn invsqrt(&self) -> (Choice, FieldElement) {
        FieldElement::sqrt_ratio_i(&FieldElement::one(), self)
    }
}

#[cfg(test)]
extern crate rand;

#[cfg(test)]
mod test {
    use field::*;
    use subtle::ConditionallyNegatable;

    /// Random element a of GF(2^255-19), from Sage
    /// a = 1070314506888354081329385823235218444233221\
    ///     2228051251926706380353716438957572
    static A_BYTES: [u8; 32] =
        [ 0x04, 0xfe, 0xdf, 0x98, 0xa7, 0xfa, 0x0a, 0x68,
          0x84, 0x92, 0xbd, 0x59, 0x08, 0x07, 0xa7, 0x03,
          0x9e, 0xd1, 0xf6, 0xf2, 0xe1, 0xd9, 0xe2, 0xa4,
          0xa4, 0x51, 0x47, 0x36, 0xf3, 0xc3, 0xa9, 0x17];

    /// Byte representation of a**2
    static ASQ_BYTES: [u8; 32] =
        [ 0x75, 0x97, 0x24, 0x9e, 0xe6, 0x06, 0xfe, 0xab,
          0x24, 0x04, 0x56, 0x68, 0x07, 0x91, 0x2d, 0x5d,
          0x0b, 0x0f, 0x3f, 0x1c, 0xb2, 0x6e, 0xf2, 0xe2,
          0x63, 0x9c, 0x12, 0xba, 0x73, 0x0b, 0xe3, 0x62];

    /// Byte representation of 1/a
    static AINV_BYTES: [u8; 32] =
        [0x96, 0x1b, 0xcd, 0x8d, 0x4d, 0x5e, 0xa2, 0x3a,
         0xe9, 0x36, 0x37, 0x93, 0xdb, 0x7b, 0x4d, 0x70,
         0xb8, 0x0d, 0xc0, 0x55, 0xd0, 0x4c, 0x1d, 0x7b,
         0x90, 0x71, 0xd8, 0xe9, 0xb6, 0x18, 0xe6, 0x30];

    /// Byte representation of a^((p-5)/8)
    static AP58_BYTES: [u8; 32] =
        [0x6a, 0x4f, 0x24, 0x89, 0x1f, 0x57, 0x60, 0x36,
         0xd0, 0xbe, 0x12, 0x3c, 0x8f, 0xf5, 0xb1, 0x59,
         0xe0, 0xf0, 0xb8, 0x1b, 0x20, 0xd2, 0xb5, 0x1f,
         0x15, 0x21, 0xf9, 0xe3, 0xe1, 0x61, 0x21, 0x55];

    #[test]
    fn a_mul_a_vs_a_squared_constant() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let asq = FieldElement::from_bytes(&ASQ_BYTES);
        assert_eq!(asq, &a * &a);
    }

    #[test]
    fn a_square_vs_a_squared_constant() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let asq = FieldElement::from_bytes(&ASQ_BYTES);
        assert_eq!(asq, a.square());
    }

    #[test]
    fn a_square2_vs_a_squared_constant() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let asq = FieldElement::from_bytes(&ASQ_BYTES);
        assert_eq!(a.square2(), &asq+&asq);
    }

    #[test]
    fn a_invert_vs_inverse_of_a_constant() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        let should_be_inverse = a.invert();
        assert_eq!(ainv, should_be_inverse);
        assert_eq!(FieldElement::one(), &a * &should_be_inverse);
    }

    #[test]
    fn batch_invert_a_matches_nonbatched() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ap58 = FieldElement::from_bytes(&AP58_BYTES);
        let asq  = FieldElement::from_bytes(&ASQ_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        let a2   = &a + &a;
        let a_list = vec![a, ap58, asq, ainv, a2];
        let mut ainv_list = a_list.clone();
        FieldElement::batch_invert(&mut ainv_list[..]);
        for i in 0..5 {
            assert_eq!(a_list[i].invert(), ainv_list[i]);
        }
    }

    #[test]
    fn sqrt_ratio_behavior() {
        let zero = FieldElement::zero();
        let one = FieldElement::one();
        let i = constants::SQRT_M1;
        let two = &one + &one; // 2 is nonsquare mod p.
        let four = &two + &two; // 4 is square mod p.

        // 0/0 should return (1, 0) since u is 0
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&zero, &zero);
        assert_eq!(choice.unwrap_u8(), 1);
        assert_eq!(sqrt, zero);
        assert_eq!(sqrt.is_negative().unwrap_u8(), 0);

        // 1/0 should return (0, 0) since v is 0, u is nonzero
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&one, &zero);
        assert_eq!(choice.unwrap_u8(), 0);
        assert_eq!(sqrt, zero);
        assert_eq!(sqrt.is_negative().unwrap_u8(), 0);

        // 2/1 is nonsquare, so we expect (0, sqrt(i*2))
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&two, &one);
        assert_eq!(choice.unwrap_u8(), 0);
        assert_eq!(sqrt.square(), &two * &i);
        assert_eq!(sqrt.is_negative().unwrap_u8(), 0);

        // 4/1 is square, so we expect (1, sqrt(4))
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&four, &one);
        assert_eq!(choice.unwrap_u8(), 1);
        assert_eq!(sqrt.square(), four);
        assert_eq!(sqrt.is_negative().unwrap_u8(), 0);

        // 1/4 is square, so we expect (1, 1/sqrt(4))
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&one, &four);
        assert_eq!(choice.unwrap_u8(), 1);
        assert_eq!(&sqrt.square() * &four, one);
        assert_eq!(sqrt.is_negative().unwrap_u8(), 0);
    }

    #[test]
    fn a_p58_vs_ap58_constant() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ap58 = FieldElement::from_bytes(&AP58_BYTES);
        assert_eq!(ap58, a.pow_p58());
    }

    #[test]
    fn equality() {
        let a    = FieldElement::from_bytes(&A_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        assert!(a == a);
        assert!(a != ainv);
    }

    /// Notice that the last element has the high bit set, which
    /// should be ignored
    static B_BYTES: [u8;32] =
        [113, 191, 169, 143,  91, 234, 121,  15,
         241, 131, 217,  36, 230, 101,  92, 234,
           8, 208, 170, 251,  97, 127,  70, 210,
          58,  23, 166,  87, 240, 169, 184, 178];

    #[test]
    fn from_bytes_highbit_is_ignored() {
        let mut cleared_bytes = B_BYTES;
        cleared_bytes[31] &= 127u8;
        let with_highbit_set    = FieldElement::from_bytes(&B_BYTES);
        let without_highbit_set = FieldElement::from_bytes(&cleared_bytes);
        assert_eq!(without_highbit_set, with_highbit_set);
    }

    #[test]
    fn conditional_negate() {
        let       one = FieldElement::one();
        let minus_one = FieldElement::minus_one();
        let mut x = one;
        x.conditional_negate(Choice::from(1));
        assert_eq!(x, minus_one);
        x.conditional_negate(Choice::from(0));
        assert_eq!(x, minus_one);
        x.conditional_negate(Choice::from(1));
        assert_eq!(x, one);
    }

    #[test]
    fn encoding_is_canonical() {
        // Encode 1 wrongly as 1 + (2^255 - 19) = 2^255 - 18
        let one_encoded_wrongly_bytes: [u8;32] = [0xee, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f];
        // Decode to a field element
        let one = FieldElement::from_bytes(&one_encoded_wrongly_bytes);
        // .. then check that the encoding is correct
        let one_bytes = one.to_bytes();
        assert_eq!(one_bytes[0], 1);
        for i in 1..32 {
            assert_eq!(one_bytes[i], 0);
        }
    }

    #[test]
    fn batch_invert_empty() {
        FieldElement::batch_invert(&mut []);
    }

    #[test]
    fn make_vectors() {
        // reminder to self: to create just this vector, run
        // cargo test field::test::make_vectors
        use std::fs::File;
        use std::io::prelude::*;
        use std::path::Path;
        use engine25519_as::*;
        use self::rand::Rng;

        fn write_helper(file: &mut File, elem: FieldElement) {
            let elem_bytes = elem.to_bytes();
            let _ = file.write(&elem_bytes);
            /*
            for i in 0..elem_bytes.len()/4 {
                let word: u32 = elem_bytes.pread::<u32>(i).unwrap();
                let _ = write!(file, "{:02x}", elem_bytes[i]);
            }
            let _ = write!(file, " ");*/
        }

        fn write_test_header(file: &mut File,
            loading_address: u32,
            mcode: &[i32],
            num_src_regs: u32,
            reg_window: u32,
            num_tests: u32,
        ) {
            let mcode_len: u32 = mcode.len() as u32;
            let _ = file.write(&(0x5645_4354 as u32).to_le_bytes());
            let _ = file.write(&( ((loading_address & 0xFFFF << 16)
                                | (mcode_len & 0xFFFF)
                                ) as u32)
                                .to_le_bytes() ); // load address 0 + code length
            let _ = file.write(&( ((num_src_regs & 0x1F) << 27 // number of source registers per test
                                | (reg_window & 0xF) << 23   // register window to use
                                | (num_tests & 0x3F_FFFF)   // number of tests
                                ) as u32)
                                .to_le_bytes() ); // 2 registers, window 0, 1 vector
            // the actual microcode
            for i in 0..mcode_len {
                let _ = file.write(&(mcode[i as usize] as u32).to_le_bytes());
            }

            // pad with 0's to a 256-bit stride
            for _ in 0..(8 - ((3 + mcode_len) % 8)) {  // 3 words for metadata + code length
                let _ = file.write(&[0,0,0,0]); // write out 32-bit words of 0 (as array of u8)
            }
        }

        let path = Path::new("test_vectors.bin");
        let mut file = File::create(&path).unwrap();

        // Metadata record format. Each test should have the following layout:
        //   0x0 0x56454354   "VECT" - indicates a valid vector set
        //   0x4 [31   load address   16]                                 [15  length of code  0]
        //   0x8 [31  N registers to load  27] [26 W window 23] [22  X number of vectors sets  0]
        //   0xC [microcode] (variable length)
        //   [ padding of 0x0 until 0x20 * align ]
        //   0x20*align [X test vectors]
        // Records can repeat; as long as "VECT" is found, the test framework will attemp to load and run the test
        //
        // End of records MUST end with a word that is NOT 0x56454354
        //    This is because the ROM read can "wrap around" and the test will run forever
        //    We use 0xFFFF_FFFF to indicate this
        //
        // For each test, vectors are storted with the following convention:
        //   Check result is always in r31
        //   N Registers loaded starting at r0 into window W
        fn test_add(mut file: &mut File) {
            // test addition. two input registers (r0, r1), one output register (r31).
            let num_src_regs = 2;
            let reg_window = 0;
            let num_tests = 5; // one manual test + 4 random vectors
            let loading_address = 0; // microcode loading address

            let mcode = assemble_engine25519!(
                start:
                    add %2, %0, %1
                    trd %3, %2
                    sub %31, %2, %3
                    fin
            );

            write_test_header(&mut file, loading_address, &mcode, num_src_regs, reg_window, num_tests);

            // test vectors
            // 1 plus -1 = 0 -> this works overflow path
            let a = FieldElement::one();
            let b = FieldElement::minus_one();
            let q = &a + &b;

            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // four random numbers
            for _ in 0..4 {
                let a = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let b = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let q = &a + &b;
                write_helper(&mut file, a);
                write_helper(&mut file, b);
                write_helper(&mut file, q);
            }
        }

        fn ref_fact(n: usize) -> FieldElement {
            let mut a = FieldElement::one();
            let mut result = FieldElement::one();
            for _ in 0..n {
                result = &result * &a;
                a = &a + &FieldElement::one();
            }
            result
        }

        fn test_loop(mut file: &mut File) {
            // test addition. two input registers (r0, r1), one output register (r31).
            let num_src_regs = 1;
            let reg_window = 0;
            let num_tests = 5; // 5 sequential tests
            let loading_address = 0; // microcode loading address

            // compute a factorial using a loop
            // also tests psa/psb with constants
            // %0 is the argument, %31 is the result
            // %10 is the multiplicand for the factorial
            // %0 is re-used as the loop counter
            let mcode = assemble_engine25519!(
                start:
                    psa %10, #1
                    psb %31, #1
                loop:
                    mul %31, %31, %10
                    add %10, %10, #1
                    sub %0, %0, #1
                    brz end, %0
                    brz loop, #0
                end:
                    fin
            );

            write_test_header(&mut file, loading_address, &mcode, num_src_regs, reg_window, num_tests);

            // test vectors
            let mut n = FieldElement::one();
            for i in 1..6 {
                write_helper(&mut file, n);
                n = &n + &FieldElement::one(); // mirror i's progression
                let q = ref_fact(i);
                write_helper(&mut file, q);
            }
        }

        fn test_cswap(mut file: &mut File) {
            // test cswap. three input registers: (r0, r1) to swap, (r2) to control swap, one output register (r31).
            let num_src_regs = 3;
            let reg_window = 15;
            let num_tests = 4;
            let loading_address = 0; // microcode loading address

            // psa is used to move %0 to %31 mostly to test that psa works
            let mcode = assemble_engine25519!(
                start:
                    xor %30, %0, %1
                    msk %30, %2, %30
                    xor %0, %30, %0
                    xor %1, %30, %1
                    psa %31, %0
                    fin
            );
            write_test_header(&mut file, loading_address, &mcode, num_src_regs, reg_window, num_tests);

            // test vectors
            for i in 0..4 {
                let a = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let b = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let swap: FieldElement;
                let q: FieldElement;
                if i % 2 == 0 {
                    swap = FieldElement::zero();
                    q = a;
                } else {
                    swap = FieldElement::one();
                    q = b;
                }
                write_helper(&mut file, a);
                write_helper(&mut file, b);
                write_helper(&mut file, swap);
                write_helper(&mut file, q);
            }
        }

        fn test_mul(mut file: &mut File) {
            let extra_tests = 100; // vary this to add more random vectors at the end

            // test multiplier. two input registers: (r0, r1), one output register (r31).
            let num_src_regs = 2;
            let reg_window = 0;
            let num_tests = 22 + extra_tests;
            let loading_address = 0; // microcode loading address

            let mcode = assemble_engine25519!(
                start:
                    mul %31, %1, %0
                    fin
            );
            write_test_header(&mut file, loading_address, &mcode, num_src_regs, reg_window, num_tests);

            // 1: 1*1 - simple case
            let a = FieldElement::one();
            let b = FieldElement::one();
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 2: 1*-1 - simple case
            let a = FieldElement::one();
            let b = FieldElement::minus_one();
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 3
            let a = FieldElement::from_bytes(&[
                0xEB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7f,]);
            let b = FieldElement::one();
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 4
            let a = FieldElement::from_bytes(&[
                0xA4, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
                0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
                0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
                0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0x2A,
                ]);
            let b = FieldElement::from_bytes(&[
                3, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ]);
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 5
            let a = FieldElement::from_bytes(&[
                0xED, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7f,
                ]);
            let b = FieldElement::from_bytes(&[
                1, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ]);
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 6
            let a = FieldElement::from_bytes(&[
                0xF7, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3f,
                ]);
            let b = FieldElement::from_bytes(&[
                2, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ]);
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 7
            let a = FieldElement::from_bytes(&[
                0xA5, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
                0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
                0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
                0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0x2A,
                ]);
            let b = FieldElement::from_bytes(&[
                3, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ]);
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 8
            let a = FieldElement::from_bytes(&[
                0xA5, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
                0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
                0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA,
                0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0x2A,
                ]);
            let b = FieldElement::from_bytes(&[
                3, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ]);
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 9: not normalized input!
            let a = FieldElement::from_bytes(&[
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7f,
                ]);
            let b = FieldElement::from_bytes(&[
                1, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ]);
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 10
            let a = FieldElement::from_bytes(&[
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3f,
                ]);
            let b = FieldElement::from_bytes(&[
                2, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ]);
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 11
            let a = FieldElement::from_bytes(&[
                0xF8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x3f,
                ]);
            let b = FieldElement::from_bytes(&[
                4, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ]);
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 12
            let a = FieldElement::from_bytes(&[
                0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99,
                0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99,
                0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99,
                0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x19,
                ]);
            let b = FieldElement::from_bytes(&[
                5, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ]);
            let q = &a * &b;
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 13
            let a = FieldElement::from_bytes(&[
                0x94, 0xc2, 0xf9, 0x3b, 0xb7, 0xe7, 0xe5, 0x78,
                0x22, 0x23, 0x00, 0x14, 0x55, 0x41, 0x56, 0x05,
                0xb0, 0xfe, 0x1d, 0x61, 0x0d, 0x0b, 0x08, 0xc9,
                0x22, 0x3a, 0xc4, 0x55, 0xcd, 0xb0, 0x93, 0x52,
                ]);
            let b = FieldElement::from_bytes(&[
                0x17, 0x0c, 0x1e, 0x93, 0xea, 0x6e, 0x51, 0xc0,
                0xcb, 0xf9, 0x48, 0xe7, 0x60, 0x36, 0x1f, 0xaf,
                0x65, 0x8d, 0xf2, 0xe9, 0x36, 0xd2, 0x71, 0x00,
                0x94, 0x56, 0x48, 0x55, 0x1c, 0xe9, 0x48, 0x1d,
            ]);
            let q = &a * &b;
            //  08 55 8c eb 97 70 ea b5  da c7 eb 83 d1 3a b3 a7
            //  99 31 f4 be 87 3c 26 e9  1c d0 9c 82 08 da 5c 0d
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);

            // 14
            let a = FieldElement::from_bytes(&[
                0x6d, 0xad, 0x72, 0xf8, 0x64, 0x1b, 0x8f, 0x43,
                0xba, 0x50, 0xb5, 0x83, 0xe1, 0x5f, 0xd6, 0x43,
                0x9b, 0xb2, 0xbc, 0x60, 0xae, 0x92, 0x3a, 0xdb,
                0x05, 0x83, 0x4a, 0xd6, 0x19, 0x36, 0x95, 0x87,
                ]);
            let b = FieldElement::from_bytes(&[
                0xe4, 0x34, 0x15, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ]);
            let q = &a * &b;
            //  000002a6 bc74dd8d 2e43fe6f 23132ca5 d3e70179 c129465a 7c4d49cc ccf864a7
            write_helper(&mut file, a);
            write_helper(&mut file, b);
            write_helper(&mut file, q);
            // 0xa7, 0x64, 0xf8, 0xcc, 0xcc, 0x49, 0x4d, 0x7c,
            // 0x5a, 0x46, 0x29, 0xc1, 0x79, 0x01, 0xe7, 0xd3,
            // 0xa5, 0x2c, 0x13, 0x23, 0x6f, 0xfe, 0x43, 0x2e,
            // 0x8d, 0xdd, 0x74, 0xbc, 0xa6, 0x02, 0x00, 0x00,

            // 15-22
            for _ in 0..(8+extra_tests) {
                let a = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let b = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let q = &a * &b;
                write_helper(&mut file, a);
                write_helper(&mut file, b);
                write_helper(&mut file, q);
            }
        }


        fn test_diff_add_and_double(mut file: &mut File) {
            use montgomery::ProjectivePoint;

            // test cswap. three input registers: (r0, r1) to swap, (r2) to control swap, one output register (r31).
            let num_src_regs = 5;
            let reg_window = 0;
            let num_tests = 8;
            let loading_address = 0; // microcode loading address

            let mcode = assemble_engine25519!(
                start:
                    // test preamble
                    psa %20, %0
                    psa %21, %1
                    psa %22, %2
                    psa %23, %3
                    psa %24, %4

                    // P.U in %20
                    // P.W in %21
                    // Q.U in %22
                    // Q.W in %23
                    // affine_PmQ in %24
                    // %30 is the TRD scratch register
                    // %29 is the subtraction temporary value register

                    // let t0 = &P.U + &P.W;
                    add %0, %20, %21
                    trd %30, %0
                    sub %0, %0, %30
                    // let t1 = &P.U - &P.W;
                    sub %21, #3, %21    // negate &P.W using #FIELDPRIME (#3)
                    add %1, %20, %21
                    trd %30, %1
                    sub %1, %1, %30
                    // let t2 = &Q.U + &Q.W;
                    add %2, %22, %23
                    trd %30, %2
                    sub %2, %2, %30
                    // let t3 = &Q.U - &Q.W;
                    sub %23, #3, %23
                    add %3, %22, %23
                    trd %30, %3
                    sub %3, %3, %30
                    // let t4 = t0.square();   // (U_P + W_P)^2 = U_P^2 + 2 U_P W_P + W_P^2
                    mul %4, %0, %0
                    // let t5 = t1.square();   // (U_P - W_P)^2 = U_P^2 - 2 U_P W_P + W_P^2
                    mul %5, %1, %1
                    // let t6 = &t4 - &t5;     // 4 U_P W_P
                    sub %29, #3, %5
                    add %6, %4, %29
                    trd %30, %6
                    sub %6, %6, %30
                    // let t7 = &t0 * &t3;     // (U_P + W_P) (U_Q - W_Q) = U_P U_Q + W_P U_Q - U_P W_Q - W_P W_Q
                    mul %7, %0, %3
                    // let t8 = &t1 * &t2;     // (U_P - W_P) (U_Q + W_Q) = U_P U_Q - W_P U_Q + U_P W_Q - W_P W_Q
                    mul %8, %1, %2
                    // let t9  = &t7 + &t8;    // 2 (U_P U_Q - W_P W_Q)
                    add %9, %7, %8
                    trd %30, %9
                    sub %9, %9, %30
                    // let t10 = &t7 - &t8;    // 2 (W_P U_Q - U_P W_Q)
                    sub %29, #3, %8
                    add %10, %7, %29
                    trd %30, %10
                    sub %10, %10, %30
                    // let t11 =  t9.square(); // 4 (U_P U_Q - W_P W_Q)^2
                    mul %11, %9, %9
                    // let t12 = t10.square(); // 4 (W_P U_Q - U_P W_Q)^2
                    mul %12, %10, %10
                    // let t13 = &APLUS2_OVER_FOUR * &t6; // (A + 2) U_P U_Q
                    mul %13, #4, %6   // #4 is A+2/4
                    // let t14 = &t4 * &t5;    // ((U_P + W_P)(U_P - W_P))^2 = (U_P^2 - W_P^2)^2
                    mul %14, %4, %5
                    // let t15 = &t13 + &t5;   // (U_P - W_P)^2 + (A + 2) U_P W_P
                    add %15, %13, %5
                    trd %30, %15
                    sub %15, %15, %30
                    // let t16 = &t6 * &t15;   // 4 (U_P W_P) ((U_P - W_P)^2 + (A + 2) U_P W_P)
                    mul %16, %6, %15
                    // let t17 = affine_PmQ * &t12; // U_D * 4 (W_P U_Q - U_P W_Q)^2
                    mul %17, %24, %12    // affine_PmQ loaded into %24

                    ///// these can be eliminated down the road, but included for 1:1 algorithm correspodence to reference in early testing
                    // let t18 = t11;               // W_D * 4 (U_P U_Q - W_P W_Q)^2
                    psa %18, %11

                    // P.U = t14;  // U_{P'} = (U_P + W_P)^2 (U_P - W_P)^2
                    psa %20, %14
                    // P.W = t16;  // W_{P'} = (4 U_P W_P) ((U_P - W_P)^2 + ((A + 2)/4) 4 U_P W_P)
                    psa %21, %16
                    // Q.U = t18;  // U_{Q'} = W_D * 4 (U_P U_Q - W_P W_Q)^2
                    psa %22, %18
                    // Q.W = t17;  // W_{Q'} = U_D * 4 (W_P U_Q - U_P W_Q)^2
                    psa %23, %17

                    // test postamble -- sum together the points to create a single composite test output
                    add %31, %20, %21
                    trd %30, %31
                    sub %31, %31, %30
                    add %31, %31, %22
                    trd %30, %31
                    sub %31, %31, %30
                    add %31, %31, %23
                    trd %30, %31
                    sub %31, %31, %30 // leave result in r31

                    fin  // finish execution
            );            write_test_header(&mut file, loading_address, &mcode, num_src_regs, reg_window, num_tests);

            use montgomery::differential_add_and_double;

            // test vectors
            for _ in 0..8 {
                let pu = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let pw = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let qu = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let qw = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                let pmq = FieldElement::from_bytes(&rand::thread_rng().gen::<[u8; 32]>());
                write_helper(&mut file, pu);
                write_helper(&mut file, pw);
                write_helper(&mut file, qu);
                write_helper(&mut file, qw);
                write_helper(&mut file, pmq);
                #[allow(non_snake_case)]
                let mut P: ProjectivePoint = ProjectivePoint{U:pu, W:pw};
                #[allow(non_snake_case)]
                let mut Q: ProjectivePoint = ProjectivePoint{U:qu, W:qw};
                differential_add_and_double(&mut P, &mut Q, &pmq);
                write_helper(&mut file, &(&P.U + &P.W) + &(&Q.U + &Q.W));
            }
        }

        fn test_scalar_mul(mut file: &mut File) {
            use montgomery::ProjectivePoint;

            // test cswap. three input registers: (r0, r1) to swap, (r2) to control swap, one output register (r31).
            let num_src_regs = 7;
            let reg_window = 0;
            let num_tests = 1;
            let loading_address = 0; // microcode loading address

            let mcode = assemble_engine25519!(
                start:
                    psa %25, %0  // x0.U
                    psa %26, %1  // x0.W
                    psa %27, %2  // x1.U
                    psa %28, %3  // x1.W
                    psa %24, %4  // affine point
                    psa %31, %5  // scalar
                    psa %19, %6  // the number 254

                    // P.U in %20
                    // P.W in %21
                    // Q.U in %22
                    // Q.W in %23
                    // affine_PmQ in %24
                    // %30 is the TRD scratch register and cswap dummy
                    // %29 is the subtraction temporary value register and k_t
                    // x0.U in %25
                    // x0.W in %26
                    // x1.U in %27
                    // x1.W in %28
                    // %19 is the loop counter, starts with 254 (if 0, loop runs exactly once)
                    // %31 is the scalar
                    // %18 is the swap variable
                    psa %18, #0

                    // for i in (0..255).rev()
                mainloop:
                    // let choice: u8 = (bits[i + 1] ^ bits[i]) as u8;
                    // ProjectivePoint::conditional_swap(&mut x0, &mut x1, choice.into());
                    xbt %29, %31        // orignally[k_t = (k>>t) & 1] now[k_t = k[254]]
                    shl %31, %31        // k = k<<1
                    xor %18, %18, %29   // swap ^= k_t

                    // cswap x0.U (%25), x1.U (%27)
                    xor %30, %25, %27
                    msk %30, %18, %30
                    xor %25, %30, %25
                    xor %27, %30, %27
                    // cswap x0.W (%26), x1.W (%28)
                    xor %30, %26, %28
                    msk %30, %18, %30
                    xor %26, %30, %26
                    xor %28, %30, %28

                    psa %18, %29  // swap = k_t

                        // differential_add_and_double(&mut x0, &mut x1, &affine_u);
                        psa %20, %25
                        psa %21, %26
                        psa %22, %27
                        psa %23, %28
                        // affine_u is already in %24

                        // let t0 = &P.U + &P.W;
                        add %0, %20, %21
                        trd %30, %0
                        sub %0, %0, %30
                        // let t1 = &P.U - &P.W;
                        sub %21, #3, %21    // negate &P.W using #FIELDPRIME (#3)
                        add %1, %20, %21
                        trd %30, %1
                        sub %1, %1, %30
                        // let t2 = &Q.U + &Q.W;
                        add %2, %22, %23
                        trd %30, %2
                        sub %2, %2, %30
                        // let t3 = &Q.U - &Q.W;
                        sub %23, #3, %23
                        add %3, %22, %23
                        trd %30, %3
                        sub %3, %3, %30
                        // let t4 = t0.square();   // (U_P + W_P)^2 = U_P^2 + 2 U_P W_P + W_P^2
                        mul %4, %0, %0
                        // let t5 = t1.square();   // (U_P - W_P)^2 = U_P^2 - 2 U_P W_P + W_P^2
                        mul %5, %1, %1
                        // let t6 = &t4 - &t5;     // 4 U_P W_P
                        sub %29, #3, %5
                        add %6, %4, %29
                        trd %30, %6
                        sub %6, %6, %30
                        // let t7 = &t0 * &t3;     // (U_P + W_P) (U_Q - W_Q) = U_P U_Q + W_P U_Q - U_P W_Q - W_P W_Q
                        mul %7, %0, %3
                        // let t8 = &t1 * &t2;     // (U_P - W_P) (U_Q + W_Q) = U_P U_Q - W_P U_Q + U_P W_Q - W_P W_Q
                        mul %8, %1, %2
                        // let t9  = &t7 + &t8;    // 2 (U_P U_Q - W_P W_Q)
                        add %9, %7, %8
                        trd %30, %9
                        sub %9, %9, %30
                        // let t10 = &t7 - &t8;    // 2 (W_P U_Q - U_P W_Q)
                        sub %29, #3, %8
                        add %10, %7, %29
                        trd %30, %10
                        sub %10, %10, %30
                        // let t11 =  t9.square(); // 4 (U_P U_Q - W_P W_Q)^2
                        mul %11, %9, %9
                        // let t12 = t10.square(); // 4 (W_P U_Q - U_P W_Q)^2
                        mul %12, %10, %10
                        // let t13 = &APLUS2_OVER_FOUR * &t6; // (A + 2) U_P U_Q
                        mul %13, #4, %6   // #4 is A+2/4
                        // let t14 = &t4 * &t5;    // ((U_P + W_P)(U_P - W_P))^2 = (U_P^2 - W_P^2)^2
                        mul %14, %4, %5
                        // let t15 = &t13 + &t5;   // (U_P - W_P)^2 + (A + 2) U_P W_P
                        add %15, %13, %5
                        trd %30, %15
                        sub %15, %15, %30
                        // let t16 = &t6 * &t15;   // 4 (U_P W_P) ((U_P - W_P)^2 + (A + 2) U_P W_P)
                        mul %16, %6, %15
                        // let t17 = affine_PmQ * &t12; // U_D * 4 (W_P U_Q - U_P W_Q)^2
                        mul %17, %24, %12    // affine_PmQ loaded into %24

                        ///// these can be eliminated down the road, but included for 1:1 algorithm correspodence to reference in early testing
                        // P.U = t14;  // U_{P'} = (U_P + W_P)^2 (U_P - W_P)^2
                        psa %20, %14
                        // P.W = t16;  // W_{P'} = (4 U_P W_P) ((U_P - W_P)^2 + ((A + 2)/4) 4 U_P W_P)
                        psa %21, %16
                        // let t18 = t11;               // W_D * 4 (U_P U_Q - W_P W_Q)^2
                        // Q.U = t18;  // U_{Q'} = W_D * 4 (U_P U_Q - W_P W_Q)^2
                        psa %22, %11   // collapsed two to save a register
                        // Q.W = t17;  // W_{Q'} = U_D * 4 (W_P U_Q - U_P W_Q)^2
                        psa %23, %17

                        ///// 'return' arguments for next iteration, can be optimized out later
                        psa %25, %20
                        psa %26, %21
                        psa %27, %22
                        psa %28, %23

                    brz end, %19     // if loop counter is 0, quit
                    sub %19, %19, #1 // subtract one from the loop counter and run again
                    brz mainloop, #0    // go back to the top
                end:
                    // ProjectivePoint::conditional_swap(&mut x0, &mut x1, Choice::from(bits[0] as u8));
                    // cswap x0.U (%25), x1.U (%27)
                    xor %30, %25, %27
                    msk %30, %18, %30
                    xor %25, %30, %25
                    xor %27, %30, %27
                    // cswap x0.W (%26), x1.W (%28)
                    xor %30, %26, %28
                    msk %30, %18, %30
                    xor %26, %30, %26
                    xor %28, %30, %28

                    //// test post-amble
                    // test postamble -- sum together the points to create a single composite test output
                    add %31, %25, %26
                    trd %30, %31
                    sub %31, %31, %30

                    fin  // finish execution
            );

            write_test_header(&mut file, loading_address, &mcode, num_src_regs, reg_window, num_tests);

            use scalar::Scalar;
            use montgomery::MontgomeryPoint;
            use montgomery::differential_add_and_double;

            fn clamp_scalar(mut scalar: [u8; 32]) -> Scalar {
                scalar[0] &= 248;
                scalar[31] &= 127;
                scalar[31] |= 64;
                Scalar::from_bits(scalar)
            }

            let scalar: Scalar = clamp_scalar(rand::thread_rng().gen::<[u8; 32]>());
            let mp: MontgomeryPoint = MontgomeryPoint {0: rand::thread_rng().gen::<[u8; 32]>() };

            // Algorithm 8 of Costello-Smith 2017
            let affine_u = FieldElement::from_bytes(&mp.0);
            let mut x0 = ProjectivePoint {
                U: FieldElement::one(),
                W: FieldElement::zero(),
            };
            let mut x1 = ProjectivePoint {
                U: affine_u,
                W: FieldElement::one(),
            };

            // test vectors input to test routine
            write_helper(&mut file, x0.U);
            write_helper(&mut file, x0.W);
            write_helper(&mut file, x1.U);
            write_helper(&mut file, x1.W);
            write_helper(&mut file, affine_u);
            file.write(&scalar.bytes).unwrap();
            let number254 = FieldElement::from_bytes(&[
                 254, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ]);
            write_helper(&mut file, number254);

            let bits: [i8; 256] = scalar.bits();

            for i in (0..255).rev() {
                let choice: u8 = (bits[i + 1] ^ bits[i]) as u8;

                debug_assert!(choice == 0 || choice == 1);

                ProjectivePoint::conditional_swap(&mut x0, &mut x1, choice.into());
                differential_add_and_double(&mut x0, &mut x1, &affine_u);
            }
            ProjectivePoint::conditional_swap(&mut x0, &mut x1, Choice::from(bits[0] as u8));

            // result is in x0
            // result vector
            write_helper(&mut file, &x0.U + &x0.W);
        }

        test_scalar_mul(&mut file);
        test_add(&mut file);
        test_loop(&mut file);
        test_cswap(&mut file);
        test_mul(&mut file);
        test_diff_add_and_double(&mut file);

        // end sequence
        let _ = file.write(&(0xFFFF_FFFF as u32).to_le_bytes());
    }
}
