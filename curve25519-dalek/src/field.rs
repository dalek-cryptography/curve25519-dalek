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

#![allow(unused_qualifications)]

use cfg_if::cfg_if;

use subtle::Choice;
use subtle::ConditionallyNegatable;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

use crate::backend;
use crate::constants;

#[cfg(feature = "digest")]
use digest::{
    core_api::BlockSizeUser,
    generic_array::{typenum::U64, GenericArray},
    typenum::{IsGreater, True},
    Digest, FixedOutput, HashMarker,
};

cfg_if! {
    if #[cfg(curve25519_dalek_backend = "fiat")] {
        /// A `FieldElement` represents an element of the field
        /// \\( \mathbb Z / (2\^{255} - 19)\\).
        ///
        /// The `FieldElement` type is an alias for one of the platform-specific
        /// implementations.
        ///
        /// Using formally-verified field arithmetic from fiat-crypto.
        #[cfg(curve25519_dalek_bits = "32")]
        pub(crate) type FieldElement = backend::serial::fiat_u32::field::FieldElement2625;

        /// A `FieldElement` represents an element of the field
        /// \\( \mathbb Z / (2\^{255} - 19)\\).
        ///
        /// The `FieldElement` type is an alias for one of the platform-specific
        /// implementations.
        ///
        /// Using formally-verified field arithmetic from fiat-crypto.
        #[cfg(curve25519_dalek_bits = "64")]
        pub(crate) type FieldElement = backend::serial::fiat_u64::field::FieldElement51;
    } else if #[cfg(curve25519_dalek_bits = "64")] {
        /// A `FieldElement` represents an element of the field
        /// \\( \mathbb Z / (2\^{255} - 19)\\).
        ///
        /// The `FieldElement` type is an alias for one of the platform-specific
        /// implementations.
        pub(crate) type FieldElement = backend::serial::u64::field::FieldElement51;
    } else {
        /// A `FieldElement` represents an element of the field
        /// \\( \mathbb Z / (2\^{255} - 19)\\).
        ///
        /// The `FieldElement` type is an alias for one of the platform-specific
        /// implementations.
        pub(crate) type FieldElement = backend::serial::u32::field::FieldElement2625;
    }
}

impl Eq for FieldElement {}

impl PartialEq for FieldElement {
    fn eq(&self, other: &FieldElement) -> bool {
        self.ct_eq(other).into()
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
    /// Load a `FieldElement` from 64 bytes, by reducing modulo q.
    #[cfg(feature = "digest")]
    pub(crate) fn from_bytes_wide(bytes: &[u8; 64]) -> Self {
        let mut fl = [0u8; 32];
        let mut gl = [0u8; 32];
        fl.copy_from_slice(&bytes[..32]);
        gl.copy_from_slice(&bytes[32..]);
        // Mask off the top bits of both halves, since from_bytes masks them off anyway. We'll add
        // them back in later.
        let fl_top_bit = (fl[31] >> 7) as u16;
        let gl_top_bit = (gl[31] >> 7) as u16;
        fl[31] &= 0x7f;
        gl[31] &= 0x7f;

        // Interpret both sides as field elements
        let mut fe_f = Self::from_bytes(&fl);
        let fe_g = Self::from_bytes(&gl);

        // The full field elem is now fe_f + 2²⁵⁵ fl_top_bit + 2²⁵⁶ fe_g + 2⁵¹¹ gl_top_bit

        // Add the masked off bits back to fe_f. fl_top_bit, if set, is 2^255 ≡ 19 (mod q).
        // gl_top_bit, if set, is 2^511 ≡ 722 (mod q)
        let top_bits_sum = {
            // This only need to be a u16 because the max value is 741
            let addend: u16 = fl_top_bit * 19 + gl_top_bit * 722;
            let mut addend_bytes = [0u8; 32];
            addend_bytes[..2].copy_from_slice(&addend.to_le_bytes());
            Self::from_bytes(&addend_bytes)
        };
        fe_f += &top_bits_sum;

        // Now add the high half into fe_f. The RHS is multiplied by 2^256 ≡ 38 (mod q)
        const THIRTY_EIGHT: FieldElement = FieldElement::from_bytes(&[
            38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ]);
        fe_f += &(&THIRTY_EIGHT * &fe_g);

        fe_f
    }

    /// Determine if this `FieldElement` is negative, in the sense
    /// used in the ed25519 paper: `x` is negative if the low bit is
    /// set.
    ///
    /// # Return
    ///
    /// If negative, return `Choice(1)`.  Otherwise, return `Choice(0)`.
    pub(crate) fn is_negative(&self) -> Choice {
        let bytes = self.to_bytes();
        (bytes[0] & 1).into()
    }

    /// Determine if this `FieldElement` is zero.
    ///
    /// # Return
    ///
    /// If zero, return `Choice(1)`.  Otherwise, return `Choice(0)`.
    pub(crate) fn is_zero(&self) -> Choice {
        let zero = [0u8; 32];
        let bytes = self.to_bytes();

        bytes.ct_eq(&zero)
    }

    /// Compute (self^(2^250-1), self^11), used as a helper function
    /// within invert() and pow22523().
    #[rustfmt::skip] // keep alignment of explanatory comments
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

    /// Given a slice of pub(crate)lic `FieldElements`, replace each with its inverse.
    ///
    /// When an input `FieldElement` is zero, its value is unchanged.
    #[cfg(feature = "alloc")]
    pub(crate) fn batch_invert(inputs: &mut [FieldElement]) {
        // Montgomery’s Trick and Fast Implementation of Masked AES
        // Genelle, Prouff and Quisquater
        // Section 3.2

        let n = inputs.len();
        let mut scratch = vec![FieldElement::ONE; n];

        // Keep an accumulator of all of the previous products
        let mut acc = FieldElement::ONE;

        // Pass through the input vector, recording the previous
        // products in the scratch space
        for (input, scratch) in inputs.iter().zip(scratch.iter_mut()) {
            *scratch = acc;
            // acc <- acc * input, but skipping zeros (constant-time)
            acc.conditional_assign(&(&acc * input), !input.is_zero());
        }

        // acc is nonzero because we skipped zeros in inputs
        assert!(bool::from(!acc.is_zero()));

        // Compute the inverse of all products
        acc = acc.invert();

        // Pass through the vector backwards to compute the inverses
        // in place
        for (input, scratch) in inputs.iter_mut().rev().zip(scratch.into_iter().rev()) {
            let tmp = &acc * input;
            // input <- acc * scratch, then acc <- tmp
            // Again, we skip zeros in a constant-time way
            let nz = !input.is_zero();
            input.conditional_assign(&(&acc * &scratch), nz);
            acc.conditional_assign(&tmp, nz);
        }
    }

    /// Given a nonzero field element, compute its inverse.
    ///
    /// The inverse is computed as self^(p-2), since
    /// x^(p-2)x = x^(p-1) = 1 (mod p).
    ///
    /// This function returns zero on input zero.
    #[rustfmt::skip] // keep alignment of explanatory comments
    #[allow(clippy::let_and_return)]
    pub(crate) fn invert(&self) -> FieldElement {
        // The bits of p-2 = 2^255 -19 -2 are 11010111111...11.
        //
        //                                 nonzero bits of exponent
        let (t19, t3) = self.pow22501();   // t19: 249..0 ; t3: 3,1,0
        let t20 = t19.pow2k(5);            // 254..5
        let t21 = &t20 * &t3;              // 254..5,3,1,0

        t21
    }

    /// Raise this field element to the power (p-5)/8 = 2^252 -3.
    #[rustfmt::skip] // keep alignment of explanatory comments
    #[allow(clippy::let_and_return)]
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
    pub(crate) fn sqrt_ratio_i(u: &FieldElement, v: &FieldElement) -> (Choice, FieldElement) {
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

        let v3 = &v.square() * v;
        let v7 = &v3.square() * v;
        let mut r = &(u * &v3) * &(u * &v7).pow_p58();
        let check = v * &r.square();

        let i = &constants::SQRT_M1;

        let correct_sign_sqrt = check.ct_eq(u);
        let flipped_sign_sqrt = check.ct_eq(&(-u));
        let flipped_sign_sqrt_i = check.ct_eq(&(&(-u) * i));

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
    pub(crate) fn invsqrt(&self) -> (Choice, FieldElement) {
        FieldElement::sqrt_ratio_i(&FieldElement::ONE, self)
    }

    #[cfg(feature = "digest")]
    /// Perform hashing to a [`FieldElement`], per the
    /// [`hash_to_curve`](https://www.rfc-editor.org/rfc/rfc9380.html#section-5.2) specification.
    /// Uses the suite `edwards25519_XMD:SHA-512_ELL2_NU_`. The input is the concatenation of the
    /// elements of `bytes`. Likewise for the domain separator with `domain_sep`. At least one
    /// element of `domain_sep`, MUST be nonempty, and the concatenation MUST NOT exceed 255 bytes.
    ///
    /// # Panics
    /// Panics if `domain_sep.collect().len() == 0` or `> 255`
    pub fn hash_to_field<D>(bytes: &[&[u8]], domain_sep: &[&[u8]]) -> Self
    where
        D: BlockSizeUser + Default + FixedOutput<OutputSize = U64> + HashMarker,
        D::BlockSize: IsGreater<D::OutputSize, Output = True>,
    {
        let l_i_b_str = 48u16.to_be_bytes();
        let z_pad = GenericArray::<u8, D::BlockSize>::default();

        let mut hasher = D::new().chain_update(z_pad);

        for slice in bytes {
            hasher = hasher.chain_update(slice);
        }

        hasher = hasher.chain_update(l_i_b_str).chain_update([0u8]);

        let mut domain_sep_len = 0usize;
        for slice in domain_sep {
            hasher = hasher.chain_update(slice);
            domain_sep_len += slice.len();
        }

        let domain_sep_len = u8::try_from(domain_sep_len)
            .expect("Unexpected overflow from domain separator's size.");
        assert_ne!(
            domain_sep_len, 0,
            "Domain separator MUST have nonzero length."
        );

        let b_0 = hasher.chain_update([domain_sep_len]).finalize();

        let mut hasher = D::new().chain_update(b_0.as_slice()).chain_update([1u8]);

        for slice in domain_sep {
            hasher = hasher.chain_update(slice)
        }

        let b_1 = hasher.chain_update([domain_sep_len]).finalize();

        // §5.2, we only generate count * m * L = 1 * 1 * (256 + 128)/8 = 48 bytes
        let mut bytes_wide = [0u8; 64];
        bytes_wide[..48].copy_from_slice(&b_1.as_slice()[..48]);
        bytes_wide[..48].reverse();

        FieldElement::from_bytes_wide(&bytes_wide)
    }
}

#[cfg(test)]
mod test {
    use crate::field::*;

    /// Random element a of GF(2^255-19), from Sage
    /// a = 1070314506888354081329385823235218444233221\
    ///     2228051251926706380353716438957572
    static A_BYTES: [u8; 32] = [
        0x04, 0xfe, 0xdf, 0x98, 0xa7, 0xfa, 0x0a, 0x68, 0x84, 0x92, 0xbd, 0x59, 0x08, 0x07, 0xa7,
        0x03, 0x9e, 0xd1, 0xf6, 0xf2, 0xe1, 0xd9, 0xe2, 0xa4, 0xa4, 0x51, 0x47, 0x36, 0xf3, 0xc3,
        0xa9, 0x17,
    ];

    /// Byte representation of a**2
    static ASQ_BYTES: [u8; 32] = [
        0x75, 0x97, 0x24, 0x9e, 0xe6, 0x06, 0xfe, 0xab, 0x24, 0x04, 0x56, 0x68, 0x07, 0x91, 0x2d,
        0x5d, 0x0b, 0x0f, 0x3f, 0x1c, 0xb2, 0x6e, 0xf2, 0xe2, 0x63, 0x9c, 0x12, 0xba, 0x73, 0x0b,
        0xe3, 0x62,
    ];

    /// Byte representation of 1/a
    static AINV_BYTES: [u8; 32] = [
        0x96, 0x1b, 0xcd, 0x8d, 0x4d, 0x5e, 0xa2, 0x3a, 0xe9, 0x36, 0x37, 0x93, 0xdb, 0x7b, 0x4d,
        0x70, 0xb8, 0x0d, 0xc0, 0x55, 0xd0, 0x4c, 0x1d, 0x7b, 0x90, 0x71, 0xd8, 0xe9, 0xb6, 0x18,
        0xe6, 0x30,
    ];

    /// Byte representation of a^((p-5)/8)
    static AP58_BYTES: [u8; 32] = [
        0x6a, 0x4f, 0x24, 0x89, 0x1f, 0x57, 0x60, 0x36, 0xd0, 0xbe, 0x12, 0x3c, 0x8f, 0xf5, 0xb1,
        0x59, 0xe0, 0xf0, 0xb8, 0x1b, 0x20, 0xd2, 0xb5, 0x1f, 0x15, 0x21, 0xf9, 0xe3, 0xe1, 0x61,
        0x21, 0x55,
    ];

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
        assert_eq!(a.square2(), &asq + &asq);
    }

    #[test]
    fn a_invert_vs_inverse_of_a_constant() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        let should_be_inverse = a.invert();
        assert_eq!(ainv, should_be_inverse);
        assert_eq!(FieldElement::ONE, &a * &should_be_inverse);
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn batch_invert_a_matches_nonbatched() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let ap58 = FieldElement::from_bytes(&AP58_BYTES);
        let asq = FieldElement::from_bytes(&ASQ_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        let a0 = &a - &a;
        let a2 = &a + &a;
        let a_list = vec![a, ap58, asq, ainv, a0, a2];
        let mut ainv_list = a_list.clone();
        FieldElement::batch_invert(&mut ainv_list[..]);
        for i in 0..6 {
            assert_eq!(a_list[i].invert(), ainv_list[i]);
        }
    }

    #[test]
    fn sqrt_ratio_behavior() {
        let zero = FieldElement::ZERO;
        let one = FieldElement::ONE;
        let i = constants::SQRT_M1;
        let two = &one + &one; // 2 is nonsquare mod p.
        let four = &two + &two; // 4 is square mod p.

        // 0/0 should return (1, 0) since u is 0
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&zero, &zero);
        assert!(bool::from(choice));
        assert_eq!(sqrt, zero);
        assert!(bool::from(!sqrt.is_negative()));

        // 1/0 should return (0, 0) since v is 0, u is nonzero
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&one, &zero);
        assert!(bool::from(!choice));
        assert_eq!(sqrt, zero);
        assert!(bool::from(!sqrt.is_negative()));

        // 2/1 is nonsquare, so we expect (0, sqrt(i*2))
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&two, &one);
        assert!(bool::from(!choice));
        assert_eq!(sqrt.square(), &two * &i);
        assert!(bool::from(!sqrt.is_negative()));

        // 4/1 is square, so we expect (1, sqrt(4))
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&four, &one);
        assert!(bool::from(choice));
        assert_eq!(sqrt.square(), four);
        assert!(bool::from(!sqrt.is_negative()));

        // 1/4 is square, so we expect (1, 1/sqrt(4))
        let (choice, sqrt) = FieldElement::sqrt_ratio_i(&one, &four);
        assert!(bool::from(choice));
        assert_eq!(&sqrt.square() * &four, one);
        assert!(bool::from(!sqrt.is_negative()));
    }

    #[test]
    fn a_p58_vs_ap58_constant() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let ap58 = FieldElement::from_bytes(&AP58_BYTES);
        assert_eq!(ap58, a.pow_p58());
    }

    #[test]
    fn equality() {
        let a = FieldElement::from_bytes(&A_BYTES);
        let ainv = FieldElement::from_bytes(&AINV_BYTES);
        assert!(a == a);
        assert!(a != ainv);
    }

    /// Notice that the last element has the high bit set, which
    /// should be ignored
    static B_BYTES: [u8; 32] = [
        113, 191, 169, 143, 91, 234, 121, 15, 241, 131, 217, 36, 230, 101, 92, 234, 8, 208, 170,
        251, 97, 127, 70, 210, 58, 23, 166, 87, 240, 169, 184, 178,
    ];

    #[test]
    fn from_bytes_highbit_is_ignored() {
        let mut cleared_bytes = B_BYTES;
        cleared_bytes[31] &= 127u8;
        let with_highbit_set = FieldElement::from_bytes(&B_BYTES);
        let without_highbit_set = FieldElement::from_bytes(&cleared_bytes);
        assert_eq!(without_highbit_set, with_highbit_set);
    }

    #[test]
    fn conditional_negate() {
        let one = FieldElement::ONE;
        let minus_one = FieldElement::MINUS_ONE;
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
        let one_encoded_wrongly_bytes: [u8; 32] = [
            0xee, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0x7f,
        ];
        // Decode to a field element
        let one = FieldElement::from_bytes(&one_encoded_wrongly_bytes);
        // .. then check that the encoding is correct
        let one_bytes = one.to_bytes();
        assert_eq!(one_bytes[0], 1);
        for byte in &one_bytes[1..] {
            assert_eq!(*byte, 0);
        }
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn batch_invert_empty() {
        FieldElement::batch_invert(&mut []);
    }

    // The following two consts were generated with the following sage script:
    //
    // import random
    //
    // F = GF(2**255 - 19)
    // # Use a seed to make sure we produce the same test vectors every time
    // random.seed("Ozamataz Buckshank")
    //
    // # Generates test vectors, each of the form (input_bytes, reduced_field_elem_bytes),
    // # where input_bytes is length input_bytes_len
    // def gen_example(input_bytes_len):
    //     # Generate random bytes
    //     input_bytes = [random.randint(0, 255) for _ in range(input_bytes_len)]
    //
    //     # Now convert to a field element and get the reduced byte representation
    //     elem = F(int.from_bytes(input_bytes, byteorder='little'))
    //     reduced_bytes = list(int(elem).to_bytes(32, byteorder='little'))
    //
    //     # Format input and output as hex strings
    //     input_bytes_hex = ''.join(f'{byte:02x}' for byte in input_bytes)
    //     reduced_bytes_hex = ''.join(f'{byte:02x}' for byte in reduced_bytes)
    //     return f"(\"{input_bytes_hex}\", \"{reduced_bytes_hex}\")"
    //
    // print("SET 1: Input bytes are length 64")
    // for _ in range(5):
    //     print(gen_example(64))
    //
    // print("SET 2: Input bytes are length 48")
    // for _ in range(5):
    //     print(gen_example(48))

    /// Test vectors for FieldElement::from_bytes_wide. Elements are of the form (len-64 bytestring,
    /// reduced field element)
    #[cfg(feature = "digest")]
    const FROM_BYTES_WIDE_KAT_BIG: &[(&str, &str)] = &[
        (
            "77b663085cac0e916f40dbeea5116f201816406e68ccf01b32a97162ae1d5bf95d0d01c2c72fbeeb27a63\
            5b85b715d5ce6f74118a60a7aec53c798ad648a482f",
            "62b38bd402c4498f5cead14643e54dd649e20a0810610e36a73f1f27a0a81f7e",
        ),
        (
            "d437c75ec79886650243a79c62933bb307eb12ff16d05db4a6a8a877f4a91abb6eeb64d2e20519c021799\
            3a1dc5639283a06639985a2c892208171503335afb5",
            "3d2ec29972783de9043e8b982278beaba9d7c5c3ebef257e7cd38168928f1c33",
        ),
        (
            "6daa9e1abe6c604fb6e841c04bf90a6ef88aef6b1eab17dd44f7207ef472cd2d54bac849f703e64f36e56\
            77e7e86b82be7d26aa220daf1f208bb36dcc1a12338",
            "28546a0e7303852bc6eead8312f06eeb48d9ca87f60bfeec98ba402ebb751703",
        ),
        (
            "c3920e326dbf806a50105be78263c1dc9390fb4741587b250cd758c2bfa3ed70faedbbc5f9b1d024e00fe\
            7d7daf796866853f42e72d638e6533c5eb5b7caf3c6",
            "40eaf38b802a7be1956ba7f3fe2d2ad717f23f40342deb5180cb55ae04bb1d79",
        ),
        (
            "23f143c72ead6c0f336b4e746a06921f0eb180002e8ce916d196de16216788617c6aeb90a074a85196f03\
            81375011248927c1215e9ec65b382a6ec556fb3f504",
            "b1bf354a04fd6d2e8321c24ecb3d3ed2c42e3f21c7b60ab8374effd7a709011e",
        ),
    ];

    /// Test vectors for FieldElement::from_bytes_wide. Elements are of the form (len-48 bytestring,
    /// reduced field element)
    #[cfg(feature = "digest")]
    const FROM_BYTES_WIDE_KAT_MEDIUM: &[(&str, &str)] = &[
        (
            "82e9cbe4928e3d0bbf1f91824a91acfb30d929f7a2fa5cbcc967c63ea0f3357c29c19f1bc9dcad69d85c1\
            c6265970685",
            "989582fe6c540cbbdee7c612570aa7ba44d929f7a2fa5cbcc967c63ea0f3357c",
        ),
        (
            "5480494df4fb3a3b19da17e1c8b9192ccb09ec76720321977079300c42c17b9e95b01eb37ffe7048fcd1c\
            9e6094da6c4",
            "85b6d7e3e8c200fc8b050d234129c95ce809ec76720321977079300c42c17b1e",
        ),
        (
            "93ec8a480dde098f74bcd341ef4f248f6440cc6e631d7000784f66975a4fd628438bb1350ba4c1421fec3\
            670decced06",
            "8598e540b737c87718c9fae9f3b870966540cc6e631d7000784f66975a4fd628",
        ),
        (
            "fd0154ff9a5c4c9ee4e8183c23db97018e0e6201a812f6d4faedda50652d51f65c110b9a1a100a3fc3ff1\
            c4ea3cf22e4",
            "b895f8dc8dc0caf9dfdf66d460adc2deaf0e6201a812f6d4faedda50652d5176",
        ),
        (
            "0e829dc955e0a1e0dbda9849cb2022b295275782348bd6308b3d0c5836f3ca0130911a17fd54054c3a0f8\
            b2486f8ce85",
            "2e0f8f37e77d6c29831d3db6b404db8ea9275782348bd6308b3d0c5836f3ca01",
        ),
    ];

    #[cfg(feature = "digest")]
    #[test]
    fn from_bytes_wide() {
        // Do the 64-byte input ones first
        for (input_bytes, expected_reduced) in FROM_BYTES_WIDE_KAT_BIG {
            let reduce_fe = FieldElement::from_bytes_wide(
                &hex::decode(input_bytes)
                    .unwrap()
                    .as_slice()
                    .try_into()
                    .unwrap(),
            );
            assert_eq!(
                &reduce_fe.to_bytes(),
                hex::decode(expected_reduced).unwrap().as_slice()
            );
        }

        // Now do the 48-byte inputs
        for (input_bytes, expected_reduced) in FROM_BYTES_WIDE_KAT_MEDIUM {
            let mut padded_input_bytes = [0u8; 64];
            padded_input_bytes[..48].copy_from_slice(&hex::decode(input_bytes).unwrap());
            let reduce_fe = FieldElement::from_bytes_wide(&padded_input_bytes);
            assert_eq!(
                &reduce_fe.to_bytes(),
                hex::decode(expected_reduced).unwrap().as_slice()
            );
        }
    }

    /// Hash to field test vectors from
    /// https://www.rfc-editor.org/rfc/rfc9380.html#name-edwards25519_xmdsha-512_ell2
    /// These are of the form (input_msg, output_field_elem)
    #[cfg(feature = "digest")]
    const RFC_HASH_TO_FIELD_KAT: &[(&[u8], &str)] = &[
        (
            b"",
            "7f3e7fb9428103ad7f52db32f9df32505d7b427d894c5093f7a0f0374a30641d"
        ),
        (
            b"abc",
            "09cfa30ad79bd59456594a0f5d3a76f6b71c6787b04de98be5cd201a556e253b"
        ),
        (
            b"abcdef0123456789",
            "475ccff99225ef90d78cc9338e9f6a6bb7b17607c0c4428937de75d33edba941",
        ),
        (
            b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
            qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
            "049a1c8bd51bcb2aec339f387d1ff51428b88d0763a91bcdf6929814ac95d03d"
        ),
        (
            b"a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
            aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
            aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
            aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
            aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
            aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "3cb0178a8137cefa5b79a3a57c858d7eeeaa787b2781be4a362a2f0750d24fa0"
        )
    ];

    #[test]
    #[cfg(feature = "digest")]
    fn hash_to_field() {
        use sha2::Sha512;
        let dst = "QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_NU_";

        for (msg, expected_hash_hex) in RFC_HASH_TO_FIELD_KAT {
            let fe = FieldElement::hash_to_field::<Sha512>(&[msg], &[dst.as_bytes()]);
            let expected_fe = {
                let mut expected_hash = hex::decode(expected_hash_hex).unwrap();
                expected_hash.reverse();
                FieldElement::from_bytes(&expected_hash.try_into().unwrap())
            };

            assert_eq!(fe, expected_fe);
        }
    }
}
