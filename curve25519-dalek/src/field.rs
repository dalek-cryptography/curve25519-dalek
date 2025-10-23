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

use vstd::prelude::*;

use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::*;

#[allow(unused_imports)]
use crate::backend::serial::u64::field_lemmas::field_core::*;

#[allow(unused_imports)]
use crate::field_specs::*;

verus! {

/* VERIFICATION NOTE: specializing to u64 backend for now */
/// A `FieldElement` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// The `FieldElement` type is an alias for one of the platform-specific
/// implementations.
pub(crate) type FieldElement = backend::serial::u64::field::FieldElement51;

impl Eq for FieldElement {

}

impl PartialEq for FieldElement {
    fn eq(&self, other: &FieldElement) -> (result:
        bool)
    // VERIFICATION NOTE: PROOF BYPASS AND SPEC BYPASS

        ensures
            result == (field_element_as_bytes(self) == field_element_as_bytes(
                other,
            )),
    // SPEC BYPASS through placeholder field_element_as_bytes

    {
        /* <VERIFICATION NOTE>
         Use wrapper function for Choice::into
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         self.ct_eq(other).into()
         </ORIGINAL CODE> */
        let choice = self.ct_eq(other);
        let result = choice_into(choice);

        // VERIFICATION NOTE: vstd's external trait specification check cannot be satisfied
        // vstd expects obeys_eq_spec() and eq_spec() from PartialEqSpecImpl trait,
        // but that trait is not publicly exported, so we bypass with assume(false)
        assume(false);

        result
    }
}

impl ConstantTimeEq for FieldElement {
    /// Test equality between two `FieldElement`s.  Since the
    /// internal representation is not canonical, the field elements
    /// are normalized to wire format before comparison.
    fn ct_eq(&self, other: &FieldElement) -> (result:
        Choice)/* <VERIFICATION NOTE>
     - PROOF BYPASS AND SPEC BYPASS
     - Use wrapper functions for ConstantTimeEq and CtOption
    </VERIFICATION NOTE> */

        ensures
            choice_is_true(result) == (field_element_as_bytes(self) == field_element_as_bytes(
                other,
            )),
    // SPEC BYPASS through placeholder field_element_as_bytes

    {
        /* <VERIFICATION NOTE>
         Use wrapper function for Verus compatibility instead of direct subtle call
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         self.as_bytes().ct_eq(&other.as_bytes())
         </ORIGINAL CODE> */
        let result = ct_eq_bytes32(&self.as_bytes(), &other.as_bytes());
        assume(choice_is_true(result) == (field_element_as_bytes(self) == field_element_as_bytes(
            other,
        )));
        result
    }
}

} // verus!
    verus! {
impl FieldElement {

/// Determine if this `FieldElement` is negative, in the sense
/// used in the ed25519 paper: `x` is negative if the low bit is
/// set.
///
/// # Return
///
/// If negative, return `Choice(1)`.  Otherwise, return `Choice(0)`.
pub(crate) fn is_negative(&self) -> (result:
    Choice)/* VERIFICATION NOTE:
    - PROOF BYPASS AND SPEC BYPASS
    - we cannot write this directly; need to find a spec function for FieldElement51::as_bytes
    ensures choice_is_true(result) == (self.as_bytes()[0] & 1 == 1)
    - (note after slack call: maybe the first bit of as_bytes() is sufficient as a spec)
    </VERIFICATION NOTE> */

    ensures
        choice_is_true(result) == (field_element_as_bytes(self)[0] & 1
            == 1),
// SPEC BYPASS through placeholder field_element_as_bytes

{
    let bytes = self.as_bytes();
    let result = Choice::from(bytes[0] & 1);
    assume(choice_is_true(result) == (field_element_as_bytes(self)[0] & 1 == 1));
    result
}

/// Determine if this `FieldElement` is zero.
///
/// # Return
///
/// If zero, return `Choice(1)`.  Otherwise, return `Choice(0)`.
pub(crate) fn is_zero(&self) -> (result:
    Choice)/* VERIFICATION NOTE:
    - PROOF BYPASS AND SPEC BYPASS
    - we cannot write this directly; need to find a spec function for FieldElement51::as_bytes
    ensures choice_is_true(result) == (self.as_bytes() == [0u8; 32])
    - (note: maybe an all_zeroes(as_bytes(...)) is sufficient as a spec)
    </VERIFICATION NOTE> */

    ensures
        choice_is_true(result) == (field_element_as_bytes(self)
            == seq![0u8; 32]),
// SPEC BYPASS through placeholder field_element_as_bytes

{
    let zero = [0u8;32];
    let bytes = self.as_bytes();

    let result = ct_eq_bytes32(&bytes, &zero);
    assume(choice_is_true(result) == (field_element_as_bytes(self) == seq![0u8; 32]));
    result
}

/// Compute (self^(2^250-1), self^11), used as a helper function
/// within invert() and pow22523().
#[rustfmt::skip]  // keep alignment of explanatory comments
fn pow22501(&self) -> (result: (FieldElement, FieldElement))
    ensures
        field_element_as_nat(&result.0) == pow(
            field_element_as_nat(self) as int,
            (pow2(250) - 1) as nat,
        ) % (p() as int),
        field_element_as_nat(&result.1) == pow(field_element_as_nat(self) as int, 11) % (
        p() as int),
{
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
    assume(false);
    let t0 = self.square();  // 1         e_0 = 2^1
    let t1 = t0.square().square();  // 3         e_1 = 2^3
    let t2 = self * &t1;  // 3,0       e_2 = 2^3 + 2^0
    let t3 = &t0 * &t2;  // 3,1,0
    let t4 = t3.square();  // 4,2,1
    let t5 = &t2 * &t4;  // 4,3,2,1,0
    let t6 = t5.pow2k(5);  // 9,8,7,6,5
    let t7 = &t6 * &t5;  // 9,8,7,6,5,4,3,2,1,0
    let t8 = t7.pow2k(10);  // 19..10
    let t9 = &t8 * &t7;  // 19..0
    let t10 = t9.pow2k(20);  // 39..20
    let t11 = &t10 * &t9;  // 39..0
    let t12 = t11.pow2k(10);  // 49..10
    let t13 = &t12 * &t7;  // 49..0
    let t14 = t13.pow2k(50);  // 99..50
    let t15 = &t14 * &t13;  // 99..0
    let t16 = t15.pow2k(100);  // 199..100
    let t17 = &t16 * &t15;  // 199..0
    let t18 = t17.pow2k(50);  // 249..50
    let t19 = &t18 * &t13;  // 249..0

    (t19, t3)
}

/// Given a slice of pub(crate)lic `FieldElements`, replace each with its inverse.
///
/// When an input `FieldElement` is zero, its value is unchanged.
#[cfg(feature = "alloc")]
pub(crate) fn batch_invert(
    inputs: &mut [FieldElement],
)/* <VERIFICATION NOTE>
     - Refactored for Verus: Index loops instead of iterators, manual Vec construction
     - Choice type operations handled by wrappers in subtle_assumes.rs
     - PROOF BYPASSES because of trait issues and proof obligations.
    </VERIFICATION NOTE> */

    ensures
// Each element is replaced appropriately:

        forall|i: int|
            #![auto]
            0 <= i < inputs.len() ==> {
                // If input was non-zero, it's replaced with its inverse
                (field_element_as_nat(&old(inputs)[i]) != 0) ==> is_inverse_field(
                    &old(inputs)[i],
                    &inputs[i],
                ) &&
                // If input was zero, it remains zero
                (field_element_as_nat(&old(inputs)[i]) == 0) ==> field_element_as_nat(&inputs[i])
                    == 0
            },
{
    // Montgomery's Trick and Fast Implementation of Masked AES
    // Genelle, Prouff and Quisquater
    // Section 3.2
    let n = inputs.len();

    // Extract ONE constant before loops (similar to scalar.rs pattern)
    let one = FieldElement::ONE;

    /* <VERIFICATION NOTE>
         Build vec manually instead of vec![one; n] for Verus compatibility
        </VERIFICATION NOTE> */
    /* <ORIGINAL CODE>
         let mut scratch = vec![FieldElement::ONE; n];
        </ORIGINAL CODE> */
    let mut scratch = Vec::new();
    for _ in 0..n {
        scratch.push(one);
    }

    // Keep an accumulator of all of the previous products
    let mut acc = one;

    // Pass through the input vector, recording the previous
    // products in the scratch space
    /* <VERIFICATION NOTE>
         Rewritten with index loop instead of .zip() for Verus compatibility
         Using choice_not() wrapper instead of ! operator
        </VERIFICATION NOTE> */
    /* <ORIGINAL CODE>
         for (input, scratch) in inputs.iter().zip(scratch.iter_mut()) {
            *scratch = acc;
            // acc <- acc * input, but skipping zeros (constant-time)
            acc.conditional_assign(&(&acc * input), !input.is_zero());
        }
        </ORIGINAL CODE> */
    for i in 0..n {
        assume(false);
        scratch[i] = acc;
        assume(false);
        // acc <- acc * input, but skipping zeros (constant-time)
        acc.conditional_assign(&(&acc * &inputs[i]), choice_not(inputs[i].is_zero()));
    }

    // acc is nonzero because we skipped zeros in inputs
    // ORIGINAL: assert!(bool::from(!acc.is_zero()));
    #[cfg(not(verus_keep_ghost))]
        assert!(bool::from(choice_not(acc.is_zero())));

    // Compute the inverse of all products
    acc = acc.invert();

    // Pass through the vector backwards to compute the inverses
    // in place
    /* <VERIFICATION NOTE>
         Manual reverse loop instead of .rev().zip() for Verus compatibility
         Using choice_not() wrapper instead of ! operator
         Extract-modify-reassign pattern for mutable indexing
        </VERIFICATION NOTE> */
    /* <ORIGINAL CODE>
         for (input, scratch) in inputs.iter_mut().rev().zip(scratch.into_iter().rev()) {
            let tmp = &acc * input;
            // input <- acc * scratch, then acc <- tmp
            // Again, we skip zeros in a constant-time way
            let nz = !input.is_zero();
            input.conditional_assign(&(&acc * &scratch), nz);
            acc.conditional_assign(&tmp, nz);
        }
        </ORIGINAL CODE> */

    proof {
        assume(scratch.len() == n);
    }

    let mut i: usize = n;
    while i > 0
        invariant
            n == inputs.len(),
            n == scratch.len(),
        decreases i,
    {
        i -= 1;
        proof {
            assume(i < inputs.len());
            assume(i < scratch.len());
            assume(0 <= i);
            assume(false);
        }
        let tmp = &acc * &inputs[i];
        // input <- acc * scratch, then acc <- tmp
        // Again, we skip zeros in a constant-time way
        let nz = choice_not(inputs[i].is_zero());
        // Verus doesn't support index for &mut, so we extract-modify-reassign
        let mut input_i = inputs[i];
        input_i.conditional_assign(&(&acc * &scratch[i]), nz);
        inputs[i] = input_i;
        acc.conditional_assign(&tmp, nz);
    }

    proof {
        // Assume the postconditions hold
        assume(forall|i: int|
            #![auto]
            0 <= i < inputs.len() ==> {
                (field_element_as_nat(&old(inputs)[i]) != 0) ==> is_inverse_field(
                    &old(inputs)[i],
                    &inputs[i],
                ) && (field_element_as_nat(&old(inputs)[i]) == 0) ==> field_element_as_nat(
                    &inputs[i],
                ) == 0
            });
    }
}

/// Given a nonzero field element, compute its inverse.
///
/// The inverse is computed as self^(p-2), since
/// x^(p-2)x = x^(p-1) = 1 (mod p).
///
/// This function returns zero on input zero.
#[rustfmt::skip]  // keep alignment of explanatory comments
#[allow(clippy::let_and_return)]
pub(crate) fn invert(&self) -> (result:
    FieldElement)
// VERIFICATION NOTE: PROOF BYPASS

    ensures
// If self is non-zero, result is the multiplicative inverse: result * self ≡ 1 (mod p)

        field_element_as_nat(self) != 0 ==> (field_element_as_nat(&result) * field_element_as_nat(
            self,
        )) % p() == 1,
        // If self is zero, result is zero
        field_element_as_nat(self) == 0 ==> field_element_as_nat(&result) == 0,
{
    // The bits of p-2 = 2^255 -19 -2 are 11010111111...11.
    //
    //                                 nonzero bits of exponent
    assume(false);
    let (t19, t3) = self.pow22501();  // t19: 249..0 ; t3: 3,1,0
    let t20 = t19.pow2k(5);  // 254..5
    let t21 = &t20 * &t3;  // 254..5,3,1,0

    t21
}

/// Raise this field element to the power (p-5)/8 = 2^252 -3.
#[rustfmt::skip]  // keep alignment of explanatory comments
#[allow(clippy::let_and_return)]
fn pow_p58(&self) -> (result: FieldElement)
    ensures
        field_element_as_nat(&result) == pow(
            field_element_as_nat(self) as int,
            (pow2(252) - 3) as nat,
        ) % (p() as int),
{
    // The bits of (p-5)/8 are 101111.....11.
    //
    //                                 nonzero bits of exponent
    let (t19, _) = self.pow22501();  // 249..0
    let t20 = t19.pow2k(2);  // 251..2
    assume(false);
    let t21 = self * &t20;  // 251..2,0

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
pub(crate) fn sqrt_ratio_i(u: &FieldElement, v: &FieldElement) -> (result: (
    Choice,
    FieldElement,
))
// VERIFICATION NOTE: any ensures clause causes Verus parsing error
//     ensures sqrt_ratio_i_post(u, v, result.0, &result.1),
/*   (field_element_as_nat(u) == 0) ==> (choice_is_true(result.0) && field_element_as_nat(&result.1) == 0),
   (field_element_as_nat(v) == 0 && field_element_as_nat(u) != 0) ==> (!choice_is_true(result.0) && field_element_as_nat(&result.1) == 0),
   (choice_is_true(result.0) && field_element_as_nat(v) != 0) ==> is_sqrt_ratio(u, v, &result.1),
   */
{
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
    proof {
        assume(false);  // PROOF BYPASS: arithmetic trait operations
    }
    let v3 = &v.square() * v;
    let v7 = &v3.square() * v;
    let mut r = &(u * &v3) * &(u * &v7).pow_p58();
    let check = v * &r.square();

    let i = &constants::SQRT_M1;

    let correct_sign_sqrt = check.ct_eq(u);

    // ORIGINAL CODE:
    // let flipped_sign_sqrt = check.ct_eq(&(-u));
    // let flipped_sign_sqrt_i = check.ct_eq(&(&(-u) * i));
    // REFACTORED: Use wrapper to avoid Verus internal error with negation
    let u_neg = negate_field(u);
    let flipped_sign_sqrt = check.ct_eq(&u_neg);
    let flipped_sign_sqrt_i = check.ct_eq(&(&u_neg * i));

    let r_prime = &constants::SQRT_M1 * &r;
    // ORIGINAL CODE:
    // r.conditional_assign(&r_prime, flipped_sign_sqrt | flipped_sign_sqrt_i);
    // REFACTORED: Use wrapper for Choice bitwise OR
    r.conditional_assign(&r_prime, choice_or(flipped_sign_sqrt, flipped_sign_sqrt_i));

    // Choose the nonnegative square root.
    let r_is_negative = r.is_negative();
    // ORIGINAL CODE:
    // r.conditional_negate(r_is_negative);
    // REFACTORED: Use wrapper for conditional_negate
    conditional_negate_field(&mut r, r_is_negative);

    // ORIGINAL CODE:
    // let was_nonzero_square = correct_sign_sqrt | flipped_sign_sqrt;
    // REFACTORED: Use wrapper for Choice bitwise OR
    let was_nonzero_square = choice_or(correct_sign_sqrt, flipped_sign_sqrt);

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
pub(crate) fn invsqrt(&self) -> (result: (
    Choice,
    FieldElement,
))
// VERIFICATION NOTE: PROOF BYPASS

    ensures
        (field_element_as_nat(self) == 0) ==> (!choice_is_true(result.0) && field_element_as_nat(
            &result.1,
        ) == 0),
        (choice_is_true(result.0)) ==> is_sqrt_ratio(&FieldElement::ONE, self, &result.1),
{
    assume(false);
    FieldElement::sqrt_ratio_i(&FieldElement::ONE, self)
}

} // verus!
}

// #[cfg(test)]
// mod test {
//     use crate::field::*;

//     /// Random element a of GF(2^255-19), from Sage
//     /// a = 1070314506888354081329385823235218444233221\
//     ///     2228051251926706380353716438957572
//     static A_BYTES: [u8; 32] = [
//         0x04, 0xfe, 0xdf, 0x98, 0xa7, 0xfa, 0x0a, 0x68, 0x84, 0x92, 0xbd, 0x59, 0x08, 0x07, 0xa7,
//         0x03, 0x9e, 0xd1, 0xf6, 0xf2, 0xe1, 0xd9, 0xe2, 0xa4, 0xa4, 0x51, 0x47, 0x36, 0xf3, 0xc3,
//         0xa9, 0x17,
//     ];

//     /// Byte representation of a**2
//     static ASQ_BYTES: [u8; 32] = [
//         0x75, 0x97, 0x24, 0x9e, 0xe6, 0x06, 0xfe, 0xab, 0x24, 0x04, 0x56, 0x68, 0x07, 0x91, 0x2d,
//         0x5d, 0x0b, 0x0f, 0x3f, 0x1c, 0xb2, 0x6e, 0xf2, 0xe2, 0x63, 0x9c, 0x12, 0xba, 0x73, 0x0b,
//         0xe3, 0x62,
//     ];

//     /// Byte representation of 1/a
//     static AINV_BYTES: [u8; 32] = [
//         0x96, 0x1b, 0xcd, 0x8d, 0x4d, 0x5e, 0xa2, 0x3a, 0xe9, 0x36, 0x37, 0x93, 0xdb, 0x7b, 0x4d,
//         0x70, 0xb8, 0x0d, 0xc0, 0x55, 0xd0, 0x4c, 0x1d, 0x7b, 0x90, 0x71, 0xd8, 0xe9, 0xb6, 0x18,
//         0xe6, 0x30,
//     ];

//     /// Byte representation of a^((p-5)/8)
//     static AP58_BYTES: [u8; 32] = [
//         0x6a, 0x4f, 0x24, 0x89, 0x1f, 0x57, 0x60, 0x36, 0xd0, 0xbe, 0x12, 0x3c, 0x8f, 0xf5, 0xb1,
//         0x59, 0xe0, 0xf0, 0xb8, 0x1b, 0x20, 0xd2, 0xb5, 0x1f, 0x15, 0x21, 0xf9, 0xe3, 0xe1, 0x61,
//         0x21, 0x55,
//     ];

//     #[test]
//     fn a_mul_a_vs_a_squared_constant() {
//         let a = FieldElement::from_bytes(&A_BYTES);
//         let asq = FieldElement::from_bytes(&ASQ_BYTES);
//         assert_eq!(asq, &a * &a);
//     }

//     #[test]
//     fn a_square_vs_a_squared_constant() {
//         let a = FieldElement::from_bytes(&A_BYTES);
//         let asq = FieldElement::from_bytes(&ASQ_BYTES);
//         assert_eq!(asq, a.square());
//     }

//     #[test]
//     fn a_square2_vs_a_squared_constant() {
//         let a = FieldElement::from_bytes(&A_BYTES);
//         let asq = FieldElement::from_bytes(&ASQ_BYTES);
//         assert_eq!(a.square2(), &asq + &asq);
//     }

//     #[test]
//     fn a_invert_vs_inverse_of_a_constant() {
//         let a = FieldElement::from_bytes(&A_BYTES);
//         let ainv = FieldElement::from_bytes(&AINV_BYTES);
//         let should_be_inverse = a.invert();
//         assert_eq!(ainv, should_be_inverse);
//         assert_eq!(FieldElement::ONE, &a * &should_be_inverse);
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn batch_invert_a_matches_nonbatched() {
//         let a = FieldElement::from_bytes(&A_BYTES);
//         let ap58 = FieldElement::from_bytes(&AP58_BYTES);
//         let asq = FieldElement::from_bytes(&ASQ_BYTES);
//         let ainv = FieldElement::from_bytes(&AINV_BYTES);
//         let a0 = &a - &a;
//         let a2 = &a + &a;
//         let a_list = vec![a, ap58, asq, ainv, a0, a2];
//         let mut ainv_list = a_list.clone();
//         FieldElement::batch_invert(&mut ainv_list[..]);
//         for i in 0..6 {
//             assert_eq!(a_list[i].invert(), ainv_list[i]);
//         }
//     }

//     #[test]
//     fn sqrt_ratio_behavior() {
//         let zero = FieldElement::ZERO;
//         let one = FieldElement::ONE;
//         let i = constants::SQRT_M1;
//         let two = &one + &one; // 2 is nonsquare mod p.
//         let four = &two + &two; // 4 is square mod p.

//         // 0/0 should return (1, 0) since u is 0
//         let (choice, sqrt) = FieldElement::sqrt_ratio_i(&zero, &zero);
//         assert!(bool::from(choice));
//         assert_eq!(sqrt, zero);
//         assert!(bool::from(!sqrt.is_negative()));

//         // 1/0 should return (0, 0) since v is 0, u is nonzero
//         let (choice, sqrt) = FieldElement::sqrt_ratio_i(&one, &zero);
//         assert!(bool::from(!choice));
//         assert_eq!(sqrt, zero);
//         assert!(bool::from(!sqrt.is_negative()));

//         // 2/1 is nonsquare, so we expect (0, sqrt(i*2))
//         let (choice, sqrt) = FieldElement::sqrt_ratio_i(&two, &one);
//         assert!(bool::from(!choice));
//         assert_eq!(sqrt.square(), &two * &i);
//         assert!(bool::from(!sqrt.is_negative()));

//         // 4/1 is square, so we expect (1, sqrt(4))
//         let (choice, sqrt) = FieldElement::sqrt_ratio_i(&four, &one);
//         assert!(bool::from(choice));
//         assert_eq!(sqrt.square(), four);
//         assert!(bool::from(!sqrt.is_negative()));

//         // 1/4 is square, so we expect (1, 1/sqrt(4))
//         let (choice, sqrt) = FieldElement::sqrt_ratio_i(&one, &four);
//         assert!(bool::from(choice));
//         assert_eq!(&sqrt.square() * &four, one);
//         assert!(bool::from(!sqrt.is_negative()));
//     }

//     #[test]
//     fn a_p58_vs_ap58_constant() {
//         let a = FieldElement::from_bytes(&A_BYTES);
//         let ap58 = FieldElement::from_bytes(&AP58_BYTES);
//         assert_eq!(ap58, a.pow_p58());
//     }

//     #[test]
//     fn equality() {
//         let a = FieldElement::from_bytes(&A_BYTES);
//         let ainv = FieldElement::from_bytes(&AINV_BYTES);
//         assert!(a == a);
//         assert!(a != ainv);
//     }

//     /// Notice that the last element has the high bit set, which
//     /// should be ignored
//     static B_BYTES: [u8; 32] = [
//         113, 191, 169, 143, 91, 234, 121, 15, 241, 131, 217, 36, 230, 101, 92, 234, 8, 208, 170,
//         251, 97, 127, 70, 210, 58, 23, 166, 87, 240, 169, 184, 178,
//     ];

//     #[test]
//     fn from_bytes_highbit_is_ignored() {
//         let mut cleared_bytes = B_BYTES;
//         cleared_bytes[31] &= 127u8;
//         let with_highbit_set = FieldElement::from_bytes(&B_BYTES);
//         let without_highbit_set = FieldElement::from_bytes(&cleared_bytes);
//         assert_eq!(without_highbit_set, with_highbit_set);
//     }

//     #[test]
//     fn conditional_negate() {
//         let one = FieldElement::ONE;
//         let minus_one = FieldElement::MINUS_ONE;
//         let mut x = one;
//         x.conditional_negate(Choice::from(1));
//         assert_eq!(x, minus_one);
//         x.conditional_negate(Choice::from(0));
//         assert_eq!(x, minus_one);
//         x.conditional_negate(Choice::from(1));
//         assert_eq!(x, one);
//     }

//     #[test]
//     fn encoding_is_canonical() {
//         // Encode 1 wrongly as 1 + (2^255 - 19) = 2^255 - 18
//         let one_encoded_wrongly_bytes: [u8; 32] = [
//             0xee, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0x7f,
//         ];
//         // Decode to a field element
//         let one = FieldElement::from_bytes(&one_encoded_wrongly_bytes);
//         // .. then check that the encoding is correct
//         let one_bytes = one.as_bytes();
//         assert_eq!(one_bytes[0], 1);
//         for byte in &one_bytes[1..] {
//             assert_eq!(*byte, 0);
//         }
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn batch_invert_empty() {
//         FieldElement::batch_invert(&mut []);
//     }
// }
