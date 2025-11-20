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

use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;

use crate::lemmas::field_lemmas::as_bytes_lemmas::*;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::*;

#[allow(unused_imports)]
use crate::core_assumes::*;

#[allow(unused_imports)]
use crate::specs::field_specs::*;

#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;

#[allow(unused_imports)]
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::as_bytes_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::pow22501_t19_lemma::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::pow22501_t3_lemma::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::pow_p58_lemma::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::u64_5_as_nat_lemmas::*;

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

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::cmp::PartialEqSpecImpl for FieldElement {
    open spec fn obeys_eq_spec() -> bool {
        true  // Equality obeys eq_spec via constant-time comparison

    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other)
    }
}

impl PartialEq for FieldElement {
    fn eq(&self, other: &FieldElement) -> (result:
        bool)/* VERIFICATION NOTE:
     - DRAFT SPEC: spec_fe51_to_bytes is a complex spec function that should correspond to as_bytes()
     - PartialEqSpecImpl trait provides the external specification
     - Proof follows from ct_eq and choice_into postconditions
     */

        ensures
            result == (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other)),
    {
        /* <VERIFICATION NOTE>
         Use wrapper function for Choice::into
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         self.ct_eq(other).into()
         </ORIGINAL CODE> */
        let choice = self.ct_eq(other);
        let result = choice_into(choice);

        proof {
            // Proof chain:
            // 1. ct_eq ensures: choice_is_true(choice) == (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other))
            // 2. choice_into ensures: result == choice_is_true(choice)
            // 3. Therefore: result == (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other))
            // This is a direct consequence of the two postconditions
            assert(result == choice_is_true(choice));  // from choice_into
            assert(choice_is_true(choice) == (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(
                other,
            )));  // from ct_eq
            assert(result == (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other)));
        }

        result
    }
}

impl ConstantTimeEq for FieldElement {
    /// Test equality between two `FieldElement`s.  Since the
    /// internal representation is not canonical, the field elements
    /// are normalized to wire format before comparison.
    fn ct_eq(&self, other: &FieldElement) -> (result:
        Choice)/* <VERIFICATION NOTE>
     - Use wrapper functions for ConstantTimeEq and CtOption
     - DRAFT SPEC: spec_fe51_to_bytes is a complex spec function that should correspond to as_bytes()
     - Proof uses lemma_as_bytes_equals_spec_fe51_to_bytes
    </VERIFICATION NOTE> */

        ensures
            choice_is_true(result) == (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other)),
    {
        /* <VERIFICATION NOTE>
         Use wrapper function for Verus compatibility instead of direct subtle call
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         self.as_bytes().ct_eq(&other.as_bytes())
         </ORIGINAL CODE> */
        // Call as_bytes() in exec mode (outside proof block)
        let self_bytes = self.as_bytes();
        let other_bytes = other.as_bytes();
        let result = ct_eq_bytes32(&self_bytes, &other_bytes);

        proof {
            // Proof chain:
            // 1. ct_eq_bytes32 ensures: choice_is_true(result) == (self_bytes == other_bytes)
            // 2. Array equality <==> sequence equality
            // 3. as_bytes postcondition: u8_32_as_nat(&bytes) == u64_5_as_nat(fe.limbs) % p()
            // 4. lemma_as_bytes_equals_spec_fe51_to_bytes: seq_from32(&bytes) == spec_fe51_to_bytes(fe)
            //    when u8_32_as_nat(&bytes) == u64_5_as_nat(fe.limbs) % p()
            // 5. Therefore: choice_is_true(result) == (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other))
            // From as_bytes() postcondition, we know:
            // - u8_32_as_nat(&self_bytes) == u64_5_as_nat(self.limbs) % p()
            // - u8_32_as_nat(&other_bytes) == u64_5_as_nat(other.limbs) % p()
            // Apply lemmas with the bytes and the postcondition requirement
            lemma_as_bytes_equals_spec_fe51_to_bytes(self, &self_bytes);
            lemma_as_bytes_equals_spec_fe51_to_bytes(other, &other_bytes);

            // Now we have:
            // - seq_from32(&self_bytes) == spec_fe51_to_bytes(self)
            // - seq_from32(&other_bytes) == spec_fe51_to_bytes(other)

            // Prove the bidirectional implication:
            // (self_bytes == other_bytes) <==> (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other))

            // Forward direction: array equality implies spec equality
            if self_bytes == other_bytes {
                // Arrays equal => all elements equal => sequences equal
                assert forall|i: int| 0 <= i < 32 implies self_bytes[i] == other_bytes[i] by {}
                assert(seq_from32(&self_bytes) == seq_from32(&other_bytes));
                assert(spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other));
            }
            // Backward direction: spec equality implies array equality

            if spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other) {
                assert(seq_from32(&self_bytes) == seq_from32(&other_bytes));
                lemma_seq_eq_implies_array_eq(&self_bytes, &other_bytes);
                assert(self_bytes == other_bytes);
            }
            // Therefore: (self_bytes == other_bytes) <==> (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other))
            // And since ct_eq_bytes32 ensures: choice_is_true(result) == (self_bytes == other_bytes)
            // We conclude: choice_is_true(result) == (spec_fe51_to_bytes(self) == spec_fe51_to_bytes(other))

        }

        result
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
    pub(crate) fn is_negative(&self) -> (result:
        Choice)/* VERIFICATION NOTE:
    - DRAFT SPEC: spec_fe51_to_bytes is a complex spec function that should correspond to as_bytes()
    - Proof uses lemma_as_bytes_equals_spec_fe51_to_bytes to connect as_bytes() with spec_fe51_to_bytes()
    </VERIFICATION NOTE> */

        ensures
            choice_is_true(result) == (spec_fe51_to_bytes(self)[0] & 1 == 1),
    {
        let bytes = self.as_bytes();
        let result = Choice::from(bytes[0] & 1);

        proof {
            // From as_bytes() postcondition: u8_32_as_nat(&bytes) == u64_5_as_nat(self.limbs) % p()
            // Apply lemma to establish that bytes matches spec_fe51_to_bytes
            lemma_as_bytes_equals_spec_fe51_to_bytes(self, &bytes);
        }

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
    // SPEC BYPASS through placeholder spec_fe51_to_bytes

            choice_is_true(result) == (spec_fe51_to_bytes(self) == seq![0u8; 32]),
    {
        let zero = [0u8;32];
        let bytes = self.as_bytes();

        let result = ct_eq_bytes32(&bytes, &zero);

        proof {
            // Proof: choice_is_true(result) == (spec_fe51_to_bytes(self) == seq![0u8; 32])
            //
            // From ct_eq_bytes32 postcondition: choice_is_true(result) == (bytes == zero)
            // From as_bytes() postcondition: u8_32_as_nat(&bytes) == u64_5_as_nat(self.limbs) % p()
            //
            // Apply lemma to establish: seq_from32(&bytes) == spec_fe51_to_bytes(self)
            lemma_as_bytes_equals_spec_fe51_to_bytes(self, &bytes);

            // Prove bidirectional implication: (bytes == zero) <==> (spec_fe51_to_bytes(self) == seq![0u8; 32])

            if bytes == zero {
                // Forward: byte array equality implies spec equality
                assert(spec_fe51_to_bytes(self) == seq![0u8; 32]);
            }
            if spec_fe51_to_bytes(self) == seq![0u8; 32] {
                // Backward: spec equality implies byte array equality
                assert(seq_from32(&bytes) == seq_from32(&zero));
                assert(bytes == zero);
            }
        }

        result
    }

    /// Compute (self^(2^250-1), self^11), used as a helper function
    /// within invert() and pow22523().
    #[rustfmt::skip]  // keep alignment of explanatory comments
    fn pow22501(&self) -> (result: (FieldElement, FieldElement))
        requires
            limbs_bounded(self, 54),
        ensures
    // Bounded limbs (maintained by all field operations)

            limbs_bounded(&result.0, 54),
            limbs_bounded(&result.1, 54),
            // Mathematical values
            spec_field_element(&result.0) == (pow(
                spec_field_element(self) as int,
                (pow2(250) - 1) as nat,
            ) as nat) % p(),
            spec_field_element(&result.1) == (pow(spec_field_element(self) as int, 11) as nat)
                % p(),
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
        let t0 = self.square();  // 1         e_0 = 2^1
        // NOTE: Changing the code!!!
        // NOTE: We are now using the intermediate variable t0_sq to track the postcondition of the first square.
        // NOTE: This is a workaround to allow us to prove the postcondition of the second square.
        // NOTE: I'm struggling to prove that t0.square().square() is the same as t0_sq.square().
        // Break apart chained call to track intermediate postcondition
        // NOTE: Using intermediate variable t0_sq to track the postcondition
        let t0_sq = t0.square();  // e = 4 (intermediate step)
        // let t1 = t0.square().square();  // 3         e_1 = 2^3 = 8
        let t1 = t0_sq.square();  // 3         e_1 = 2^3 = 8
        let t2 = self * &t1;  // 3,0       e_2 = 2^3 + 2^0 = 9
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

        proof {
            // Assert the field operation postconditions that the lemma requires
            pow255_gt_19();  // Prove p() > 0

            // Square operation postconditions (from .square() method ensures clause)
            assert(u64_5_as_nat(t0.limbs) % p() == pow(u64_5_as_nat(self.limbs) as int, 2) as nat
                % p());
            assert(u64_5_as_nat(t0_sq.limbs) % p() == pow(u64_5_as_nat(t0.limbs) as int, 2) as nat
                % p());
            assert(u64_5_as_nat(t1.limbs) % p() == pow(u64_5_as_nat(t0_sq.limbs) as int, 2) as nat
                % p());

            // For mul operations, use lemma to convert from field_mul to direct multiplication
            assert(u64_5_as_nat(t2.limbs) % p() == (u64_5_as_nat(self.limbs) * u64_5_as_nat(
                t1.limbs,
            )) % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(self.limbs) as int,
                    u64_5_as_nat(t1.limbs) as int,
                    p() as int,
                );
            };
            assert(u64_5_as_nat(t3.limbs) % p() == (u64_5_as_nat(t0.limbs) * u64_5_as_nat(t2.limbs))
                % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(t0.limbs) as int,
                    u64_5_as_nat(t2.limbs) as int,
                    p() as int,
                );
            };

            // Use lemma to prove t3 = x^11 and all intermediate steps
            lemma_pow22501_prove_t3(
                self.limbs,
                t0.limbs,
                t0_sq.limbs,
                t1.limbs,
                t2.limbs,
                t3.limbs,
            );

            let base = u64_5_as_nat(self.limbs) as int;

            // Prove t19 = x^(2^250-1) using explicit lemma

            // Multiplication: t5 = t2 * t4
            assert(u64_5_as_nat(t5.limbs) % p() == (u64_5_as_nat(t2.limbs) * u64_5_as_nat(t4.limbs))
                % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(t2.limbs) as int,
                    u64_5_as_nat(t4.limbs) as int,
                    p() as int,
                );
            };

            // Multiplication: t7 = t6 * t5
            assert(u64_5_as_nat(t7.limbs) % p() == (u64_5_as_nat(t6.limbs) * u64_5_as_nat(t5.limbs))
                % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(t6.limbs) as int,
                    u64_5_as_nat(t5.limbs) as int,
                    p() as int,
                );
            };

            // Multiplication: t9 = t8 * t7
            assert(u64_5_as_nat(t9.limbs) % p() == (u64_5_as_nat(t8.limbs) * u64_5_as_nat(t7.limbs))
                % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(t8.limbs) as int,
                    u64_5_as_nat(t7.limbs) as int,
                    p() as int,
                );
            };

            // Multiplication: t11 = t10 * t9
            assert(u64_5_as_nat(t11.limbs) % p() == (u64_5_as_nat(t10.limbs) * u64_5_as_nat(
                t9.limbs,
            )) % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(t10.limbs) as int,
                    u64_5_as_nat(t9.limbs) as int,
                    p() as int,
                );
            };

            // Multiplication: t13 = t12 * t7
            assert(u64_5_as_nat(t13.limbs) % p() == (u64_5_as_nat(t12.limbs) * u64_5_as_nat(
                t7.limbs,
            )) % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(t12.limbs) as int,
                    u64_5_as_nat(t7.limbs) as int,
                    p() as int,
                );
            };

            // Multiplication: t15 = t14 * t13
            assert(u64_5_as_nat(t15.limbs) % p() == (u64_5_as_nat(t14.limbs) * u64_5_as_nat(
                t13.limbs,
            )) % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(t14.limbs) as int,
                    u64_5_as_nat(t13.limbs) as int,
                    p() as int,
                );
            };

            // Multiplication: t17 = t16 * t15
            assert(u64_5_as_nat(t17.limbs) % p() == (u64_5_as_nat(t16.limbs) * u64_5_as_nat(
                t15.limbs,
            )) % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(t16.limbs) as int,
                    u64_5_as_nat(t15.limbs) as int,
                    p() as int,
                );
            };

            // Multiplication: t19 = t18 * t13
            assert(u64_5_as_nat(t19.limbs) % p() == (u64_5_as_nat(t18.limbs) * u64_5_as_nat(
                t13.limbs,
            )) % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(t18.limbs) as int,
                    u64_5_as_nat(t13.limbs) as int,
                    p() as int,
                );
            };

            // Use our comprehensive lemma to prove t19 = x^(2^250-1)
            lemma_pow22501_prove_t19(
                self.limbs,
                t0.limbs,
                t1.limbs,
                t2.limbs,
                t3.limbs,
                t4.limbs,
                t5.limbs,
                t6.limbs,
                t7.limbs,
                t8.limbs,
                t9.limbs,
                t10.limbs,
                t11.limbs,
                t12.limbs,
                t13.limbs,
                t14.limbs,
                t15.limbs,
                t16.limbs,
                t17.limbs,
                t18.limbs,
                t19.limbs,
            );

            // Bridge from u64_5_as_nat postconditions to spec_field_element postconditions
            // The previous proof established:
            //assert(u64_5_as_nat(t19.limbs) % p() == (pow(u64_5_as_nat(self.limbs) as int, (pow2(250) - 1) as nat) as nat) % p());
            //assert(u64_5_as_nat(t3.limbs) % p() == (pow(u64_5_as_nat(self.limbs) as int, 11) as nat) % p());

            // Use bridge lemma to prove the spec_field_element postconditions
            lemma_bridge_pow_as_nat_to_spec(&t19, self, (pow2(250) - 1) as nat);
            lemma_bridge_pow_as_nat_to_spec(&t3, self, 11);

            // Bounded limbs: all field operations (mul, square, pow2k) maintain the bound < 2^54
            // t19 is the result of mul (&t18 * &t13), so it inherits the bound from mul's postcondition
            // t3 is the result of mul (&t0 * &t2), so it inherits the bound from mul's postcondition
            assert(limbs_bounded(&t19, 54));
            assert(limbs_bounded(&t3, 54));
        }

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

        requires
            forall|i: int|
                #![trigger old(inputs)[i]]
                0 <= i < old(inputs).len() ==> (forall|j: int|
                    0 <= j < 5 ==> old(inputs)[i].limbs[j] < 1u64 << 54),
        ensures
    // Each element is replaced appropriately:

            forall|i: int|
                #![auto]
                0 <= i < inputs.len() ==> {
                    // If input was non-zero, it's replaced with its inverse
                    (spec_field_element(&old(inputs)[i]) != 0) ==> is_inverse_field(
                        &old(inputs)[i],
                        &inputs[i],
                    ) &&
                    // If input was zero, it remains zero
                    (spec_field_element(&old(inputs)[i]) == 0) ==> spec_field_element(&inputs[i])
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
        proof {
            // PROOF BYPASS: assume acc limbs are bounded
            // (This would follow from the loop invariant, but we haven't proven that yet)
            assume(limbs_bounded(&acc, 54));
        }
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
            assume(false);
        }

        let mut i: usize = n;
        while i > 0
            invariant
                n == inputs.len(),
                n == scratch.len(),
            decreases i,
        {
            i -= 1;
            assume(false);
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
                    (spec_field_element(&old(inputs)[i]) != 0) ==> is_inverse_field(
                        &old(inputs)[i],
                        &inputs[i],
                    ) && (spec_field_element(&old(inputs)[i]) == 0) ==> spec_field_element(
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

        requires
            limbs_bounded(self, 54),
        ensures
    // If self is non-zero, result is the multiplicative inverse: result * self ≡ 1 (mod p)

            spec_field_element(self) != 0 ==> (spec_field_element(&result) * spec_field_element(
                self,
            )) % p() == 1,
            // If self is zero, result is zero
            spec_field_element(self) == 0 ==> spec_field_element(&result) == 0,
            spec_field_element(&result) == math_field_inv(spec_field_element(self)),
            limbs_bounded(&result, 54),
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
        requires
            limbs_bounded(self, 54),
        ensures
    // Bounded limbs (maintained by all field operations)

            limbs_bounded(&result, 54),
            // Mathematical value
            spec_field_element(&result) == (pow(
                spec_field_element(self) as int,
                (pow2(252) - 3) as nat,
            ) as nat) % p(),
    {
        // The bits of (p-5)/8 are 101111.....11.
        //
        //                                 nonzero bits of exponent
        let (t19, _) = self.pow22501();  // 249..0 = x^(2^250-1)
        let t20 = t19.pow2k(2);  // 251..2 = x^(2^252-4)
        let t21 = self * &t20;  // 251..2,0 = x^(2^252-3)

        proof {
            pow255_gt_19();

            // Bridge from spec_field_element to u64_5_as_nat
            assert(u64_5_as_nat(t19.limbs) % p() == spec_field_element(&t19));
            assert(u64_5_as_nat(self.limbs) % p() == spec_field_element(self));

            // Use lemma_pow_mod_noop to bridge from spec_field_element to u64_5_as_nat
            lemma_pow_mod_noop(u64_5_as_nat(self.limbs) as int, (pow2(250) - 1) as nat, p() as int);
            assert(pow(u64_5_as_nat(self.limbs) as int, (pow2(250) - 1) as nat) >= 0) by {
                lemma_pow_nonnegative(u64_5_as_nat(self.limbs) as int, (pow2(250) - 1) as nat);
            }
            assert(pow((u64_5_as_nat(self.limbs) % p()) as int, (pow2(250) - 1) as nat) >= 0) by {
                lemma_pow_nonnegative(
                    (u64_5_as_nat(self.limbs) % p()) as int,
                    (pow2(250) - 1) as nat,
                );
            }
            assert(pow(u64_5_as_nat(self.limbs) as int, (pow2(250) - 1) as nat) as nat % p() == pow(
                (u64_5_as_nat(self.limbs) % p()) as int,
                (pow2(250) - 1) as nat,
            ) as nat % p());
            assert(u64_5_as_nat(t19.limbs) % p() == pow(
                u64_5_as_nat(self.limbs) as int,
                (pow2(250) - 1) as nat,
            ) as nat % p());

            // Multiplication: t21 = self * t20
            assert(u64_5_as_nat(t21.limbs) % p() == (u64_5_as_nat(self.limbs) * u64_5_as_nat(
                t20.limbs,
            )) % p()) by {
                lemma_mul_mod_noop_general(
                    u64_5_as_nat(self.limbs) as int,
                    u64_5_as_nat(t20.limbs) as int,
                    p() as int,
                );
            };

            // Use lemma to prove t21 = x^(2^252-3)
            lemma_pow_p58_prove(self.limbs, t19.limbs, t20.limbs, t21.limbs);

            // Bridge back from u64_5_as_nat to spec_field_element
            lemma_bridge_pow_as_nat_to_spec(&t21, self, (pow2(252) - 3) as nat);

            // Bounded limbs: t21 is the result of mul (self * &t20), which maintains the bound
            assert(limbs_bounded(&t21, 54));
        }

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
        ensures
    // When u = 0: always return (true, 0)

            (spec_field_element(u) == 0) ==> (choice_is_true(result.0) && spec_field_element(
                &result.1,
            ) == 0),
            // When v = 0 but u ≠ 0: return (false, 0) [division by zero case]
            (spec_field_element(v) == 0 && spec_field_element(u) != 0) ==> (!choice_is_true(
                result.0,
            ) && spec_field_element(&result.1) == 0),
            // When successful and v ≠ 0: r² * v ≡ u (mod p)
            (choice_is_true(result.0) && spec_field_element(v) != 0) ==> is_sqrt_ratio(
                u,
                v,
                &result.1,
            ),
            // When unsuccessful and v ≠ 0: r² * v ≡ i*u (mod p) [nonsquare case]
            (!choice_is_true(result.0) && spec_field_element(v) != 0 && spec_field_element(u) != 0)
                ==> is_sqrt_ratio_times_i(
                u,
                v,
                &result.1,
            ),
    // VERIFICATION NOTE: PROOF BYPASS

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
            assume(false);  // PROOF BYPASS
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
    // When self = 0: return (false, 0)

            (spec_field_element(self) == 0) ==> (!choice_is_true(result.0) && spec_field_element(
                &result.1,
            ) == 0),
            // When successful and self ≠ 0: r² * self ≡ 1 (mod p)
            (choice_is_true(result.0)) ==> is_sqrt_ratio(&FieldElement::ONE, self, &result.1),
            // When unsuccessful and self ≠ 0: r² * self ≡ i (mod p) [nonsquare case]
            (!choice_is_true(result.0) && spec_field_element(self) != 0) ==> is_sqrt_ratio_times_i(
                &FieldElement::ONE,
                self,
                &result.1,
            ),
    {
        assume(false);
        FieldElement::sqrt_ratio_i(&FieldElement::ONE, self)
    }
}

// verus!
} // verus!
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
