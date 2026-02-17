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
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::as_bytes_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::batch_invert_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::invert_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::pow22501_t19_lemma::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::pow22501_t3_lemma::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::pow_p58_lemma::*;
use crate::lemmas::field_lemmas::sqrt_m1_lemmas::*;
use crate::lemmas::field_lemmas::sqrt_ratio_lemmas::*;
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
        spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other)
    }
}

impl PartialEq for FieldElement {
    fn eq(&self, other: &FieldElement) -> (result:
        bool)/* VERIFICATION NOTE:
     - DRAFT SPEC: spec_fe51_as_bytes is a complex spec function that should correspond to as_bytes()
     - PartialEqSpecImpl trait provides the external specification
     - Proof follows from ct_eq and choice_into postconditions
     */

        ensures
            result == (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other)),
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
            // 1. ct_eq ensures: choice_is_true(choice) == (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other))
            // 2. choice_into ensures: result == choice_is_true(choice)
            // 3. Therefore: result == (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other))
            // This is a direct consequence of the two postconditions
            assert(result == choice_is_true(choice));  // from choice_into
            assert(choice_is_true(choice) == (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(
                other,
            )));  // from ct_eq
            assert(result == (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other)));
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
     - DRAFT SPEC: spec_fe51_as_bytes is a complex spec function that should correspond to as_bytes()
     - Proof uses lemma_as_bytes_equals_spec_fe51_to_bytes
    </VERIFICATION NOTE> */

        ensures
            choice_is_true(result) == (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other)),
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
            // 4. lemma_as_bytes_equals_spec_fe51_to_bytes: seq_from32(&bytes) == spec_fe51_as_bytes(fe)
            //    when u8_32_as_nat(&bytes) == u64_5_as_nat(fe.limbs) % p()
            // 5. Therefore: choice_is_true(result) == (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other))
            // From as_bytes() postcondition, we know:
            // - u8_32_as_nat(&self_bytes) == u64_5_as_nat(self.limbs) % p()
            // - u8_32_as_nat(&other_bytes) == u64_5_as_nat(other.limbs) % p()
            // Apply lemmas with the bytes and the postcondition requirement
            lemma_as_bytes_equals_spec_fe51_to_bytes(self, &self_bytes);
            lemma_as_bytes_equals_spec_fe51_to_bytes(other, &other_bytes);

            // Now we have:
            // - seq_from32(&self_bytes) == spec_fe51_as_bytes(self)
            // - seq_from32(&other_bytes) == spec_fe51_as_bytes(other)

            // Prove the bidirectional implication:
            // (self_bytes == other_bytes) <==> (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other))

            // Forward direction: array equality implies spec equality
            if self_bytes == other_bytes {
                // Arrays equal => all elements equal => sequences equal
                assert forall|i: int| 0 <= i < 32 implies self_bytes[i] == other_bytes[i] by {}
                assert(seq_from32(&self_bytes) == seq_from32(&other_bytes));
                assert(spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other));
            }
            // Backward direction: spec equality implies array equality

            if spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other) {
                assert(seq_from32(&self_bytes) == seq_from32(&other_bytes));
                lemma_seq_eq_implies_array_eq(&self_bytes, &other_bytes);
                assert(self_bytes == other_bytes);
            }
            // Therefore: (self_bytes == other_bytes) <==> (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other))
            // And since ct_eq_bytes32 ensures: choice_is_true(result) == (self_bytes == other_bytes)
            // We conclude: choice_is_true(result) == (spec_fe51_as_bytes(self) == spec_fe51_as_bytes(other))

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
    - DRAFT SPEC: spec_fe51_as_bytes is a complex spec function that should correspond to as_bytes()
    - Proof uses lemma_as_bytes_equals_spec_fe51_to_bytes to connect as_bytes() with spec_fe51_as_bytes()
    </VERIFICATION NOTE> */

        ensures
            choice_is_true(result) == (spec_fe51_as_bytes(self)[0] & 1 == 1),
    {
        let bytes = self.as_bytes();
        let result = Choice::from(bytes[0] & 1);

        proof {
            // From as_bytes() postcondition: u8_32_as_nat(&bytes) == u64_5_as_nat(self.limbs) % p()
            // Apply lemma to establish that bytes matches spec_fe51_as_bytes
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
    // SPEC BYPASS through placeholder spec_fe51_as_bytes

            choice_is_true(result) == (spec_fe51_as_bytes(self) == seq![0u8; 32]),
    {
        let zero = [0u8;32];
        let bytes = self.as_bytes();

        let result = ct_eq_bytes32(&bytes, &zero);

        proof {
            // Proof: choice_is_true(result) == (spec_fe51_as_bytes(self) == seq![0u8; 32])
            //
            // From ct_eq_bytes32 postcondition: choice_is_true(result) == (bytes == zero)
            // From as_bytes() postcondition: u8_32_as_nat(&bytes) == u64_5_as_nat(self.limbs) % p()
            //
            // Apply lemma to establish: seq_from32(&bytes) == spec_fe51_as_bytes(self)
            lemma_as_bytes_equals_spec_fe51_to_bytes(self, &bytes);

            // Prove bidirectional implication: (bytes == zero) <==> (spec_fe51_as_bytes(self) == seq![0u8; 32])

            if bytes == zero {
                // Forward: byte array equality implies spec equality
                assert(spec_fe51_as_bytes(self) == seq![0u8; 32]);
            }
            if spec_fe51_as_bytes(self) == seq![0u8; 32] {
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
            fe51_limbs_bounded(self, 54),
        ensures
    // Bounded limbs (maintained by all field operations)

            fe51_limbs_bounded(&result.0, 54),
            fe51_limbs_bounded(&result.1, 54),
            // Mathematical values
            fe51_as_canonical_nat(&result.0) == field_canonical(
                pow(fe51_as_canonical_nat(self) as int, (pow2(250) - 1) as nat) as nat,
            ),
            fe51_as_canonical_nat(&result.1) == field_canonical(
                pow(fe51_as_canonical_nat(self) as int, 11) as nat,
            ),
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

            // Bridge from u64_5_as_nat postconditions to fe51_as_canonical_nat postconditions
            // The previous proof established:
            //assert(u64_5_as_nat(t19.limbs) % p() == (pow(u64_5_as_nat(self.limbs) as int, (pow2(250) - 1) as nat) as nat) % p());
            //assert(u64_5_as_nat(t3.limbs) % p() == (pow(u64_5_as_nat(self.limbs) as int, 11) as nat) % p());

            // Use bridge lemma to prove the fe51_as_canonical_nat postconditions
            lemma_bridge_pow_as_nat_to_spec(&t19, self, (pow2(250) - 1) as nat);
            lemma_bridge_pow_as_nat_to_spec(&t3, self, 11);

            // Bounded limbs: all field operations (mul, square, pow2k) maintain the bound < 2^54
            // t19 is the result of mul (&t18 * &t13), so it inherits the bound from mul's postcondition
            // t3 is the result of mul (&t0 * &t2), so it inherits the bound from mul's postcondition
            assert(fe51_limbs_bounded(&t19, 54));
            assert(fe51_limbs_bounded(&t3, 54));
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
    </VERIFICATION NOTE> */

        requires
            forall|i: int|
                #![trigger old(inputs)[i]]
                0 <= i < old(inputs).len() ==> fe51_limbs_bounded(&old(inputs)[i], 54),
        ensures
    // Each element is replaced appropriately:

            forall|i: int|
                #![auto]
                0 <= i < inputs.len() ==> (
                // If input was non-zero, it's replaced with its inverse
                ((fe51_as_canonical_nat(&old(inputs)[i]) != 0) ==> is_inverse_field(
                    &old(inputs)[i],
                    &inputs[i],
                )) &&
                // If input was zero, it remains zero
                ((fe51_as_canonical_nat(&old(inputs)[i]) == 0) ==> fe51_as_canonical_nat(&inputs[i])
                    == 0)),
    {
        // Montgomery's Trick and Fast Implementation of Masked AES
        // Genelle, Prouff and Quisquater
        // Section 3.2
        let n = inputs.len();

        // Extract ONE constant before loops (similar to scalar.rs pattern)
        let one = FieldElement::ONE;

        proof {
            // ONE has limbs [1, 0, 0, 0, 0], which is bounded by 54 bits
            assert(fe51_limbs_bounded(&one, 54)) by {
                assert(one.limbs[0] == 1);
                assert(one.limbs[1] == 0);
                assert(one.limbs[2] == 0);
                assert(one.limbs[3] == 0);
                assert(one.limbs[4] == 0);
                assert(1u64 < (1u64 << 54)) by (compute);
                assert(0u64 < (1u64 << 54)) by (compute);
            };
            // ONE has canonical nat value 1
            assert(fe51_as_canonical_nat(&one) == 1) by {
                assert(u64_5_as_nat(one.limbs) == 1) by {
                    assert(one.limbs[0] == 1);
                    assert(one.limbs[1] == 0);
                    assert(one.limbs[2] == 0);
                    assert(one.limbs[3] == 0);
                    assert(one.limbs[4] == 0);
                };
                p_gt_2();
                lemma_small_mod(1nat, p());
            };
        }

        /* <VERIFICATION NOTE>
         Build vec manually instead of vec![one; n] for Verus compatibility
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         let mut scratch = vec![FieldElement::ONE; n];
        </ORIGINAL CODE> */
        let mut scratch = Vec::new();
        for _k in 0..n  // Added loop variable _k to help with verification

            invariant
                scratch.len() == _k,
                scratch@ =~= Seq::new(_k as nat, |j: int| one),
        {
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
        // Ghost: track the original inputs for postcondition
        let ghost original_inputs = inputs@;

        for i in 0..n
            invariant
                n == inputs.len(),
                n == scratch.len(),
                original_inputs.len() == n,
                fe51_limbs_bounded(&acc, 54),
                forall|j: int| #![auto] 0 <= j < i ==> fe51_limbs_bounded(&scratch[j], 54),
                forall|j: int|
                    #![auto]
                    0 <= j < inputs.len() ==> fe51_limbs_bounded(&inputs[j], 54),
                // Inputs are NOT modified by forward loop
                inputs@ === original_inputs,
                // scratch[j] holds the partial product of nonzeros for 0..j
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> fe51_as_canonical_nat(&scratch[j]) == partial_product_nonzeros(
                        original_inputs,
                        j,
                    ),
                // acc holds the partial product of nonzeros for 0..i
                fe51_as_canonical_nat(&acc) == partial_product_nonzeros(original_inputs, i as int),
        {
            scratch[i] = acc;

            // acc <- acc * input, but skipping zeros (constant-time)
            /* <ORIGINAL CODE>
             acc.conditional_assign(&new_acc, choice_not(inputs[i].is_zero()));
            </ORIGINAL CODE> */
            let new_acc = &acc * &inputs[i];

            // Ghost: snapshot acc value before conditional_assign
            let ghost old_acc_val = fe51_as_canonical_nat(&acc);
            let ghost a_i = fe51_as_canonical_nat(&inputs[i as int]);

            let is_zero_choice = inputs[i].is_zero();
            let nz_choice = choice_not(is_zero_choice);
            acc.conditional_assign(&new_acc, nz_choice);

            proof {
                // acc == PP(i+1): by bridge lemma + step relation + case split on a_i
                assert(fe51_as_canonical_nat(&acc) == partial_product_nonzeros(
                    original_inputs,
                    (i + 1) as int,
                )) by {
                    lemma_is_zero_iff_canonical_nat_zero(inputs[i as int]);
                    if a_i != 0 {
                        assert(choice_is_true(nz_choice));
                    } else {
                        assert(!choice_is_true(nz_choice));
                    }
                };
            }
        }

        // acc is nonzero because we skipped zeros in inputs
        // ORIGINAL: assert!(bool::from(!acc.is_zero()));
        #[cfg(not(verus_keep_ghost))]
        assert!(bool::from(choice_not(acc.is_zero())));

        // Compute the inverse of all products
        acc = acc.invert();

        proof {
            // After inversion: field_mul(acc, PP(n)) == 1
            assert(field_mul(
                fe51_as_canonical_nat(&acc),
                partial_product_nonzeros(original_inputs, n as int),
            ) == 1) by {
                let pp_n = partial_product_nonzeros(original_inputs, n as int);
                assert(pp_n % p() != 0) by {
                    lemma_partial_product_nonzeros_is_nonzero(original_inputs, n as int);
                };
                lemma_inv_mul_cancel(pp_n);
            };
        }

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

        let mut i: usize = n;
        while i > 0
            invariant
                n == inputs.len(),
                n == scratch.len(),
                original_inputs.len() == n,
                i <= n,
                fe51_limbs_bounded(&acc, 54),
                forall|j: int|
                    #![auto]
                    0 <= j < scratch.len() ==> fe51_limbs_bounded(&scratch[j], 54),
                forall|j: int|
                    #![auto]
                    0 <= j < inputs.len() ==> fe51_limbs_bounded(&inputs[j], 54),
                // Elements below i haven't been modified yet in backward loop
                forall|j: int| #![auto] 0 <= j < i ==> inputs[j] === original_inputs[j],
                // scratch holds the partial products (unchanged from forward loop)
                forall|j: int|
                    #![auto]
                    0 <= j < n ==> fe51_as_canonical_nat(&scratch[j]) == partial_product_nonzeros(
                        original_inputs,
                        j,
                    ),
                // KEY INVARIANT: acc is the "remaining inverse"
                // field_mul(acc, PP(i)) == 1
                field_mul(
                    fe51_as_canonical_nat(&acc),
                    partial_product_nonzeros(original_inputs, i as int),
                ) == 1,
                // Postcondition for already processed elements (i..n)
                forall|j: int|
                    #![auto]
                    i <= j < n ==> (((fe51_as_canonical_nat(&original_inputs[j]) != 0)
                        ==> is_inverse_field(&original_inputs[j], &inputs[j])) && ((
                    fe51_as_canonical_nat(&original_inputs[j]) == 0) ==> fe51_as_canonical_nat(
                        &inputs[j],
                    ) == 0)),
            decreases i,
        {
            i -= 1;

            // Ghost: snapshot values before the loop body modifies them
            let ghost old_acc_val = fe51_as_canonical_nat(&acc);
            let ghost a_i = fe51_as_canonical_nat(&inputs[i as int]);

            let tmp = &acc * &inputs[i];
            // input <- acc * scratch, then acc <- tmp
            // Again, we skip zeros in a constant-time way
            let nz = choice_not(inputs[i].is_zero());
            // Verus doesn't support index for &mut, so we extract-modify-reassign
            /* <ORIGINAL CODE>
             input_i.conditional_assign(&(&acc * &scratch[i]), nz);
            </ORIGINAL CODE> */
            let mut input_i = inputs[i];
            let acc_times_scratch = &acc * &scratch[i];
            input_i.conditional_assign(&acc_times_scratch, nz);
            inputs[i] = input_i;
            acc.conditional_assign(&tmp, nz);

            proof {
                // Bridge: a_i == 0 iff is_zero bytes are all zero
                assert((spec_fe51_as_bytes(&original_inputs[i as int]) == seq![0u8; 32]) <==> (
                fe51_as_canonical_nat(&original_inputs[i as int]) == 0)) by {
                    lemma_is_zero_iff_canonical_nat_zero(original_inputs[i as int]);
                };

                if a_i != 0 {
                    assert(choice_is_true(nz));
                    // inputs[i] is the inverse of original_inputs[i],
                    // and the acc invariant field_mul(acc, PP(i)) == 1 is maintained
                    assert(is_inverse_field(&original_inputs[i as int], &inputs[i as int])
                        && field_mul(
                        fe51_as_canonical_nat(&acc),
                        partial_product_nonzeros(original_inputs, i as int),
                    ) == 1) by {
                        lemma_backward_step(old_acc_val, a_i, original_inputs, i as int);
                        lemma_field_mul_comm(fe51_as_canonical_nat(&inputs[i as int]), a_i);
                    };
                } else {
                    assert(!choice_is_true(nz));
                    // PP(i) == PP(i+1) since a_i == 0, so acc invariant holds
                    assert(partial_product_nonzeros(original_inputs, (i + 1) as int)
                        == partial_product_nonzeros(original_inputs, i as int));
                }
            }
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
        FieldElement)/* VERIFICATION NOTE:
    - Computes self^(p-2) using Fermat's Little Theorem: a^(p-1) ≡ 1 (mod p) => a^(p-2) * a ≡ 1 (mod p)
    - p-2 = 2^255 - 21 = (2^250 - 1) * 2^5 + 11
    */

        requires
            fe51_limbs_bounded(self, 54),
        ensures
    // If self is non-zero, result is the multiplicative inverse: result * self ≡ 1 (mod p)

            fe51_as_canonical_nat(self) != 0 ==> field_canonical(
                fe51_as_canonical_nat(&result) * fe51_as_canonical_nat(self),
            ) == 1,
            // If self is zero, result is zero
            fe51_as_canonical_nat(self) == 0 ==> fe51_as_canonical_nat(&result) == 0,
            fe51_as_canonical_nat(&result) == field_inv(fe51_as_canonical_nat(self)),
            fe51_limbs_bounded(&result, 54),
    {
        // The bits of p-2 = 2^255 -19 -2 are 11010111111...11.
        //
        //                                 nonzero bits of exponent
        let (t19, t3) = self.pow22501();  // t19: 249..0 ; t3: 3,1,0
        let t20 = t19.pow2k(5);  // 254..5
        let t21 = &t20 * &t3;  // 254..5,3,1,0

        proof {
            lemma_invert_correctness(self, &t19, &t3, &t20, &t21);
        }

        t21
    }

    /// Raise this field element to the power (p-5)/8 = 2^252 -3.
    #[rustfmt::skip]  // keep alignment of explanatory comments
    #[allow(clippy::let_and_return)]
    fn pow_p58(&self) -> (result: FieldElement)
        requires
            fe51_limbs_bounded(self, 54),
        ensures
    // Bounded limbs (maintained by all field operations)

            fe51_limbs_bounded(&result, 54),
            // Mathematical value
            fe51_as_canonical_nat(&result) == field_canonical(
                pow(fe51_as_canonical_nat(self) as int, (pow2(252) - 3) as nat) as nat,
            ),
    {
        // The bits of (p-5)/8 are 101111.....11.
        //
        //                                 nonzero bits of exponent
        let (t19, _) = self.pow22501();  // 249..0 = x^(2^250-1)
        let t20 = t19.pow2k(2);  // 251..2 = x^(2^252-4)
        let t21 = self * &t20;  // 251..2,0 = x^(2^252-3)

        proof {
            pow255_gt_19();

            // Bridge from fe51_as_canonical_nat to u64_5_as_nat
            assert(u64_5_as_nat(t19.limbs) % p() == fe51_as_canonical_nat(&t19));
            assert(u64_5_as_nat(self.limbs) % p() == fe51_as_canonical_nat(self));

            // Use lemma_pow_mod_noop to bridge from fe51_as_canonical_nat to u64_5_as_nat
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

            // Bridge back from u64_5_as_nat to fe51_as_canonical_nat
            lemma_bridge_pow_as_nat_to_spec(&t21, self, (pow2(252) - 3) as nat);

            // Bounded limbs: t21 is the result of mul (self * &t20), which maintains the bound
            assert(fe51_limbs_bounded(&t21, 54));
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
        requires
    // Input bounds for sqrt_ratio_i
    // u and v can be up to 54-bit bounded (from sub/add operations in decompress)

            fe51_limbs_bounded(u, 54),
            fe51_limbs_bounded(v, 54),
        ensures
    // When u = 0: always return (true, 0)

            (fe51_as_canonical_nat(u) == 0) ==> (choice_is_true(result.0) && fe51_as_canonical_nat(
                &result.1,
            ) == 0),
            // When v = 0 but u ≠ 0: return (false, 0) [division by zero case]
            (fe51_as_canonical_nat(v) == 0 && fe51_as_canonical_nat(u) != 0) ==> (!choice_is_true(
                result.0,
            ) && fe51_as_canonical_nat(&result.1) == 0),
            // When successful and v ≠ 0: r² * v ≡ u (mod p)
            (choice_is_true(result.0) && fe51_as_canonical_nat(v) != 0) ==> fe51_is_sqrt_ratio(
                u,
                v,
                &result.1,
            ),
            // When unsuccessful and v ≠ 0: r² * v ≡ i*u (mod p) [nonsquare case]
            (!choice_is_true(result.0) && fe51_as_canonical_nat(v) != 0 && fe51_as_canonical_nat(u)
                != 0) ==> fe51_is_sqrt_ratio_times_i(u, v, &result.1),
            // The result is always the "non-negative" square root (LSB = 0)
            // This is a fundamental property of sqrt_ratio_i that the original code
            // relies on for decompression sign bit handling
            fe51_as_canonical_nat(&result.1) % 2 == 0,
            // Limb bounds: result is 52-bit bounded (from conditional_negate)
            fe51_limbs_bounded(&result.1, 52),
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
        /* ORIGINAL_CODE
        let v3 = &v.square() * v;
        let v7 = &v3.square() * v;
        let mut r = &(u * &v3) * &(u * &v7).pow_p58();
        let check = v * &r.square();
        */
        // MODIFIED: Split expressions for bounds proof assertions
        let v_sq = v.square();
        proof {
            assert(fe51_limbs_bounded(&v_sq, 52));
        }
        let v3 = &v_sq * v;
        proof {
            assert(fe51_limbs_bounded(&v3, 52));
        }
        let v3_sq = v3.square();
        proof {
            assert(fe51_limbs_bounded(&v3_sq, 52));
        }
        let v7 = &v3_sq * v;
        proof {
            assert(fe51_limbs_bounded(&v7, 52));
        }
        let uv3 = u * &v3;
        proof {
            assert(fe51_limbs_bounded(&uv3, 52));
        }
        let uv7 = u * &v7;
        proof {
            assert(fe51_limbs_bounded(&uv7, 52));
        }
        let pow_result = uv7.pow_p58();
        proof {
            assert(fe51_limbs_bounded(&pow_result, 54));
        }
        let mut r = &uv3 * &pow_result;
        proof {
            assert(fe51_limbs_bounded(&r, 52));
        }
        let r_sq = r.square();
        proof {
            assert(fe51_limbs_bounded(&r_sq, 52));
        }
        let check = v * &r_sq;
        proof {
            assert(fe51_limbs_bounded(&check, 52));
        }

        let i = &constants::SQRT_M1;

        let correct_sign_sqrt = check.ct_eq(u);

        // ORIGINAL CODE:
        // let flipped_sign_sqrt = check.ct_eq(&(-u));
        // let flipped_sign_sqrt_i = check.ct_eq(&(&(-u) * i));
        // REFACTORED: Use wrapper to avoid Verus internal error with negation
        let u_neg = negate_field_element(u);
        proof {
            assert(fe51_limbs_bounded(&u_neg, 52));
            axiom_sqrt_m1_limbs_bounded();
        }
        let flipped_sign_sqrt = check.ct_eq(&u_neg);
        let u_neg_i = &u_neg * i;
        proof {
            assert(fe51_limbs_bounded(&u_neg_i, 52));
        }
        let flipped_sign_sqrt_i = check.ct_eq(&u_neg_i);

        let r_prime = &constants::SQRT_M1 * &r;
        proof {
            assert(fe51_limbs_bounded(&r_prime, 52));
            assert(fe51_limbs_bounded(&r, 52));
        }
        // ORIGINAL CODE:
        // r.conditional_assign(&r_prime, flipped_sign_sqrt | flipped_sign_sqrt_i);
        // REFACTORED: Use wrapper for Choice bitwise OR
        let ghost r_before_assign = r;
        r.conditional_assign(&r_prime, choice_or(flipped_sign_sqrt, flipped_sign_sqrt_i));

        proof {
            // After conditional_assign: r.limbs are either r_before_assign.limbs or r_prime.limbs
            // Both are 52-bit bounded, so r is 52-bit bounded
            assert(fe51_limbs_bounded(&r_before_assign, 52));
            assert(fe51_limbs_bounded(&r_prime, 52));
            // The ensures says r.limbs == r_prime.limbs OR r.limbs == old(r).limbs
            assert(r.limbs == r_prime.limbs || r.limbs == r_before_assign.limbs);
            assert(fe51_limbs_bounded(&r, 52));
        }

        // Choose the nonnegative square root.
        let r_is_negative = r.is_negative();
        let ghost r_before_negate = r;
        // ORIGINAL CODE:
        // r.conditional_negate(r_is_negative);
        // REFACTORED: Use specialized wrapper with specs
        conditional_negate_field_element(&mut r, r_is_negative);

        proof {
            // Parity (even) and 52-bit bound after conditional_negate
            lemma_negate_makes_nonnegative(&r_before_negate, &r, r_is_negative);
        }

        // ORIGINAL CODE:
        // let was_nonzero_square = correct_sign_sqrt | flipped_sign_sqrt;
        // REFACTORED: Use wrapper for Choice bitwise OR
        let was_nonzero_square = choice_or(correct_sign_sqrt, flipped_sign_sqrt);

        proof {
            // =================================================================
            // Block 1: Bridging — connect FE51 intermediates to nat-level spec
            // =================================================================
            let pn = p();
            p_gt_2();
            let u_nat = fe51_as_canonical_nat(u);
            let v_nat = fe51_as_canonical_nat(v);
            let r_orig_nat = fe51_as_canonical_nat(&r_before_assign);

            // Connect square outputs to field_square at nat level
            assert(fe51_as_canonical_nat(&r_sq) == field_square(r_orig_nat)) by {
                let limbs_nat = u64_5_as_nat(r_before_assign.limbs);
                lemma_pow_2_is_mul(limbs_nat as int);
                lemma_mul_mod_noop_general(limbs_nat as int, limbs_nat as int, pn as int);
            };
            assert(fe51_as_canonical_nat(&check) == field_mul(v_nat, field_square(r_orig_nat)));

            assert(fe51_as_canonical_nat(&v_sq) == field_square(v_nat)) by {
                let v_limbs = u64_5_as_nat(v.limbs);
                lemma_pow_2_is_mul(v_limbs as int);
                lemma_mul_mod_noop_general(v_limbs as int, v_limbs as int, pn as int);
            };

            let v3_nat = field_mul(field_square(v_nat), v_nat);
            assert(fe51_as_canonical_nat(&v3) == v3_nat);

            assert(fe51_as_canonical_nat(&v3_sq) == field_square(v3_nat)) by {
                let v3_limbs = u64_5_as_nat(v3.limbs);
                lemma_pow_2_is_mul(v3_limbs as int);
                lemma_mul_mod_noop_general(v3_limbs as int, v3_limbs as int, pn as int);
            };

            let v7_nat = field_mul(field_square(v3_nat), v_nat);
            assert(fe51_as_canonical_nat(&v7) == v7_nat);

            let w_nat = field_mul(u_nat, v7_nat);
            assert(fe51_as_canonical_nat(&uv7) == w_nat);

            let uv3_nat = field_mul(u_nat, v3_nat);
            assert(fe51_as_canonical_nat(&uv3) == uv3_nat);

            let k_nat = ((pn - 5) / 8) as nat;
            lemma_p_divisibility_facts();
            assert(k_nat == (pow2(252) - 3) as nat);

            let pow_result_nat = fe51_as_canonical_nat(&pow_result);
            assert(pow_result_nat == (pow(w_nat as int, k_nat) as nat) % pn);

            assert(pow(w_nat as int, k_nat) >= 0) by {
                lemma_pow_nonnegative(w_nat as int, k_nat);
            };

            assert(r_orig_nat == field_mul(uv3_nat, pow_result_nat));

            // =================================================================
            // Block 2: Setup — canonical nats, ct_eq conversion, conditional_assign
            // =================================================================
            let check_nat = fe51_as_canonical_nat(&check);
            let r_assigned_nat = fe51_as_canonical_nat(&r_before_negate);
            let r_final_nat = fe51_as_canonical_nat(&r);

            assert(u_nat < pn && v_nat < pn && check_nat < pn && r_orig_nat < pn && r_assigned_nat
                < pn && r_final_nat < pn) by {
                lemma_mod_bound(u_nat as int, pn as int);
                lemma_mod_bound(v_nat as int, pn as int);
                lemma_mod_bound(check_nat as int, pn as int);
                lemma_mod_bound(r_orig_nat as int, pn as int);
                lemma_mod_bound(r_assigned_nat as int, pn as int);
                lemma_mod_bound(r_final_nat as int, pn as int);
            };

            // Convert ct_eq byte-level results to canonical nat equality
            assert(choice_is_true(correct_sign_sqrt) == (check_nat == u_nat)) by {
                lemma_ct_eq_iff_canonical_nat(&check, u);
            };
            assert(choice_is_true(flipped_sign_sqrt) == (check_nat == fe51_as_canonical_nat(
                &u_neg,
            ))) by {
                lemma_ct_eq_iff_canonical_nat(&check, &u_neg);
            };
            assert(choice_is_true(flipped_sign_sqrt_i) == (check_nat == fe51_as_canonical_nat(
                &u_neg_i,
            ))) by {
                lemma_ct_eq_iff_canonical_nat(&check, &u_neg_i);
            };

            let correct_sign = choice_is_true(correct_sign_sqrt);
            let flipped_sign = choice_is_true(flipped_sign_sqrt);
            let flipped_sign_i = choice_is_true(flipped_sign_sqrt_i);
            let was_sq = choice_is_true(was_nonzero_square);

            assert(correct_sign == (check_nat == u_nat));
            assert(flipped_sign == (check_nat == fe51_as_canonical_nat(&u_neg)));
            assert(flipped_sign == (check_nat == field_neg(u_nat)));
            assert(flipped_sign_i == (check_nat == fe51_as_canonical_nat(&u_neg_i)));
            assert(flipped_sign_i == (check_nat == field_mul(field_neg(u_nat), sqrt_m1())));

            // Establish r_assigned_nat from conditional_assign
            assert((flipped_sign || flipped_sign_i) ==> r_assigned_nat == field_mul(
                sqrt_m1(),
                r_orig_nat,
            ));
            assert(!(flipped_sign || flipped_sign_i) ==> r_assigned_nat == r_orig_nat);

            // =================================================================
            // Block 3: Fourth root of unity pattern (when u != 0 && v != 0)
            // =================================================================
            if v_nat != 0 && u_nat != 0 {
                lemma_check_fourth_root_pattern(u_nat, v_nat, check_nat, r_orig_nat);
            }
            // =================================================================
            // Block 4: Zero propagation
            // =================================================================

            lemma_sqrt_ratio_zero_propagation(u_nat, v_nat, r_orig_nat, check_nat);

            // =================================================================
            // Block 5: Correctness + negation transfer
            // =================================================================
            lemma_sqrt_ratio_correctness(
                u_nat,
                v_nat,
                check_nat,
                r_orig_nat,
                r_assigned_nat,
                correct_sign,
                flipped_sign,
                flipped_sign_i,
                was_sq,
            );

            // Transfer postcondition 1: u == 0 ==> was_sq && r_final == 0
            if u_nat == 0 {
                assert(was_sq);
                assert(r_assigned_nat == 0);
                assert(r_final_nat == 0) by {
                    lemma_small_mod(0nat, pn);
                    lemma_mod_self_0(pn as int);
                };
            }
            // Transfer postcondition 2: v == 0 && u != 0 ==> !was_sq && r_final == 0

            if v_nat == 0 && u_nat != 0 {
                assert(!was_sq);
                assert(r_assigned_nat == 0);
                assert(r_final_nat == 0) by {
                    lemma_small_mod(0nat, pn);
                    lemma_mod_self_0(pn as int);
                };
            }
            // Transfer through negation: field_square(field_neg(r)) == field_square(r)

            if r_final_nat != r_assigned_nat {
                assert(r_final_nat == field_neg(r_assigned_nat));
                assert(field_canonical(r_final_nat * r_final_nat * v_nat) == field_canonical(
                    r_assigned_nat * r_assigned_nat * v_nat,
                )) by {
                    lemma_small_mod(r_assigned_nat, pn);
                    lemma_neg_square_eq(r_assigned_nat);
                    lemma_field_mul_square_canonical(r_final_nat, v_nat);
                    lemma_field_mul_square_canonical(r_assigned_nat, v_nat);
                };
                if r_assigned_nat == 0 {
                    assert(r_final_nat == 0) by {
                        lemma_small_mod(0nat, pn);
                        lemma_mod_self_0(pn as int);
                    };
                }
            }
            // Transfer postcondition 3: was_sq && v != 0 ==> is_sqrt_ratio(u, v, r_final)

            if was_sq && v_nat != 0 {
                assert(is_sqrt_ratio(u_nat, v_nat, r_assigned_nat));
            }
            // Transfer postcondition 4: !was_sq && v != 0 && u != 0 ==> is_sqrt_ratio_times_i

            if !was_sq && v_nat != 0 && u_nat != 0 {
                assert(is_sqrt_ratio_times_i(u_nat, v_nat, r_assigned_nat));
            }
        }

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

            (fe51_as_canonical_nat(self) == 0) ==> (!choice_is_true(result.0)
                && fe51_as_canonical_nat(&result.1) == 0),
            // When successful and self ≠ 0: r² * self ≡ 1 (mod p)
            (choice_is_true(result.0)) ==> fe51_is_sqrt_ratio(&FieldElement::ONE, self, &result.1),
            // When unsuccessful and self ≠ 0: r² * self ≡ i (mod p) [nonsquare case]
            (!choice_is_true(result.0) && fe51_as_canonical_nat(self) != 0)
                ==> fe51_is_sqrt_ratio_times_i(&FieldElement::ONE, self, &result.1),
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
