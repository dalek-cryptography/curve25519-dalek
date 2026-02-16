// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
//! Scalar multiplication on the Montgomery form of Curve25519.
//!
//! To avoid notational confusion with the Edwards code, we use
//! variables \\( u, v \\) for the Montgomery curve, so that “Montgomery
//! \\(u\\)” here corresponds to “Montgomery \\(x\\)” elsewhere.
//!
//! Montgomery arithmetic works not on the curve itself, but on the
//! \\(u\\)-line, which discards sign information and unifies the curve
//! and its quadratic twist.  See [_Montgomery curves and their
//! arithmetic_][costello-smith] by Costello and Smith for more details.
//!
//! The `MontgomeryPoint` struct contains the affine \\(u\\)-coordinate
//! \\(u\_0(P)\\) of a point \\(P\\) on either the curve or the twist.
//! Here the map \\(u\_0 : \mathcal M \rightarrow \mathbb F\_p \\) is
//! defined by \\(u\_0((u,v)) = u\\); \\(u\_0(\mathcal O) = 0\\).  See
//! section 5.4 of Costello-Smith for more details.
//!
//! # Scalar Multiplication
//!
//! Scalar multiplication on `MontgomeryPoint`s is provided by the `*`
//! operator, which implements the Montgomery ladder.
//!
//! # Edwards Conversion
//!
//! The \\(2\\)-to-\\(1\\) map from the Edwards model to the Montgomery
//! \\(u\\)-line is provided by `EdwardsPoint::to_montgomery()`.
//!
//! To lift a `MontgomeryPoint` to an `EdwardsPoint`, use
//! `MontgomeryPoint::to_edwards()`, which takes a sign parameter.
//! This function rejects `MontgomeryPoints` which correspond to points
//! on the twist.
//!
//! [costello-smith]: https://eprint.iacr.org/2017/212.pdf
// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]

use core::{
    hash::{Hash, Hasher},
    ops::{Mul, MulAssign},
};

use crate::constants::{APLUS2_OVER_FOUR, MONTGOMERY_A, MONTGOMERY_A_NEG};
#[cfg(feature = "zeroize")]
use crate::core_assumes::zeroize_bool;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::core_assumes::*;
use crate::edwards::{CompressedEdwardsY, EdwardsPoint};
use crate::field::FieldElement;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::bits_as_nat_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
use crate::scalar::{clamp_integer, Scalar};
#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[allow(unused_imports)]
use crate::specs::montgomery_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar52_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;

#[allow(unused_imports)]
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::as_bytes_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::constants_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::from_bytes_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::sqrt_ratio_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::montgomery_curve_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::spec_clamp_integer;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::calc;
#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::lemmas::field_lemmas::constants_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::montgomery_lemmas::*;

use crate::traits::Identity;

#[cfg(verus_keep_ghost)]
use crate::backend::serial::u64::subtle_assumes::choice_is_true;
use crate::backend::serial::u64::subtle_assumes::{
    choice_into, choice_not, conditional_negate_field_element, conditional_select_field_element,
    conditional_swap_montgomery_projective, ct_eq_bytes32, select_u8,
};

use subtle::Choice;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;
#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

verus! {

/// Holds the \\(u\\)-coordinate of a point on the Montgomery form of
/// Curve25519 or its twist.
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MontgomeryPoint(pub [u8; 32]);

/* ORIGINAL CODE: #[derive(Default)] on MontgomeryPoint — expanded to add Verus
   postconditions proving all bytes are zero and spec_montgomery(result) == 0. */

impl Default for MontgomeryPoint {
    fn default() -> (result: MontgomeryPoint)
        ensures
            forall|i: int| 0 <= i < 32 ==> #[trigger] result.0[i] == 0u8,
            spec_montgomery(result) == 0,
    {
        let result = MontgomeryPoint([0u8;32]);
        proof {
            assert forall|i: int| 0 <= i < 32 implies #[trigger] result.0[i] == 0u8 by {}
            assert(spec_montgomery(result) == 0) by {
                lemma_zero_limbs_is_zero(result);
            }
        }
        result
    }
}

/// Equality of `MontgomeryPoint`s is defined mod p.
impl ConstantTimeEq for MontgomeryPoint {
    fn ct_eq(&self, other: &MontgomeryPoint) -> (result: Choice)
        ensures
    // Two MontgomeryPoints are equal if their u-coordinates are equal mod p

            choice_is_true(result) == (field_element_from_bytes(&self.0)
                == field_element_from_bytes(&other.0)),
    {
        let self_fe = FieldElement::from_bytes(&self.0);
        let other_fe = FieldElement::from_bytes(&other.0);

        let result = self_fe.ct_eq(&other_fe);

        proof {
            // FieldElement::ct_eq compares canonical encodings, so it agrees with equality
            // of the corresponding field elements (mod p).
            let bytes_eq = spec_fe51_as_bytes(&self_fe) == spec_fe51_as_bytes(&other_fe);
            let field_eq = field_element_from_bytes(&self.0) == field_element_from_bytes(&other.0);

            assert(choice_is_true(result) == bytes_eq);

            // from_bytes ensures: u64_5_as_nat(fe.limbs) == u8_32_as_nat(bytes) % pow2(255)
            // Unfolding open spec fns gives: fe51_as_canonical_nat == field_element_from_bytes
            assert(fe51_as_canonical_nat(&self_fe) == field_element_from_bytes(&self.0));
            assert(fe51_as_canonical_nat(&other_fe) == field_element_from_bytes(&other.0));

            // Canonical bytes are injective for canonical field values.
            assert(bytes_eq ==> field_eq) by {
                if bytes_eq {
                    lemma_fe51_to_bytes_equal_implies_field_element_equal(&self_fe, &other_fe);
                }
            }
            assert(field_eq ==> bytes_eq) by {
                if field_eq {
                    lemma_field_element_equal_implies_fe51_to_bytes_equal(&self_fe, &other_fe);
                }
            }

            assert(bytes_eq == field_eq);
            assert(choice_is_true(result) == field_eq);
        }

        result
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::cmp::PartialEqSpecImpl for MontgomeryPoint {
    open spec fn obeys_eq_spec() -> bool {
        true  // Equality is based on constant-time comparison that obeys eq_spec

    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        // Two MontgomeryPoints are equal if their u-coordinates are equal mod p
        field_element_from_bytes(&self.0) == field_element_from_bytes(&other.0)
    }
}

impl PartialEq for MontgomeryPoint {
    // VERIFICATION NOTE: PartialEqSpecImpl trait provides the external specification
    fn eq(&self, other: &MontgomeryPoint) -> (result: bool)
        ensures
            result == (field_element_from_bytes(&self.0) == field_element_from_bytes(&other.0)),
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
            assert(choice_is_true(choice) == (field_element_from_bytes(&self.0)
                == field_element_from_bytes(&other.0)));
            assert(result == choice_is_true(choice));
        }

        result
    }
}

impl Eq for MontgomeryPoint {

}

// Equal MontgomeryPoints must hash to the same value. So we have to get them into a canonical
// encoding first
impl Hash for MontgomeryPoint {
    fn hash<H: Hasher>(&self, state: &mut H)
        ensures/*  VERIFICATION NOTE:
             (1) The postcondition is expressed using the abstract `spec_state_after_hash*` model for
                 `core::hash::Hash::hash` on fixed-size arrays (see `core_assumes.rs`).
            (2) `spec_state_after_hash_montgomery` hashes the canonical encoding
                 `spec_fe51_as_bytes(spec_fe51_from_bytes(point.0))`. */

            *state == spec_state_after_hash_montgomery(*old(state), self),
    {
        // Do a round trip through a `FieldElement`. `as_bytes` is guaranteed to give a canonical
        // 32-byte encoding
        /* ORIGINAL CODE: let canonical_bytes = FieldElement::from_bytes(&self.0).as_bytes();
           Split to keep `fe` available for proof blocks. */
        let fe = FieldElement::from_bytes(&self.0);
        let canonical_bytes = fe.as_bytes();

        /* GHOST: track the initial state for reasoning about state transformation */
        let ghost initial_state = *state;

        // Hash the canonical bytes
        canonical_bytes.hash(state);

        proof {
            // Relate the spec-side canonical bytes to the exec-side `canonical_bytes`.
            let canonical_seq = spec_fe51_as_bytes(&spec_fe51_from_bytes(&self.0));
            let canonical_arr = seq_to_array_32(canonical_seq);

            assert(initial_state == *old(state));

            // Step 1: `canonical_bytes` agrees with `spec_fe51_as_bytes(&fe)`.
            assert(seq_from32(&canonical_bytes) == spec_fe51_as_bytes(&fe)) by {
                lemma_as_bytes_equals_spec_fe51_to_bytes(&fe, &canonical_bytes);
            }

            // Step 2: `spec_fe51_from_bytes` has the same canonical value as `fe`.
            let fe_spec = spec_fe51_from_bytes(&self.0);
            lemma_from_u8_32_as_nat(&self.0);
            lemma_as_nat_32_mod_255(&self.0);
            // Both fe and fe_spec have the same limb value from the same bytes,
            // so unfolding open spec fns gives equal canonical nats.
            assert(fe51_as_canonical_nat(&fe) == fe51_as_canonical_nat(&fe_spec));
            assert(spec_fe51_as_bytes(&fe) == spec_fe51_as_bytes(&fe_spec)) by {
                lemma_field_element_equal_implies_fe51_to_bytes_equal(&fe, &fe_spec);
            }

            // Step 3: Therefore, the canonical sequence equals the exec-view sequence.
            assert(spec_fe51_as_bytes(&fe) == canonical_seq);
            assert(seq_from32(&canonical_bytes) == canonical_seq);

            // Step 4: Convert the spec canonical sequence back to an array and match arrays.
            assert(canonical_seq.len() == 32);
            assert(canonical_seq =~= seq_from32(&canonical_arr));
            assert(seq_from32(&canonical_bytes) == seq_from32(&canonical_arr));
            assert(canonical_bytes == canonical_arr) by {
                lemma_seq_eq_implies_array_eq(&canonical_bytes, &canonical_arr);
            }

            // Step 5: Use the abstract hash model.
            assert(*state == spec_state_after_hash(initial_state, &canonical_bytes));
            assert(*state == spec_state_after_hash(initial_state, &canonical_arr));
            assert(*state == spec_state_after_hash_montgomery(initial_state, self));
        }
    }
}

impl Identity for MontgomeryPoint {
    /// Return the group identity element, which has order 4.
    fn identity() -> (result: MontgomeryPoint)
        ensures
    // The identity point has u-coordinate = 0

            spec_montgomery(result) == 0,
    {
        let result = MontgomeryPoint([0u8;32]);
        proof {
            assert forall|i: int| 0 <= i < 32 implies #[trigger] result.0[i] == 0u8 by {}
            assert(spec_montgomery(result) == 0) by {
                lemma_zero_limbs_is_zero(result);
            }
        }
        result
    }
}

impl crate::traits::IsIdentitySpecImpl for MontgomeryPoint {
    /// For MontgomeryPoint, is_identity returns true iff u-coordinate is 0
    open spec fn is_identity_spec(&self) -> bool {
        spec_montgomery(*self) == 0
    }
}

#[cfg(feature = "zeroize")]
impl Zeroize for MontgomeryPoint {
    fn zeroize(&mut self)
        ensures
    // All bytes are zero

            forall|i: int| 0 <= i < 32 ==> #[trigger] self.0[i] == 0u8,
            // The u-coordinate is 0 (identity point)
            spec_montgomery(*self) == 0,
    {
        /* ORIGINAL CODE: self.0.zeroize(); */
        crate::core_assumes::zeroize_bytes32(&mut self.0);
        proof {
            assert(spec_montgomery(*self) == 0) by {
                lemma_zero_limbs_is_zero(*self);
            }
        }
    }
}

impl MontgomeryPoint {
    /// Fixed-base scalar multiplication (i.e. multiplication by the base point).
    pub fn mul_base(scalar: &Scalar) -> (result: Self)
        requires
            scalar.bytes[31] <= 127,
        ensures
            is_valid_montgomery_point(result),
            // Functional correctness: result.u = [scalar] * basepoint (u-coordinate)
            // Use scalar_as_nat (not spec_scalar) to match implementation behavior
            spec_montgomery(result) == montgomery_scalar_mul_u(
                spec_x25519_basepoint_u(),
                scalar_as_nat(scalar),
            ),
    {
        // ORIGINAL CODE: EdwardsPoint::mul_base(scalar).to_montgomery()
        let temp = EdwardsPoint::mul_base(scalar);
        proof {
            assert((1u64 << 52) < (1u64 << 54)) by (bit_vector);
            assert(fe51_limbs_bounded(&temp.X, 54));
        }
        let result = temp.to_montgomery();
        proof {
            let B = spec_ed25519_basepoint();
            let n = scalar_as_nat(scalar);

            assert(spec_montgomery(result) == montgomery_u_from_edwards_y(
                edwards_scalar_mul(B, n).1,
            ));

            assert(math_on_edwards_curve(B.0, B.1)) by {
                axiom_basepoint_on_curve();
            }
            assert(math_on_edwards_curve(edwards_scalar_mul(B, n).0, edwards_scalar_mul(B, n).1))
                by {
                axiom_edwards_to_montgomery_commutes_with_scalar_mul(B.0, B.1, n);
            }
            assert(montgomery_u_from_edwards_y(edwards_scalar_mul(B, n).1)
                == montgomery_scalar_mul_u(montgomery_u_from_edwards_y(B.1), n)) by {
                axiom_edwards_to_montgomery_commutes_with_scalar_mul(B.0, B.1, n);
            }
            assert(montgomery_u_from_edwards_y(B.1) == spec_x25519_basepoint_u()) by {
                axiom_edwards_basepoint_maps_to_montgomery_basepoint();
            }
            assert(is_valid_u_coordinate(montgomery_u_from_edwards_y(edwards_scalar_mul(B, n).1)))
                by {
                axiom_edwards_to_montgomery_preserves_validity(
                    edwards_scalar_mul(B, n).0,
                    edwards_scalar_mul(B, n).1,
                );
            }
        }
        result
    }

    /// Multiply this point by `clamp_integer(bytes)`. For a description of clamping, see
    /// [`clamp_integer`].
    pub fn mul_clamped(self, bytes: [u8; 32]) -> (result: Self)
        requires
            is_valid_montgomery_point(self),
        ensures/* VERIFICATION NOTE: Result represents [n]self where n is the clamped integer value
      The corresponding scalar is not reduced modulo the group order. */

            ({
                let P = canonical_montgomery_lift(spec_montgomery(self));
                let clamped_bytes = spec_clamp_integer(bytes);
                let n = u8_32_as_nat(&clamped_bytes);
                let R = montgomery_scalar_mul(P, n);
                spec_montgomery(result) == spec_u_coordinate(R)
            }),
    {
        // We have to construct a Scalar that is not reduced mod l, which breaks scalar invariant
        // #2. But #2 is not necessary for correctness of variable-base multiplication. All that
        // needs to hold is invariant #1, i.e., the scalar is less than 2^255. This is guaranteed
        // by clamping.
        // Further, we don't do any reduction or arithmetic with this clamped value, so there's no
        // issues arising from the fact that the curve point is not necessarily in the prime-order
        // subgroup.
        /* ORIGINAL CODE: let s = Scalar { bytes: clamp_integer(bytes) }; s * self
           Split to keep `clamped` for proof blocks; uses &self * &s for Verus postcondition. */
        let clamped = clamp_integer(bytes);
        let s = Scalar { bytes: clamped };
        let result = &self * &s;
        proof {
            // Prove the postcondition using:
            // - `clamp_integer` ensures `clamped == spec_clamp_integer(bytes)`
            // - `&MontgomeryPoint * &Scalar` ensures multiplication by `scalar_as_nat(&s)`
            assert(clamped == spec_clamp_integer(bytes));
            assert(scalar_as_nat(&s) == u8_32_as_nat(&spec_clamp_integer(bytes)));
            assert({
                let P = canonical_montgomery_lift(spec_montgomery(self));
                let clamped_bytes = spec_clamp_integer(bytes);
                let n = u8_32_as_nat(&clamped_bytes);
                let R = montgomery_scalar_mul(P, n);
                spec_montgomery(result) == spec_u_coordinate(R)
            });
        }
        result
    }

    /// Multiply the basepoint by `clamp_integer(bytes)`. For a description of clamping, see
    /// [`clamp_integer`].
    pub fn mul_base_clamped(bytes: [u8; 32]) -> (result: Self)
        ensures
            is_valid_montgomery_point(result),
            // Functional correctness: result.u = [clamp(bytes)] * basepoint (u-coordinate)
            // Use scalar_as_nat (not spec_scalar) because clamped values are in [2^254, 2^255)
            // which exceeds group_order ℓ ≈ 2^252, so spec_scalar would incorrectly reduce
            spec_montgomery(result) == montgomery_scalar_mul_u(
                spec_x25519_basepoint_u(),
                scalar_as_nat(&Scalar { bytes: spec_clamp_integer(bytes) }),
            ),
    {
        // See reasoning in Self::mul_clamped why it is OK to make an unreduced Scalar here. We
        // note that fixed-base multiplication is also defined for all values of `bytes` less than
        // 2^255.
        let s = Scalar { bytes: clamp_integer(bytes) };
        // clamp_integer ensures s.bytes[31] <= 127, satisfying mul_base's requires
        let result = Self::mul_base(&s);
        // Postconditions follow from mul_base since s.bytes == spec_clamp_integer(bytes)
        result
    }

    /// Given `self` \\( = u\_0(P) \\), and a big-endian bit representation of an integer
    /// \\(n\\), return \\( u\_0(\[n\]P) \\). This is constant time in the length of `bits`.
    ///
    /// **NOTE:** You probably do not want to use this function. Almost every protocol built on
    /// Curve25519 uses _clamped multiplication_, explained
    /// [here](https://neilmadden.blog/2020/05/28/whats-the-curve25519-clamping-all-about/).
    /// When in doubt, use [`Self::mul_clamped`].
    /* VERIFICATION NOTE: original code; followed by refactored version without using Iterator - unsupported by Verus)*/
    /* <ORIGINAL CODE>
    pub fn mul_bits_be(&self, bits: impl Iterator<Item = bool>) -> MontgomeryPoint {
        // Algorithm 8 of Costello-Smith 2017
        let affine_u = FieldElement::from_bytes(&self.0);
        let mut x0 = ProjectivePoint::identity();
        let mut x1 = ProjectivePoint { U: affine_u, W: FieldElement::ONE };

        // Go through the bits from most to least significant, using a sliding window of 2
        let mut prev_bit = false;
        for cur_bit in bits {
            let choice: u8 = (prev_bit ^ cur_bit) as u8;

            debug_assert!(choice == 0 || choice == 1);

            ProjectivePoint::conditional_swap(&mut x0, &mut x1, choice.into());
            differential_add_and_double(&mut x0, &mut x1, &affine_u);

            prev_bit = cur_bit;
        }
        // The final value of prev_bit above is scalar.bits()[0], i.e., the LSB of scalar
        ProjectivePoint::conditional_swap(&mut x0, &mut x1, Choice::from(prev_bit as u8));
        // Don't leave the bit in the stack
        #[cfg(feature = "zeroize")]
        prev_bit.zeroize();

        x0.as_affine()
    }
    </ORIGINAL CODE>
    */
    /// Version of mul_bits_be that takes a slice of bits instead of an iterator.
    /// This version uses a while loop instead of for-loop to be Verus-compatible.
    ///
    /// Given `self` \\( = u\_0(P) \\), and a big-endian bit representation of an integer
    /// \\(n\\) as a slice, return \\( u\_0(\[n\]P) \\).
    ///
    // VERIFICATION NOTE: refactored mul_bits_be code
    #[verifier::rlimit(20)]
    pub fn mul_bits_be(&self, bits: &[bool]) -> (result: MontgomeryPoint)
        requires
            bits.len() <= 255,
            is_valid_montgomery_point(*self),
        ensures
            ({
                // Let P be the canonical affine lift of input u-coordinate
                let P = canonical_montgomery_lift(spec_montgomery(*self));
                let n = bits_be_as_nat(bits, bits.len() as int);
                let R = montgomery_scalar_mul(P, n);

                // result encodes u([n]P)
                spec_montgomery(result) == spec_u_coordinate(R)
            }),
    {
        // Algorithm 8 of Costello-Smith 2017
        let affine_u = FieldElement::from_bytes(&self.0);
        let mut x0 = ProjectivePoint::identity();
        let mut x1 = ProjectivePoint { U: affine_u, W: FieldElement::ONE };

        // Go through the bits from most to least significant, using a sliding window of 2
        let mut prev_bit = false;
        let mut i: usize = 0;
        proof {
            // Establish the loop invariant at i = 0.
            // VERIFICATION NOTE: refactoring lemma calls into `assert...by` style breaks rlimit.
            let u0 = spec_montgomery(*self);
            let P = canonical_montgomery_lift(u0);
            assert(is_valid_u_coordinate(u0));

            // Connect affine_u to u0 (both are the canonical field element decoded from self.0).
            assert(fe51_as_canonical_nat(&affine_u) == u0) by {
                let bytes_nat = u8_32_as_nat(&self.0) % pow2(255);
                assert(fe51_as_nat(&affine_u) == bytes_nat);
                assert(fe51_as_canonical_nat(&affine_u) == bytes_nat % p());
                assert(u0 == field_element_from_bytes(&self.0));
                assert(u0 == bytes_nat % p());
            }

            // Bounds for initial points
            // x0 = (1:0) by ProjectivePoint::identity().
            assert(fe51_limbs_bounded(&x0.U, 51));
            assert(fe51_limbs_bounded(&x0.W, 51));
            lemma_fe51_limbs_bounded_weaken(&x0.U, 51, 52);
            lemma_fe51_limbs_bounded_weaken(&x0.W, 51, 52);
            assert(fe51_limbs_bounded(&x0.U, 52));
            assert(fe51_limbs_bounded(&x0.W, 52));
            assert(fe51_limbs_bounded(&affine_u, 51));

            lemma_one_limbs_bounded_51();
            assert(fe51_limbs_bounded(&x1.W, 51));
            lemma_fe51_limbs_bounded_weaken(&x1.W, 51, 52);
            lemma_fe51_limbs_bounded_weaken(&affine_u, 51, 52);
            assert(fe51_limbs_bounded(&x1.U, 52));
            assert(fe51_limbs_bounded(&x1.W, 52));
            assert(fe51_limbs_bounded(&affine_u, 51));
            assert(is_valid_u_coordinate(fe51_as_canonical_nat(&affine_u)));

            // Scalar invariant at i = 0: k = 0
            assert(bits_be_as_nat(bits, 0) == 0);
            assert(spec_projective_u_coordinate(x0) == 0);
            assert(spec_u_coordinate(montgomery_scalar_mul(P, 0)) == 0);
            assert(spec_projective_u_coordinate(x1) == u0) by {
                // x1 = (affine_u : 1), so its u-coordinate is affine_u.
                lemma_one_field_element_value();
                lemma_field_inv_one();
                assert(fe51_as_canonical_nat(&x1.W) == 1);
                assert(spec_projective_u_coordinate(x1) == field_mul(
                    fe51_as_canonical_nat(&x1.U),
                    field_inv(1),
                ));
                assert(field_inv(1) == 1);
                assert(spec_projective_u_coordinate(x1) == field_mul(
                    fe51_as_canonical_nat(&x1.U),
                    1,
                ));
                lemma_field_mul_one_right(fe51_as_canonical_nat(&x1.U));
                assert(spec_projective_u_coordinate(x1) == fe51_as_canonical_nat(&x1.U) % p());
                assert(fe51_as_canonical_nat(&x1.U) % p() == fe51_as_canonical_nat(&x1.U)) by {
                    let t = fe51_as_nat(&x1.U) % p();
                    assert(fe51_as_canonical_nat(&x1.U) == t);
                    assert(fe51_as_canonical_nat(&x1.U) % p() == t % p());
                    p_gt_2();
                    lemma_mod_division_less_than_divisor(fe51_as_nat(&x1.U) as int, p() as int);
                    assert(t < p());
                    lemma_small_mod(t, p());
                    assert(t % p() == t);
                }
                // x1.U was initialized from affine_u
                assert(x1.U == affine_u);
                assert(spec_projective_u_coordinate(x1) == fe51_as_canonical_nat(&affine_u));
                assert(fe51_as_canonical_nat(&affine_u) == u0);
            }
            assert(spec_u_coordinate(montgomery_scalar_mul(P, 1)) == u0) by {
                // montgomery_scalar_mul(P, 1) = P + [0]P = P
                assert(montgomery_scalar_mul(P, 0) == MontgomeryAffine::Infinity);
                assert(montgomery_scalar_mul(P, 1) == montgomery_add(
                    P,
                    montgomery_scalar_mul(P, 0),
                ));
                assert(montgomery_scalar_mul(P, 1) == montgomery_add(
                    P,
                    MontgomeryAffine::Infinity,
                ));
                assert(montgomery_add(P, MontgomeryAffine::Infinity) == P);
                assert(montgomery_scalar_mul(P, 1) == P);
                // P is the canonical lift of u0, so its u-coordinate is u0
                assert(spec_u_coordinate(P) == u0) by {
                    // canonical_montgomery_lift(u0) returns (u0 % p, v), and u0 is already reduced mod p
                    assert(u0 == u0 % p()) by {
                        assert(u0 == field_element_from_bytes(&self.0));
                        let t = u8_32_as_nat(&self.0) % pow2(255);
                        assert(u0 == t % p());
                        assert(u0 % p() == (t % p()) % p());
                        p_gt_2();
                        lemma_mod_division_less_than_divisor(t as int, p() as int);
                        assert((t % p()) < p());
                        lemma_small_mod(t % p(), p());
                        assert((t % p()) % p() == t % p());
                    }
                    assert(spec_u_coordinate(canonical_montgomery_lift(u0)) == u0);
                }
            }

            // Representation invariants needed to instantiate `differential_add_and_double` spec.
            if u0 != 0 {
                // x0 = identity = (1:0) represents ∞ = [0]P.
                assert(projective_represents_montgomery_or_infinity(
                    x0,
                    montgomery_scalar_mul(P, 0),
                ));

                // x1 = (u0:1) represents P = [1]P.
                assert(projective_represents_montgomery_or_infinity(
                    x1,
                    montgomery_scalar_mul(P, 1),
                )) by {
                    assert(montgomery_scalar_mul(P, 1) == P);
                    // Finite points require W != 0 and U = u * W.
                    assert(fe51_as_canonical_nat(&x1.W) == 1) by {
                        lemma_one_field_element_value();
                    }
                    assert(fe51_as_canonical_nat(&x1.W) != 0);
                    assert(fe51_as_canonical_nat(&x1.U) == u0) by {
                        assert(x1.U == affine_u);
                        assert(fe51_as_canonical_nat(&affine_u) == u0);
                    }
                    assert(spec_u_coordinate(P) == u0);
                    assert(fe51_as_canonical_nat(&x1.U) == field_mul(
                        spec_u_coordinate(P),
                        fe51_as_canonical_nat(&x1.W),
                    )) by {
                        lemma_field_mul_one_right(spec_u_coordinate(P));
                    }
                }

                // Establish the ladder invariant at i = 0 (k = 0, prev_bit = false).
                reveal(montgomery_ladder_invariant);
                assert(montgomery_ladder_invariant(x0, x1, P, 0, false));
            }
        }
        // VERIFICATION NOTE: refactoring lemma calls into `assert...by` style breaks rlimit.
        while i < bits.len()
            invariant
                i <= bits.len(),
                // Limb bounds needed for `differential_add_and_double` and `as_affine`
                fe51_limbs_bounded(&x0.U, 52),
                fe51_limbs_bounded(&x0.W, 52),
                fe51_limbs_bounded(&x1.U, 52),
                fe51_limbs_bounded(&x1.W, 52),
                fe51_limbs_bounded(&affine_u, 51),
                // Basepoint decoding/validity (needed for canonical lift reasoning)
                fe51_as_canonical_nat(&affine_u) == spec_montgomery(*self),
                is_valid_u_coordinate(spec_montgomery(*self)),
                is_valid_u_coordinate(fe51_as_canonical_nat(&affine_u)),
                // Scalar-multiplication relationship (Montgomery ladder invariant)
                ({
                    let u0 = spec_montgomery(*self);
                    if u0 == 0 {
                        // Degenerate case: u0=0 is the (0,0) 2-torsion point; all multiples have u=0.
                        &&& spec_projective_u_coordinate(x0) == 0
                        &&& spec_projective_u_coordinate(x1) == 0
                    } else {
                        let P = canonical_montgomery_lift(u0);
                        let k = bits_be_as_nat(bits, i as int);
                        montgomery_ladder_invariant(x0, x1, P, k, prev_bit)
                    }
                }),
            decreases bits.len() - i,
        {
            let cur_bit = bits[i];
            let choice: u8 = (prev_bit ^ cur_bit) as u8;
            // VERIFICATION: extracted from inline `choice.into()` to name the Choice for proof
            let swap_choice = Choice::from(choice);

            #[cfg(not(verus_keep_ghost))]
            debug_assert!(choice == 0 || choice == 1);

            let ghost x0_before_swap = x0;
            let ghost x1_before_swap = x1;
            conditional_swap_montgomery_projective(&mut x0, &mut x1, swap_choice);
            proof {
                let u0 = spec_montgomery(*self);
                let k = bits_be_as_nat(bits, i as int);

                // Connect affine_u to u0
                assert(fe51_as_canonical_nat(&affine_u) == u0);

                if u0 == 0 {
                    // In the degenerate u0=0 case, the loop invariant only tracks that both
                    // projective u-coordinates are 0, and conditional_swap preserves this.
                    assert(spec_projective_u_coordinate(x0_before_swap) == 0);
                    assert(spec_projective_u_coordinate(x1_before_swap) == 0);
                    assert(spec_projective_u_coordinate(x0) == 0);
                    assert(spec_projective_u_coordinate(x1) == 0);
                } else {
                    let P = canonical_montgomery_lift(u0);

                    // Representation facts from the loop invariant (before the swap).
                    assert(montgomery_ladder_invariant(
                        x0_before_swap,
                        x1_before_swap,
                        P,
                        k,
                        prev_bit,
                    ));

                    // Determine whether the swap occurred: swap iff (prev_bit ^ cur_bit)
                    let swapped_now = prev_bit ^ cur_bit;
                    if swapped_now {
                        assert(choice == 1u8);
                        assert(choice_is_true(swap_choice));
                        // From conditional_swap spec: x0 = old(x1), x1 = old(x0)
                        assert(x0.U == x1_before_swap.U);
                        assert(x0.W == x1_before_swap.W);
                        assert(x1.U == x0_before_swap.U);
                        assert(x1.W == x0_before_swap.W);
                    } else {
                        assert(choice == 0u8);
                        assert(!choice_is_true(swap_choice));
                        // No swap: x0,x1 unchanged
                        assert(x0.U == x0_before_swap.U);
                        assert(x0.W == x0_before_swap.W);
                        assert(x1.U == x1_before_swap.U);
                        assert(x1.W == x1_before_swap.W);
                    }

                    // After the swap, the invariant switches from prev_bit to cur_bit.
                    if swapped_now {
                        // swapped_now == (prev_bit ^ cur_bit) means cur_bit == !prev_bit
                        assert(cur_bit == !prev_bit) by {
                            assert(swapped_now == (prev_bit ^ cur_bit));
                        }
                        crate::lemmas::montgomery_lemmas::lemma_ladder_invariant_swap(
                            x0_before_swap,
                            x1_before_swap,
                            P,
                            k,
                            prev_bit,
                        );
                        assert(montgomery_ladder_invariant(
                            x1_before_swap,
                            x0_before_swap,
                            P,
                            k,
                            !prev_bit,
                        ));
                        // conditional_swap: x0 = old(x1), x1 = old(x0)
                        assert(x0 == x1_before_swap) by {
                            assert(x0.U == x1_before_swap.U);
                            assert(x0.W == x1_before_swap.W);
                        }
                        assert(x1 == x0_before_swap) by {
                            assert(x1.U == x0_before_swap.U);
                            assert(x1.W == x0_before_swap.W);
                        }
                        assert(montgomery_ladder_invariant(x0, x1, P, k, cur_bit));
                    } else {
                        // swapped_now == false means cur_bit == prev_bit, and no swap occurred.
                        assert(cur_bit == prev_bit) by {
                            assert(swapped_now == (prev_bit ^ cur_bit));
                        }
                        assert(x0 == x0_before_swap) by {
                            assert(x0.U == x0_before_swap.U);
                            assert(x0.W == x0_before_swap.W);
                        }
                        assert(x1 == x1_before_swap) by {
                            assert(x1.U == x1_before_swap.U);
                            assert(x1.W == x1_before_swap.W);
                        }
                        assert(montgomery_ladder_invariant(x0, x1, P, k, cur_bit));
                    }

                }

                // The call to `differential_add_and_double` below is justified by the limb-bound
                // invariants on x0/x1 and affine_u.
            }
            proof {
                // Prepare the antecedents needed to instantiate the postconditions of
                // `differential_add_and_double` (Cases 1 and 2 depend on the old(P)/old(Q) representations).
                let u0 = spec_montgomery(*self);
                if u0 != 0 {
                    let P = canonical_montgomery_lift(u0);
                    let k = bits_be_as_nat(bits, i as int);
                    // After the conditional swap, (x0, x1) satisfy ladder_invariant with `cur_bit`.
                    assert(montgomery_ladder_invariant(x0, x1, P, k, cur_bit));
                    reveal(montgomery_ladder_invariant);
                    if cur_bit {
                        assert(projective_represents_montgomery_or_infinity(
                            x0,
                            montgomery_scalar_mul(P, k + 1),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x1,
                            montgomery_scalar_mul(P, k),
                        ));
                    } else {
                        assert(projective_represents_montgomery_or_infinity(
                            x0,
                            montgomery_scalar_mul(P, k),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x1,
                            montgomery_scalar_mul(P, k + 1),
                        ));
                    }
                }
            }
            let ghost x0_before_dad = x0;
            let ghost x1_before_dad = x1;
            differential_add_and_double(&mut x0, &mut x1, &affine_u);

            prev_bit = cur_bit;
            i = i + 1;
            proof {
                // Re-establish the full loop invariant for the next iteration.
                let u0 = spec_montgomery(*self);
                let P = canonical_montgomery_lift(u0);
                let k = bits_be_as_nat(bits, (i - 1) as int);

                let base = canonical_montgomery_lift(fe51_as_canonical_nat(&affine_u));
                assert(base == P);

                if u0 == 0 {
                    // Use the degenerate-case postcondition of `differential_add_and_double`:
                    // if u(P-Q)=0 and both inputs have u=0, both outputs have u=0.
                    assert(fe51_as_canonical_nat(&affine_u) == 0);
                    assert(spec_projective_u_coordinate(x0_before_dad) == 0);
                    assert(spec_projective_u_coordinate(x1_before_dad) == 0);
                    assert(spec_projective_u_coordinate(x0) == 0);
                    assert(spec_projective_u_coordinate(x1) == 0);
                } else {
                    // Instantiate the ladder-step postcondition of `differential_add_and_double`.
                    assert(fe51_as_canonical_nat(&affine_u) != 0);

                    if cur_bit {
                        // Case 2: inputs were swapped: ([k+1]P, [k]P) -> ([2k+2]P, [2k+1]P)
                        // Use Case 2 postcondition of differential_add_and_double
                        assert(projective_represents_montgomery_or_infinity(
                            x0,
                            montgomery_scalar_mul(P, 2nat * k + 2nat),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x1,
                            montgomery_scalar_mul(P, 2nat * k + 1nat),
                        ));
                    } else {
                        // Case 1: inputs in order: ([k]P, [k+1]P) -> ([2k]P, [2k+1]P)
                        // Use Case 1 postcondition of differential_add_and_double
                        assert(projective_represents_montgomery_or_infinity(
                            x0,
                            montgomery_scalar_mul(P, 2nat * k),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x1,
                            montgomery_scalar_mul(P, 2nat * k + 1nat),
                        ));
                    }
                }

                // bits_be_as_nat update: k_next = 2*k + b
                let b = if cur_bit {
                    1nat
                } else {
                    0nat
                };
                assert(bits_be_as_nat(bits, i as int) == b + 2nat * k);
                // Re-establish ladder_invariant at the updated k (i has been incremented) and prev_bit.
                if u0 != 0 {
                    let k_next = bits_be_as_nat(bits, i as int);
                    // k_next == 2*k + b
                    assert(k_next == b + 2nat * k);
                    reveal(montgomery_ladder_invariant);
                    if prev_bit {
                        // x0 = [k_next+1]P and x1 = [k_next]P
                        assert(cur_bit);
                        assert(b == 1nat);
                        assert(k_next == 2nat * k + 1nat);
                        assert(k_next + 1 == 2nat * k + 2nat);
                        assert(projective_represents_montgomery_or_infinity(
                            x0,
                            montgomery_scalar_mul(P, 2nat * k + 2nat),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x1,
                            montgomery_scalar_mul(P, 2nat * k + 1nat),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x0,
                            montgomery_scalar_mul(P, k_next + 1),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x1,
                            montgomery_scalar_mul(P, k_next),
                        ));
                    } else {
                        // x0 = [k_next]P and x1 = [k_next+1]P
                        assert(!cur_bit);
                        assert(b == 0nat);
                        assert(k_next == 2nat * k);
                        assert(k_next + 1 == 2nat * k + 1nat);
                        assert(projective_represents_montgomery_or_infinity(
                            x0,
                            montgomery_scalar_mul(P, 2nat * k),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x1,
                            montgomery_scalar_mul(P, 2nat * k + 1nat),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x0,
                            montgomery_scalar_mul(P, k_next),
                        ));
                        assert(projective_represents_montgomery_or_infinity(
                            x1,
                            montgomery_scalar_mul(P, k_next + 1),
                        ));
                    }
                    assert(montgomery_ladder_invariant(x0, x1, P, k_next, prev_bit));
                }
            }
        }
        // The final value of prev_bit above is scalar.bits()[0], i.e., the LSB of scalar
        let ghost x0_before_final_swap = x0;
        let ghost x1_before_final_swap = x1;
        let ghost saved_prev_bit = prev_bit;  // save before zeroize for proof
        // VERIFICATION: rewritten from `Choice::from(prev_bit as u8)` because Verus
        // cannot reason about `bool as u8`; if-expression is equivalent
        let final_choice_u8: u8 = if prev_bit {
            1u8
        } else {
            0u8
        };
        let final_swap_choice = Choice::from(final_choice_u8);
        conditional_swap_montgomery_projective(&mut x0, &mut x1, final_swap_choice);
        // Don't leave the bit in the stack
        #[cfg(feature = "zeroize")]
        zeroize_bool(&mut prev_bit);

        proof {
            // After the final conditional swap, x0 encodes u([n]P) where n is the full bitstring.
            let u0 = spec_montgomery(*self);
            let P = canonical_montgomery_lift(u0);
            let n = bits_be_as_nat(bits, bits.len() as int);

            // Connect saved_prev_bit to final_swap_choice.
            // From Choice::from spec: (u == 1) == choice_is_true(Choice::from(u))
            // Note: use saved_prev_bit since prev_bit may have been zeroized
            assert(choice_is_true(final_swap_choice) == saved_prev_bit);

            if u0 == 0 {
                // In the u0=0 degenerate case, both sides are 0.
                assert(spec_projective_u_coordinate(x0) == 0);
                lemma_u_coordinate_scalar_mul_canonical_lift_zero(n);
                assert(spec_u_coordinate(montgomery_scalar_mul(P, n)) == 0);
                assert(spec_projective_u_coordinate(x0) == spec_u_coordinate(
                    montgomery_scalar_mul(P, n),
                ));
            } else {
                // The final swap ensures x0 holds [n]P regardless of saved_prev_bit.
                // From loop invariant, we have projective_represents_montgomery_or_infinity
                // for x0_before_final_swap or x1_before_final_swap (depending on saved_prev_bit).
                // Note: use saved_prev_bit since prev_bit may have been zeroized
                reveal(montgomery_ladder_invariant);
                if saved_prev_bit {
                    assert(x0.U == x1_before_final_swap.U);
                    assert(x0.W == x1_before_final_swap.W);
                    // x1_before_final_swap represents [n]P
                    assert(projective_represents_montgomery_or_infinity(
                        x1_before_final_swap,
                        montgomery_scalar_mul(P, n),
                    ));
                    assert(projective_represents_montgomery_or_infinity(
                        x1_before_final_swap,
                        montgomery_scalar_mul(P, n),
                    ));
                    // After swap, x0 has the same coordinates, so also represents [n]P
                    assert(projective_represents_montgomery_or_infinity(
                        x0,
                        montgomery_scalar_mul(P, n),
                    ));
                } else {
                    assert(x0.U == x0_before_final_swap.U);
                    assert(x0.W == x0_before_final_swap.W);
                    // x0_before_final_swap represents [n]P
                    assert(projective_represents_montgomery_or_infinity(
                        x0_before_final_swap,
                        montgomery_scalar_mul(P, n),
                    ));
                    assert(projective_represents_montgomery_or_infinity(
                        x0_before_final_swap,
                        montgomery_scalar_mul(P, n),
                    ));
                    // No swap, x0 still represents [n]P
                    assert(projective_represents_montgomery_or_infinity(
                        x0,
                        montgomery_scalar_mul(P, n),
                    ));
                }
                // Use lemma to get u-coordinate equality
                lemma_projective_represents_implies_u_coordinate(x0, montgomery_scalar_mul(P, n));
                // The lemma gives: spec_projective_u_coordinate(x0) == (spec_u_coordinate(...) % p())
                // For canonical points, u-coordinates are already < p, so % p() is identity.
                lemma_canonical_scalar_mul_u_coord_reduced(u0, n);
                let u_coord = spec_u_coordinate(montgomery_scalar_mul(P, n));
                assert(u_coord < p());
                assert(u_coord % p() == u_coord) by {
                    lemma_small_mod(u_coord, p());
                }
                assert(spec_projective_u_coordinate(x0) == spec_u_coordinate(
                    montgomery_scalar_mul(P, n),
                ));
            }
            // Bounds needed for as_affine
            assert(fe51_limbs_bounded(&x0.U, 52));
            assert(fe51_limbs_bounded(&x0.W, 52));
            lemma_fe51_limbs_bounded_weaken(&x0.U, 52, 54);
            lemma_fe51_limbs_bounded_weaken(&x0.W, 52, 54);
            assert(fe51_limbs_bounded(&x0.U, 54));
            assert(fe51_limbs_bounded(&x0.W, 54));
        }
        let result = x0.as_affine();
        proof {
            // Discharge the function postcondition.
            let u0 = spec_montgomery(*self);
            let P = canonical_montgomery_lift(u0);
            let n = bits_be_as_nat(bits, bits.len() as int);
            // as_affine returns the affine u-coordinate of x0
            assert(spec_montgomery(result) == spec_projective_u_coordinate(x0));
            // From loop invariant at exit and final conditional swap, x0 encodes u([n]P)
            assert(spec_projective_u_coordinate(x0) == spec_u_coordinate(
                montgomery_scalar_mul(P, n),
            ));
        }
        result
    }

    /// View this `MontgomeryPoint` as an array of bytes.
    pub const fn as_bytes(&self) -> (result: &[u8; 32])
        ensures
            result == &self.0,
    {
        &self.0
    }

    /// Convert this `MontgomeryPoint` to an array of bytes.
    pub const fn to_bytes(&self) -> (result: [u8; 32])
        ensures
            result == self.0,
    {
        self.0
    }

    /// Attempt to convert to an `EdwardsPoint`, using the supplied
    /// choice of sign for the `EdwardsPoint`.
    ///
    /// # Inputs
    ///
    /// * `sign`: a `u8` donating the desired sign of the resulting
    ///   `EdwardsPoint`.  `0` denotes positive and `1` negative.
    ///
    /// # Return
    ///
    /// * `Some(EdwardsPoint)` if `self` is the \\(u\\)-coordinate of a
    /// point on (the Montgomery form of) Curve25519;
    ///
    /// * `None` if `self` is the \\(u\\)-coordinate of a point on the
    /// twist of (the Montgomery form of) Curve25519;
    ///
    pub fn to_edwards(&self, sign: u8) -> (result: Option<EdwardsPoint>)
        ensures
            match result {
                Some(edwards) => montgomery_corresponds_to_edwards(*self, edwards)
                    && is_well_formed_edwards_point(edwards) && edwards_point_as_affine(edwards)
                    == spec_montgomery_to_edwards_affine(spec_montgomery(*self), sign),
                None => is_equal_to_minus_one(spec_montgomery(*self)),
            },
    {
        // To decompress the Montgomery u coordinate to an
        // `EdwardsPoint`, we apply the birational map to obtain the
        // Edwards y coordinate, then do Edwards decompression.
        //
        // The birational map is y = (u-1)/(u+1).
        //
        // The exceptional points are the zeros of the denominator,
        // i.e., u = -1.
        //
        // But when u = -1, v^2 = u*(u^2+486662*u+1) = 486660.
        //
        // Since this is nonsquare mod p, u = -1 corresponds to a point
        // on the twist, not the curve, so we can reject it early.
        let u = FieldElement::from_bytes(&self.0);

        if u == FieldElement::MINUS_ONE {
            proof {
                assume(is_equal_to_minus_one(spec_montgomery(*self)));
            }
            return None;
        }
        let one = FieldElement::ONE;

        /* VERIFICATION NOTE: need to prove preconditions for arithmetic traits */
        assume(false);

        let y = &(&u - &one) * &(&u + &one).invert();

        let mut y_bytes = y.as_bytes();
        y_bytes[31] ^= sign << 7;

        let result = CompressedEdwardsY(y_bytes).decompress();

        proof {
            // assumed postconditions
            match result {
                Some(edwards) => {
                    assume(montgomery_corresponds_to_edwards(*self, edwards));
                    assume(is_well_formed_edwards_point(edwards));
                    assume(edwards_point_as_affine(edwards) == spec_montgomery_to_edwards_affine(
                        spec_montgomery(*self),
                        sign,
                    ));
                },
                None => {
                    assume(is_equal_to_minus_one(spec_montgomery(*self)));
                },
            }
        }

        result
    }
}

/// Perform the Elligator2 mapping to a Montgomery point.
///
/// See <https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-10#section-6.7.1>
/// Also: RFC 9380 Section 6.7.1
//
// TODO Determine how much of the hash-to-group API should be exposed after the CFRG
//      draft gets into a more polished/accepted state.
#[allow(unused)]
pub(crate) fn elligator_encode(r_0: &FieldElement) -> (result: MontgomeryPoint)
    requires
        fe51_limbs_bounded(r_0, 51),
    ensures
        spec_montgomery(result) == spec_elligator_encode(fe51_as_canonical_nat(r_0)),
        spec_montgomery(result) < p(),
        !is_equal_to_minus_one(spec_montgomery(result)),
        is_valid_montgomery_point(result),
{
    let one = FieldElement::ONE;
    let zero = FieldElement::ZERO;  // moved from after sqrt_ratio_i for proof block access
    proof {
        // Constant limb bounds
        lemma_one_limbs_bounded_51();
        lemma_zero_limbs_bounded_51();
        lemma_montgomery_a_limbs_bounded_51();

        // Common weakenings used to satisfy 54-bit preconditions
        lemma_fe51_limbs_bounded_weaken(&one, 51, 54);
        lemma_fe51_limbs_bounded_weaken(&zero, 51, 54);
        lemma_fe51_limbs_bounded_weaken(&MONTGOMERY_A, 51, 54);
        lemma_fe51_limbs_bounded_weaken(r_0, 51, 54);
    }

    /* ORIGINAL CODE: let d_1 = &one + &r_0.square2(); */
    let r_0_sq2 = r_0.square2();
    proof {
        assert(fe51_limbs_bounded(&r_0_sq2, 53));  // from square2 postcondition
        assert(sum_of_limbs_bounded(&one, &r_0_sq2, u64::MAX)) by {
            lemma_fe51_limbs_bounded_weaken(&one, 51, 53);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&one, &r_0_sq2, 53);
        }
    }
    let d_1 = &one + &r_0_sq2;  // 2r^2

    proof {
        assert(fe51_limbs_bounded(&d_1, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&one, 51, 53);
            lemma_add_bounds_propagate(&one, &r_0_sq2, 53);
        }
    }
    proof {
        assert(fe51_limbs_bounded(&MONTGOMERY_A_NEG, 54)) by {
            lemma_montgomery_a_neg_limbs_bounded_51();
            lemma_fe51_limbs_bounded_weaken(&MONTGOMERY_A_NEG, 51, 54);
        }
    }
    /* ORIGINAL CODE: let d = &MONTGOMERY_A_NEG * &(d_1.invert()); */
    let d_1_inv = d_1.invert();
    let d = &MONTGOMERY_A_NEG * &d_1_inv;  // (-A)/(1+2r^2)
    proof {
        assert(fe51_limbs_bounded(&d, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&d, 52, 54);
        }
    }

    let d_sq = &d.square();
    let au = &MONTGOMERY_A * &d;

    /* ORIGINAL CODE: let inner = &(d_sq + &au) + &one; */
    proof {
        assert(sum_of_limbs_bounded(d_sq, &au, u64::MAX)) by {
            lemma_fe51_limbs_bounded_weaken(d_sq, 52, 54);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(d_sq, &au, 54);
        }
    }
    let d_sq_plus_au = d_sq + &au;
    proof {
        assert(fe51_limbs_bounded(&d_sq_plus_au, 53)) by {
            assert forall|i: int| 0 <= i < 5 implies d_sq_plus_au.limbs[i] < (1u64 << 53) by {
                assert(d_sq.limbs[i] < (1u64 << 52));
                assert(au.limbs[i] < (1u64 << 52));
                assert((1u64 << 52) + (1u64 << 52) == (1u64 << 53)) by (bit_vector);
            }
        }
        assert(sum_of_limbs_bounded(&d_sq_plus_au, &one, u64::MAX)) by {
            lemma_fe51_limbs_bounded_weaken(&one, 51, 53);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&d_sq_plus_au, &one, 53);
        }
    }
    let inner = &d_sq_plus_au + &one;  // inner = d^2 + A*d + 1

    proof {
        assert(fe51_limbs_bounded(&inner, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&one, 51, 53);
            lemma_add_bounds_propagate(&d_sq_plus_au, &one, 53);
        }
    }
    let eps = &d * &inner;  // eps = d^3 + Ad^2 + d

    proof {
        assert(fe51_limbs_bounded(&one, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&one, 51, 54);
        }
    }
    let (eps_is_sq, _eps) = FieldElement::sqrt_ratio_i(&eps, &one);

    /* ORIGINAL CODE: let Atemp = FieldElement::conditional_select(&MONTGOMERY_A, &zero, eps_is_sq); */
    let Atemp = conditional_select_field_element(&MONTGOMERY_A, &zero, eps_is_sq);  // 0, or A if nonsquare

    proof {
        assert(fe51_limbs_bounded(&Atemp, 54)) by {
            if choice_is_true(eps_is_sq) {
                assert(Atemp == zero);
                assert(fe51_limbs_bounded(&Atemp, 54));
            } else {
                assert(Atemp == MONTGOMERY_A);
                assert(fe51_limbs_bounded(&Atemp, 54));
            }
        }
        assert(sum_of_limbs_bounded(&d, &Atemp, u64::MAX)) by {
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&d, &Atemp, 54);
        }
    }
    let mut u = &d + &Atemp;  // d, or d+A if nonsquare
    let ghost u_pre = u;

    /* ORIGINAL CODE: u.conditional_negate(!eps_is_sq); */
    let neg_choice = choice_not(eps_is_sq);
    proof {
        assert(fe51_limbs_bounded(&u, 54)) by {
            assert(fe51_limbs_bounded(&d, 52));  // from mul postcondition
            lemma_fe51_limbs_bounded_weaken(&Atemp, 51, 52);
            lemma_add_bounds_propagate(&d, &Atemp, 52);
            lemma_fe51_limbs_bounded_weaken(&u, 53, 54);
        }
    }
    conditional_negate_field_element(&mut u, neg_choice);  // d, or -d-A if nonsquare

    /* ORIGINAL CODE: MontgomeryPoint(u.as_bytes()) */
    let result = MontgomeryPoint(u.as_bytes());

    proof {
        let r = fe51_as_canonical_nat(r_0);
        let A = fe51_as_canonical_nat(&MONTGOMERY_A);

        // ---------------------------------------------------------------------
        // Step 0: Bridge exec variables to spec-level math expressions.
        //   Show each intermediate FieldElement (r_0_sq2, d_1, d, d_sq, au,
        //   inner, eps) equals its counterpart in spec_elligator_encode.
        // ---------------------------------------------------------------------
        // r_0_sq2 matches 2*r^2
        assert(fe51_as_canonical_nat(&r_0_sq2) == field_mul(2, field_square(r))) by {
            // square2 postcondition: u64_5_as_nat(r_0_sq2.limbs) % p == 2 * pow(u64_5_as_nat(r0.limbs),2) % p
            let r0_raw = u64_5_as_nat(r_0.limbs);
            let r0_sq_raw = pow(r0_raw as int, 2) as nat;
            assert(fe51_as_canonical_nat(r_0) == r0_raw % p());

            // square2 postcondition
            assert(u64_5_as_nat(r_0_sq2.limbs) % p() == (2 * pow(r0_raw as int, 2)) as nat % p());

            // Reduce r0_sq_raw modulo p to field_square(r0_raw%p)
            assert(r0_sq_raw % p() == field_square(r0_raw % p())) by {
                assert(r0_sq_raw % p() == pow(r0_raw as int, 2) as nat % p());
                lemma_square_matches_field_square(r0_raw, r0_sq_raw);
            }

            // (2 * r0_sq_raw) % p = field_mul(2, r0_sq_raw % p)
            assert((2 * r0_sq_raw) % p() == field_mul(2, r0_sq_raw % p())) by {
                p_gt_2();
                lemma_mul_mod_noop_general(2, r0_sq_raw as int, p() as int);
                lemma_small_mod(2nat, p());
            }

            assert(fe51_as_canonical_nat(&r_0_sq2) == u64_5_as_nat(r_0_sq2.limbs) % p());
            // Connect square2's postcondition to our `r0_sq_raw` name.
            assert(u64_5_as_nat(r_0_sq2.limbs) % p() == (2 * r0_sq_raw) % p()) by {
                // square2 gives: u64_5_as_nat(...) % p == ((2 * pow(r0_raw,2)) as nat) % p
                // and r0_sq_raw is `pow(r0_raw,2) as nat`.
                assert(pow(r0_raw as int, 2) >= 0) by {
                    lemma_pow_nonnegative(r0_raw as int, 2);
                }
                assert((2 * pow(r0_raw as int, 2)) as nat == 2 * (pow(r0_raw as int, 2) as nat));
                assert(r0_sq_raw == pow(r0_raw as int, 2) as nat);
            }
            assert(r0_raw % p() == r);
        }

        // d_1 = 1 + 2*r^2
        assert(fe51_as_canonical_nat(&d_1) == field_add(1, fe51_as_canonical_nat(&r_0_sq2))) by {
            lemma_one_field_element_value();
            assert(fe51_as_canonical_nat(&one) == 1);
            assert(fe51_as_canonical_nat(&d_1) == field_add(
                fe51_as_canonical_nat(&one),
                fe51_as_canonical_nat(&r_0_sq2),
            ));
        }
        assert(fe51_as_canonical_nat(&d_1) == field_add(1, field_mul(2, field_square(r))));

        // d = (-A) / (1 + 2*r^2)
        assert(fe51_as_canonical_nat(&d) == field_mul(
            field_neg(A),
            field_inv(field_add(1, field_mul(2, field_square(r)))),
        )) by {
            // From invert:
            assert(fe51_as_canonical_nat(&d_1_inv) == field_inv(fe51_as_canonical_nat(&d_1)));
            // From mul:
            assert(fe51_as_canonical_nat(&d) == field_mul(
                fe51_as_canonical_nat(&MONTGOMERY_A_NEG),
                fe51_as_canonical_nat(&d_1_inv),
            ));
            // MONTGOMERY_A_NEG encodes -A:
            assert(fe51_as_canonical_nat(&MONTGOMERY_A_NEG) == field_neg(A)) by {
                axiom_montgomery_a_neg_is_neg_a();
            }
            // Replace d_1 with denom (asserted above).
            assert(fe51_as_canonical_nat(&d_1) == field_add(1, field_mul(2, field_square(r))));
        }

        // d_sq = d^2
        assert(fe51_as_canonical_nat(&d_sq) == field_square(fe51_as_canonical_nat(&d))) by {
            // square postcondition is in terms of u64_5_as_nat; bridge to field_square
            let d_raw = u64_5_as_nat(d.limbs);
            let d_sq_raw = u64_5_as_nat(d_sq.limbs);
            assert(fe51_as_canonical_nat(&d) == d_raw % p());
            assert(d_sq_raw % p() == pow(d_raw as int, 2) as nat % p());
            lemma_square_matches_field_square(d_raw, d_sq_raw);
        }

        // au = A * d
        assert(fe51_as_canonical_nat(&au) == field_mul(A, fe51_as_canonical_nat(&d)));

        // inner = d^2 + A*d + 1
        assert(fe51_as_canonical_nat(&inner) == field_add(
            field_add(fe51_as_canonical_nat(&d_sq), fe51_as_canonical_nat(&au)),
            1,
        )) by {
            lemma_one_field_element_value();
            assert(fe51_as_canonical_nat(&one) == 1);
            assert(fe51_as_canonical_nat(&d_sq_plus_au) == field_add(
                fe51_as_canonical_nat(&d_sq),
                fe51_as_canonical_nat(&au),
            ));
            assert(fe51_as_canonical_nat(&inner) == field_add(
                fe51_as_canonical_nat(&d_sq_plus_au),
                fe51_as_canonical_nat(&one),
            ));
        }

        // eps = d * inner
        assert(fe51_as_canonical_nat(&eps) == field_mul(
            fe51_as_canonical_nat(&d),
            fe51_as_canonical_nat(&inner),
        ));

        let eps_nat = fe51_as_canonical_nat(&eps);

        // ---------------------------------------------------------------------
        // Step 1: Prove choice_is_true(eps_is_sq) <==> is_square(eps).
        //   The exec code branches on the Choice from sqrt_ratio_i, but
        //   spec_elligator_encode branches on is_square. This equivalence
        //   lets Steps 2-3 align the exec branches with the spec branches.
        // ---------------------------------------------------------------------
        assert(choice_is_true(eps_is_sq) <==> is_square(eps_nat)) by {
            let v_nat = fe51_as_canonical_nat(&one);
            p_gt_2();
            assert(v_nat == 1) by {
                lemma_one_field_element_value();
            }

            if choice_is_true(eps_is_sq) {
                // Success: either eps=0 or is_sqrt_ratio(eps, 1, _eps), giving a square witness.
                if eps_nat == 0 {
                    assert(is_square(eps_nat)) by {
                        assert(exists|y: nat|
                            (#[trigger] field_mul(y, y)) == field_canonical(eps_nat)) by {
                            // witness y = 0
                            assert(field_mul(0, 0) == field_canonical(eps_nat));
                        }
                    }
                } else {
                    assert(fe51_is_sqrt_ratio(&eps, &one, &_eps));
                    let y = fe51_as_canonical_nat(&_eps);
                    assert(field_mul(y, y) == field_canonical(eps_nat)) by {
                        // is_sqrt_ratio with v=1 means y^2 == eps (mod p)
                        assert((y * y * v_nat) % p() == field_canonical(eps_nat));
                        assert(v_nat == 1);
                        lemma_mul_basics((y * y) as int);
                        assert((y * y * 1nat) % p() == (y * y) % p());
                        // LHS is a mod result, so eps_nat < p() and eps_nat % p() = eps_nat
                        p_gt_2();
                        lemma_mod_bound((y * y) as int, p() as int);
                        assert(eps_nat < p());
                        lemma_small_mod(eps_nat, p());
                    }
                    assert(is_square(eps_nat)) by {
                        assert(exists|w: nat|
                            (#[trigger] field_mul(w, w)) == field_canonical(eps_nat)) by {
                            let w = y;
                            assert(field_mul(w, w) == field_canonical(eps_nat));
                        }
                    }
                }
            } else {
                // Failure implies eps != 0 (sqrt_ratio_i spec: u==0 => success).
                assert(eps_nat != 0);
                assert(fe51_is_sqrt_ratio_times_i(&eps, &one, &_eps));
                // Show eps is not a quadratic residue: if it had a sqrt, contradiction.
                assert(!is_square(eps_nat)) by {
                    if is_square(eps_nat) {
                        let y0 = choose|y: nat| (#[trigger] (y * y) % p()) == (eps_nat % p());
                        let y = y0 % p();
                        lemma_square_mod_noop(y0);
                        assert(field_square(y) == field_square(y0));
                        // Build the "times i" witness x from sqrt_ratio_i failure.
                        let x = fe51_as_canonical_nat(&_eps);
                        assert(x < p()) by {
                            lemma_mod_bound(u64_5_as_nat(_eps.limbs) as int, p() as int);
                        }
                        assert(exists|w: nat|
                            w < p() && #[trigger] field_mul(field_square(w), 1) == (sqrt_m1()
                                * eps_nat) % p()) by {
                            let w = x;
                            // from is_sqrt_ratio_times_i with v=1
                            assert((x * x * 1nat) % p() == (sqrt_m1() * eps_nat) % p());
                            // field_mul(field_square(w), 1) == field_square(w)
                            p_gt_2();
                            let a = field_square(w);
                            // a is already reduced mod p, so a < p
                            lemma_mod_bound((w * w) as int, p() as int);
                            assert(a < p());
                            assert(field_mul(a, 1) == a) by {
                                assert(a * 1 == a);
                                lemma_small_mod(a, p());
                            }
                            assert(field_square(w) == (sqrt_m1() * eps_nat) % p()) by {
                                assert((w * w) % p() == (sqrt_m1() * eps_nat) % p());
                            }
                        }
                        // Apply lemma: no y with y^2 = eps_nat (mod p)
                        // Strengthen eps_nat != 0 to eps_nat % p != 0 for the lemma's precondition.
                        p_gt_2();
                        assert(eps_nat == u64_5_as_nat(eps.limbs) % p());
                        lemma_mod_bound(u64_5_as_nat(eps.limbs) as int, p() as int);
                        assert(eps_nat < p());
                        lemma_small_mod(eps_nat, p());
                        assert(eps_nat % p() == eps_nat);
                        assert(eps_nat % p() != 0);
                        lemma_no_square_root_when_times_i(eps_nat, 1, y);
                        assert(false);
                    }
                }
            }
        }

        // ---------------------------------------------------------------------
        // Step 2: Derive the spec value of u after conditional_select + negate.
        //   u = d when eps is square, u = -(d+A) otherwise — matching
        //   the two branches of spec_elligator_encode.
        // ---------------------------------------------------------------------
        assert(fe51_as_canonical_nat(&u) == if choice_is_true(eps_is_sq) {
            fe51_as_canonical_nat(&d)
        } else {
            field_neg(field_add(fe51_as_canonical_nat(&d), A))
        }) by {
            // conditional_select: Atemp = 0 if square, else A
            assert(fe51_as_canonical_nat(&Atemp) == if choice_is_true(eps_is_sq) {
                0
            } else {
                A
            }) by {
                if choice_is_true(eps_is_sq) {
                    assert(Atemp == zero);
                    assert(fe51_as_canonical_nat(&Atemp) == 0) by {
                        lemma_zero_field_element_value();
                    }
                } else {
                    assert(Atemp == MONTGOMERY_A);
                    // fe51_as_canonical_nat(&MONTGOMERY_A) is A by definition
                }
            }
            assert(fe51_as_canonical_nat(&u_pre) == if choice_is_true(eps_is_sq) {
                fe51_as_canonical_nat(&d)
            } else {
                field_add(fe51_as_canonical_nat(&d), A)
            }) by {
                if choice_is_true(eps_is_sq) {
                    assert(fe51_as_canonical_nat(&u_pre) == field_add(
                        fe51_as_canonical_nat(&d),
                        0,
                    ));
                    // field_add(x, 0) = x for any field element x
                    assert(field_add(fe51_as_canonical_nat(&d), 0) == fe51_as_canonical_nat(&d))
                        by {
                        let x = fe51_as_canonical_nat(&d);
                        p_gt_2();
                        // x < p, so (x + 0) % p = x
                        lemma_mod_bound(u64_5_as_nat(d.limbs) as int, p() as int);
                        lemma_small_mod(x, p());
                    }
                } else {
                    assert(fe51_as_canonical_nat(&u_pre) == field_add(
                        fe51_as_canonical_nat(&d),
                        A,
                    ));
                }
            }
            // conditional_negate with choice_not: negates when nonsquare
            if choice_is_true(eps_is_sq) {
                assert(!choice_is_true(neg_choice));
                assert(fe51_as_canonical_nat(&u) == fe51_as_canonical_nat(&u_pre));
            } else {
                assert(choice_is_true(neg_choice));
                assert(fe51_as_canonical_nat(&u) == field_neg(fe51_as_canonical_nat(&u_pre)));
                assert(fe51_as_canonical_nat(&u) == field_neg(
                    field_add(fe51_as_canonical_nat(&d), A),
                ));
            }
        }

        // ---------------------------------------------------------------------
        // Step 3: Encode u into MontgomeryPoint bytes and prove postconditions.
        //   Show spec_montgomery(result) == spec_elligator_encode(r),
        //   result < p(), and result != -1 (for safe to_edwards conversion).
        // ---------------------------------------------------------------------
        let u_bytes = result.0;
        assert(spec_montgomery(result) == fe51_as_canonical_nat(&u)) by {
            // as_bytes gives canonical bytes whose nat value equals the field element (already < p)
            assert(u8_32_as_nat(&u_bytes) == fe51_as_canonical_nat(&u));
            pow255_gt_19();
            lemma_small_mod(fe51_as_canonical_nat(&u), pow2(255));
            lemma_small_mod(fe51_as_canonical_nat(&u), p());
        }

        // Now match the spec_elligator_encode definition.
        let spec_u = spec_elligator_encode(r);
        assert(spec_montgomery(result) == spec_u) by {
            // Unfold spec_elligator_encode and rewrite it in terms of our computed `d` and `eps`.
            let denom = field_add(1, field_mul(2, field_square(r)));
            let d_spec = field_mul(field_neg(A), field_inv(denom));
            assert(d_spec == fe51_as_canonical_nat(&d));

            let d_sq_spec = field_square(d_spec);
            let eps_spec = field_mul(
                d_spec,
                field_add(field_add(d_sq_spec, field_mul(A, d_spec)), 1),
            );
            assert(eps_spec == eps_nat);

            // By definition:
            //   spec_elligator_encode(r) = if is_square(eps_spec) { d_spec } else { -(d_spec + A) }
            assert(spec_u == if is_square(eps_nat) {
                fe51_as_canonical_nat(&d)
            } else {
                field_neg(field_add(fe51_as_canonical_nat(&d), A))
            }) by {
                // Directly unfold the spec function body.
                // (Avoid `compute` here; the expression involves exec-derived values.)
                assert(spec_u == if is_square(eps_spec) {
                    d_spec
                } else {
                    field_neg(field_add(d_spec, A))
                });
            }

            // Finally, use the established case-split for `u` (which matches `is_square(eps_nat)`).
            if is_square(eps_nat) {
                assert(choice_is_true(eps_is_sq));
                assert(spec_montgomery(result) == fe51_as_canonical_nat(&d));
            } else {
                assert(!choice_is_true(eps_is_sq));
                assert(spec_montgomery(result) == field_neg(
                    field_add(fe51_as_canonical_nat(&d), A),
                ));
            }
        }

        assert(spec_montgomery(result) < p()) by {
            p_gt_2();
            lemma_mod_bound(spec_montgomery(result) as int, p() as int);
        }

        assert(!is_equal_to_minus_one(spec_montgomery(result))) by {
            lemma_elligator_never_minus_one(r);
        }

        assert(is_valid_montgomery_point(result)) by {
            axiom_elligator_encode_outputs_valid_u(r);
            assert(is_valid_u_coordinate(spec_montgomery(result)));
        }
    }

    result
}

/// A `ProjectivePoint` holds a point on the projective line
/// \\( \mathbb P(\mathbb F\_p) \\), which we identify with the Kummer
/// line of the Montgomery curve.
#[derive(Copy, Clone, Debug)]
pub struct ProjectivePoint {
    pub U: FieldElement,
    pub W: FieldElement,
}

impl Identity for ProjectivePoint {
    fn identity() -> (result: ProjectivePoint)
        ensures
    // The identity point is (1:0) in projective coordinates

            fe51_as_canonical_nat(&result.U) == 1,
            fe51_as_canonical_nat(&result.W) == 0,
            // Actual representation uses field constants ONE/ZERO
            fe51_limbs_bounded(&result.U, 51),
            fe51_limbs_bounded(&result.W, 51),
            // Weakened bounds help SMT solver in callers
            fe51_limbs_bounded(&result.U, 54),
            fe51_limbs_bounded(&result.W, 54),
    {
        let result = ProjectivePoint { U: FieldElement::ONE, W: FieldElement::ZERO };
        proof {
            // Field element values
            assert(fe51_as_canonical_nat(&result.U) == 1) by {
                lemma_one_field_element_value();
            }
            assert(fe51_as_canonical_nat(&result.W) == 0) by {
                lemma_zero_field_element_value();
            }
            // Limb bounds: first establish at 51, then weaken to 54
            assert(fe51_limbs_bounded(&result.U, 51)) by {
                lemma_one_limbs_bounded_51();
            }
            assert(fe51_limbs_bounded(&result.W, 51)) by {
                lemma_zero_limbs_bounded_51();
            }
            assert(fe51_limbs_bounded(&result.U, 54)) by {
                lemma_one_limbs_bounded_51();
                lemma_fe51_limbs_bounded_weaken(&result.U, 51, 54);
            }
            assert(fe51_limbs_bounded(&result.W, 54)) by {
                lemma_zero_limbs_bounded_51();
                lemma_fe51_limbs_bounded_weaken(&result.W, 51, 54);
            }
        }
        result
    }
}

impl crate::traits::IsIdentitySpecImpl for ProjectivePoint {
    /// For ProjectivePoint, identity is (1:0) in projective coords, i.e., W == 0
    open spec fn is_identity_spec(&self) -> bool {
        fe51_as_canonical_nat(&self.W) == 0
    }
}

impl Default for ProjectivePoint {
    fn default() -> (result: ProjectivePoint)
        ensures
    // Default returns the identity point

            fe51_as_canonical_nat(&result.U) == 1,
            fe51_as_canonical_nat(&result.W) == 0,
    {
        ProjectivePoint::identity()
    }
}

impl ConditionallySelectable for ProjectivePoint {
    fn conditional_select(a: &ProjectivePoint, b: &ProjectivePoint, choice: Choice) -> (result:
        ProjectivePoint)
        ensures
    // If choice is false (0), return a

            !choice_is_true(choice) ==> {
                &&& result.U == a.U
                &&& result.W == a.W
            },
            // If choice is true (1), return b
            choice_is_true(choice) ==> {
                &&& result.U == b.U
                &&& result.W == b.W
            },
    {
        let result = ProjectivePoint {
            U: FieldElement::conditional_select(&a.U, &b.U, choice),
            W: FieldElement::conditional_select(&a.W, &b.W, choice),
        };

        proof {
            // FieldElement::conditional_select postconditions are stated in terms of limb equality.
            assert(!choice_is_true(choice) ==> result.U.limbs == a.U.limbs);
            assert(choice_is_true(choice) ==> result.U.limbs == b.U.limbs);
            assert(!choice_is_true(choice) ==> result.W.limbs == a.W.limbs);
            assert(choice_is_true(choice) ==> result.W.limbs == b.W.limbs);

            if !choice_is_true(choice) {
                assert(result.U.limbs == a.U.limbs);
                assert(result.W.limbs == a.W.limbs);
                assert(result.U == a.U);
                assert(result.W == a.W);
            }
            if choice_is_true(choice) {
                assert(result.U.limbs == b.U.limbs);
                assert(result.W.limbs == b.W.limbs);
                assert(result.U == b.U);
                assert(result.W == b.W);
            }
        }

        result
    }
}

impl ProjectivePoint {
    /// Dehomogenize this point to affine coordinates.
    ///
    /// # Return
    ///
    /// * \\( u = U / W \\) if \\( W \neq 0 \\);
    /// * \\( 0 \\) if \\( W \eq 0 \\);
    ///
    /// # Specification
    /// The resulting MontgomeryPoint has u-coordinate equal to U/W (or 0 if W=0)
    pub fn as_affine(&self) -> (result: MontgomeryPoint)
        requires
            fe51_limbs_bounded(&self.U, 54),
            fe51_limbs_bounded(&self.W, 54),
        ensures
    // For projective point (U:W), the affine u-coordinate is u = U/W (or 0 if W=0)

            spec_montgomery(result) == {
                let u_proj = fe51_as_canonical_nat(&self.U);
                let w_proj = fe51_as_canonical_nat(&self.W);
                if w_proj == 0 {
                    0
                } else {
                    field_mul(u_proj, field_inv(w_proj))
                }
            },
    {
        let w_inv = self.W.invert();
        let u = &self.U * &w_inv;
        let u_bytes = u.as_bytes();
        /* ORIGINAL CODE: let result = MontgomeryPoint(u.as_bytes()); */
        let result = MontgomeryPoint(u_bytes);
        proof {
            // The affine u-coordinate is u = U * W^{-1}.
            let u_proj = fe51_as_canonical_nat(&self.U);
            let w_proj = fe51_as_canonical_nat(&self.W);

            // First, connect the computed field element `u` to the spec-level expression.
            assert(fe51_as_canonical_nat(&w_inv) == field_inv(w_proj));
            assert(fe51_as_canonical_nat(&u) == field_mul(u_proj, field_inv(w_proj)));

            // Next, show that the MontgomeryPoint encoding of `u` decodes back to `u`.
            assert(u8_32_as_nat(&u_bytes) == fe51_as_canonical_nat(&u));

            // fe51_as_canonical_nat(&u) is reduced mod p, hence < p.
            assert(fe51_as_canonical_nat(&u) < p()) by {
                assert(p() > 0) by {
                    pow255_gt_19();
                }
                lemma_mod_bound(u64_5_as_nat(u.limbs) as int, p() as int);
            }
            assert(p() < pow2(255)) by {
                pow255_gt_19();
            }
            assert(fe51_as_canonical_nat(&u) < pow2(255));

            assert(field_element_from_bytes(&u_bytes) == fe51_as_canonical_nat(&u)) by {
                // field_element_from_bytes(bytes) == field_canonical(u8_32_as_nat(bytes) % 2^255)
                // and the canonical value fits into 255 bits, so the % 2^255 is a no-op.
                assert(u8_32_as_nat(&u_bytes) < pow2(255)) by {
                    assert(u8_32_as_nat(&u_bytes) == fe51_as_canonical_nat(&u));
                }
                assert(u8_32_as_nat(&u_bytes) % pow2(255) == u8_32_as_nat(&u_bytes)) by {
                    lemma_small_mod(u8_32_as_nat(&u_bytes), pow2(255));
                }
                assert(field_element_from_bytes(&u_bytes) == field_canonical(
                    u8_32_as_nat(&u_bytes),
                ));
                assert(field_element_from_bytes(&u_bytes) == field_canonical(
                    fe51_as_canonical_nat(&u),
                ));
                assert(field_canonical(fe51_as_canonical_nat(&u)) == fe51_as_canonical_nat(&u)) by {
                    lemma_small_mod(fe51_as_canonical_nat(&u), p());
                }
            }

            assert(result.0 == u_bytes);
            assert(spec_montgomery(result) == field_element_from_bytes(&u_bytes));
            assert(spec_montgomery(result) == field_mul(u_proj, field_inv(w_proj)));

            if w_proj == 0 {
                assert(field_inv(w_proj) == 0) by {
                    reveal(field_inv);
                }
                assert(field_mul(u_proj, field_inv(w_proj)) == 0) by {
                    reveal(field_mul);
                    lemma_mul_by_zero_is_zero(u_proj as int);
                }
                assert(spec_montgomery(result) == 0);
            } else {
                assert(spec_montgomery(result) == field_mul(u_proj, field_inv(w_proj)));
            }
        }
        result
    }
}

/// Perform the double-and-add step of the Montgomery ladder.
///
/// Given projective points
/// \\( (U\_P : W\_P) = u(P) \\),
/// \\( (U\_Q : W\_Q) = u(Q) \\),
/// and the affine difference
/// \\(      u\_{P-Q} = u(P-Q) \\), set
/// $$
///     (U\_P : W\_P) \gets u(\[2\]P)
/// $$
/// and
/// $$
///     (U\_Q : W\_Q) \gets u(P + Q).
/// $$
#[rustfmt::skip]  // keep alignment of explanatory comments
fn differential_add_and_double(
    P: &mut ProjectivePoint,
    Q: &mut ProjectivePoint,
    affine_PmQ: &FieldElement,
)
    requires
// Bounds needed for the underlying field operations

        fe51_limbs_bounded(&old(P).U, 52),
        fe51_limbs_bounded(&old(P).W, 52),
        fe51_limbs_bounded(&old(Q).U, 52),
        fe51_limbs_bounded(&old(Q).W, 52),
        // This matches the invariant maintained by the caller (mul_bits_be)
        fe51_limbs_bounded(affine_PmQ, 51),
        is_valid_u_coordinate(fe51_as_canonical_nat(affine_PmQ)),
    ensures
// === Bounds preserved for callers ===

        fe51_limbs_bounded(&P.U, 52),
        fe51_limbs_bounded(&P.W, 52),
        fe51_limbs_bounded(&Q.U, 52),
        fe51_limbs_bounded(&Q.W, 52),
        // Degenerate case: if u(P-Q)=0 and both inputs have u=0, outputs preserve u=0.
        (fe51_as_canonical_nat(affine_PmQ) == 0 && spec_projective_u_coordinate(*old(P)) == 0
            && spec_projective_u_coordinate(*old(Q)) == 0) ==> (spec_projective_u_coordinate(*P)
            == 0 && spec_projective_u_coordinate(*Q) == 0),
        // Montgomery ladder step: P' = [2]P (xDBL), Q' = P + Q (xADD).
        // Case 1: P = [k]B, Q = [k+1]B  ==>  P' = [2k]B, Q' = [2k+1]B
        ({
            let B = canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ));
            forall|k: nat|
                fe51_as_canonical_nat(affine_PmQ) != 0
                    && #[trigger] projective_represents_montgomery_or_infinity(
                    *old(P),
                    montgomery_scalar_mul(B, k),
                ) && #[trigger] projective_represents_montgomery_or_infinity(
                    *old(Q),
                    montgomery_scalar_mul(B, k + 1),
                ) ==> {
                    &&& projective_represents_montgomery_or_infinity(
                        *P,
                        montgomery_scalar_mul(B, 2 * k),
                    )
                    &&& projective_represents_montgomery_or_infinity(
                        *Q,
                        montgomery_scalar_mul(B, 2 * k + 1),
                    )
                }
        }),
        // Case 2 (swapped): P = [k+1]B, Q = [k]B  ==>  P' = [2k+2]B, Q' = [2k+1]B
        ({
            let B = canonical_montgomery_lift(fe51_as_canonical_nat(affine_PmQ));
            forall|k: nat|
                fe51_as_canonical_nat(affine_PmQ) != 0
                    && #[trigger] projective_represents_montgomery_or_infinity(
                    *old(P),
                    montgomery_scalar_mul(B, k + 1),
                ) && #[trigger] projective_represents_montgomery_or_infinity(
                    *old(Q),
                    montgomery_scalar_mul(B, k),
                ) ==> {
                    &&& projective_represents_montgomery_or_infinity(
                        *P,
                        montgomery_scalar_mul(B, 2 * k + 2),
                    )
                    &&& projective_represents_montgomery_or_infinity(
                        *Q,
                        montgomery_scalar_mul(B, 2 * k + 1),
                    )
                }
        }),
{
    proof {
        // Precondition plumbing for field ops used below.
        lemma_fe51_limbs_bounded_weaken(&P.U, 52, 54);
        lemma_fe51_limbs_bounded_weaken(&P.W, 52, 54);
        lemma_fe51_limbs_bounded_weaken(&Q.U, 52, 54);
        lemma_fe51_limbs_bounded_weaken(&Q.W, 52, 54);
        lemma_fe51_limbs_bounded_weaken(affine_PmQ, 51, 54);

        // APLUS2_OVER_FOUR is a small constant ([121666, 0, 0, 0, 0]).
        assert(fe51_limbs_bounded(&APLUS2_OVER_FOUR, 51)) by {
            assert(APLUS2_OVER_FOUR.limbs[0] == 121666);
            assert(APLUS2_OVER_FOUR.limbs[1] == 0);
            assert(APLUS2_OVER_FOUR.limbs[2] == 0);
            assert(APLUS2_OVER_FOUR.limbs[3] == 0);
            assert(APLUS2_OVER_FOUR.limbs[4] == 0);
            assert forall|i: int| 0 <= i < 5 implies APLUS2_OVER_FOUR.limbs[i] < (1u64 << 51) by {
                if i == 0 {
                    assert(121666u64 < (1u64 << 51)) by (bit_vector);
                } else {
                    assert(APLUS2_OVER_FOUR.limbs[i] == 0);
                    assert(0u64 < (1u64 << 51)) by (bit_vector);
                }
            }
        }
        lemma_fe51_limbs_bounded_weaken(&APLUS2_OVER_FOUR, 51, 54);

        // Sums used for t0/t2 must not overflow u64.
        lemma_sum_of_limbs_bounded_from_fe51_bounded(&P.U, &P.W, 52);
        lemma_sum_of_limbs_bounded_from_fe51_bounded(&Q.U, &Q.W, 52);
    }
    let ghost P_in = *P;
    let ghost Q_in = *Q;
    let t0 = &P.U + &P.W;
    let t1 = &P.U - &P.W;
    let t2 = &Q.U + &Q.W;
    let t3 = &Q.U - &Q.W;

    proof {
        // Bounds for t0 and t2 (used by square and mul preconditions).
        assert(fe51_limbs_bounded(&t0, 53)) by {
            lemma_add_bounds_propagate(&P.U, &P.W, 52);
        }
        assert(fe51_limbs_bounded(&t0, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&t0, 53, 54);
        }

        assert(fe51_limbs_bounded(&t2, 53)) by {
            lemma_add_bounds_propagate(&Q.U, &Q.W, 52);
        }
        assert(fe51_limbs_bounded(&t2, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&t2, 53, 54);
        }

        // Sub results are 54-bounded by spec.
        assert(fe51_limbs_bounded(&t1, 54));
        assert(fe51_limbs_bounded(&t3, 54));
    }
    let t4 = t0.square();  // (U_P + W_P)^2 = U_P^2 + 2 U_P W_P + W_P^2
    let t5 = t1.square();  // (U_P - W_P)^2 = U_P^2 - 2 U_P W_P + W_P^2

    proof {
        // square() produces 52-bounded outputs; weaken as needed for subtraction/multiplication.
        assert(fe51_limbs_bounded(&t4, 52));
        assert(fe51_limbs_bounded(&t5, 52));
        assert(fe51_limbs_bounded(&t4, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&t4, 52, 54);
        }
        assert(fe51_limbs_bounded(&t5, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&t5, 52, 54);
        }
    }
    let t6 = &t4 - &t5;  // 4 U_P W_P

    proof {
        // Multiplication requires 54-bounded operands.
        assert(fe51_limbs_bounded(&t6, 54));
    }
    let t7 = &t0 * &t3;  // (U_P + W_P) (U_Q - W_Q) = U_P U_Q + W_P U_Q - U_P W_Q - W_P W_Q
    let t8 = &t1 * &t2;  // (U_P - W_P) (U_Q + W_Q) = U_P U_Q - W_P U_Q + U_P W_Q - W_P W_Q

    proof {
        // Sums used for t9 must not overflow u64.
        assert(fe51_limbs_bounded(&t7, 52));
        assert(fe51_limbs_bounded(&t8, 52));
        lemma_sum_of_limbs_bounded_from_fe51_bounded(&t7, &t8, 52);
        // And subtraction precondition for t10.
        lemma_fe51_limbs_bounded_weaken(&t7, 52, 54);
        lemma_fe51_limbs_bounded_weaken(&t8, 52, 54);
    }
    let t9 = &t7 + &t8;  // 2 (U_P U_Q - W_P W_Q)
    let t10 = &t7 - &t8;  // 2 (W_P U_Q - U_P W_Q)

    proof {
        // Bounds for t9 (used by square precondition).
        assert(fe51_limbs_bounded(&t9, 53)) by {
            lemma_add_bounds_propagate(&t7, &t8, 52);
        }
        assert(fe51_limbs_bounded(&t9, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&t9, 53, 54);
        }
        // Sub gives 54-bounded output
        assert(fe51_limbs_bounded(&t10, 54));
    }
    let t11 = t9.square();  // 4 (U_P U_Q - W_P W_Q)^2
    let t12 = t10.square();  // 4 (W_P U_Q - U_P W_Q)^2

    proof {
        // Bounds from square(): both are 52-bounded.
        assert(fe51_limbs_bounded(&t11, 52));
        assert(fe51_limbs_bounded(&t12, 52));
    }
    let t13 = &APLUS2_OVER_FOUR * &t6;  // (A + 2) U_P U_Q

    let t14 = &t4 * &t5;  // ((U_P + W_P)(U_P - W_P))^2 = (U_P^2 - W_P^2)^2
    proof {
        // Precondition for t15 addition.
        assert(fe51_limbs_bounded(&t13, 52));
        assert(fe51_limbs_bounded(&t5, 52));
        lemma_sum_of_limbs_bounded_from_fe51_bounded(&t13, &t5, 52);
    }
    let t15 = &t13 + &t5;  // (U_P - W_P)^2 + (A + 2) U_P W_P

    proof {
        // Precondition for t16 multiplication.
        assert(fe51_limbs_bounded(&t15, 53)) by {
            lemma_add_bounds_propagate(&t13, &t5, 52);
        }
        assert(fe51_limbs_bounded(&t15, 54)) by {
            lemma_fe51_limbs_bounded_weaken(&t15, 53, 54);
        }
    }
    let t16 = &t6 * &t15;  // 4 (U_P W_P) ((U_P - W_P)^2 + (A + 2) U_P W_P)

    proof {
        // Precondition for affine_PmQ * t12.
        assert(fe51_limbs_bounded(affine_PmQ, 54)) by {
            lemma_fe51_limbs_bounded_weaken(affine_PmQ, 51, 54);
        }
        assert(fe51_limbs_bounded(&t12, 54));
    }
    let t17 = affine_PmQ * &t12;  // U_D * 4 (W_P U_Q - U_P W_Q)^2
    let t18 = t11;  // W_D * 4 (U_P U_Q - W_P W_Q)^2

    P.U = t14;  // U_{P'} = (U_P + W_P)^2 (U_P - W_P)^2
    P.W = t16;  // W_{P'} = (4 U_P W_P) ((U_P - W_P)^2 + ((A + 2)/4) 4 U_P W_P)
    Q.U = t18;  // U_{Q'} = W_D * 4 (U_P U_Q - W_P W_Q)^2
    Q.W = t17;  // W_{Q'} = U_D * 4 (W_P U_Q - U_P W_Q)^2

    proof {
        // Bound postconditions
        assert(fe51_limbs_bounded(&t14, 52));
        assert(fe51_limbs_bounded(&t16, 52));
        assert(fe51_limbs_bounded(&t18, 52));
        assert(fe51_limbs_bounded(&t17, 52));
        assert(fe51_limbs_bounded(&P.U, 52));
        assert(fe51_limbs_bounded(&P.W, 52));
        assert(fe51_limbs_bounded(&Q.U, 52));
        assert(fe51_limbs_bounded(&Q.W, 52));

        // Connect the field-level xDBL/xADD formulas here to the abstract group law using the
        // step-level axioms in `montgomery_curve_lemmas`.
        let u_diff = fe51_as_canonical_nat(affine_PmQ);
        let B = canonical_montgomery_lift(u_diff);

        // Basepoint u-coordinate: canonical lift stores u mod p, and `u_diff` is already reduced.
        assert(spec_u_coordinate(B) == u_diff) by {
            let raw = fe51_as_nat(affine_PmQ);
            assert(u_diff == raw % p());
            p_gt_2();
            lemma_mod_division_less_than_divisor(raw as int, p() as int);
            assert(u_diff < p());
            lemma_small_mod(u_diff, p());
            assert(u_diff % p() == u_diff);
            assert(spec_u_coordinate(B) == u_diff % p());
        };

        // Cache input coordinates as nats (for the x-only axioms).
        let U_P0 = fe51_as_canonical_nat(&P_in.U);
        let W_P0 = fe51_as_canonical_nat(&P_in.W);
        let U_Q0 = fe51_as_canonical_nat(&Q_in.U);
        let W_Q0 = fe51_as_canonical_nat(&Q_in.W);

        // Square() produces a pow-based spec; connect it to `field_square`.
        let t0_raw = fe51_as_nat(&t0);
        let t1_raw = fe51_as_nat(&t1);
        let t4_raw = fe51_as_nat(&t4);
        let t5_raw = fe51_as_nat(&t5);
        let t9_raw = fe51_as_nat(&t9);
        let t10_raw = fe51_as_nat(&t10);
        let t11_raw = fe51_as_nat(&t11);
        let t12_raw = fe51_as_nat(&t12);

        assert(t4_raw % p() == pow(t0_raw as int, 2) as nat % p());
        lemma_square_matches_field_square(t0_raw, t4_raw);
        assert(fe51_as_canonical_nat(&t4) == field_square(fe51_as_canonical_nat(&t0)));

        assert(t5_raw % p() == pow(t1_raw as int, 2) as nat % p());
        lemma_square_matches_field_square(t1_raw, t5_raw);
        assert(fe51_as_canonical_nat(&t5) == field_square(fe51_as_canonical_nat(&t1)));

        assert(t11_raw % p() == pow(t9_raw as int, 2) as nat % p());
        lemma_square_matches_field_square(t9_raw, t11_raw);
        assert(fe51_as_canonical_nat(&t11) == field_square(fe51_as_canonical_nat(&t9)));

        assert(t12_raw % p() == pow(t10_raw as int, 2) as nat % p());
        lemma_square_matches_field_square(t10_raw, t12_raw);
        assert(fe51_as_canonical_nat(&t12) == field_square(fe51_as_canonical_nat(&t10)));

        // Basic add/sub/mul specs (already provided by FieldElement ops).
        assert(fe51_as_canonical_nat(&t0) == field_add(U_P0, W_P0));
        assert(fe51_as_canonical_nat(&t1) == field_sub(U_P0, W_P0));
        assert(fe51_as_canonical_nat(&t2) == field_add(U_Q0, W_Q0));
        assert(fe51_as_canonical_nat(&t3) == field_sub(U_Q0, W_Q0));

        assert(fe51_as_canonical_nat(&t6) == field_sub(
            fe51_as_canonical_nat(&t4),
            fe51_as_canonical_nat(&t5),
        ));
        assert(fe51_as_canonical_nat(&t7) == field_mul(
            fe51_as_canonical_nat(&t0),
            fe51_as_canonical_nat(&t3),
        ));
        assert(fe51_as_canonical_nat(&t8) == field_mul(
            fe51_as_canonical_nat(&t1),
            fe51_as_canonical_nat(&t2),
        ));
        assert(fe51_as_canonical_nat(&t9) == field_add(
            fe51_as_canonical_nat(&t7),
            fe51_as_canonical_nat(&t8),
        ));
        assert(fe51_as_canonical_nat(&t10) == field_sub(
            fe51_as_canonical_nat(&t7),
            fe51_as_canonical_nat(&t8),
        ));
        assert(fe51_as_canonical_nat(&t13) == field_mul(
            fe51_as_canonical_nat(&APLUS2_OVER_FOUR),
            fe51_as_canonical_nat(&t6),
        ));
        assert(fe51_as_canonical_nat(&t15) == field_add(
            fe51_as_canonical_nat(&t13),
            fe51_as_canonical_nat(&t5),
        ));
        assert(fe51_as_canonical_nat(&t14) == field_mul(
            fe51_as_canonical_nat(&t4),
            fe51_as_canonical_nat(&t5),
        ));
        assert(fe51_as_canonical_nat(&t16) == field_mul(
            fe51_as_canonical_nat(&t6),
            fe51_as_canonical_nat(&t15),
        ));
        assert(fe51_as_canonical_nat(&t17) == field_mul(u_diff, fe51_as_canonical_nat(&t12)));
        assert(fe51_as_canonical_nat(&t18) == fe51_as_canonical_nat(&t11));

        // The output coordinates match the nat-level xDBL/xADD specs.
        let (U2, W2) = spec_xdbl_projective(U_P0, W_P0);
        let (U3, W3) = spec_xadd_projective(U_P0, W_P0, U_Q0, W_Q0, u_diff);
        assert(fe51_as_canonical_nat(&P.U) == U2) by {
            assert(P.U == t14);
            reveal(spec_xdbl_projective);
            assert(U2 == field_mul(
                field_square(field_add(U_P0, W_P0)),
                field_square(field_sub(U_P0, W_P0)),
            ));
            assert(fe51_as_canonical_nat(&P.U) == fe51_as_canonical_nat(&t14));
        };
        assert(fe51_as_canonical_nat(&P.W) == W2) by {
            assert(P.W == t16);
            reveal(spec_xdbl_projective);
            assert(W2 == field_mul(
                field_sub(field_square(field_add(U_P0, W_P0)), field_square(field_sub(U_P0, W_P0))),
                field_add(
                    field_mul(
                        fe51_as_canonical_nat(&APLUS2_OVER_FOUR),
                        field_sub(
                            field_square(field_add(U_P0, W_P0)),
                            field_square(field_sub(U_P0, W_P0)),
                        ),
                    ),
                    field_square(field_sub(U_P0, W_P0)),
                ),
            ));
            assert(fe51_as_canonical_nat(&P.W) == fe51_as_canonical_nat(&t16));
        };
        assert(fe51_as_canonical_nat(&Q.U) == U3) by {
            assert(Q.U == t18);
            assert(t18 == t11);
            reveal(spec_xadd_projective);
            assert(U3 == field_square(
                field_add(
                    field_mul(field_add(U_P0, W_P0), field_sub(U_Q0, W_Q0)),
                    field_mul(field_sub(U_P0, W_P0), field_add(U_Q0, W_Q0)),
                ),
            ));
            assert(fe51_as_canonical_nat(&Q.U) == fe51_as_canonical_nat(&t11));
        };
        assert(fe51_as_canonical_nat(&Q.W) == W3) by {
            assert(Q.W == t17);
            reveal(spec_xadd_projective);
            assert(W3 == field_mul(
                u_diff,
                field_square(
                    field_sub(
                        field_mul(field_add(U_P0, W_P0), field_sub(U_Q0, W_Q0)),
                        field_mul(field_sub(U_P0, W_P0), field_add(U_Q0, W_Q0)),
                    ),
                ),
            ));
            assert(fe51_as_canonical_nat(&Q.W) == fe51_as_canonical_nat(&t17));
        };

        // Degenerate basepoint: u(P-Q)=0 and both inputs have u=0 => both outputs have u=0.
        if u_diff == 0 && spec_projective_u_coordinate(*old(P)) == 0
            && spec_projective_u_coordinate(*old(Q)) == 0 {
            // Q.W includes a factor of u_diff, so Q is ∞ and u(Q)=0.
            assert(fe51_as_canonical_nat(&Q.W) == 0) by {
                assert(Q.W == t17);
                assert(fe51_as_canonical_nat(&Q.W) == fe51_as_canonical_nat(&t17));
                assert(fe51_as_canonical_nat(&t17) == field_mul(
                    u_diff,
                    fe51_as_canonical_nat(&t12),
                ));
                // u_diff == 0 implies u_diff % p() == 0
                p_gt_2();
                lemma_small_mod(0nat, p());
                assert(u_diff % p() == 0);
                lemma_field_mul_zero_left(u_diff, fe51_as_canonical_nat(&t12));
                assert(field_mul(u_diff, fe51_as_canonical_nat(&t12)) == 0);
            };
            assert(spec_projective_u_coordinate(*Q) == 0);

            // For P, u(old(P))=0 implies either W=0 or U=0, which makes (U+W)^2 == (U-W)^2 and hence P.W=0.
            let U_old = fe51_as_canonical_nat(&old(P).U);
            let W_old = fe51_as_canonical_nat(&old(P).W);
            if W_old != 0 {
                // u = U/W = 0 => U = 0
                assert(W_old % p() != 0) by {
                    let W_raw = fe51_as_nat(&old(P).W);
                    assert(W_old == W_raw % p());
                    p_gt_2();
                    lemma_mod_division_less_than_divisor(W_raw as int, p() as int);
                    assert(W_old < p());
                    lemma_small_mod(W_old, p());
                    assert(W_old % p() == W_old);
                }
                assert(field_mul(U_old, field_inv(W_old)) == 0) by {
                    assert(spec_projective_u_coordinate(*old(P)) == field_mul(
                        U_old,
                        field_inv(W_old),
                    ));
                }
                lemma_inv_mul_cancel(W_old);
                lemma_field_mul_assoc(U_old, field_inv(W_old), W_old);
                assert(field_mul(field_mul(U_old, field_inv(W_old)), W_old) == field_mul(
                    U_old,
                    field_mul(field_inv(W_old), W_old),
                ));
                assert(field_mul(field_inv(W_old), W_old) == 1);
                lemma_field_mul_one_right(U_old);
                assert(field_mul(0, W_old) == 0) by {
                    lemma_field_mul_zero_left(0, W_old);
                }
                assert(U_old % p() == 0);
                assert(U_old == 0) by {
                    let U_raw = fe51_as_nat(&old(P).U);
                    assert(U_old == U_raw % p());
                    p_gt_2();
                    lemma_mod_division_less_than_divisor(U_raw as int, p() as int);
                    assert(U_old < p());
                    lemma_small_mod(U_old, p());
                    assert(U_old % p() == U_old);
                }
            }
            // xDBL produces W2=0 when U=0 or W=0

            assert(fe51_as_canonical_nat(&P.W) == 0) by {
                lemma_xdbl_degenerate_gives_w_zero(U_old, W_old);
            }
            assert(spec_projective_u_coordinate(*P) == 0);
        }
        // Case 1: P = [k]B, Q = [k+1]B  ==>  P' = [2k]B, Q' = [2k+1]B

        assert forall|k: nat|
            fe51_as_canonical_nat(affine_PmQ) != 0
                && #[trigger] projective_represents_montgomery_or_infinity(
                *old(P),
                montgomery_scalar_mul(B, k),
            ) && #[trigger] projective_represents_montgomery_or_infinity(
                *old(Q),
                montgomery_scalar_mul(B, k + 1),
            ) implies {
            &&& projective_represents_montgomery_or_infinity(*P, montgomery_scalar_mul(B, 2 * k))
            &&& projective_represents_montgomery_or_infinity(
                *Q,
                montgomery_scalar_mul(B, 2 * k + 1),
            )
        } by {
            if fe51_as_canonical_nat(affine_PmQ) != 0
                && projective_represents_montgomery_or_infinity(
                *old(P),
                montgomery_scalar_mul(B, k),
            ) && projective_represents_montgomery_or_infinity(
                *old(Q),
                montgomery_scalar_mul(B, k + 1),
            ) {
                let P_aff = montgomery_scalar_mul(B, k);
                let Q_aff = montgomery_scalar_mul(B, k + 1);

                // Lift projective representation facts to nat form for the xDBL/xADD axioms.
                assert(projective_represents_montgomery_or_infinity_nat(U_P0, W_P0, P_aff)) by {
                    match P_aff {
                        MontgomeryAffine::Infinity => {
                            assert(W_P0 == 0);
                            assert(U_P0 != 0);
                        },
                        MontgomeryAffine::Finite { u, v: _ } => {
                            assert(W_P0 != 0);
                            assert(U_P0 == field_mul(u, W_P0));
                        },
                    }
                }
                assert(projective_represents_montgomery_or_infinity_nat(U_Q0, W_Q0, Q_aff)) by {
                    match Q_aff {
                        MontgomeryAffine::Infinity => {
                            assert(W_Q0 == 0);
                            assert(U_Q0 != 0);
                        },
                        MontgomeryAffine::Finite { u, v: _ } => {
                            assert(W_Q0 != 0);
                            assert(U_Q0 == field_mul(u, W_Q0));
                        },
                    }
                }

                // xDBL: output P represents montgomery_add(P_aff, P_aff) = [2k]B
                axiom_xdbl_projective_correct(P_aff, U_P0, W_P0);
                assert(projective_represents_montgomery_or_infinity_nat(
                    fe51_as_canonical_nat(&P.U),
                    fe51_as_canonical_nat(&P.W),
                    montgomery_add(P_aff, P_aff),
                )) by {
                    assert((fe51_as_canonical_nat(&P.U), fe51_as_canonical_nat(&P.W)) == (U2, W2));
                }
                assert(projective_represents_montgomery_or_infinity(
                    *P,
                    montgomery_add(P_aff, P_aff),
                )) by {
                    match montgomery_add(P_aff, P_aff) {
                        MontgomeryAffine::Infinity => {
                            assert(fe51_as_canonical_nat(&P.W) == 0);
                        },
                        MontgomeryAffine::Finite { u, v: _ } => {
                            assert(fe51_as_canonical_nat(&P.W) != 0);
                            assert(fe51_as_canonical_nat(&P.U) == field_mul(
                                u,
                                fe51_as_canonical_nat(&P.W),
                            ));
                        },
                    }
                }
                lemma_montgomery_scalar_mul_double(B, k);

                // xADD: output Q represents montgomery_add(P_aff, Q_aff) = [2k+1]B
                lemma_montgomery_scalar_mul_succ(B, k);
                assert(Q_aff == montgomery_add(B, P_aff));
                assert(B != MontgomeryAffine::Infinity);
                assert(P_aff != Q_aff) by {
                    if P_aff == Q_aff {
                        assert(montgomery_add(B, P_aff) == P_aff);
                        axiom_montgomery_add_associative(B, P_aff, montgomery_neg(P_aff));
                        axiom_montgomery_add_inverse(P_aff);
                        axiom_montgomery_add_identity(B);
                        assert(B == MontgomeryAffine::Infinity);
                        assert(false);
                    }
                }
                assert(montgomery_sub(Q_aff, P_aff) == B) by {
                    axiom_montgomery_add_associative(B, P_aff, montgomery_neg(P_aff));
                    axiom_montgomery_add_inverse(P_aff);
                    axiom_montgomery_add_identity(B);
                }
                axiom_xadd_projective_correct(P_aff, Q_aff, U_P0, W_P0, U_Q0, W_Q0, u_diff);
                assert(projective_represents_montgomery_or_infinity(
                    *Q,
                    montgomery_add(P_aff, Q_aff),
                ));
                lemma_montgomery_scalar_mul_add(B, k, k + 1);
                assert(k + (k + 1) == 2 * k + 1);
            }
        };

        // Case 2: P = [k+1]B, Q = [k]B  ==>  P' = [2k+2]B, Q' = [2k+1]B
        assert forall|k: nat|
            fe51_as_canonical_nat(affine_PmQ) != 0
                && #[trigger] projective_represents_montgomery_or_infinity(
                *old(P),
                montgomery_scalar_mul(B, k + 1),
            ) && #[trigger] projective_represents_montgomery_or_infinity(
                *old(Q),
                montgomery_scalar_mul(B, k),
            ) implies {
            &&& projective_represents_montgomery_or_infinity(
                *P,
                montgomery_scalar_mul(B, 2 * k + 2),
            )
            &&& projective_represents_montgomery_or_infinity(
                *Q,
                montgomery_scalar_mul(B, 2 * k + 1),
            )
        } by {
            if fe51_as_canonical_nat(affine_PmQ) != 0
                && projective_represents_montgomery_or_infinity(
                *old(P),
                montgomery_scalar_mul(B, k + 1),
            ) && projective_represents_montgomery_or_infinity(
                *old(Q),
                montgomery_scalar_mul(B, k),
            ) {
                let P_aff = montgomery_scalar_mul(B, k + 1);
                let Q_aff = montgomery_scalar_mul(B, k);

                // xDBL: output P represents [2]P_aff = [2k+2]B
                assert(projective_represents_montgomery_or_infinity_nat(U_P0, W_P0, P_aff)) by {
                    match P_aff {
                        MontgomeryAffine::Infinity => {
                            assert(W_P0 == 0);
                            assert(U_P0 != 0);
                        },
                        MontgomeryAffine::Finite { u, v: _ } => {
                            assert(W_P0 != 0);
                            assert(U_P0 == field_mul(u, W_P0));
                        },
                    }
                }
                axiom_xdbl_projective_correct(P_aff, U_P0, W_P0);
                assert(projective_represents_montgomery_or_infinity(
                    *P,
                    montgomery_add(P_aff, P_aff),
                ));
                lemma_montgomery_scalar_mul_double(B, k + 1);
                assert(2 * (k + 1) == 2 * k + 2);

                // xADD: output Q represents P_aff + Q_aff = [2k+1]B
                lemma_montgomery_scalar_mul_succ(B, k);
                assert(P_aff == montgomery_add(B, Q_aff));
                assert(P_aff != Q_aff) by {
                    if P_aff == Q_aff {
                        assert(montgomery_add(B, Q_aff) == Q_aff);
                        axiom_montgomery_add_associative(B, Q_aff, montgomery_neg(Q_aff));
                        axiom_montgomery_add_inverse(Q_aff);
                        axiom_montgomery_add_identity(B);
                        assert(B == MontgomeryAffine::Infinity);
                        assert(false);
                    }
                }
                assert(montgomery_sub(P_aff, Q_aff) == B) by {
                    axiom_montgomery_add_associative(B, Q_aff, montgomery_neg(Q_aff));
                    axiom_montgomery_add_inverse(Q_aff);
                    axiom_montgomery_add_identity(B);
                }
                axiom_xadd_projective_correct(P_aff, Q_aff, U_P0, W_P0, U_Q0, W_Q0, u_diff);
                assert(projective_represents_montgomery_or_infinity(
                    *Q,
                    montgomery_add(P_aff, Q_aff),
                ));
                lemma_montgomery_scalar_mul_add(B, k + 1, k);
                assert((k + 1) + k == 2 * k + 1);
            }
        };
    }
}

define_mul_assign_variants!(LHS = MontgomeryPoint, RHS = Scalar);

define_mul_variants_verus!(
    LHS = MontgomeryPoint,
    RHS = Scalar,
    Output = MontgomeryPoint
);

define_mul_variants_verus!(
    LHS = Scalar,
    RHS = MontgomeryPoint,
    Output = MontgomeryPoint
);

// NOTE: MulSpecImpl for &MontgomeryPoint * &Scalar in arithm_trait_specs.rs
/// Multiply this `MontgomeryPoint` by a `Scalar`.
impl Mul<&Scalar> for &MontgomeryPoint {
    type Output = MontgomeryPoint;

    /// Given `self` \\( = u\_0(P) \\), and a `Scalar` \\(n\\), return \\( u\_0(\[n\]P) \\)
    ///
    fn mul(self, scalar: &Scalar) -> (result: MontgomeryPoint)
        ensures
    // The canonical Montgomery lift point P corresponding to this u-coordinate
    // is multiplied by the unreduced scalar value

            ({
                let P = canonical_montgomery_lift(spec_montgomery(*self));
                let n_unreduced = scalar_as_nat(scalar);
                let R = montgomery_scalar_mul(P, n_unreduced);
                spec_montgomery(result) == spec_u_coordinate(R)
            }),
    {
        // We multiply by the integer representation of the given Scalar. By scalar invariant #1,
        // the MSB is 0, so we can skip it.
        /* ORIGINAL CODE (using Iterator):
        self.mul_bits_be(scalar.bits_le().rev().skip(1))
        */
        // Verus-compatible version: use bits_le()  to get array, then reverse and skip MSB
        let bits_le = scalar.bits_le();
        let mut bits_be = [false;255];
        let mut i = 0;
        while i < 255
            invariant
                i <= 255,
                forall|j: int| 0 <= j < i as int ==> bits_be[j] == bits_le[254 - j],
            decreases 255 - i,
        {
            bits_be[i] = bits_le[254 - i];
            i += 1;
        }
        let bits_be_slice: &[bool] = &bits_be;
        /* ORIGINAL CODE:
        let result = self.mul_bits_be(&bits_be);
        */
        let result = self.mul_bits_be(bits_be_slice);
        proof {
            // Show that the 255-bit slice `bits_be` represents the same integer as `scalar`.
            // We rely on scalar invariant #1 (MSB is clear), i.e. scalar.bytes[31] <= 127.
            assert(scalar.bytes[31] <= 127);

            let scalar_bytes = &scalar.bytes;
            assert(bits_as_nat(&bits_le) == u8_32_as_nat(scalar_bytes));
            assert(bits_as_nat(&bits_le) < pow2(255)) by {
                lemma_u8_32_as_nat_lt_pow2_255(scalar_bytes);
            }

            assert(!bits_le[255]) by {
                lemma_bits_as_nat_lt_pow2_255_implies_msb_false(&bits_le);
            }

            assert(bits_be_slice.len() == 255);
            assert(bits_be_slice.len() as int == 255);
            assert(i == 255);
            assert(forall|j: int| 0 <= j < 255 ==> #[trigger] bits_be_slice[j] == bits_le[254 - j])
                by {
                assert(forall|j: int| 0 <= j < i as int ==> bits_be[j] == bits_le[254 - j]);
            }

            // Interpret the big-endian bits as a nat.
            let n = bits_be_as_nat(bits_be_slice, 255);
            assert(n == bits_from_index_to_nat(&bits_le, 0, 255)) by {
                lemma_bits_be_as_nat_eq_bits_from_index(&bits_le, bits_be_slice, 255);
                assert((255 - 255) as nat == 0);
            }

            // Since the MSB is 0, the 255-bit view equals the full 256-bit value.
            assert(n == bits_as_nat(&bits_le)) by {
                lemma_bits_as_nat_eq_bits_from_index(&bits_le);
                lemma_bits_from_index_to_nat_split_last(&bits_le, 0, 255);
                assert((if bits_le[255] {
                    1nat
                } else {
                    0nat
                }) == 0nat);
                assert(bits_from_index_to_nat(&bits_le, 0, 256) == bits_from_index_to_nat(
                    &bits_le,
                    0,
                    255,
                ));
            }

            // Conclude the scalar value matches the bits interpreted by mul_bits_be.
            assert(n == scalar_as_nat(scalar)) by {
                assert(scalar_as_nat(scalar) == u8_32_as_nat(scalar_bytes));
                assert(n == bits_as_nat(&bits_le));
            }
        }
        result
    }
}

impl MulAssign<&Scalar> for MontgomeryPoint {
    fn mul_assign(&mut self, scalar: &Scalar)
        requires
            is_valid_montgomery_point(*old(self)),
            scalar.bytes[31] <= 127,
        ensures
    // Result represents [n]old(self) where n is the UNREDUCED scalar value
    // Uses canonical Montgomery lift

            ({
                let P = canonical_montgomery_lift(spec_montgomery(*old(self)));
                let n_unreduced = scalar_as_nat(scalar);
                let R = montgomery_scalar_mul(P, n_unreduced);
                spec_montgomery(*self) == spec_u_coordinate(R)
            }),
    {
        *self = &*self * scalar;
    }
}

// NOTE: MulSpecImpl for &Scalar * &MontgomeryPoint in arithm_trait_specs.rs
impl Mul<&MontgomeryPoint> for &Scalar {
    type Output = MontgomeryPoint;

    /* VERIFICATION NOTE
     -This operation is commutative and delegates to `point * scalar`.
       See the documentation for `&MontgomeryPoint * &Scalar` for details.
     */
    fn mul(self, point: &MontgomeryPoint) -> (result: MontgomeryPoint)
        ensures
    // Delegates to point * self, which multiplies by the unreduced scalar using canonical lift

            ({
                let P = canonical_montgomery_lift(spec_montgomery(*point));
                let n_unreduced = scalar_as_nat(self);
                let R = montgomery_scalar_mul(P, n_unreduced);
                spec_montgomery(result) == spec_u_coordinate(R)
            }),
    {
        point * self
    }
}

// NOTE: MulSpecImpl and owned-type Mul implementations for Scalar * MontgomeryPoint
// are in arithm_trait_specs.rs
} // verus!
// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------
// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::constants;
//     #[cfg(feature = "alloc")]
//     use alloc::vec::Vec;
//     use rand_core::{CryptoRng, RngCore};
//     #[test]
//     fn identity_in_different_coordinates() {
//         let id_projective = ProjectivePoint::identity();
//         let id_montgomery = id_projective.as_affine();
//         assert!(id_montgomery == MontgomeryPoint::identity());
//     }
//     #[test]
//     fn identity_in_different_models() {
//         assert!(EdwardsPoint::identity().to_montgomery() == MontgomeryPoint::identity());
//     }
//     #[test]
//     #[cfg(feature = "serde")]
//     fn serde_bincode_basepoint_roundtrip() {
//         use bincode;
//         let encoded = bincode::serialize(&constants::X25519_BASEPOINT).unwrap();
//         let decoded: MontgomeryPoint = bincode::deserialize(&encoded).unwrap();
//         assert_eq!(encoded.len(), 32);
//         assert_eq!(decoded, constants::X25519_BASEPOINT);
//         let raw_bytes = constants::X25519_BASEPOINT.as_bytes();
//         let bp: MontgomeryPoint = bincode::deserialize(raw_bytes).unwrap();
//         assert_eq!(bp, constants::X25519_BASEPOINT);
//     }
//     /// Test Montgomery -> Edwards on the X/Ed25519 basepoint
//     #[test]
//     fn basepoint_montgomery_to_edwards() {
//         // sign bit = 0 => basepoint
//         assert_eq!(
//             constants::ED25519_BASEPOINT_POINT,
//             constants::X25519_BASEPOINT.to_edwards(0).unwrap()
//         );
//         // sign bit = 1 => minus basepoint
//         assert_eq!(
//             -constants::ED25519_BASEPOINT_POINT,
//             constants::X25519_BASEPOINT.to_edwards(1).unwrap()
//         );
//     }
//     /// Test Edwards -> Montgomery on the X/Ed25519 basepoint
//     #[test]
//     fn basepoint_edwards_to_montgomery() {
//         assert_eq!(
//             constants::ED25519_BASEPOINT_POINT.to_montgomery(),
//             constants::X25519_BASEPOINT
//         );
//     }
//     /// Check that Montgomery -> Edwards fails for points on the twist.
//     #[test]
//     fn montgomery_to_edwards_rejects_twist() {
//         let one = FieldElement::ONE;
//         // u = 2 corresponds to a point on the twist.
//         let two = MontgomeryPoint((&one + &one).as_bytes());
//         assert!(two.to_edwards(0).is_none());
//         // u = -1 corresponds to a point on the twist, but should be
//         // checked explicitly because it's an exceptional point for the
//         // birational map.  For instance, libsignal will accept it.
//         let minus_one = MontgomeryPoint((-&one).as_bytes());
//         assert!(minus_one.to_edwards(0).is_none());
//     }
//     #[test]
//     fn eq_defined_mod_p() {
//         let mut u18_bytes = [0u8; 32];
//         u18_bytes[0] = 18;
//         let u18 = MontgomeryPoint(u18_bytes);
//         let u18_unred = MontgomeryPoint([255; 32]);
//         assert_eq!(u18, u18_unred);
//     }
//     /// Returns a random point on the prime-order subgroup
//     fn rand_prime_order_point(mut rng: impl RngCore + CryptoRng) -> EdwardsPoint {
//         let s: Scalar = Scalar::random(&mut rng);
//         EdwardsPoint::mul_base(&s)
//     }
//     /// Given a bytestring that's little-endian at the byte level, return an iterator over all the
//     /// bits, in little-endian order.
//     fn bytestring_bits_le(x: &[u8]) -> impl DoubleEndedIterator<Item = bool> + Clone + '_ {
//         let bitlen = x.len() * 8;
//         (0..bitlen).map(|i| {
//             // As i runs from 0..256, the bottom 3 bits index the bit, while the upper bits index
//             // the byte. Since self.bytes is little-endian at the byte level, this iterator is
//             // little-endian on the bit level
//             ((x[i >> 3] >> (i & 7)) & 1u8) == 1
//         })
//     }
//     #[test]
//     fn montgomery_ladder_matches_edwards_scalarmult() {
//         let mut csprng = rand_core::OsRng;
//         for _ in 0..100 {
//             let p_edwards = rand_prime_order_point(&mut csprng);
//             let p_montgomery: MontgomeryPoint = p_edwards.to_montgomery();
//             let s: Scalar = Scalar::random(&mut csprng);
//             let expected = s * p_edwards;
//             let result = s * p_montgomery;
//             assert_eq!(result, expected.to_montgomery())
//         }
//     }
//     // Tests that, on the prime-order subgroup, MontgomeryPoint::mul_bits_be is the same as
//     // multiplying by the Scalar representation of the same bits
//     #[test]
//     fn montgomery_mul_bits_be() {
//         let mut csprng = rand_core::OsRng;
//         for _ in 0..100 {
//             // Make a random prime-order point P
//             let p_edwards = rand_prime_order_point(&mut csprng);
//             let p_montgomery: MontgomeryPoint = p_edwards.to_montgomery();
//             // Make a random integer b
//             let mut bigint = [0u8; 64];
//             csprng.fill_bytes(&mut bigint[..]);
//             let bigint_bits_be = bytestring_bits_le(&bigint).rev();
//             // Check that bP is the same whether calculated as scalar-times-edwards or
//             // integer-times-montgomery.
//             let expected = Scalar::from_bytes_mod_order_wide(&bigint) * p_edwards;
//             let result = p_montgomery.mul_bits_be(bigint_bits_be);
//             assert_eq!(result, expected.to_montgomery())
//         }
//     }
//     // Tests that MontgomeryPoint::mul_bits_be is consistent on any point, even ones that might be
//     // on the curve's twist. Specifically, this tests that b₁(b₂P) == b₂(b₁P) for random
//     // integers b₁, b₂ and random (curve or twist) point P.
//     #[test]
//     fn montgomery_mul_bits_be_twist() {
//         let mut csprng = rand_core::OsRng;
//         for _ in 0..100 {
//             // Make a random point P on the curve or its twist
//             let p_montgomery = {
//                 let mut buf = [0u8; 32];
//                 csprng.fill_bytes(&mut buf);
//                 MontgomeryPoint(buf)
//             };
//             // Compute two big integers b₁ and b₂
//             let mut bigint1 = [0u8; 64];
//             let mut bigint2 = [0u8; 64];
//             csprng.fill_bytes(&mut bigint1[..]);
//             csprng.fill_bytes(&mut bigint2[..]);
//             // Compute b₁P and b₂P
//             let bigint1_bits_be = bytestring_bits_le(&bigint1).rev();
//             let bigint2_bits_be = bytestring_bits_le(&bigint2).rev();
//             let prod1 = p_montgomery.mul_bits_be(bigint1_bits_be.clone());
//             let prod2 = p_montgomery.mul_bits_be(bigint2_bits_be.clone());
//             // Check that b₁(b₂P) == b₂(b₁P)
//             assert_eq!(
//                 prod1.mul_bits_be(bigint2_bits_be),
//                 prod2.mul_bits_be(bigint1_bits_be)
//             );
//         }
//     }
//     /// Check that mul_base_clamped and mul_clamped agree
//     #[test]
//     fn mul_base_clamped() {
//         let mut csprng = rand_core::OsRng;
//         // Test agreement on a large integer. Even after clamping, this is not reduced mod l.
//         let a_bytes = [0xff; 32];
//         assert_eq!(
//             MontgomeryPoint::mul_base_clamped(a_bytes),
//             constants::X25519_BASEPOINT.mul_clamped(a_bytes)
//         );
//         // Test agreement on random integers
//         for _ in 0..100 {
//             // This will be reduced mod l with probability l / 2^256 ≈ 6.25%
//             let mut a_bytes = [0u8; 32];
//             csprng.fill_bytes(&mut a_bytes);
//             assert_eq!(
//                 MontgomeryPoint::mul_base_clamped(a_bytes),
//                 constants::X25519_BASEPOINT.mul_clamped(a_bytes)
//             );
//         }
//     }
//     #[cfg(feature = "alloc")]
//     const ELLIGATOR_CORRECT_OUTPUT: [u8; 32] = [
//         0x5f, 0x35, 0x20, 0x00, 0x1c, 0x6c, 0x99, 0x36, 0xa3, 0x12, 0x06, 0xaf, 0xe7, 0xc7, 0xac,
//         0x22, 0x4e, 0x88, 0x61, 0x61, 0x9b, 0xf9, 0x88, 0x72, 0x44, 0x49, 0x15, 0x89, 0x9d, 0x95,
//         0xf4, 0x6e,
//     ];
//     #[test]
//     #[cfg(feature = "alloc")]
//     fn montgomery_elligator_correct() {
//         let bytes: Vec<u8> = (0u8..32u8).collect();
//         let bits_in: [u8; 32] = (&bytes[..]).try_into().expect("Range invariant broken");
//         let fe = FieldElement::from_bytes(&bits_in);
//         let eg = elligator_encode(&fe);
//         assert_eq!(eg.to_bytes(), ELLIGATOR_CORRECT_OUTPUT);
//     }
//     #[test]
//     fn montgomery_elligator_zero_zero() {
//         let zero = [0u8; 32];
//         let fe = FieldElement::from_bytes(&zero);
//         let eg = elligator_encode(&fe);
//         assert_eq!(eg.to_bytes(), zero);
//     }
// }
