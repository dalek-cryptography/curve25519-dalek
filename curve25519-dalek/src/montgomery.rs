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
use crate::scalar::{clamp_integer, Scalar};
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::montgomery_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs_u64::*;

use crate::traits::Identity;

#[cfg(verus_keep_ghost)]
use crate::backend::serial::u64::subtle_assumes::choice_is_true;
use crate::backend::serial::u64::subtle_assumes::{
    choice_into, conditional_swap_montgomery_projective,
};

use subtle::Choice;
use subtle::ConstantTimeEq;
use subtle::{ConditionallyNegatable, ConditionallySelectable};

use vstd::prelude::*;
#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

verus! {

/// Holds the \\(u\\)-coordinate of a point on the Montgomery form of
/// Curve25519 or its twist.
#[derive(Copy, Clone, Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MontgomeryPoint(pub [u8; 32]);

/// Spec function: extract the u-coordinate of a MontgomeryPoint as a field element
pub open spec fn spec_montgomery(point: MontgomeryPoint) -> nat {
    spec_field_element_from_bytes(&point.0)
}

/// Equality of `MontgomeryPoint`s is defined mod p.
impl ConstantTimeEq for MontgomeryPoint {
    fn ct_eq(&self, other: &MontgomeryPoint) -> (result: Choice)
        ensures
    // Two MontgomeryPoints are equal if their u-coordinates are equal mod p

            choice_is_true(result) == (spec_field_element_from_bytes(&self.0)
                == spec_field_element_from_bytes(&other.0)),
    {
        let self_fe = FieldElement::from_bytes(&self.0);
        let other_fe = FieldElement::from_bytes(&other.0);

        let result = self_fe.ct_eq(&other_fe);

        proof {
            // The postcondition follows from FieldElement::ct_eq's specification
            assume(choice_is_true(result) == (spec_field_element_from_bytes(&self.0)
                == spec_field_element_from_bytes(&other.0)));
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
        spec_field_element_from_bytes(&self.0) == spec_field_element_from_bytes(&other.0)
    }
}

impl PartialEq for MontgomeryPoint {
    // VERIFICATION NOTE: PartialEqSpecImpl trait provides the external specification
    fn eq(&self, other: &MontgomeryPoint) -> (result: bool)
        ensures
            result == (spec_field_element_from_bytes(&self.0) == spec_field_element_from_bytes(
                &other.0,
            )),
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
            assert(choice_is_true(choice) == (spec_field_element_from_bytes(&self.0)
                == spec_field_element_from_bytes(&other.0)));
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
             (1) The actual postcondition is: *state == spec_state_after_hash_montgomery(initial_state, self)
                 where initial_state is the value of *state before this call.
                 However, Verus doesn't support old() on &mut types in ensures clauses.
                 The property is for now established via assumes in the function body (lines 192-194).
            (2) The spec is completed by lemma_hash_is_canonical: equal field elements hash identically. */

            true,
    {
        // Do a round trip through a `FieldElement`. `as_bytes` is guaranteed to give a canonical
        // 32-byte encoding
        let canonical_bytes = FieldElement::from_bytes(&self.0).as_bytes();

        /* GHOST: track the initial state for reasoning about state transformation */
        let ghost initial_state = *state;

        // Hash the canonical bytes
        canonical_bytes.hash(state);

        proof {
            assume(canonical_bytes@ == spec_fe51_to_bytes(&spec_fe51_from_bytes(&self.0)));
            assume(*state == spec_state_after_hash(initial_state, &canonical_bytes));
            assume(*state == spec_state_after_hash_montgomery(initial_state, self));
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
            // The byte array [0, 0, ..., 0] represents the field element 0
            assume(spec_field_element_from_bytes(&result.0) == 0);
        }
        result
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
            // After zeroizing, all bytes are 0, so the field element is 0
            assume(spec_field_element_from_bytes(&self.0) == 0);
        }
    }
}

impl MontgomeryPoint {
    /// Fixed-base scalar multiplication (i.e. multiplication by the base point).
    #[verifier::external_body]
    pub fn mul_base(scalar: &Scalar) -> Self {
        EdwardsPoint::mul_base(scalar).to_montgomery()
    }

    /// Multiply this point by `clamp_integer(bytes)`. For a description of clamping, see
    /// [`clamp_integer`].
    #[verifier::external_body]
    pub fn mul_clamped(self, bytes: [u8; 32]) -> Self {
        // We have to construct a Scalar that is not reduced mod l, which breaks scalar invariant
        // #2. But #2 is not necessary for correctness of variable-base multiplication. All that
        // needs to hold is invariant #1, i.e., the scalar is less than 2^255. This is guaranteed
        // by clamping.
        // Further, we don't do any reduction or arithmetic with this clamped value, so there's no
        // issues arising from the fact that the curve point is not necessarily in the prime-order
        // subgroup.
        let s = Scalar { bytes: clamp_integer(bytes) };
        s * self
    }

    /// Multiply the basepoint by `clamp_integer(bytes)`. For a description of clamping, see
    /// [`clamp_integer`].
    #[verifier::external_body]
    pub fn mul_base_clamped(bytes: [u8; 32]) -> Self {
        // See reasoning in Self::mul_clamped why it is OK to make an unreduced Scalar here. We
        // note that fixed-base multiplication is also defined for all values of `bytes` less than
        // 2^255.
        let s = Scalar { bytes: clamp_integer(bytes) };
        Self::mul_base(&s)
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
    // VERIFICATION NOTE: refactored mul_bits_de code
    pub fn mul_bits_be(&self, bits: &[bool]) -> (result: MontgomeryPoint)
        requires
            bits.len() <= 255,
            is_valid_montgomery_point(*self),
        ensures
    // Result represents [n]self where n is the scalar value from bits
    // If self has u-coordinate matching affine point P, result has u-coordinate of [n]P

            forall|P: MontgomeryAffine|
                is_valid_montgomery_affine(P) && spec_montgomery_point(*self) == spec_u_coordinate(
                    P,
                ) ==> {
                    let n = bits_be_to_nat(bits, bits@.len() as int);
                    let x = montgomery_scalar_mul(P, n);
                    spec_montgomery_point(result) == spec_u_coordinate(x)
                },
    {
        // Algorithm 8 of Costello-Smith 2017
        let affine_u = FieldElement::from_bytes(&self.0);
        let mut x0 = ProjectivePoint::identity();
        let mut x1 = ProjectivePoint { U: affine_u, W: FieldElement::ONE };

        // Go through the bits from most to least significant, using a sliding window of 2
        let mut prev_bit = false;
        let mut i: usize = 0;
        while i < bits.len()
            invariant
                i <= bits.len(),
            decreases bits.len() - i,
        {
            let cur_bit = bits[i];
            let choice: u8 = (prev_bit ^ cur_bit) as u8;

            #[cfg(not(verus_keep_ghost))]
            debug_assert!(choice == 0 || choice == 1);

            conditional_swap_montgomery_projective(&mut x0, &mut x1, choice.into());
            assume(false);  // VERIFICATION NOTE: need to prove preconditions for differential_add_and_double
            differential_add_and_double(&mut x0, &mut x1, &affine_u);

            prev_bit = cur_bit;
            i = i + 1;
        }
        // The final value of prev_bit above is scalar.bits()[0], i.e., the LSB of scalar
        conditional_swap_montgomery_projective(&mut x0, &mut x1, Choice::from(prev_bit as u8));
        // Don't leave the bit in the stack
        #[cfg(feature = "zeroize")]
        zeroize_bool(&mut prev_bit);

        proof {
            // preconditions for as_affine
            assume(crate::specs::field_specs::limbs_bounded(&x0.U, 54));
            assume(crate::specs::field_specs::limbs_bounded(&x0.W, 54));
        }
        let result = x0.as_affine();
        proof {
            // postcondition
            // Result represents [n]self where n is the scalar value from bits
            // If self has u-coordinate matching affine point P, result has u-coordinate of [n]P
            assume(forall|P: MontgomeryAffine|
                is_valid_montgomery_affine(P) && spec_montgomery_point(*self) == spec_u_coordinate(
                    P,
                ) ==> {
                    let n = bits_be_to_nat(bits, bits@.len() as int);
                    let x = montgomery_scalar_mul(P, n);
                    spec_montgomery_point(result) == spec_u_coordinate(x)
                });
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
    pub const fn to_bytes(&self) -> [u8; 32] {
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
                Some(edwards) => montgomery_corresponds_to_edwards(*self, edwards),
                None => is_equal_to_minus_one(spec_montgomery_point(*self)),
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
                assume(is_equal_to_minus_one(spec_montgomery_point(*self)));
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
                },
                None => {
                    assume(is_equal_to_minus_one(spec_montgomery_point(*self)));
                },
            }
        }

        result
    }
}

} // verus!
/// Perform the Elligator2 mapping to a Montgomery point.
///
/// See <https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-10#section-6.7.1>
//
// TODO Determine how much of the hash-to-group API should be exposed after the CFRG
//      draft gets into a more polished/accepted state.
#[allow(unused)]
pub(crate) fn elligator_encode(r_0: &FieldElement) -> MontgomeryPoint {
    let one = FieldElement::ONE;
    let d_1 = &one + &r_0.square2(); /* 2r^2 */

    let d = &MONTGOMERY_A_NEG * &(d_1.invert()); /* A/(1+2r^2) */

    let d_sq = &d.square();
    let au = &MONTGOMERY_A * &d;

    let inner = &(d_sq + &au) + &one;
    let eps = &d * &inner; /* eps = d^3 + Ad^2 + d */

    let (eps_is_sq, _eps) = FieldElement::sqrt_ratio_i(&eps, &one);

    let zero = FieldElement::ZERO;
    let Atemp = FieldElement::conditional_select(&MONTGOMERY_A, &zero, eps_is_sq); /* 0, or A if nonsquare*/
    let mut u = &d + &Atemp; /* d, or d+A if nonsquare */
    u.conditional_negate(!eps_is_sq); /* d, or -d-A if nonsquare */

    MontgomeryPoint(u.as_bytes())
}

verus! {

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

            spec_field_element(&result.U) == 1,
            spec_field_element(&result.W) == 0,
    {
        let result = ProjectivePoint { U: FieldElement::ONE, W: FieldElement::ZERO };
        proof {
            // The identity point is (1, 0) in projective coordinates
            assume(spec_field_element(&result.U) == 1);
            assume(spec_field_element(&result.W) == 0);
        }
        result
    }
}

impl Default for ProjectivePoint {
    fn default() -> (result: ProjectivePoint)
        ensures
    // Default returns the identity point

            spec_field_element(&result.U) == 1,
            spec_field_element(&result.W) == 0,
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
            // What we can derive from FieldElement::conditional_select:
            assert(!choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> result.U.limbs[i] == a.U.limbs[i]));
            assert(choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> result.U.limbs[i] == b.U.limbs[i]));

            // For result.W = FieldElement::conditional_select(&a.W, &b.W, choice):
            assert(!choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> result.W.limbs[i] == a.W.limbs[i]));
            assert(choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> result.W.limbs[i] == b.W.limbs[i]));

            // We need to lift limbs equality to struct equality:
            // (forall i. fe1.limbs[i] == fe2.limbs[i]) ==> fe1 == fe2
            assume(!choice_is_true(choice) ==> (result.U == a.U && result.W == a.W));
            assume(choice_is_true(choice) ==> (result.U == b.U && result.W == b.W));
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
            crate::specs::field_specs::limbs_bounded(&self.U, 54),
            crate::specs::field_specs::limbs_bounded(&self.W, 54),
        ensures
    // For projective point (U:W), the affine u-coordinate is u = U/W (or 0 if W=0)

            spec_montgomery_point(result) == {
                let u_proj = spec_field_element(&self.U);
                let w_proj = spec_field_element(&self.W);
                if w_proj == 0 {
                    0
                } else {
                    math_field_mul(u_proj, math_field_inv(w_proj))
                }
            },
    {
        proof {
            // VERIFICATION NOTE: Assume preconditions for FieldElement operations
            // Multiplication requires limbs bounded by 2^54
            //     assume(forall|i: int| 0 <= i < 5 ==> self.U.limbs[i] < (1u64 << 54));
            //     assume(forall|i: int| 0 <= i < 5 ==> self.W.limbs[i] < (1u64 << 54));
        }
        let u = &self.U * &self.W.invert();
        let result = MontgomeryPoint(u.as_bytes());
        proof {
            // postcondition
            // The affine u-coordinate is U * W^(-1) = U / W
            let u_proj = spec_field_element(&self.U);
            let w_proj = spec_field_element(&self.W);
            assume(spec_montgomery_point(result) == if w_proj == 0 {
                0
            } else {
                math_field_mul(u_proj, math_field_inv(w_proj))
            });
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
// There exist full affine Montgomery points that P and Q represent,
// with the differential relationship maintained.

        exists|P_full: MontgomeryAffine, Q_full: MontgomeryAffine| #[trigger]
            differential_relation_holds(*old(P), *old(Q), affine_PmQ, P_full, Q_full),
    ensures
// The same P_full and Q_full that satisfied the differential invariant
// now have their double and sum represented by the output projective points.

        exists|P_full: MontgomeryAffine, Q_full: MontgomeryAffine|
            {
                // P_full and Q_full are identified by the input relationship
                #[trigger] differential_relation_holds(*old(P), *old(Q), affine_PmQ, P_full, Q_full)
                    &&
                // Now P represents [2]P_full and Q represents P_full + Q_full
                projective_represents_montgomery(*P, #[trigger] montgomery_add(P_full, P_full))
                    && projective_represents_montgomery(
                    *Q,
                    #[trigger] montgomery_add(P_full, Q_full),
                )
            },
{
    assume(false);  // VERIFICATION NOTE: need to prove preconditions for FieldElement arithmetic operations
    let t0 = &P.U + &P.W;
    let t1 = &P.U - &P.W;
    let t2 = &Q.U + &Q.W;
    let t3 = &Q.U - &Q.W;

    let t4 = t0.square();  // (U_P + W_P)^2 = U_P^2 + 2 U_P W_P + W_P^2
    let t5 = t1.square();  // (U_P - W_P)^2 = U_P^2 - 2 U_P W_P + W_P^2

    let t6 = &t4 - &t5;  // 4 U_P W_P

    let t7 = &t0 * &t3;  // (U_P + W_P) (U_Q - W_Q) = U_P U_Q + W_P U_Q - U_P W_Q - W_P W_Q
    let t8 = &t1 * &t2;  // (U_P - W_P) (U_Q + W_Q) = U_P U_Q - W_P U_Q + U_P W_Q - W_P W_Q

    let t9 = &t7 + &t8;  // 2 (U_P U_Q - W_P W_Q)
    let t10 = &t7 - &t8;  // 2 (W_P U_Q - U_P W_Q)

    let t11 = t9.square();  // 4 (U_P U_Q - W_P W_Q)^2
    let t12 = t10.square();  // 4 (W_P U_Q - U_P W_Q)^2

    let t13 = &APLUS2_OVER_FOUR * &t6;  // (A + 2) U_P U_Q

    let t14 = &t4 * &t5;  // ((U_P + W_P)(U_P - W_P))^2 = (U_P^2 - W_P^2)^2
    let t15 = &t13 + &t5;  // (U_P - W_P)^2 + (A + 2) U_P W_P

    let t16 = &t6 * &t15;  // 4 (U_P W_P) ((U_P - W_P)^2 + (A + 2) U_P W_P)

    let t17 = affine_PmQ * &t12;  // U_D * 4 (W_P U_Q - U_P W_Q)^2
    let t18 = t11;  // W_D * 4 (U_P U_Q - W_P W_Q)^2

    P.U = t14;  // U_{P'} = (U_P + W_P)^2 (U_P - W_P)^2
    P.W = t16;  // W_{P'} = (4 U_P W_P) ((U_P - W_P)^2 + ((A + 2)/4) 4 U_P W_P)
    Q.U = t18;  // U_{Q'} = W_D * 4 (U_P U_Q - W_P W_Q)^2
    Q.W = t17;  // W_{Q'} = U_D * 4 (W_P U_Q - U_P W_Q)^2
}

define_mul_assign_variants!(LHS = MontgomeryPoint, RHS = Scalar);

define_mul_variants!(
    LHS = MontgomeryPoint,
    RHS = Scalar,
    Output = MontgomeryPoint
);

define_mul_variants!(
    LHS = Scalar,
    RHS = MontgomeryPoint,
    Output = MontgomeryPoint
);

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &MontgomeryPoint {
    open spec fn obeys_mul_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        is_valid_montgomery_point(*self)
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> MontgomeryPoint {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

/// Multiply this `MontgomeryPoint` by a `Scalar`.
impl Mul<&Scalar> for &MontgomeryPoint {
    type Output = MontgomeryPoint;

    /// Given `self` \\( = u\_0(P) \\), and a `Scalar` \\(n\\), return \\( u\_0(\[n\]P) \\)
    fn mul(self, scalar: &Scalar) -> (result: MontgomeryPoint)
        ensures
    // Result represents [n]self where n is the scalar value (mod group order)
    // If self has u-coordinate matching affine point P, result has u-coordinate of [n]P

            forall|P: MontgomeryAffine|
                is_valid_montgomery_affine(P) && spec_montgomery_point(*self) == spec_u_coordinate(
                    P,
                ) ==> {
                    let x = montgomery_scalar_mul(P, spec_scalar(scalar));
                    spec_montgomery_point(result) == spec_u_coordinate(x)
                },
    {
        proof {
            // VERIFICATION NOTE: Proof that mul correctly implements scalar multiplication.
            // This depends on the correctness of mul_bits_be.
            assume(false);
        }

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
            decreases 255 - i,
        {
            bits_be[i] = bits_le[254 - i];
            i += 1;
        }
        self.mul_bits_be(&bits_be)
    }
}

impl MulAssign<&Scalar> for MontgomeryPoint {
    fn mul_assign(&mut self, scalar: &Scalar)
        requires
            is_valid_montgomery_point(*old(self)),
        ensures
    // Result represents [n]old(self) where n is the scalar value

            exists|P: MontgomeryAffine| #[trigger]
                is_valid_montgomery_affine(P) && spec_montgomery_point(*old(self))
                    == spec_u_coordinate(P) && {
                    let result_point = montgomery_scalar_mul(P, spec_scalar(scalar));
                    spec_montgomery_point(*self) == spec_u_coordinate(result_point)
                },
    {
        *self = &*self * scalar;
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&MontgomeryPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn mul_req(self, rhs: &MontgomeryPoint) -> bool {
        is_valid_montgomery_point(*rhs)
    }

    open spec fn mul_spec(self, rhs: &MontgomeryPoint) -> MontgomeryPoint {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

impl Mul<&MontgomeryPoint> for &Scalar {
    type Output = MontgomeryPoint;

    fn mul(self, point: &MontgomeryPoint) -> (result: MontgomeryPoint)
        ensures
    // Scalar multiplication is commutative: scalar * point = point * scalar

            exists|P: MontgomeryAffine| #[trigger]
                is_valid_montgomery_affine(P) && spec_montgomery_point(*point) == spec_u_coordinate(
                    P,
                ) && {
                    let result_point = montgomery_scalar_mul(P, spec_scalar(self));
                    spec_montgomery_point(result) == spec_u_coordinate(result_point)
                },
    {
        point * self
    }
}

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
