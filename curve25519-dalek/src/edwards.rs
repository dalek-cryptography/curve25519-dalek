// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2020 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
//! Group operations for Curve25519, in Edwards form.
//!
//! ## Encoding and Decoding
//!
//! Encoding is done by converting to and from a `CompressedEdwardsY`
//! struct, which is a typed wrapper around `[u8; 32]`.
//!
//! ## Equality Testing
//!
//! The `EdwardsPoint` struct implements the [`subtle::ConstantTimeEq`]
//! trait for constant-time equality checking, and the Rust `Eq` trait
//! for variable-time equality checking.
//!
//! ## Cofactor-related functions
//!
//! The order of the group of points on the curve \\(\mathcal E\\)
//! is \\(|\mathcal E| = 8\ell \\), so its structure is \\( \mathcal
//! E = \mathcal E\[8\] \times \mathcal E[\ell]\\).  The torsion
//! subgroup \\( \mathcal E\[8\] \\) consists of eight points of small
//! order.  Technically, all of \\(\mathcal E\\) is torsion, but we
//! use the word only to refer to the small \\(\mathcal E\[8\]\\) part, not
//! the large prime-order \\(\mathcal E[\ell]\\) part.
//!
//! To test if a point is in \\( \mathcal E\[8\] \\), use
//! [`EdwardsPoint::is_small_order`].
//!
//! To test if a point is in \\( \mathcal E[\ell] \\), use
//! [`EdwardsPoint::is_torsion_free`].
//!
//! To multiply by the cofactor, use [`EdwardsPoint::mul_by_cofactor`].
//!
//! To avoid dealing with cofactors entirely, consider using Ristretto.
//!
//! ## Scalars
//!
//! Scalars are represented by the [`Scalar`] struct. To construct a scalar, see
//! [`Scalar::from_canonical_bytes`] or [`Scalar::from_bytes_mod_order_wide`].
//!
//! ## Scalar Multiplication
//!
//! Scalar multiplication on Edwards points is provided by:
//!
//! * the `*` operator between a `Scalar` and a `EdwardsPoint`, which
//! performs constant-time variable-base scalar multiplication;
//!
//! * the `*` operator between a `Scalar` and a
//! `EdwardsBasepointTable`, which performs constant-time fixed-base
//! scalar multiplication;
//!
//! * an implementation of the
//! [`MultiscalarMul`](../traits/trait.MultiscalarMul.html) trait for
//! constant-time variable-base multiscalar multiplication;
//!
//! * an implementation of the
//! [`VartimeMultiscalarMul`](../traits/trait.VartimeMultiscalarMul.html)
//! trait for variable-time variable-base multiscalar multiplication;
//!
//! ## Implementation
//!
//! The Edwards arithmetic is implemented using the “extended twisted
//! coordinates” of Hisil, Wong, Carter, and Dawson, and the
//! corresponding complete formulas.  For more details,
//! see the [`curve_models` submodule][curve_models]
//! of the internal documentation.
//!
//! ## Validity Checking
//!
//! There is no function for checking whether a point is valid.
//! Instead, the `EdwardsPoint` struct is guaranteed to hold a valid
//! point on the curve.
//!
//! We use the Rust type system to make invalid points
//! unrepresentable: `EdwardsPoint` objects can only be created via
//! successful decompression of a compressed point, or else by
//! operations on other (valid) `EdwardsPoint`s.
//!
//! [curve_models]: https://docs.rs/curve25519-dalek/latest/curve25519-dalek/backend/serial/curve_models/index.html
// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]

use alloc::vec::Vec;
use core::array::TryFromSliceError;
use core::borrow::Borrow;
use core::fmt::Debug;
use core::iter::Sum;
use core::ops::{Add, Neg, Sub};
use core::ops::{AddAssign, SubAssign};
use core::ops::{Mul, MulAssign};

use cfg_if::cfg_if;

#[cfg(feature = "digest")]
use digest::{generic_array::typenum::U64, Digest};

#[cfg(feature = "group")]
use {
    group::{cofactor::CofactorGroup, prime::PrimeGroup, GroupEncoding},
    subtle::CtOption,
};

#[cfg(feature = "group")]
use rand_core::RngCore;

use subtle::Choice;
use subtle::ConditionallyNegatable;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::constants;

use crate::field::FieldElement;
use crate::scalar::{clamp_integer, Scalar};

use crate::montgomery::MontgomeryPoint;

use crate::backend::serial::curve_models::AffineNielsPoint;
use crate::backend::serial::curve_models::CompletedPoint;
use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::backend::serial::curve_models::ProjectivePoint;
#[allow(unused_imports)] // Used in verus! blocks
use crate::core_assumes::{compressed_edwards_y_from_array_result, try_into_32_bytes_array};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;

/* VERIFICATION NOTE: Only importing LookupTableRadix16 since other radix variants
were removed during manual expansion focusing on radix-16. */
#[cfg(feature = "precomputed-tables")]
use crate::window::LookupTableRadix16;

#[cfg(feature = "precomputed-tables")]
use crate::traits::BasepointTable;

use crate::traits::ValidityCheck;
use crate::traits::{Identity, IsIdentity};

#[cfg(feature = "alloc")]
use crate::traits::MultiscalarMul;
#[cfg(feature = "alloc")]
use crate::traits::{VartimeMultiscalarMul, VartimePrecomputedMultiscalarMul};

#[allow(unused_imports)] // Used in verus! blocks
use crate::backend::serial::u64::field::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::backend::serial::u64::subtle_assumes::*;
#[cfg(feature = "digest")]
#[allow(unused_imports)]
use crate::core_assumes::sha512_hash_bytes;
#[cfg(all(feature = "digest", verus_keep_ghost))]
#[allow(unused_imports)]
use crate::core_assumes::spec_sha512;
#[allow(unused_imports)] // Used in verus! blocks for pow2 arithmetic facts
use crate::lemmas::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for identity bytes proof
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for Edwards curve constants
use crate::lemmas::edwards_lemmas::constants_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for curve equation proofs
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for decompress proofs
use crate::lemmas::edwards_lemmas::decompress_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for mul_base (Pippenger) proofs
use crate::lemmas::edwards_lemmas::mul_base_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for decompress proofs
use crate::lemmas::edwards_lemmas::step1_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for bound weakening
use crate::lemmas::field_lemmas::add_lemmas::*;
#[allow(unused_imports)]
// Used in verus! blocks for is_valid proof (canonical bytes ↔ field value)
use crate::lemmas::field_lemmas::as_bytes_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for general field constants (ONE, ZERO)
use crate::lemmas::field_lemmas::constants_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for field algebra lemmas
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for bytes/word conversion lemmas
use crate::lemmas::scalar_byte_lemmas::bytes_to_scalar_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for radix-16 lemmas
use crate::lemmas::scalar_lemmas_::radix16_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for bytes_as_nat_prefix / words_as_nat_u64
use crate::specs::core_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::core_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::edwards_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::field_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::field_specs_u64::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::montgomery_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar52_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[allow(unused_imports)]
use crate::specs::window_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

// ------------------------------------------------------------------------
// Compressed points
// ------------------------------------------------------------------------

verus! {

/// In "Edwards y" / "Ed25519" format, the curve point \\((x,y)\\) is
/// determined by the \\(y\\)-coordinate and the sign of \\(x\\).
///
/// The first 255 bits of a `CompressedEdwardsY` represent the
/// \\(y\\)-coordinate.  The high bit of the 32nd byte gives the sign of \\(x\\).
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct CompressedEdwardsY(pub [u8; 32]);

impl ConstantTimeEq for CompressedEdwardsY {
    fn ct_eq(&self, other: &CompressedEdwardsY) -> (result: Choice)
        ensures
            choice_is_true(result) == (self.0 == other.0),
    {
        /* <VERIFICATION NOTE>
         Use wrapper function ct_eq_bytes32 instead of direct subtle call to ct_eq for Verus compatibility.
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         self.as_bytes().ct_eq(other.as_bytes())
         </ORIGINAL CODE> */
        ct_eq_bytes32(self.as_bytes(), other.as_bytes())
    }
}

impl Debug for CompressedEdwardsY {
    /* VERIFICATION NOTE: we don't cover debugging */
    #[verifier::external_body]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "CompressedEdwardsY: {:?}", self.as_bytes())
    }
}

impl CompressedEdwardsY {
    /// View this `CompressedEdwardsY` as an array of bytes.
    pub const fn as_bytes(&self) -> (result: &[u8; 32])
        ensures
            result == self.0,
    {
        &self.0
    }

    /// Copy this `CompressedEdwardsY` to an array of bytes.
    pub const fn to_bytes(&self) -> (result: [u8; 32])
        ensures
            result == self.0,
    {
        self.0
    }

    /// Attempt to decompress to an `EdwardsPoint`.
    ///
    /// Returns `None` if the input is not the \\(y\\)-coordinate of a
    /// curve point.
    ///
    pub fn decompress(&self) -> (result: Option<EdwardsPoint>)
        ensures
    // Decompression succeeds iff the y-coordinate is valid

            math_is_valid_y_coordinate(field_element_from_bytes(&self.0)) <==> result.is_some(),
            // When successful, the result has these properties:
            result.is_some() ==> (
            // The Y coordinate matches the one from the compressed representation
            fe51_as_canonical_nat(&result.unwrap().Y) == field_element_from_bytes(
                &self.0,
            )
            // Z is 1 in the decompressed representation
             && fe51_as_canonical_nat(&result.unwrap().Z)
                == 1
            // The point is valid on the Edwards curve
             && is_well_formed_edwards_point(
                result.unwrap(),
            )
            // The X coordinate sign bit matches the compressed sign bit when y² ≠ 1.
            // When y² == 1, x = 0 so negation is the identity and sign bit is always 0.
             && (field_square(field_element_from_bytes(&self.0)) != 1
                ==> fe51_as_canonical_nat_sign_bit(&result.unwrap().X) == (self.0[31] >> 7))),
    {
        let (is_valid_y_coord, X, Y, Z) = decompress::step_1(self);

        proof {
            assert(choice_is_true(is_valid_y_coord) ==> math_is_valid_y_coordinate(
                field_element_from_bytes(&self.0),
            ));
            assert(choice_is_true(is_valid_y_coord) ==> math_on_edwards_curve(
                fe51_as_canonical_nat(&X),
                fe51_as_canonical_nat(&Y),
            ));
        }
        if choice_into(is_valid_y_coord) {
            let point = decompress::step_2(self, X, Y, Z);
            let result = Some(point);
            proof {
                // Extract values for lemma
                let x_orig = fe51_as_canonical_nat(&X);

                // Establish step_2 postconditions needed by lemma
                // step_2 ensures Y and Z are preserved by reference equality
                assert(&point.Y == &Y);
                assert(&point.Z == &Z);
                assert(fe51_as_canonical_nat(&point.Y) == field_element_from_bytes(&self.0));
                assert(fe51_as_canonical_nat(&point.Z) == 1);

                // x_orig < p() is trivially true since x_orig = fe51_as_canonical_nat(&X) = ...%p()
                pow255_gt_19();
                assert(x_orig < p()) by {
                    lemma_mod_bound(fe51_as_nat(&X) as int, p() as int);
                };

                // Use the unified lemma to prove all postconditions
                lemma_decompress_valid_branch(&self.0, x_orig, &point);

                // Strengthen to well-formedness: bounds + sum bounds.
                assert(fe51_limbs_bounded(&point.Y, 51));
                assert(fe51_limbs_bounded(&point.Z, 51));
                assert((1u64 << 51) < (1u64 << 52)) by (bit_vector);
                lemma_fe51_limbs_bounded_weaken(&point.Y, 51, 52);
                lemma_fe51_limbs_bounded_weaken(&point.Z, 51, 52);

                assert(edwards_point_limbs_bounded(point));
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&point.Y, &point.X, 52);
                assert(is_well_formed_edwards_point(point));
            }
            result
        } else {
            let result = None;
            result
        }
    }
}

mod decompress {
    use super::*;

    #[rustfmt::skip]  // keep alignment of explanatory comments
    pub(super) fn step_1(repr: &CompressedEdwardsY) -> (result: (
        Choice,
        FieldElement,
        FieldElement,
        FieldElement,
    ))  // Result components: (is_valid, X, Y, Z)
        ensures
    // The returned Y field element matches the one extracted from the compressed representation

            ({
                let (is_valid, X, Y, Z) = result;
                fe51_as_canonical_nat(&Y) == field_element_from_bytes(&repr.0)
                    &&
                // The returned Z field element is 1
                fe51_as_canonical_nat(&Z) == 1
                    &&
                // The choice is true iff the Y is valid and (X, Y) is on the curve
                (choice_is_true(is_valid) <==> math_is_valid_y_coordinate(
                    fe51_as_canonical_nat(&Y),
                )) && (choice_is_true(is_valid) ==> math_on_edwards_curve(
                    fe51_as_canonical_nat(&X),
                    fe51_as_canonical_nat(&Y),
                )) &&
                // Limb bounds for step_2
                // X is 52-bit bounded from sqrt_ratio_i (relaxed from 51)
                fe51_limbs_bounded(&X, 52) && fe51_limbs_bounded(&Y, 51) && fe51_limbs_bounded(
                    &Z,
                    51,
                )
                    &&
                // X is the non-negative root (LSB = 0) - from sqrt_ratio_i
                // This is needed in the proof of decompress
                fe51_as_canonical_nat(&X) % 2 == 0
            }),
    {
        // =================================================================
        // PHASE 1: Setup Y, Z, compute u = y² - 1, v = d·y² + 1
        // =================================================================
        let Y = FieldElement::from_bytes(repr.as_bytes());
        assert(field_element_from_bytes(&repr.0) == fe51_as_canonical_nat(&Y));
        let Z = FieldElement::ONE;
        proof {
            // Y is 51-bit bounded (from from_bytes), which implies 54-bit for square
            assert((1u64 << 51) < (1u64 << 54)) by (bit_vector);
        }

        let YY = Y.square();  // Y² - requires 54-bit bounded input

        proof {
            // Limb bounds for field operation preconditions (overflow prevention):
            // - lemma_one_limbs_bounded_51: ONE.limbs[i] < 2^51, needed for `u = &YY - &Z`
            // - lemma_edwards_d_limbs_bounded: EDWARDS_D.limbs[i] < 2^51, needed for `yy_times_d = &YY * &EDWARDS_D`
            lemma_one_limbs_bounded_51();
            lemma_edwards_d_limbs_bounded();
        }

        let u = &YY - &Z;  // u = y² - 1
        let yy_times_d = &YY * &constants::EDWARDS_D;

        proof {
            // Setup for Add: yy_times_d (52-bit from mul) + Z = ONE
            // (inlined from lemma_decompress_add_no_overflow)
            // 2^52 + 1 < u64::MAX
            assert((1u64 << 52) + 1 < u64::MAX) by (bit_vector);
            // Each limb sum is bounded
            assert forall|i: int| 0 <= i < 5 implies yy_times_d.limbs[i] + Z.limbs[i]
                < u64::MAX by {
                // limb[i] < 2^52 (from 52-bit bound)
                // Z.limbs[0] = 1, Z.limbs[1..4] = 0
            };
        }

        let v = &yy_times_d + &Z;  // v = d·y² + 1

        proof {
            // v bounds: 52-bit + 1 < 54-bit
            assert((1u64 << 52) + 1 < (1u64 << 54)) by (bit_vector);
            assert(forall|i: int| 0 <= i < 5 ==> v.limbs[i] < (1u64 << 54));
        }

        let (is_valid_y_coord, X) = FieldElement::sqrt_ratio_i(&u, &v);

        proof {
            // =================================================================
            // PHASE 2: sqrt_ratio_i postconditions
            // =================================================================
            // Ghost variable definitions for connecting to math specs
            let ghost y = fe51_as_canonical_nat(&Y);
            let ghost d = fe51_as_canonical_nat(&constants::EDWARDS_D);
            let ghost y2 = field_square(y);
            let ghost u_math = field_sub(y2, 1);
            let ghost v_math = field_add(field_mul(d, y2), 1);
            let ghost x = fe51_as_canonical_nat(&X);

            // sqrt_ratio_i postconditions encapsulated in sqrt_ratio_i_post
            assert(sqrt_ratio_i_post(u_math, v_math, choice_is_true(is_valid_y_coord), x)) by {
                // Boundedness (sqrt_ratio_i_bounded_post):
                // x = fe51_as_canonical_nat(&X) is always < p() by definition (it's mod p)
                // From step_1 postcondition: x % 2 == 0 (non-negative square root)
                pow255_gt_19();  // proves p() > 0
                assert(x < p()) by {
                    // fe51_as_canonical_nat is defined as fe51_as_nat % p()
                    // so it's always < p()
                    lemma_mod_bound(fe51_as_nat(&X) as int, p() as int);
                };
                assert(x % 2 == 0);  // From step_1 postcondition
                assert(sqrt_ratio_i_bounded_post(x));

                // Connect field elements to math versions (needed for sqrt_ratio_i_math_post)
                // YY = Y.square() → fe51_as_canonical_nat(&YY) == field_square(y)
                lemma_square_matches_field_square(fe51_as_nat(&Y), fe51_as_nat(&YY));
                assert(fe51_as_canonical_nat(&YY) == y2);

                // u = YY - Z → fe51_as_canonical_nat(&u) == u_math
                // (lemma_one_field_element_value establishes fe51_as_canonical_nat(&Z) == 1,
                // needed for both u_math and v_math assertions)
                lemma_one_field_element_value();
                assert(fe51_as_canonical_nat(&u) == u_math);

                // v = yy_times_d + Z → fe51_as_canonical_nat(&v) == v_math
                assert(field_mul(y2, d) == field_mul(d, y2)) by {
                    lemma_mul_is_commutative(y2 as int, d as int);
                    assert(y2 * d == d * y2);
                };
                assert(fe51_as_canonical_nat(&v) == v_math);

                // Math correctness (sqrt_ratio_i_math_post):
                // All four cases follow from sqrt_ratio_i ensures clauses
                assert(sqrt_ratio_i_math_post(u_math, v_math, choice_is_true(is_valid_y_coord), x));
            };

            // =================================================================
            // PHASE 3: Additional preconditions for lemma_step1_case_analysis
            // =================================================================
            assert(fe51_as_canonical_nat(&Z) == 1) by {
                lemma_one_field_element_value();
            };

            // Limb bound for step_1 postcondition (not covered by sqrt_ratio_i_post)
            assert(fe51_limbs_bounded(&X, 52));

            // Use lemma to prove curve semantics from sqrt_ratio_i result
            lemma_step1_case_analysis(y, x, u_math, v_math, choice_is_true(is_valid_y_coord));
        }
        (is_valid_y_coord, X, Y, Z)
    }

    #[rustfmt::skip]
    pub(super) fn step_2(
        repr: &CompressedEdwardsY,
        mut X: FieldElement,
        Y: FieldElement,
        Z: FieldElement,
    ) -> (result: EdwardsPoint)
        requires
    // Limb bounds for inputs (X from sqrt_ratio_i, Y from from_bytes, Z = ONE)
    // X is 52-bit bounded from sqrt_ratio_i (relaxed from 51)

            fe51_limbs_bounded(&X, 52),
            fe51_limbs_bounded(&Y, 51),
            fe51_limbs_bounded(&Z, 51),
        ensures
            fe51_as_canonical_nat(&result.X)
                ==
            // If the sign bit is 1, negate the X field element
            if (repr.0[31] >> 7) == 1 {
                field_neg(fe51_as_canonical_nat(&X))
            } else {
                fe51_as_canonical_nat(&X)
            },
            // Y and Z are unchanged
            &result.Y == &Y && &result.Z == &Z
                &&
            // X is conditionally negated based on the sign bit
            // T = X * Y (after conditional negation)
            fe51_as_canonical_nat(&result.T) == field_mul(
                fe51_as_canonical_nat(&result.X),
                fe51_as_canonical_nat(&result.Y),
            ),
            // Limb bounds needed for well-formedness in callers
            fe51_limbs_bounded(&result.X, 52),
            fe51_limbs_bounded(&result.T, 52),
    {
        // FieldElement::sqrt_ratio_i always returns the nonnegative square root,
        // so we negate according to the supplied sign bit.
        let compressed_sign_bit = Choice::from(repr.as_bytes()[31] >> 7);

        /* <VERIFICATION NOTE>
         Using conditional_negate_field_element wrapper with proper specs.
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
        X.conditional_negate(compressed_sign_bit);
        </ORIGINAL CODE> */
        let ghost original_X = X;
        proof {
            // 51-bit bounded implies 52-bit bounded (for conditional_negate precondition)
            assert((1u64 << 51) < (1u64 << 52)) by (bit_vector);
            assert(fe51_limbs_bounded(&X, 52));
            // Also establish 54-bit bound, since the wrapper uses the standard 54-bit precondition.
            lemma_fe51_limbs_bounded_weaken(&X, 52, 54);
        }
        conditional_negate_field_element(&mut X, compressed_sign_bit);

        proof {
            // `conditional_negate_field_element` is a no-op when `compressed_sign_bit` is false,
            // and performs a reduce()'d negation (52-bit bounded) when it is true.
            assert(fe51_limbs_bounded(&X, 52)) by {
                if choice_is_true(compressed_sign_bit) {
                    assert(choice_is_true(compressed_sign_bit) ==> fe51_limbs_bounded(&X, 52));
                } else {
                    assert(!choice_is_true(compressed_sign_bit) ==> X == original_X);
                    assert(X == original_X);
                }
            }
            // Y is bounded by 51 < 54 from requires
            assert(fe51_limbs_bounded(&Y, 51));
            // conditional_negate_field_element ensures the semantic property
            assert(fe51_as_canonical_nat(&X) == if choice_is_true(compressed_sign_bit) {
                field_neg(fe51_as_canonical_nat(&original_X))
            } else {
                fe51_as_canonical_nat(&original_X)
            });
            // For multiplication: need bounds by 54
            // 52 < 54 and 51 < 54, so we need to help Verus see the implication
            assert((1u64 << 52) < (1u64 << 54)) by (bit_vector);
            assert((1u64 << 51) < (1u64 << 54)) by (bit_vector);
            assert(fe51_limbs_bounded(&X, 54));
            assert(fe51_limbs_bounded(&Y, 54));
        }

        let result = EdwardsPoint { X, Y, Z, T: &X * &Y };

        proof {
            // multiplication produces correct field_mul result
            assert(fe51_as_canonical_nat(&result.T) == field_mul(
                fe51_as_canonical_nat(&result.X),
                fe51_as_canonical_nat(&result.Y),
            ));
            // Limb bounds: X remains 52-bounded (from conditional_negate_field_element),
            // and T is 52-bounded as a product.
            assert(fe51_limbs_bounded(&result.X, 52));
            assert(fe51_limbs_bounded(&result.T, 52));
        }

        result
    }

}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::TryFromSpecImpl<&[u8]> for CompressedEdwardsY {
    open spec fn obeys_try_from_spec() -> bool {
        false
    }

    open spec fn try_from_spec(v: &[u8]) -> Result<Self, Self::Error> {
        arbitrary()
    }
}

impl TryFrom<&[u8]> for CompressedEdwardsY {
    type Error = TryFromSliceError;

    fn try_from(slice: &[u8]) -> (result: Result<CompressedEdwardsY, TryFromSliceError>)
        ensures
            match result {
                Ok(point) => point.0@ == slice@,
                Err(_) => true,
            },
    {
        Self::from_slice(slice)
    }
}

} // verus!
/* VERIFICATION NOTE: we don't cover serde feature yet */
// ------------------------------------------------------------------------
// Serde support
// ------------------------------------------------------------------------
// Serializes to and from `EdwardsPoint` directly, doing compression
// and decompression internally.  This means that users can create
// structs containing `EdwardsPoint`s and use Serde's derived
// serializers to serialize those structures.
#[cfg(feature = "serde")]
use serde::de::Visitor;
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[cfg(feature = "serde")]
impl Serialize for EdwardsPoint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeTuple;
        let mut tup = serializer.serialize_tuple(32)?;
        for byte in self.compress().as_bytes().iter() {
            tup.serialize_element(byte)?;
        }
        tup.end()
    }
}

#[cfg(feature = "serde")]
impl Serialize for CompressedEdwardsY {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeTuple;
        let mut tup = serializer.serialize_tuple(32)?;
        for byte in self.as_bytes().iter() {
            tup.serialize_element(byte)?;
        }
        tup.end()
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for EdwardsPoint {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct EdwardsPointVisitor;

        impl<'de> Visitor<'de> for EdwardsPointVisitor {
            type Value = EdwardsPoint;

            fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                formatter.write_str("a valid point in Edwards y + sign format")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<EdwardsPoint, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut bytes = [0u8; 32];
                #[allow(clippy::needless_range_loop)]
                for i in 0..32 {
                    bytes[i] = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(i, &"expected 32 bytes"))?;
                }
                CompressedEdwardsY(bytes)
                    .decompress()
                    .ok_or_else(|| serde::de::Error::custom("decompression failed"))
            }
        }

        deserializer.deserialize_tuple(32, EdwardsPointVisitor)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for CompressedEdwardsY {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct CompressedEdwardsYVisitor;

        impl<'de> Visitor<'de> for CompressedEdwardsYVisitor {
            type Value = CompressedEdwardsY;

            fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                formatter.write_str("32 bytes of data")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<CompressedEdwardsY, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut bytes = [0u8; 32];
                #[allow(clippy::needless_range_loop)]
                for i in 0..32 {
                    bytes[i] = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(i, &"expected 32 bytes"))?;
                }
                Ok(CompressedEdwardsY(bytes))
            }
        }

        deserializer.deserialize_tuple(32, CompressedEdwardsYVisitor)
    }
}

// ------------------------------------------------------------------------
// Internal point representations
// ------------------------------------------------------------------------

verus! {

/// An `EdwardsPoint` represents a point on the Edwards form of Curve25519.
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct EdwardsPoint {
    // VERIFICATION NOTE: changed from pub(crate) to pub
    pub X: FieldElement,
    pub Y: FieldElement,
    pub Z: FieldElement,
    pub T: FieldElement,
}

// ------------------------------------------------------------------------
// Constructors
// ------------------------------------------------------------------------
impl Identity for CompressedEdwardsY {
    fn identity() -> (result: CompressedEdwardsY)
        ensures
    // Identity point has y = 1 and sign bit = 0

            field_element_from_bytes(&result.0) == 1,
            (result.0[31] >> 7) == 0,
    {
        let result = CompressedEdwardsY(
            [
                1,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
            ],
        );

        proof {
            // byte 31 is 0, so sign bit (bit 7) is 0
            assert(result.0[31] == 0);
            assert((0u8 >> 7) == 0) by (bit_vector);

            // field_element_from_bytes([1, 0, ...]) = 1
            // The bytes represent 1 in little-endian: byte[0] = 1, rest = 0

            // Step 1: Prove u8_32_as_nat(&result.0) == 1
            assert(result.0[0] == 1);
            assert(forall|i: int| 1 <= i < 32 ==> result.0[i] == 0);
            assert(u8_32_as_nat(&result.0) == 1) by {
                lemma_u8_32_as_nat_identity(&result.0);
            }

            // Step 2: 1 % pow2(255) == 1 (since 1 < pow2(255))
            assert(1nat % pow2(255) == 1) by {
                lemma2_to64();
                lemma_pow2_strictly_increases(0, 255);
                lemma_small_mod(1nat, pow2(255));
            }

            // Step 3: 1 % p() == 1 (since 1 < p() = 2^255 - 19)
            assert(1nat % p() == 1) by {
                p_gt_2();
                lemma_small_mod(1nat, p());
            }

            // Conclude: field_element_from_bytes = (u8_32_as_nat % pow2(255)) % p() = 1
            assert(field_element_from_bytes(&result.0) == 1);
        }

        result
    }
}

impl crate::traits::IsIdentitySpecImpl for CompressedEdwardsY {
    /// For CompressedEdwardsY, is_identity returns true iff y-coordinate is 1 with sign bit 0
    open spec fn is_identity_spec(&self) -> bool {
        field_element_from_bytes(&self.0) == 1 && (self.0[31] >> 7) == 0
    }
}

impl Default for CompressedEdwardsY {
    fn default() -> (result: CompressedEdwardsY)
        ensures
    // Identity point has y = 1 and sign bit = 0

            field_element_from_bytes(&result.0) == 1,
            (result.0[31] >> 7) == 0,
    {
        CompressedEdwardsY::identity()
    }
}

impl CompressedEdwardsY {
    /// Construct a `CompressedEdwardsY` from a slice of bytes.
    ///
    /// # Errors
    ///
    /// Returns [`TryFromSliceError`] if the input `bytes` slice does not have
    /// a length of 32.
    pub fn from_slice(bytes: &[u8]) -> (result: Result<
        CompressedEdwardsY,
        TryFromSliceError,
    >)
    // VERIFICATION NOTE: PROOF BYPASS

        ensures
            bytes@.len() == 32 ==> matches!(result, Ok(_)),
            bytes@.len() != 32 ==> matches!(result, Err(_)),
            match result {
                Ok(point) => point.0@ == bytes@,
                Err(_) => true,
            },
    {
        // ORIGINAL CODE: bytes.try_into().map(CompressedEdwardsY)
        // Verus does not support try_into and map
        // We use external wrapper functions with core_assumes for these functions.
        let arr_result = try_into_32_bytes_array(bytes);
        let result = compressed_edwards_y_from_array_result(arr_result);

        proof {
            // WORKS AUTOMATICALLY
            // From try_into_32_bytes_array: arr_result.is_ok() ==> arr_result.unwrap()@ == bytes@
            // From compressed_edwards_y_from_array_result: result.unwrap().0@ == arr_result.unwrap()@
            // Combined: result.unwrap().0@ == bytes@
        }
        result
    }
}

impl Identity for EdwardsPoint {
    fn identity() -> (result: EdwardsPoint)
        ensures
            is_identity_edwards_point(result),
            is_well_formed_edwards_point(result),
    {
        let result = EdwardsPoint {
            X: FieldElement::ZERO,
            Y: FieldElement::ONE,
            Z: FieldElement::ONE,
            T: FieldElement::ZERO,
        };
        proof {
            // ZERO has limbs [0,0,0,0,0] → fe51_as_canonical_nat = 0
            // ONE has limbs [1,0,0,0,0] → fe51_as_canonical_nat = 1
            assert(fe51_as_canonical_nat(&FieldElement::ZERO) == 0) by {
                lemma_zero_field_element_value();
            }
            assert(fe51_as_canonical_nat(&FieldElement::ONE) == 1) by {
                lemma_one_field_element_value();
            }

            // is_identity_edwards_point requires: z != 0, x == 0, y == z
            // With X=ZERO, Y=ONE, Z=ONE: z=1≠0, x=0, y=z=1 ✓

            // is_well_formed_edwards_point requires:
            // 1. is_valid_edwards_point (identity is on curve)
            assert(is_valid_edwards_point(result)) by {
                lemma_identity_is_valid_extended();
            }

            // 2. edwards_point_limbs_bounded (all limbs < 2^52)
            // ZERO/ONE have limbs [0/1, 0, 0, 0, 0] which are trivially < 2^52
            assert(edwards_point_limbs_bounded(result)) by {
                lemma_zero_limbs_bounded_51();
                lemma_one_limbs_bounded_51();
                assert(0u64 < (1u64 << 52) && 1u64 < (1u64 << 52)) by (bit_vector);
            }

            // 3. sum_of_limbs_bounded (Y + X doesn't overflow)
            // Y=ONE=[1,0,0,0,0], X=ZERO=[0,0,0,0,0]
            // 1+0 < u64::MAX, 0+0 < u64::MAX
            assert(sum_of_limbs_bounded(&result.Y, &result.X, u64::MAX)) by {
                assert(1u64 + 0u64 < u64::MAX) by (bit_vector);
                assert(0u64 + 0u64 < u64::MAX) by (bit_vector);
            }
        }
        result
    }
}

impl crate::traits::IsIdentitySpecImpl for EdwardsPoint {
    /// For EdwardsPoint, is_identity returns true iff the affine point equals (0, 1)
    open spec fn is_identity_spec(&self) -> bool {
        edwards_point_as_affine(*self) == math_edwards_identity()
    }
}

impl Default for EdwardsPoint {
    fn default() -> (result: EdwardsPoint)
        ensures
            is_identity_edwards_point(result),
    {
        EdwardsPoint::identity()
    }
}

// ------------------------------------------------------------------------
// Zeroize implementations for wiping points from memory
// ------------------------------------------------------------------------
#[cfg(feature = "zeroize")]
impl Zeroize for CompressedEdwardsY {
    /// Reset this `CompressedEdwardsY` to the compressed form of the identity element.
    fn zeroize(&mut self)
        ensures
            forall|i: int| 1 <= i < 32 ==> #[trigger] self.0[i] == 0u8,
            self.0[0]
                == 1u8,
    // VERIFICATION NOTE: this "zeroize" leaves one bit equal to 1

    {
        /* ORIGINAL CODE:
            self.0.zeroize();
            self.0[0] = 1;
        */
        crate::core_assumes::zeroize_bytes32(&mut self.0);
        self.0[0] = 1;
    }
}

#[cfg(feature = "zeroize")]
impl Zeroize for EdwardsPoint {
    /// Reset this `CompressedEdwardsPoint` to the identity element.
    fn zeroize(&mut self)
        ensures
            forall|i: int| 0 <= i < 5 ==> self.X.limbs[i] == 0,
            forall|i: int| 0 <= i < 5 ==> self.T.limbs[i] == 0,
            self.Y == FieldElement::ONE,
            self.Z == FieldElement::ONE,
    {
        self.X.zeroize();
        self.Y = FieldElement::ONE;
        self.Z = FieldElement::ONE;
        self.T.zeroize();
    }
}

// ------------------------------------------------------------------------
// Validity checks (for debugging, not CT)
// ------------------------------------------------------------------------
impl ValidityCheck for EdwardsPoint {
    fn is_valid(&self) -> (result: bool)
        requires
            edwards_point_limbs_bounded(*self),
            fe51_as_canonical_nat(&self.Z) != 0,
        ensures
            result == is_valid_edwards_point(*self),
    {
        let proj = self.as_projective();
        proof {
            // The limb bounds are preserved by as_projective() (proj.X == self.X, etc.)
            // EdwardsPoint invariant is 52-bounded
            assert(fe51_limbs_bounded(&proj.X, 52));
            assert(fe51_limbs_bounded(&proj.Y, 52));
            assert(fe51_limbs_bounded(&proj.Z, 52));
            // Weaken to 54-bounded for mul preconditions
            lemma_fe51_limbs_bounded_weaken(&proj.X, 52, 54);
            lemma_fe51_limbs_bounded_weaken(&proj.Y, 52, 54);
            lemma_fe51_limbs_bounded_weaken(&proj.Z, 52, 54);
        }
        let point_on_curve = proj.is_valid();

        proof {
            // Weaken self's coordinates for mul preconditions
            lemma_edwards_point_weaken_to_54(self);
        }
        // REFACTORED from ORIGINAL: let on_segre_image = (&self.X * &self.Y) == (&self.Z * &self.T);
        // Split to allow proof block to reference intermediate products
        let xy = &self.X * &self.Y;
        let zt = &self.Z * &self.T;
        let on_segre_image = xy == zt;

        let result = point_on_curve && on_segre_image;
        proof {
            // Connect runtime checks to spec predicate
            let x = fe51_as_canonical_nat(&self.X);
            let y = fe51_as_canonical_nat(&self.Y);
            let z = fe51_as_canonical_nat(&self.Z);
            let t = fe51_as_canonical_nat(&self.T);

            // proj.is_valid() checks ONLY the projective curve equation (not z != 0)
            assert(proj.X == self.X && proj.Y == self.Y && proj.Z == self.Z);
            assert(point_on_curve == math_on_edwards_curve_projective(x, y, z));

            // on_segre_image checks XY == ZT via PartialEq (compares canonical bytes)
            // PartialEq ensures: (a == b) <==> spec_fe51_as_bytes(a) == spec_fe51_as_bytes(b)
            assert(on_segre_image == (spec_fe51_as_bytes(&xy) == spec_fe51_as_bytes(&zt)));

            // Multiplication postcondition: fe51_as_canonical_nat of product = field_mul
            assert(fe51_as_canonical_nat(&xy) == field_mul(x, y));
            assert(fe51_as_canonical_nat(&zt) == field_mul(z, t));

            // Relate the exec equality check to the math-level equality.
            assert(on_segre_image == (field_mul(x, y) == field_mul(z, t))) by {
                // Forward: bytes_equal ==> values_equal
                if on_segre_image {
                    assert(spec_fe51_as_bytes(&xy) == spec_fe51_as_bytes(&zt));
                    lemma_fe51_to_bytes_equal_implies_field_element_equal(&xy, &zt);
                    assert(fe51_as_canonical_nat(&xy) == fe51_as_canonical_nat(&zt));
                    assert(field_mul(x, y) == field_mul(z, t));
                }
                // Reverse: values_equal ==> bytes_equal

                if field_mul(x, y) == field_mul(z, t) {
                    assert(fe51_as_canonical_nat(&xy) == fe51_as_canonical_nat(&zt));
                    lemma_field_element_equal_implies_fe51_to_bytes_equal(&xy, &zt);
                    assert(spec_fe51_as_bytes(&xy) == spec_fe51_as_bytes(&zt));
                    assert(on_segre_image);
                }
            };

            // With Z ≠ 0 as precondition, prove result equals the spec validity predicate.
            let curve_eq = math_on_edwards_curve_projective(x, y, z);
            let segre_eq = field_mul(x, y) == field_mul(z, t);

            assert(result == (curve_eq && segre_eq)) by {
                assert(result == (point_on_curve && on_segre_image));
                assert(point_on_curve == curve_eq);
                assert(on_segre_image == segre_eq);
            };

            // Connect local z to precondition: z == fe51_as_canonical_nat(&self.Z) != 0
            assert(z != 0);  // Follows from precondition fe51_as_canonical_nat(&self.Z) != 0
            // z = fe51_as_canonical_nat(...) = fe51_as_nat(...) % p(), so z < p()
            p_gt_2();
            assert(z < p()) by {
                lemma_mod_bound(fe51_as_nat(&self.Z) as int, p() as int);
            };
            assert(z % p() != 0) by {
                lemma_small_mod(z, p());
            };

            assert(is_valid_edwards_point(*self) == (z % p() != 0 && curve_eq && segre_eq));
            // Since z % p() != 0 is known, simplify
            assert(is_valid_edwards_point(*self) == (curve_eq && segre_eq));
            assert(result == is_valid_edwards_point(*self));
        }
        result
    }
}

// ------------------------------------------------------------------------
// Constant-time assignment
// ------------------------------------------------------------------------
impl ConditionallySelectable for EdwardsPoint {
    fn conditional_select(a: &EdwardsPoint, b: &EdwardsPoint, choice: Choice) -> (result:
        EdwardsPoint)
        ensures
    // If choice is false (0), return a

            !choice_is_true(choice) ==> result == *a,
            // If choice is true (1), return b
            choice_is_true(choice) ==> result == *b,
            // Well-formedness is preserved by selection
            is_well_formed_edwards_point(*a) && is_well_formed_edwards_point(*b)
                ==> is_well_formed_edwards_point(result),
    {
        let X = FieldElement::conditional_select(&a.X, &b.X, choice);
        let Y = FieldElement::conditional_select(&a.Y, &b.Y, choice);
        let Z = FieldElement::conditional_select(&a.Z, &b.Z, choice);
        let T = FieldElement::conditional_select(&a.T, &b.T, choice);

        let result = EdwardsPoint { X, Y, Z, T };

        proof {
            if choice_is_true(choice) {
                // choice is true: result should be exactly `b`
                assert(result == *b) by {
                    lemma_field_element51_eq_from_limbs_eq(X, b.X);
                    lemma_field_element51_eq_from_limbs_eq(Y, b.Y);
                    lemma_field_element51_eq_from_limbs_eq(Z, b.Z);
                    lemma_field_element51_eq_from_limbs_eq(T, b.T);
                }
            } else {
                // choice is false: result should be exactly `a`
                assert(result == *a) by {
                    lemma_field_element51_eq_from_limbs_eq(X, a.X);
                    lemma_field_element51_eq_from_limbs_eq(Y, a.Y);
                    lemma_field_element51_eq_from_limbs_eq(Z, a.Z);
                    lemma_field_element51_eq_from_limbs_eq(T, a.T);
                }
            }
        }

        result
    }
}

// ------------------------------------------------------------------------
// Equality
// ------------------------------------------------------------------------
/// Spec for ConstantTimeEq trait implementation
#[cfg(verus_keep_ghost)]
pub trait ConstantTimeEqSpecImpl {
    spec fn ct_eq_req(&self, other: &Self) -> bool;
}

#[cfg(verus_keep_ghost)]
impl ConstantTimeEqSpecImpl for EdwardsPoint {
    open spec fn ct_eq_req(&self, other: &EdwardsPoint) -> bool {
        edwards_point_limbs_bounded(*self) && edwards_point_limbs_bounded(*other)
    }
}

impl ConstantTimeEq for EdwardsPoint {
    fn ct_eq(&self, other: &EdwardsPoint) -> (result:
        Choice)/* VERIFICATION NOTE: we cannot add a "requires" clause to ct_eq with ConstantTimeEqSpecImpl,
            unlike for Add trait implementations through AddSpecImpl.
        */
    // requires self.ct_eq_req(other),

        ensures
    // Two points are equal if they represent the same affine point:
    // (X/Z, Y/Z) == (X'/Z', Y'/Z')
    // This is checked by verifying X*Z' == X'*Z and Y*Z' == Y'*Z

            choice_is_true(result) == (edwards_point_as_affine(*self) == edwards_point_as_affine(
                *other,
            )),
    {
        proof {
            /* VERUS LIMITATION: Must assume precondition

            ConstantTimeEq is an external trait (subtle crate). Approaches tried:
            - External trait specs don't support precondition methods (unlike AddSpecImpl::add_req)
            - Cannot use assume_specification (we implement the trait = duplicate spec error)
            - Type invariants don't work (require private fields; pub(crate) treated as opaque)
            */
            assume(self.ct_eq_req(other));
            // Weaken from 52-bounded (EdwardsPoint invariant) to 54-bounded (mul precondition)
            lemma_edwards_point_weaken_to_54(self);
            lemma_fe51_limbs_bounded_weaken(&other.X, 52, 54);
            lemma_fe51_limbs_bounded_weaken(&other.Y, 52, 54);
            lemma_fe51_limbs_bounded_weaken(&other.Z, 52, 54);
        }

        // We would like to check that the point (X/Z, Y/Z) is equal to
        // the point (X'/Z', Y'/Z') without converting into affine
        // coordinates (x, y) and (x', y'), which requires two inversions.
        // We have that X = xZ and X' = x'Z'. Thus, x = x' is equivalent to
        // (xZ)Z' = (x'Z')Z, and similarly for the y-coordinate.
        /* ORIGINAL CODE:
        let result = (&self.X * &other.Z).ct_eq(&(&other.X * &self.Z))
            & (&self.Y * &other.Z).ct_eq(&(&other.Y * &self.Z));
        */

        let x_eq = (&self.X * &other.Z).ct_eq(&(&other.X * &self.Z));
        let y_eq = (&self.Y * &other.Z).ct_eq(&(&other.Y * &self.Z));
        let result = choice_and(x_eq, y_eq);

        proof {
            // The equality check via cross-multiplication is equivalent to affine coordinate equality
            assume(choice_is_true(result) == (edwards_point_as_affine(*self)
                == edwards_point_as_affine(*other)));
        }

        result
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::cmp::PartialEqSpecImpl for EdwardsPoint {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    /* VERIFICATION NOTE: we cannot add a "requires" clause to eq_spec with PartialEqSpecImpl,
        unlike for Add trait implementations through AddSpecImpl.
    THIS DOES NOT WORK:
    open spec fn eq_req(&self, other: &Self) -> bool {
        edwards_point_limbs_bounded(*self) && edwards_point_limbs_bounded(*other)
    }
    */
    open spec fn eq_spec(&self, other: &Self) -> bool {
        // Two EdwardsPoints are equal if they represent the same affine point
        edwards_point_as_affine(*self) == edwards_point_as_affine(*other)
    }
}

impl PartialEq for EdwardsPoint {
    // VERIFICATION NOTE: PartialEqSpecImpl trait provides the external specification
    fn eq(&self, other: &EdwardsPoint) -> (result:
        bool)  /* VERIFICATION NOTE: we cannot add a "requires" clause to eq with PartialEqSpecImpl, */  // requires self.ct_eq_req(other),FORMATTER_NOT_INLINE_MARKER
        ensures
            result == (edwards_point_as_affine(*self) == edwards_point_as_affine(*other)),
    {
        /* ORIGINAL CODE:
        self.ct_eq(other).into()
        */
        let choice = self.ct_eq(other);
        let result = choice_into(choice);

        proof {
            assert(choice_is_true(choice) == (edwards_point_as_affine(*self)
                == edwards_point_as_affine(*other)));
            assert(result == choice_is_true(choice));
        }

        result
    }
}

impl Eq for EdwardsPoint {

}

// ------------------------------------------------------------------------
// Point conversions
// ------------------------------------------------------------------------
impl EdwardsPoint {
    /// Convert to a ProjectiveNielsPoint
    pub(crate) fn as_projective_niels(&self) -> (result: ProjectiveNielsPoint)
        requires
            edwards_point_limbs_bounded(*self),
            sum_of_limbs_bounded(&self.Y, &self.X, u64::MAX),
            is_valid_edwards_point(*self),
        ensures
            projective_niels_corresponds_to_edwards(result, *self),
            is_valid_projective_niels_point(result),
            fe51_limbs_bounded(&result.Y_plus_X, 54),
            fe51_limbs_bounded(&result.Y_minus_X, 54),
            fe51_limbs_bounded(&result.Z, 54),
            fe51_limbs_bounded(&result.T2d, 54),
    {
        proof {
            // Weaken from 52-bounded (EdwardsPoint invariant) to 54-bounded (sub/mul precondition)
            lemma_edwards_point_weaken_to_54(self);
            // EDWARDS_D2 is 54-bounded (actually 51-bounded)
            lemma_edwards_d2_limbs_bounded_54();
        }

        let result = ProjectiveNielsPoint {
            Y_plus_X: &self.Y + &self.X,
            Y_minus_X: &self.Y - &self.X,
            Z: self.Z,
            T2d: &self.T * &constants::EDWARDS_D2,
        };

        proof {
            // === Limb bounds proofs ===
            // Y_plus_X: add of 52-bounded gives 53-bounded, weaken to 54
            assert(fe51_limbs_bounded(&spec_add_fe51_limbs(&self.Y, &self.X), 53)) by {
                lemma_add_bounds_propagate(&self.Y, &self.X, 52);
            }
            assert(fe51_limbs_bounded(&result.Y_plus_X, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&result.Y_plus_X, 53, 54);
            }

            // Y_minus_X: sub postcondition guarantees 54-bounded (nothing to do)
            assert(fe51_limbs_bounded(&result.Y_minus_X, 54));

            // Z: copy of 52-bounded, weaken to 54
            assert(fe51_limbs_bounded(&result.Z, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&result.Z, 52, 54);
            }

            // T2d: mul postcondition guarantees 54-bounded (nothing to do)
            assert(fe51_limbs_bounded(&result.T2d, 54));

            // === Correspondence proof ===
            // Need: projective_niels_corresponds_to_edwards(result, *self)
            // Which requires (from the spec):
            //   y_plus_x == field_add(y, x)
            //   y_minus_x == field_sub(y, x)
            //   niels_z == z
            //   t2d == field_mul(field_mul(2, d), t)

            // Extract field element values for readability
            let x = fe51_as_canonical_nat(&self.X);
            let y = fe51_as_canonical_nat(&self.Y);
            let z = fe51_as_canonical_nat(&self.Z);
            let t = fe51_as_canonical_nat(&self.T);
            let d = fe51_as_canonical_nat(&crate::backend::serial::u64::constants::EDWARDS_D);
            let y_plus_x = fe51_as_canonical_nat(&result.Y_plus_X);
            let y_minus_x = fe51_as_canonical_nat(&result.Y_minus_X);
            let niels_z = fe51_as_canonical_nat(&result.Z);
            let t2d = fe51_as_canonical_nat(&result.T2d);

            // 1. y_plus_x == field_add(y, x) -- from add postcondition
            assert(y_plus_x == field_add(y, x));

            // 2. y_minus_x == field_sub(y, x) -- from sub postcondition
            assert(y_minus_x == field_sub(y, x));

            // 3. niels_z == z -- trivial since Z is copied
            assert(niels_z == z);

            // 4. t2d == field_mul(field_mul(2, d), t)
            assert(t2d == field_mul(field_mul(2, d), t)) by {
                // From mul postcondition: t2d == t * EDWARDS_D2
                assert(t2d == field_mul(t, fe51_as_canonical_nat(&constants::EDWARDS_D2)));

                // EDWARDS_D2 equals 2*d in the field.
                assert(fe51_as_canonical_nat(&constants::EDWARDS_D2) == field_mul(2, d)) by {
                    axiom_edwards_d2_is_2d();
                }

                // Rewrite and commute.
                assert(t2d == field_mul(t, field_mul(2, d)));
                lemma_field_mul_comm(t, field_mul(2, d));
                assert(field_mul(t, field_mul(2, d)) == field_mul(field_mul(2, d), t));
            }

            // All four conditions are satisfied, so correspondence holds
            assert(projective_niels_corresponds_to_edwards(result, *self));

            // Validity: the existential witness is *self
            assert(is_valid_projective_niels_point(result));
        }

        result
    }

    /// Convert the representation of this point from extended
    /// coordinates to projective coordinates.
    ///
    /// Free.
    pub(crate) const fn as_projective(&self) -> (result: ProjectivePoint)
        requires
            edwards_point_limbs_bounded(*self),
        ensures
            result.X == self.X,
            result.Y == self.Y,
            result.Z == self.Z,
            // ProjectivePoint invariant: 52-bounded (from EdwardsPoint invariant)
            fe51_limbs_bounded(&result.X, 52) && fe51_limbs_bounded(&result.Y, 52)
                && fe51_limbs_bounded(&result.Z, 52),
    {
        let result = ProjectivePoint { X: self.X, Y: self.Y, Z: self.Z };
        result
    }

    /// Dehomogenize to a AffineNielsPoint.
    /// Mainly for testing.
    pub(crate) fn as_affine_niels(&self) -> (result: AffineNielsPoint)
        requires
            edwards_point_limbs_bounded(*self),
            is_valid_edwards_point(*self),
        ensures
            affine_niels_corresponds_to_edwards(result, *self),
            is_valid_affine_niels_point(result),
    {
        proof {
            // Weaken from 52-bounded (EdwardsPoint invariant) to 54-bounded (invert/mul precondition)
            lemma_edwards_point_weaken_to_54(self);
            // EDWARDS_D2 is 54-bounded (actually 51-bounded)
            lemma_edwards_d2_limbs_bounded_54();
        }
        let recip = self.Z.invert();
        // recip bounded by 54 from invert() postcondition

        let x = &self.X * &recip;
        let y = &self.Y * &recip;
        // x, y bounded by 52 (and thus 54) from mul() postcondition

        let xy = &x * &y;
        // xy bounded by 52 (and thus 54) from mul() postcondition

        let xy2d = &xy * &constants::EDWARDS_D2;

        proof {
            // x and y are 52-bounded from mul postcondition, so sum_of_limbs_bounded holds
            assert(sum_of_limbs_bounded(&y, &x, u64::MAX)) by {
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&y, &x, 52);
            }
            // x and y are already 54-bounded from mul postcondition (line 502 in field.rs)
            assert(fe51_limbs_bounded(&y, 54) && fe51_limbs_bounded(&x, 54));
        }

        let result = AffineNielsPoint { y_plus_x: &y + &x, y_minus_x: &y - &x, xy2d };

        proof {
            // Prove affine_niels_corresponds_to_edwards(result, *self)
            let X = fe51_as_canonical_nat(&self.X);
            let Y = fe51_as_canonical_nat(&self.Y);
            let Z = fe51_as_canonical_nat(&self.Z);
            let d = fe51_as_canonical_nat(&crate::backend::serial::u64::constants::EDWARDS_D);

            let z_inv = field_inv(Z);
            let x_affine = field_mul(X, z_inv);  // X/Z
            let y_affine = field_mul(Y, z_inv);  // Y/Z

            assert(fe51_as_canonical_nat(&recip) == z_inv);
            assert(fe51_as_canonical_nat(&x) == x_affine);
            assert(fe51_as_canonical_nat(&y) == y_affine);

            assert(fe51_as_canonical_nat(&result.y_plus_x) == field_add(y_affine, x_affine));
            assert(fe51_as_canonical_nat(&result.y_minus_x) == field_sub(y_affine, x_affine));

            // xy2d: need to show (x*y)*(2*d) == ((x*y)*2)*d
            assert(fe51_as_canonical_nat(&xy) == field_mul(x_affine, y_affine));
            assert(fe51_as_canonical_nat(&constants::EDWARDS_D2) == field_mul(2, d)) by {
                axiom_edwards_d2_is_2d();
            }

            let xy_val = field_mul(x_affine, y_affine);
            lemma_field_mul_assoc(xy_val, 2, d);

            assert(affine_niels_corresponds_to_edwards(result, *self));

            // Validity: the existential witness is *self
            assert(is_valid_affine_niels_point(result));
        }

        result
    }

    /// Convert this `EdwardsPoint` on the Edwards model to the
    /// corresponding `MontgomeryPoint` on the Montgomery model.
    ///
    /// This function has one exceptional case; the identity point of
    /// the Edwards curve is sent to the 2-torsion point \\((0,0)\\)
    /// on the Montgomery curve.
    ///
    /// Note that this is a one-way conversion, since the Montgomery
    /// model does not retain sign information.
    pub fn to_montgomery(&self) -> (result: MontgomeryPoint)
        requires
            is_valid_edwards_point(*self),  // Gives us z != 0 for birational map
            fe51_limbs_bounded(&self.X, 54),
            // Y and Z need 52-bit bounds so U = Z + Y is 53-bit bounded (< 54 for mul)
            fe51_limbs_bounded(&self.Y, 52) && fe51_limbs_bounded(&self.Z, 52),
        ensures
            montgomery_corresponds_to_edwards(result, *self),
    {
        // We have u = (1+y)/(1-y) = (Z+Y)/(Z-Y).
        //
        // The denominator is zero only when y=1, the identity point of
        // the Edwards curve.  Since 0.invert() = 0, in this case we
        // compute the 2-torsion point (0,0).
        proof {
            // 52-bit bounded implies 54-bit bounded (for sub precondition)
            assert((1u64 << 52) < (1u64 << 54)) by (bit_vector);
            assert(fe51_limbs_bounded(&self.Y, 54));
            assert(fe51_limbs_bounded(&self.Z, 54));
            // Derive sum_of_limbs_bounded for add precondition
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&self.Z, &self.Y, 52);
        }

        // Ghost values for proof
        let ghost z = fe51_as_canonical_nat(&self.Z);
        let ghost y = fe51_as_canonical_nat(&self.Y);

        let U = &self.Z + &self.Y;
        let W = &self.Z - &self.Y;
        // W bounded by 54 from sub() postcondition
        // U bounded by 53 from add() postcondition (52-bit inputs → 53-bit output)
        proof {
            assert(fe51_limbs_bounded(&U, 53));  // from add postcondition
            assert((1u64 << 53) < (1u64 << 54)) by (bit_vector);
            assert(fe51_limbs_bounded(&U, 54));
        }

        // Ghost: track field element values through operations
        let ghost u_val = fe51_as_canonical_nat(&U);
        let ghost w_val = fe51_as_canonical_nat(&W);
        proof {
            // Operation postconditions give us:
            assert(u_val == field_add(z, y));  // add postcondition
            assert(w_val == field_sub(z, y));  // sub postcondition
        }

        /* ORIGINAL CODE:
         *   let u = &U * &W.invert();
         *   let result = MontgomeryPoint(u.as_bytes());
         *
         * Refactor: split `invert()`/`as_bytes()` into named intermediates to use their
         * postconditions locally
         */
        let W_inv = W.invert();
        let ghost w_inv_val = fe51_as_canonical_nat(&W_inv);
        proof {
            // invert postcondition
            assert(w_inv_val == field_inv(w_val));
        }

        let u = &U * &W_inv;
        let ghost u_field = fe51_as_canonical_nat(&u);
        proof {
            // mul postcondition: u_field = (Z+Y) * inv(Z-Y)
            assert(u_field == field_mul(u_val, w_inv_val));
            assert(u_field == field_mul(field_add(z, y), field_inv(field_sub(z, y))));
        }

        let u_bytes = u.as_bytes();
        let result = MontgomeryPoint(u_bytes);

        proof {
            // === Correspondence proof ===
            // Need: montgomery_corresponds_to_edwards(result, *self)
            // Step 1: Connect spec_montgomery(result) to u_field
            // as_bytes postcondition: u8_32_as_nat(&u.as_bytes()) == fe51_as_canonical_nat(&u)
            assert(u8_32_as_nat(&u_bytes) == fe51_as_canonical_nat(&u));

            // spec_montgomery(result) = field_element_from_bytes(&result.0)
            //                         = (u8_32_as_nat(&result.0) % pow2(255)) % p()
            // Since fe51_as_canonical_nat(&u) < p() < pow2(255), double mod is identity
            assert(fe51_as_canonical_nat(&u) < p()) by {
                p_gt_2();
                lemma_mod_bound(fe51_as_nat(&u) as int, p() as int);
            }
            assert(p() < pow2(255)) by {
                pow255_gt_19();  // establishes p() < pow2(255)
            }

            // u_field = fe51_as_canonical_nat(&u) < p() < pow2(255)
            // So: fe51_as_canonical_nat(&u) % pow2(255) = fe51_as_canonical_nat(&u)
            //     fe51_as_canonical_nat(&u) % p() = fe51_as_canonical_nat(&u)
            assert(field_element_from_bytes(&result.0) == u_field) by {
                lemma_small_mod(u_field, pow2(255));
                lemma_small_mod(u_field, p());
            }

            // Step 2: Get affine y-coordinate
            let (_x_affine, y_affine) = edwards_point_as_affine(*self);
            assert(y_affine == field_mul(y, field_inv(z)));

            // Step 3: z % p() != 0 directly from is_valid_edwards_point
            assert(z % p() != 0);
            // Step 4: Connect the formulas
            // u_field = (z+y) * inv(z-y)  [from operations above]
            // By axiom: this equals (1+y_affine) * inv(1-y_affine)
            let one_plus_y = field_add(1, y_affine);
            let one_minus_y = field_sub(1, y_affine);
            let affine_result = field_mul(one_plus_y, field_inv(one_minus_y));
            assert(u_field == affine_result) by {
                axiom_edwards_to_montgomery_correspondence(y, z);
            }

            // Step 5: Match the spec
            // montgomery_corresponds_to_edwards requires:
            //   if denominator == 0: u == 0  (identity case)
            //   else: u == (1+y)/(1-y)
            let denominator = field_sub(1, y_affine);
            if denominator == 0 {
                // Identity case: y_affine = 1, meaning Y = Z
                // one_minus_y == denominator == 0
                // field_inv(0) == 0 by definition
                // affine_result = field_mul(one_plus_y, 0) == 0
                assert(one_minus_y == 0);  // same as denominator
                assert(field_inv(one_minus_y) == 0);  // field_inv(0) = 0
                assert(affine_result == 0) by {
                    lemma_field_mul_zero_right(one_plus_y, field_inv(one_minus_y));
                }
                assert(u_field == 0);
            }
            assert(montgomery_corresponds_to_edwards(result, *self));
        }
        result
    }

    /// Compress this point to `CompressedEdwardsY` format.
    pub fn compress(&self) -> (result: CompressedEdwardsY)
        requires
            is_well_formed_edwards_point(*self),
        ensures
            compressed_edwards_y_corresponds_to_edwards(result, *self),
    {
        proof {
            // Weaken from 52-bounded (EdwardsPoint invariant) to 54-bounded (invert/mul precondition)
            lemma_edwards_point_weaken_to_54(self);
        }

        let recip = self.Z.invert();

        // Ghost values for proof
        let ghost x_coord = fe51_as_canonical_nat(&self.X);
        let ghost y_coord = fe51_as_canonical_nat(&self.Y);
        let ghost z_coord = fe51_as_canonical_nat(&self.Z);
        let ghost z_inv = field_inv(z_coord);

        proof {
            // From is_well_formed_edwards_point → is_valid_edwards_point → z % p != 0
            assert(z_coord % p() != 0);
            // z_coord = fe51_as_canonical_nat(...) = fe51_as_nat(...) % p(), hence < p()
            p_gt_2();
            assert(z_coord < p()) by {
                lemma_mod_bound(fe51_as_nat(&self.Z) as int, p() as int);
            };
            assert(z_coord != 0) by {
                lemma_small_mod(z_coord, p());
            };
            assert(fe51_as_canonical_nat(&recip) == z_inv);
        }

        let x = &self.X * &recip;
        let y = &self.Y * &recip;

        let ghost x_affine = fe51_as_canonical_nat(&x);
        let ghost y_affine = fe51_as_canonical_nat(&y);

        proof {
            // From mul postcondition: fe51_as_canonical_nat(&result) = field_mul(...)
            assert(x_affine == field_mul(x_coord, z_inv));
            assert(y_affine == field_mul(y_coord, z_inv));

            // These match edwards_point_as_affine
            let (spec_x_affine, spec_y_affine) = edwards_point_as_affine(*self);
            assert(spec_x_affine == x_affine);
            assert(spec_y_affine == y_affine);
        }

        let mut s: [u8; 32];

        s = y.as_bytes();
        let ghost s_before_xor: [u8; 32] = s;

        s[31] ^= x.is_negative().unwrap_u8() << 7;

        let is_neg_choice = x.is_negative();
        let sign_bit = is_neg_choice.unwrap_u8();

        proof {
            // Establish p() > 0 for lemma_mod_bound preconditions
            p_gt_2();

            // Establish y_affine < p() (from field_mul definition: result = (a*b) % p < p)
            // and x_affine < p() similarly
            assert(y_affine < p()) by {
                // field_mul returns (a * b) % p, which is < p
                p_gt_2();
                lemma_mod_bound((y_coord * z_inv) as int, p() as int);
            };
            assert(x_affine < p()) by {
                p_gt_2();
                lemma_mod_bound((x_coord * z_inv) as int, p() as int);
            };

            // as_bytes ensures: u8_32_as_nat(&s_before_xor) == fe51_as_canonical_nat(&y) == y_affine
            assert(u8_32_as_nat(&s_before_xor) == y_affine);

            // Postcondition is compressed_edwards_y_corresponds_to_edwards(result, *self)
            // which requires:
            // 1. field_element_from_bytes(&s) == y_affine (the y-coordinate)
            // 2. (s[31] >> 7) == (((x_affine % p()) % 2) as u8) (the sign bit)

            // Prove s_before_xor has bit 255 clear
            assert((s_before_xor[31] >> 7) == 0) by {
                lemma_canonical_bytes_bit255_zero(&s_before_xor, y_affine);
            }

            // Connect is_negative to x_affine parity
            assert(choice_is_true(is_neg_choice) == (fe51_as_canonical_nat(&x) % 2 == 1)) by {
                lemma_is_negative_equals_parity(&x);
            }
            assert(fe51_as_canonical_nat(&x) == x_affine);
            assert(choice_is_true(is_neg_choice) == (x_affine % 2 == 1));

            // unwrap_u8 converts choice to u8: true->1, false->0
            // Establish sign_bit value based on unwrap_u8 spec
            assert(sign_bit == ((x_affine % p()) % 2) as u8) by {
                if choice_is_true(is_neg_choice) {
                    assert(sign_bit == 1);
                    assert(x_affine % 2 == 1);
                    assert((x_affine % p()) % 2 == x_affine % 2) by {
                        assert(x_affine < p());
                        lemma_small_mod(x_affine, p());
                    };
                } else {
                    assert(sign_bit == 0);
                    assert(x_affine % 2 == 0);
                    assert((x_affine % p()) % 2 == x_affine % 2) by {
                        assert(x_affine < p());
                        lemma_small_mod(x_affine, p());
                    };
                }
            };

            // Prove XOR preserves y and sets sign bit
            assert(field_element_from_bytes(&s) == y_affine && (s[31] >> 7) == sign_bit) by {
                lemma_xor_sign_bit_preserves_y(&s_before_xor, &s, y_affine, sign_bit);
            }

            // Both parts of compressed_edwards_y_corresponds_to_edwards are satisfied
            assert(compressed_edwards_y_corresponds_to_edwards(CompressedEdwardsY(s), *self));
        }

        CompressedEdwardsY(s)
    }

    #[cfg(feature = "digest")]
    /// Maps the digest of the input bytes to the curve. This is NOT a hash-to-curve function, as
    /// it produces points with a non-uniform distribution. Rather, it performs something that
    /// resembles (but is not) half of the
    /// [`hash_to_curve`](https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-16.html#section-3-4.2.1)
    /// function from the Elligator2 spec.
    #[deprecated(
        since = "4.0.0",
        note = "previously named `hash_from_bytes`, this is not a secure hash function"
    )]
    #[verifier::external_body]
    pub fn nonspec_map_to_curve<D>(bytes: &[u8]) -> EdwardsPoint where
        D: Digest<OutputSize = U64> + Default,
     {
        let mut hash = D::new();
        hash.update(bytes);
        let h = hash.finalize();
        let mut res = [0u8;32];
        res.copy_from_slice(&h[0..32]);

        let sign_bit = (res[31] & 0x80) >> 7;

        let fe = FieldElement::from_bytes(&res);

        let M1 = crate::montgomery::elligator_encode(&fe);
        let E1_opt = M1.to_edwards(sign_bit);

        E1_opt.expect(
            "Montgomery conversion to Edwards point in Elligator failed",
        ).mul_by_cofactor()
    }

    /// VERIFICATION NOTE: Verus-compatible version of nonspec_map_to_curve that uses SHA-512 instead of Digest.
    #[cfg(feature = "digest")]
    pub fn nonspec_map_to_curve_verus(bytes: &[u8]) -> (result: EdwardsPoint)
        ensures
            is_well_formed_edwards_point(result),
            // Functional correctness: result = spec applied to first 32 bytes of SHA-512(input)
            edwards_point_as_affine(result) == spec_nonspec_map_to_curve(
                spec_sha512(bytes@).subrange(0, 32),
            ),
    {
        /* ORIGINAL CODE:
        let mut hash = D::new();
        hash.update(bytes);
        let h = hash.finalize();
        let mut res = [0u8;32];
        res.copy_from_slice(&h[0..32]);
        */
        /* REFACTOR START: */
        use crate::core_assumes::first_32_bytes;

        // Hash input using SHA-512 (produces 64 bytes, like original D::finalize())
        let hash: [u8; 64] = sha512_hash_bytes(bytes);

        // Take first 32 bytes (like original: res.copy_from_slice(&h[0..32]))
        let res: [u8; 32] = first_32_bytes(&hash);
        /* REFACTOR END*/

        // Extract sign bit from high bit of last byte
        /* ORIGINAL CODE: let sign_bit: u8 = (res[31] & 0x80u8) >> 7u8; */
        let byte31 = res[31];  // extract for proof blocks (avoids Verus array_view issue)
        let sign_bit: u8 = (byte31 & 0x80u8) >> 7u8;

        // Convert to field element
        let fe = FieldElement::from_bytes(&res);

        // Apply Elligator encoding to get Montgomery point
        let M1 = crate::montgomery::elligator_encode(&fe);

        // Convert to Edwards point
        proof {
            assert(sign_bit == 0 || sign_bit == 1) by (bit_vector)
                requires
                    sign_bit == (byte31 & 0x80u8) >> 7u8,
            ;
        }
        let E1_opt = M1.to_edwards(sign_bit);

        // elligator_encode never produces u = -1 (lemma_elligator_never_minus_one),
        // so to_edwards always returns Some. Unwrap and multiply by cofactor.
        proof {
            // to_edwards returns None only when is_equal_to_minus_one(u),
            // but elligator_encode guarantees !is_equal_to_minus_one(u).
            assert(!is_equal_to_minus_one(spec_montgomery(M1)));
            match E1_opt {
                Some(_) => {},
                None => {
                    assert(false);
                },
            }
            assert(E1_opt.is_some());
        }
        let E1 = E1_opt.expect("Montgomery conversion to Edwards point in Elligator failed");
        let result = E1.mul_by_cofactor();

        proof {
            // Step 1: res@ matches the spec hash input
            assert(res@ == spec_sha512(bytes@).subrange(0, 32));

            // Step 2: sign_bit ∈ {0,1} and normalisation is identity
            assert(sign_bit == 0 || sign_bit == 1) by (bit_vector)
                requires
                    sign_bit == (byte31 & 0x80u8) >> 7u8,
            ;
            assert(sign_bit == spec_normalize_sign(sign_bit)) by (bit_vector)
                requires
                    sign_bit == 0u8 || sign_bit == 1u8,
            ;

            // Step 3: bridge u8_32_as_nat ↔ bytes_seq_as_nat
            lemma_u8_32_as_nat_eq_bytes_seq_as_nat(&res);

            // Step 4: field element value matches spec
            let fe_nat_spec = (bytes_seq_as_nat(res@) % pow2(255)) % p();
            assert(fe51_as_canonical_nat(&fe) == fe_nat_spec) by {
                // from_bytes: u64_5_as_nat(fe.limbs) == u8_32_as_nat(&res) % pow2(255)
                // fe51_as_canonical_nat = u64_5_as_nat(fe.limbs) % p()
                // With lemma: u8_32_as_nat(&res) == bytes_seq_as_nat(res@)
            }

            // Step 5: elligator result matches spec
            let u = spec_elligator_encode(fe_nat_spec);
            assert(spec_montgomery(M1) == u);

            // Step 6: to_edwards gives exact equality with spec
            let P = spec_montgomery_to_edwards_affine(u, sign_bit);
            assert(edwards_point_as_affine(E1) == P) by {
                assert(is_valid_montgomery_point(M1));
                assert(!is_equal_to_minus_one(spec_montgomery(M1)));
                // to_edwards postcondition with sign normalisation
                assert(spec_montgomery_to_edwards_affine(
                    spec_montgomery(M1),
                    spec_normalize_sign(sign_bit),
                ) == P);
            }

            // Step 7: mul_by_cofactor links result to E1
            assert(edwards_point_as_affine(result) == edwards_scalar_mul(
                edwards_point_as_affine(E1),
                8,
            ));

            // Step 8: combine — the result equals the spec
            assert(edwards_point_as_affine(result) == edwards_scalar_mul(P, 8));
            assert(edwards_point_as_affine(result) == spec_nonspec_map_to_curve(res@));
        }

        result
    }
}

// ------------------------------------------------------------------------
// Doubling
// ------------------------------------------------------------------------
impl EdwardsPoint {
    /// Add this point to itself.
    pub(crate) fn double(&self) -> (result: EdwardsPoint)
        requires
            is_valid_edwards_point(*self),  // self is a valid extended Edwards point
            edwards_point_limbs_bounded(*self),
        ensures
            is_valid_edwards_point(result),  // result is also a valid Edwards point
            // Result equals the affine doubling of the input.
            edwards_point_as_affine(result) == edwards_double(
                edwards_point_as_affine(*self).0,
                edwards_point_as_affine(*self).1,
            ),
    {
        /* ORIGINAL CODE
        self.as_projective().double().as_extended()
        */
        let proj = self.as_projective();
        proof {
            // is_valid_edwards_point gives z % p() != 0; since z = fe51_as_canonical_nat < p,
            // z % p = z, so z != 0 — which is what is_valid_projective_point needs
            let z = fe51_as_canonical_nat(&self.Z);
            assert(z % p() != 0);
            p_gt_2();
            assert(z < p()) by {
                lemma_mod_bound(fe51_as_nat(&self.Z) as int, p() as int);
            };
            assert(z != 0) by {
                lemma_small_mod(z, p());
            };
            assert(is_valid_projective_point(proj));
            // ProjectivePoint invariant: 52-bounded (from as_projective postcondition)
            assert(fe51_limbs_bounded(&proj.X, 52) && fe51_limbs_bounded(&proj.Y, 52)
                && fe51_limbs_bounded(&proj.Z, 52));
            // sum_of_limbs_bounded follows from 52-bounded: 2^52 + 2^52 = 2^53 < u64::MAX
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&proj.X, &proj.Y, 52);
        }

        let doubled = proj.double();
        proof {
            // projective double() spec guarantees this
            assert(is_valid_completed_point(doubled));
        }

        let result = doubled.as_extended();

        proof {
            // completed → extended conversion preserves affine meaning
            assert(edwards_point_as_affine(result) == completed_point_as_affine_edwards(doubled));

            // And from the lower-level double() spec:
            assert(completed_point_as_affine_edwards(doubled) == edwards_double(
                edwards_point_as_affine(*self).0,
                edwards_point_as_affine(*self).1,
            ));
        }

        result
    }
}

// ------------------------------------------------------------------------
// Addition and Subtraction
// ------------------------------------------------------------------------
/// Spec for &EdwardsPoint + &EdwardsPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl<&EdwardsPoint> for &EdwardsPoint {
    open spec fn obeys_add_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn add_req(self, rhs: &EdwardsPoint) -> bool {
        is_well_formed_edwards_point(*self) && is_well_formed_edwards_point(*rhs)
    }

    open spec fn add_spec(self, rhs: &EdwardsPoint) -> EdwardsPoint {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

impl<'a, 'b> Add<&'b EdwardsPoint> for &'a EdwardsPoint {
    type Output = EdwardsPoint;

    fn add(self, other: &'b EdwardsPoint) -> (result:
        EdwardsPoint)/* requires clause in AddSpecImpl<&EdwardsPoint> for &EdwardsPoint above:
            is_well_formed_edwards_point(*self) && is_well_formed_edwards_point(*rhs)
        */

        ensures
            is_well_formed_edwards_point(result),
            // Semantic correctness: affine addition law
            ({
                let (x1, y1) = edwards_point_as_affine(*self);
                let (x2, y2) = edwards_point_as_affine(*other);
                edwards_point_as_affine(result) == edwards_add(x1, y1, x2, y2)
            }),
    {
        /* ORIGINAL CODE
        (self + &other.as_projective_niels()).as_extended()
        */
        // From is_well_formed_edwards_point preconditions:
        // - edwards_point_limbs_bounded(*self) and (*other)
        // - sum_of_limbs_bounded(&self.Y, &self.X, u64::MAX) and for other
        assert(sum_of_limbs_bounded(&self.Y, &self.X, u64::MAX));
        assert(edwards_point_limbs_bounded(*other));
        assert(sum_of_limbs_bounded(&other.Y, &other.X, u64::MAX));

        let other_niels = other.as_projective_niels();

        proof {
            // Limb bounds for other_niels follow from as_projective_niels postconditions
            // (which we proved earlier in this file)
            assert(fe51_limbs_bounded(&other_niels.Y_plus_X, 54));
            assert(fe51_limbs_bounded(&other_niels.Y_minus_X, 54));
            assert(fe51_limbs_bounded(&other_niels.Z, 54));
            assert(fe51_limbs_bounded(&other_niels.T2d, 54));
        }

        let sum = self + &other_niels;

        proof {
            // The inner add operation (EdwardsPoint + ProjectiveNielsPoint) → CompletedPoint
            // has postconditions that give us validity and limb bounds.
            // These follow from the ensures clause of the inner add.
            assert(is_valid_completed_point(sum));
            assert(fe51_limbs_bounded(&sum.X, 54));
            assert(fe51_limbs_bounded(&sum.Y, 54));
            assert(fe51_limbs_bounded(&sum.Z, 54));
            assert(fe51_limbs_bounded(&sum.T, 54));
        }

        let result = sum.as_extended();

        proof {
            // CompletedPoint::as_extended postconditions give us:
            // - is_well_formed_edwards_point(result)
            // - edwards_point_as_affine(result) == completed_point_as_affine_edwards(sum)
            assert(is_well_formed_edwards_point(result));
            assert(edwards_point_as_affine(result) == completed_point_as_affine_edwards(sum));

            // Connect niels_affine to other_affine via correspondence
            assert(projective_niels_point_as_affine_edwards(other_niels) == edwards_point_as_affine(
                *other,
            )) by {
                lemma_projective_niels_affine_equals_edwards_affine(other_niels, *other);
            }

            let (x1, y1) = edwards_point_as_affine(*self);
            let (x2, y2) = edwards_point_as_affine(*other);
            assert(edwards_point_as_affine(result) == edwards_add(x1, y1, x2, y2));
        }

        result
    }
}

define_add_variants!(
    LHS = EdwardsPoint,
    RHS = EdwardsPoint,
    Output = EdwardsPoint
);

impl<'b> AddAssign<&'b EdwardsPoint> for EdwardsPoint {
    fn add_assign(&mut self, _rhs: &'b EdwardsPoint)
        requires
            is_well_formed_edwards_point(*old(self)),
            is_well_formed_edwards_point(*_rhs),
        ensures
            is_well_formed_edwards_point(*self),
            // Semantic correctness: result is the addition of old(self) + rhs
            ({
                let (x1, y1) = edwards_point_as_affine(*old(self));
                let (x2, y2) = edwards_point_as_affine(*_rhs);
                edwards_point_as_affine(*self) == edwards_add(x1, y1, x2, y2)
            }),
    {
        /* ORIGINAL CODE
        *self = (self as &EdwardsPoint) + _rhs;
        CAST TO &EdwardsPoint UNSUPPORTED */
        *self = &*self + _rhs;
    }
}

define_add_assign_variants!(LHS = EdwardsPoint, RHS = EdwardsPoint);

// ------------------------------------------------------------------------
// Subtraction
// ------------------------------------------------------------------------
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::SubSpecImpl<&EdwardsPoint> for &EdwardsPoint {
    open spec fn obeys_sub_spec() -> bool {
        false
    }

    open spec fn sub_req(self, rhs: &EdwardsPoint) -> bool {
        is_well_formed_edwards_point(*self) && is_well_formed_edwards_point(*rhs)
    }

    open spec fn sub_spec(self, rhs: &EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

impl<'a, 'b> Sub<&'b EdwardsPoint> for &'a EdwardsPoint {
    type Output = EdwardsPoint;

    fn sub(self, other: &'b EdwardsPoint) -> (result:
        EdwardsPoint)/* requires clause in SubSpecImpl<&EdwardsPoint> for &EdwardsPoint above:
            is_well_formed_edwards_point(*self) && is_well_formed_edwards_point(*rhs)
        */

        ensures
            is_well_formed_edwards_point(result),
            // Semantic correctness: affine subtraction law
            ({
                let (x1, y1) = edwards_point_as_affine(*self);
                let (x2, y2) = edwards_point_as_affine(*other);
                edwards_point_as_affine(result) == edwards_sub(x1, y1, x2, y2)
            }),
    {
        /* ORIGINAL CODE
        (self - &other.as_projective_niels()).as_extended()
        */
        // From is_well_formed_edwards_point preconditions:
        // - edwards_point_limbs_bounded(*self) and (*other)
        // - sum_of_limbs_bounded(&self.Y, &self.X, u64::MAX) and for other
        assert(sum_of_limbs_bounded(&self.Y, &self.X, u64::MAX));
        assert(edwards_point_limbs_bounded(*other));
        assert(sum_of_limbs_bounded(&other.Y, &other.X, u64::MAX));

        let other_niels = other.as_projective_niels();

        proof {
            // Limb bounds for other_niels follow from as_projective_niels postconditions
            // (which we proved earlier in this file)
            assert(fe51_limbs_bounded(&other_niels.Y_plus_X, 54));
            assert(fe51_limbs_bounded(&other_niels.Y_minus_X, 54));
            assert(fe51_limbs_bounded(&other_niels.Z, 54));
            assert(fe51_limbs_bounded(&other_niels.T2d, 54));
        }

        let diff = self - &other_niels;

        proof {
            // The inner sub operation (EdwardsPoint - ProjectiveNielsPoint) → CompletedPoint
            // has postconditions that give us validity and limb bounds.
            // These follow from the ensures clause of the inner sub.
            assert(is_valid_completed_point(diff));
            assert(fe51_limbs_bounded(&diff.X, 54));
            assert(fe51_limbs_bounded(&diff.Y, 54));
            assert(fe51_limbs_bounded(&diff.Z, 54));
            assert(fe51_limbs_bounded(&diff.T, 54));
        }

        let result = diff.as_extended();

        proof {
            // CompletedPoint::as_extended postconditions give us:
            // - is_well_formed_edwards_point(result)
            // - edwards_point_as_affine(result) == completed_point_as_affine_edwards(diff)
            assert(is_well_formed_edwards_point(result));
            assert(edwards_point_as_affine(result) == completed_point_as_affine_edwards(diff));

            // The inner sub postcondition gives us:
            // completed_point_as_affine_edwards(diff) == edwards_sub(self_affine, other_niels_affine)
            let self_affine = edwards_point_as_affine(*self);
            let other_niels_affine = projective_niels_point_as_affine_edwards(other_niels);
            assert(completed_point_as_affine_edwards(diff) == edwards_sub(
                self_affine.0,
                self_affine.1,
                other_niels_affine.0,
                other_niels_affine.1,
            ));

            // The as_projective_niels postcondition gives us correspondence between other and other_niels
            assert(projective_niels_corresponds_to_edwards(other_niels, *other));

            // Use the lemma that shows the affine representations are equal
            assert(projective_niels_point_as_affine_edwards(other_niels) == edwards_point_as_affine(
                *other,
            )) by {
                lemma_projective_niels_affine_equals_edwards_affine(other_niels, *other);
            }

            // Now connect: edwards_sub with other_niels_affine == edwards_sub with other_affine
            let (x1, y1) = edwards_point_as_affine(*self);
            let (x2, y2) = edwards_point_as_affine(*other);
            assert(edwards_point_as_affine(result) == edwards_sub(x1, y1, x2, y2));
        }

        result
    }
}

define_sub_variants!(
    LHS = EdwardsPoint,
    RHS = EdwardsPoint,
    Output = EdwardsPoint
);

impl<'b> SubAssign<&'b EdwardsPoint> for EdwardsPoint {
    fn sub_assign(&mut self, _rhs: &'b EdwardsPoint)
        requires
            is_well_formed_edwards_point(*old(self)),
            is_well_formed_edwards_point(*_rhs),
        ensures
            is_well_formed_edwards_point(*self),
            // Semantic correctness: result is the subtraction of old(self) - rhs
            ({
                let (x1, y1) = edwards_point_as_affine(*old(self));
                let (x2, y2) = edwards_point_as_affine(*_rhs);
                edwards_point_as_affine(*self) == edwards_sub(x1, y1, x2, y2)
            }),
    {
        /* ORIGINAL CODE
        *self = (self as &EdwardsPoint) - _rhs;
        CAST TO &EdwardsPoint UNSUPPORTED */
        *self = &*self - _rhs;
    }
}

} // verus!
define_sub_assign_variants!(LHS = EdwardsPoint, RHS = EdwardsPoint);

verus! {

impl EdwardsPoint {
    /// Compute the sum of all EdwardsPoints in a slice.
    ///
    /// # Returns
    ///
    /// The sum of all points using elliptic curve addition.
    #[allow(clippy::needless_range_loop, clippy::op_ref)]
    pub fn sum_of_slice(points: &[EdwardsPoint]) -> (result: EdwardsPoint)
        requires
            forall|i: int|
                0 <= i < points@.len() ==> is_well_formed_edwards_point(#[trigger] points@[i]),
        ensures
            is_well_formed_edwards_point(result),
            edwards_point_as_affine(result) == sum_of_points(points@),
    {
        let n = points.len();
        let mut acc = EdwardsPoint::identity();

        proof {
            assert(points@.subrange(0, 0) =~= Seq::<EdwardsPoint>::empty());
            // identity() has affine coords (0, 1) which equals sum_of_points(empty)
            lemma_identity_affine_coords(acc);
        }

        for i in 0..n
            invariant
                n == points.len(),
                is_well_formed_edwards_point(acc),
                edwards_point_as_affine(acc) == sum_of_points(points@.subrange(0, i as int)),
                forall|j: int|
                    0 <= j < points@.len() ==> is_well_formed_edwards_point(#[trigger] points@[j]),
        {
            proof {
                let sub = points@.subrange(0, (i + 1) as int);
                assert(sub.subrange(0, i as int) =~= points@.subrange(0, i as int));
            }

            acc = &acc + &points[i];

        }

        proof {
            assert(points@.subrange(0, n as int) =~= points@);
        }

        acc
    }
}

/* <ORIGINAL CODE>
impl<T> Sum<T> for EdwardsPoint
where
    T: Borrow<EdwardsPoint>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(EdwardsPoint::identity(), |acc, item| acc + item.borrow())
    }
}
</ORIGINAL CODE> */

/* <VERIFICATION NOTE>
Iterator operations and Borrow trait are not directly supported by Verus.
We use an external_body helper to collect the iterator into Vec<EdwardsPoint>,
then call the verified sum_of_slice function for the actual computation.
TESTING: `mod test_sum` (at the bottom of this file) checks functional equivalence between
`sum_original` and the refactored `Sum::sum` implementation on random inputs.
</VERIFICATION NOTE> */

impl EdwardsPoint {
    /// Original `Sum` implementation using `Iterator::fold`.
    ///
    /// This is used for exec correctness/performance, but is not verified directly.
    /// The verified implementation is `Sum::sum` below, which reduces to `sum_of_slice`.
    /// Functional equivalence is tested in `mod test_sum` (at the bottom of this file).
    #[verifier::external_body]
    pub fn sum_original<T, I>(iter: I) -> (result: EdwardsPoint) where
        T: Borrow<EdwardsPoint>,
        I: Iterator<Item = T>,
     {
        iter.fold(EdwardsPoint::identity(), |acc, item| acc + item.borrow())
    }
}

impl<T> Sum<T> for EdwardsPoint where T: Borrow<EdwardsPoint> {
    fn sum<I>(iter: I) -> (result: Self) where I: Iterator<Item = T>
        requires
            forall|i: int|
                0 <= i < spec_points_from_iter::<T, I>(iter).len()
                    ==> #[trigger] is_well_formed_edwards_point(
                    spec_points_from_iter::<T, I>(iter)[i],
                ),
        ensures
            is_well_formed_edwards_point(result),
            edwards_point_as_affine(result) == sum_of_points(spec_points_from_iter::<T, I>(iter)),
    {
        let points = collect_points_from_iter(iter);
        EdwardsPoint::sum_of_slice(&points)
    }
}

// ------------------------------------------------------------------------
// Negation
// ------------------------------------------------------------------------
/// Spec for &EdwardsPoint negation
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::NegSpecImpl for &EdwardsPoint {
    open spec fn obeys_neg_spec() -> bool {
        false  // Set to false since we use arbitrary() as placeholder

    }

    open spec fn neg_req(self) -> bool {
        // Strengthened precondition: require well-formed point (validity + bounds + sum bounded)
        // This enables proving all postconditions without assumes
        is_well_formed_edwards_point(*self)
    }

    open spec fn neg_spec(self) -> EdwardsPoint {
        arbitrary()  // Placeholder - actual semantics are field-wise negation

    }
}

impl<'a> Neg for &'a EdwardsPoint {
    type Output = EdwardsPoint;

    fn neg(self) -> (result:
        EdwardsPoint)
    // requires clause in NegSpecImpl for &EdwardsPoint above:
    //   is_well_formed_edwards_point(*self)

        ensures
            is_well_formed_edwards_point(result),
            edwards_point_as_affine(result) == edwards_neg(edwards_point_as_affine(*self)),
    {
        /* ORIGINAL CODE
        EdwardsPoint {
            X: -(&self.X),
            Y: self.Y,
            Z: self.Z,
            T: -(&self.T),
        }
        */
        // REFACTORED: Use explicit Neg::neg() calls instead of operator shortcuts
        // to avoid Verus panic
        use core::ops::Neg;

        assert(1u64 << 52 < 1u64 << 54) by (bit_vector);

        // Store ghost values before negation
        let ghost old_x = fe51_as_canonical_nat(&self.X);
        let ghost old_y = fe51_as_canonical_nat(&self.Y);
        let ghost old_z = fe51_as_canonical_nat(&self.Z);
        let ghost old_t = fe51_as_canonical_nat(&self.T);

        let r = EdwardsPoint { X: Neg::neg(&self.X), Y: self.Y, Z: self.Z, T: Neg::neg(&self.T) };

        proof {
            // Ghost values for r
            let new_x = fe51_as_canonical_nat(&r.X);
            let new_y = fe51_as_canonical_nat(&r.Y);
            let new_z = fe51_as_canonical_nat(&r.Z);
            let new_t = fe51_as_canonical_nat(&r.T);

            // From FieldElement51::neg postconditions:
            // - new_x = field_neg(old_x)
            // - new_t = field_neg(old_t)
            // - X and T limbs are 52-bounded
            assert(new_x == field_neg(old_x));
            assert(new_t == field_neg(old_t));
            assert(new_y == old_y);  // Y unchanged
            assert(new_z == old_z);  // Z unchanged

            // 1. Prove edwards_point_limbs_bounded(r)
            // X and T are 52-bounded from neg postcondition
            assert(fe51_limbs_bounded(&r.X, 52));
            assert(fe51_limbs_bounded(&r.T, 52));
            // Y and Z bounds from precondition: is_well_formed_edwards_point implies edwards_point_limbs_bounded
            assert(fe51_limbs_bounded(&r.Y, 52));  // Y unchanged, bounded from precondition
            assert(fe51_limbs_bounded(&r.Z, 52));  // Z unchanged, bounded from precondition

            // 2. Prove sum_of_limbs_bounded(&r.Y, &r.X, u64::MAX)
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&r.Y, &r.X, 52);

            // 3. Prove is_valid_edwards_point(r)
            // Use lemma_negation_preserves_extended_validity: (-X, Y, Z, -T) is valid if (X, Y, Z, T) is
            lemma_negation_preserves_extended_validity(old_x, old_y, old_z, old_t);
            assert(is_valid_edwards_point(r));

            // 4. Prove affine semantics: edwards_point_as_affine(r) == edwards_neg(edwards_point_as_affine(*self))
            let z_inv = field_inv(old_z);

            // Key algebraic fact: (-x) * z_inv = -(x * z_inv)
            assert(field_mul(new_x, z_inv) == field_neg(field_mul(old_x, z_inv))) by {
                // new_x = field_neg(old_x)
                // field_mul(neg(a), b) = neg(field_mul(a, b)) by field algebra
                lemma_field_mul_comm(new_x, z_inv);
                lemma_field_mul_neg(z_inv, old_x);
                lemma_field_mul_comm(z_inv, old_x);
            };

            // The affine coords match: (neg(x/z), y/z) = edwards_neg((x/z, y/z))
            assert(edwards_point_as_affine(r) == edwards_neg(edwards_point_as_affine(*self)));
        }
        r
    }
}

/// Spec for EdwardsPoint (owned) negation
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::NegSpecImpl for EdwardsPoint {
    open spec fn obeys_neg_spec() -> bool {
        false  // Set to false since we delegate to &EdwardsPoint

    }

    open spec fn neg_req(self) -> bool {
        // Same requirements as &EdwardsPoint - strengthened to require well-formed point
        is_well_formed_edwards_point(self)
    }

    open spec fn neg_spec(self) -> EdwardsPoint {
        arbitrary()  // Placeholder - delegates to &EdwardsPoint negation

    }
}

impl Neg for EdwardsPoint {
    type Output = EdwardsPoint;

    fn neg(self) -> (result:
        EdwardsPoint)
    // requires clause in NegSpecImpl for EdwardsPoint above:
    //   fe51_limbs_bounded(&self.X, 52) && fe51_limbs_bounded(&self.T, 52)

        ensures
            is_well_formed_edwards_point(result),
            edwards_point_as_affine(result) == edwards_neg(edwards_point_as_affine(self)),
    {
        /* ORIGINAL CODE
        -&self
        */
        // REFACTORED: Use explicit Neg::neg() call to avoid Verus type inference issues
        use core::ops::Neg;
        Neg::neg(&self)
    }
}

// ------------------------------------------------------------------------
// Scalar multiplication
// ------------------------------------------------------------------------
impl<'b> MulAssign<&'b Scalar> for EdwardsPoint {
    fn mul_assign(&mut self, scalar: &'b Scalar)
        requires
            scalar.bytes[31] <= 127,
            is_well_formed_edwards_point(*old(self)),
        ensures
            is_well_formed_edwards_point(*self),
            edwards_point_as_affine(*self) == edwards_scalar_mul(
                edwards_point_as_affine(*old(self)),
                scalar_as_nat(scalar),
            ),
    {
        /* ORIGINAL CODE
        let result = (self as &EdwardsPoint) * scalar;
        CAST TO &EdwardsPoint UNSUPPORTED */
        let result = &*self * scalar;
        *self = result;
    }
}

} // verus!
define_mul_assign_variants!(LHS = EdwardsPoint, RHS = Scalar);

define_edwards_scalar_mul_variants_verus!();

verus! {

impl<'a, 'b> Mul<&'b Scalar> for &'a EdwardsPoint {
    type Output = EdwardsPoint;

    /// Scalar multiplication: compute `scalar * self`.
    ///
    /// For scalar multiplication of a basepoint,
    /// `EdwardsBasepointTable` is approximately 4x faster.
    fn mul(self, scalar: &'b Scalar) -> (result:
        EdwardsPoint)/* requires clause in MulSpecImpl<&Scalar> for &EdwardsPoint in arithm_trait_specs.rs:
            requires rhs.bytes[31] <= 127 && is_well_formed_edwards_point(*self)
        */

        ensures
            is_well_formed_edwards_point(result),
            edwards_point_as_affine(result) == edwards_scalar_mul(
                edwards_point_as_affine(*self),
                scalar_as_nat(scalar),
            ),
    {
        crate::backend::variable_base_mul(self, scalar)
    }
}

impl<'a, 'b> Mul<&'b EdwardsPoint> for &'a Scalar {
    type Output = EdwardsPoint;

    /// Scalar multiplication: compute `scalar * point`.
    ///
    /// For scalar multiplication of a basepoint,
    /// `EdwardsBasepointTable` is approximately 4x faster.
    fn mul(self, point: &'b EdwardsPoint) -> (result:
        EdwardsPoint)/* requires clause in MulSpecImpl<&EdwardsPoint> for &Scalar in arithm_trait_specs.rs:
            requires self.bytes[31] <= 127 && is_well_formed_edwards_point(*rhs)
        */

        ensures
            is_well_formed_edwards_point(result),
            edwards_point_as_affine(result) == edwards_scalar_mul(
                edwards_point_as_affine(*point),
                scalar_as_nat(self),
            ),
    {
        point * self
    }
}

impl EdwardsPoint {
    /// Fixed-base scalar multiplication by the Ed25519 base point.
    ///
    /// Uses precomputed basepoint tables when the `precomputed-tables` feature
    /// is enabled, trading off increased code size for ~4x better performance.
    pub fn mul_base(scalar: &Scalar) -> (result: Self)
        requires
            scalar.bytes[31] <= 127,
        ensures
            is_well_formed_edwards_point(result),
            // Functional correctness: result = [scalar] * B where B is the basepoint
            edwards_point_as_affine(result) == edwards_scalar_mul(
                spec_ed25519_basepoint(),
                scalar_as_nat(scalar),
            ),
    {
        #[cfg(not(feature = "precomputed-tables"))]
        { scalar * constants::ED25519_BASEPOINT_POINT }
        #[cfg(feature = "precomputed-tables")]
        {
            proof {
                axiom_ed25519_basepoint_table_valid();
            }
            scalar * constants::ED25519_BASEPOINT_TABLE
        }
    }

    /// Multiply this point by `clamp_integer(bytes)`. For a description of clamping, see
    /// [`clamp_integer`].
    pub fn mul_clamped(self, bytes: [u8; 32]) -> (result: Self)
        requires
            is_well_formed_edwards_point(self),
        ensures
            is_well_formed_edwards_point(result),
            // Result is scalar multiplication of self by the clamped scalar
            edwards_point_as_affine(result) == edwards_scalar_mul(
                edwards_point_as_affine(self),
                scalar_as_nat(&Scalar { bytes: spec_clamp_integer(bytes) }),
            ),
    {
        // We have to construct a Scalar that is not reduced mod l, which breaks scalar invariant
        // #2. But #2 is not necessary for correctness of variable-base multiplication. All that
        // needs to hold is invariant #1, i.e., the scalar is less than 2^255. This is guaranteed
        // by clamping.
        // Further, we don't do any reduction or arithmetic with this clamped value, so there's no
        // issues arising from the fact that the curve point is not necessarily in the prime-order
        // subgroup.
        let s = Scalar { bytes: clamp_integer(bytes) };
        proof {
            assert(is_clamped_integer(&s.bytes));
            assert(s.bytes[31] <= 127);  // needed for mul precondition
            assert(s.bytes == spec_clamp_integer(bytes));
        }
        let result = s * self;
        proof {
            assert(scalar_as_nat(&s) == scalar_as_nat(
                &Scalar { bytes: spec_clamp_integer(bytes) },
            ));
        }
        result
    }

    /// Multiply the basepoint by `clamp_integer(bytes)`. For a description of clamping, see
    /// [`clamp_integer`].
    pub fn mul_base_clamped(bytes: [u8; 32]) -> (result: Self)
        ensures
            is_well_formed_edwards_point(result),
            // Functional correctness: result = [clamped_scalar] * B where B is the basepoint
            edwards_point_as_affine(result) == edwards_scalar_mul(
                spec_ed25519_basepoint(),
                scalar_as_nat(&Scalar { bytes: spec_clamp_integer(bytes) }),
            ),
    {
        // See reasoning in Self::mul_clamped why it is OK to make an unreduced Scalar here. We
        // note that fixed-base multiplication is also defined for all values of `bytes` less than
        // 2^255.
        let s = Scalar { bytes: clamp_integer(bytes) };
        Self::mul_base(&s)
    }
}

// ------------------------------------------------------------------------
// Multiscalar Multiplication impls
// ------------------------------------------------------------------------
// These use the iterator's size hint and the target settings to
// forward to a specific backend implementation.
#[cfg(feature = "alloc")]
impl MultiscalarMul for EdwardsPoint {
    type Point = EdwardsPoint;

    #[verifier::external_body]
    fn multiscalar_mul<I, J>(scalars: I, points: J) -> EdwardsPoint where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<EdwardsPoint>,
    /* VERIFICATION NOTE: VERUS SPEC (when IntoIterator with I::Item projections is supported):
        requires
            scalars.len() == points.len(),
            forall|i| is_well_formed_edwards_point(points[i]),
        ensures
            is_well_formed_edwards_point(result),
            edwards_point_as_affine(result) == sum_of_scalar_muls(scalars, points),

        VERIFICATION NOTE: see `EdwardsPoint::multiscalar_mul_verus` below for the verified version using Iterator (not IntoIterator).
        */
    {
        // Sanity-check lengths of input iterators
        let mut scalars = scalars.into_iter();
        let mut points = points.into_iter();

        // Lower and upper bounds on iterators
        let (s_lo, s_hi) = scalars.by_ref().size_hint();
        let (p_lo, p_hi) = points.by_ref().size_hint();

        // They should all be equal
        assert_eq!(s_lo, p_lo);
        assert_eq!(s_hi, Some(s_lo));
        assert_eq!(p_hi, Some(p_lo));

        // Now we know there's a single size.  When we do
        // size-dependent algorithm dispatch, use this as the hint.
        let _size = s_lo;

        crate::backend::straus_multiscalar_mul(scalars, points)
    }
}

#[cfg(feature = "alloc")]
impl VartimeMultiscalarMul for EdwardsPoint {
    type Point = EdwardsPoint;

    #[verifier::external_body]
    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<EdwardsPoint> where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<EdwardsPoint>>,
    /* VERIFICATION NOTE: VERUS SPEC (when IntoIterator with I::Item projections is supported):
        requires
            scalars.len() == points.len(),
            forall|i| points[i].is_some() ==> is_well_formed_edwards_point(points[i].unwrap()),
        ensures
            result.is_some() <==> all_points_some(points),
            result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
            result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(scalars, unwrap_points(points)),

        VERIFICATION NOTE: see `EdwardsPoint::optional_multiscalar_mul_verus` below for the verified version using Iterator (not IntoIterator).
        */
    {
        // Sanity-check lengths of input iterators
        let mut scalars = scalars.into_iter();
        let mut points = points.into_iter();

        // Lower and upper bounds on iterators
        let (s_lo, s_hi) = scalars.by_ref().size_hint();
        let (p_lo, p_hi) = points.by_ref().size_hint();

        // They should all be equal
        assert_eq!(s_lo, p_lo);
        assert_eq!(s_hi, Some(s_lo));
        assert_eq!(p_hi, Some(p_lo));

        // Now we know there's a single size.
        // Use this as the hint to decide which algorithm to use.
        let size = s_lo;

        if size < 190 {
            crate::backend::straus_optional_multiscalar_mul(scalars, points)
        } else {
            crate::backend::pippenger_optional_multiscalar_mul(scalars, points)
        }
    }
}

} // verus!
/// Precomputation for variable-time multiscalar multiplication with `EdwardsPoint`s.
// This wraps the inner implementation in a facade type so that we can
// decouple stability of the inner type from the stability of the
// outer type.
#[cfg(feature = "alloc")]
pub struct VartimeEdwardsPrecomputation(crate::backend::VartimePrecomputedStraus);

#[cfg(feature = "alloc")]
impl VartimePrecomputedMultiscalarMul for VartimeEdwardsPrecomputation {
    type Point = EdwardsPoint;

    fn new<I>(static_points: I) -> Self
    where
        I: IntoIterator,
        I::Item: Borrow<Self::Point>,
    {
        Self(crate::backend::VartimePrecomputedStraus::new(static_points))
    }

    fn optional_mixed_multiscalar_mul<I, J, K>(
        &self,
        static_scalars: I,
        dynamic_scalars: J,
        dynamic_points: K,
    ) -> Option<Self::Point>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<Scalar>,
        K: IntoIterator<Item = Option<Self::Point>>,
    {
        self.0
            .optional_mixed_multiscalar_mul(static_scalars, dynamic_scalars, dynamic_points)
    }
}

// Import spec functions from iterator_specs for multiscalar verification
#[cfg(verus_keep_ghost)]
use crate::specs::iterator_specs::{
    all_points_some, spec_optional_points_from_iter, spec_points_from_iter, spec_scalars_from_iter,
    unwrap_points,
};
// Import runtime helper for Sum<T> trait
#[cfg(feature = "alloc")]
use crate::specs::iterator_specs::collect_points_from_iter;

verus! {

impl EdwardsPoint {
    /// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
    pub fn vartime_double_scalar_mul_basepoint(a: &Scalar, A: &EdwardsPoint, b: &Scalar) -> (result:
        EdwardsPoint)
        requires
            is_well_formed_edwards_point(*A),
            scalar_as_nat(a) < pow2(255),
            scalar_as_nat(b) < pow2(255),
        ensures
            is_well_formed_edwards_point(result),
            // Functional correctness: result = a*A + b*B where B is the Ed25519 basepoint
            edwards_point_as_affine(result) == {
                let aA = edwards_scalar_mul(edwards_point_as_affine(*A), scalar_as_nat(a));
                let bB = edwards_scalar_mul(spec_ed25519_basepoint(), scalar_as_nat(b));
                edwards_add(aA.0, aA.1, bB.0, bB.1)
            },
    {
        crate::backend::vartime_double_base_mul(a, A, b)
    }

    // Helper to count iterator elements without consuming (clones internally).
    // Verus doesn't support Iterator::clone() or Iterator::count().
    #[verifier::external_body]
    #[cfg(feature = "alloc")]
    fn iter_count<T, I: Iterator<Item = T> + Clone>(iter: &I) -> (size: usize)
        ensures
            size == spec_scalars_from_iter::<T, I>(*iter).len(),
    {
        iter.clone().count()
    }

    /*
     * VERIFICATION NOTE
     * =================
     * Verus limitations addressed in these _verus versions:
     * - IntoIterator with I::Item projections → use Iterator bounds instead
     * - size_hint() on &mut iterator → use Clone + iter_count helper
     *
     * TESTING: `scalar_mul_tests.rs` contains tests that generate random scalars and points,
     * run both original and _verus implementations, and assert equality of results.
     * This is evidence of functional equivalence between the original and refactored versions:
     *     forall scalars s, points p:
     *         optional_multiscalar_mul(s, p) == optional_multiscalar_mul_verus(s, p)
     *         multiscalar_mul(s, p) == multiscalar_mul_verus(s, p)
     */
    /// Verus-compatible version of optional_multiscalar_mul.
    /// Uses Iterator + Clone instead of IntoIterator (Verus doesn't support I::Item projections).
    /// Clone allows peeking at size without consuming the iterator (similar to original's size_hint).
    /// Dispatches to Straus (size < 190) or Pippenger (size >= 190) algorithm.
    #[cfg(feature = "alloc")]
    pub fn optional_multiscalar_mul_verus<S, I, J>(scalars: I, points: J) -> (result: Option<
        EdwardsPoint,
    >) where
        S: Borrow<Scalar>,
        I: Iterator<Item = S> + Clone,
        J: Iterator<Item = Option<EdwardsPoint>> + Clone,

        requires
    // Same number of scalars and points

            spec_scalars_from_iter::<S, I>(scalars).len() == spec_optional_points_from_iter::<J>(
                points,
            ).len(),
            // All input points (when Some) must be well-formed
            forall|i: int|
                0 <= i < spec_optional_points_from_iter::<J>(points).len() && (
                #[trigger] spec_optional_points_from_iter::<J>(points)[i]).is_some()
                    ==> is_well_formed_edwards_point(
                    spec_optional_points_from_iter::<J>(points)[i].unwrap(),
                ),
        ensures
    // Result is Some if and only if all input points are Some

            result.is_some() <==> all_points_some(spec_optional_points_from_iter::<J>(points)),
            // If result is Some, it is a well-formed Edwards point
            result.is_some() ==> is_well_formed_edwards_point(result.unwrap()),
            // Semantic correctness: result = sum(scalars[i] * points[i])
            result.is_some() ==> edwards_point_as_affine(result.unwrap()) == sum_of_scalar_muls(
                spec_scalars_from_iter::<S, I>(scalars),
                unwrap_points(spec_optional_points_from_iter::<J>(points)),
            ),
    {
        /* <ORIGINAL CODE>
        // Sanity-check lengths of input iterators
        let mut scalars = scalars.into_iter();
        let mut points = points.into_iter();

        // Lower and upper bounds on iterators
        let (s_lo, s_hi) = scalars.by_ref().size_hint();
        let (p_lo, p_hi) = points.by_ref().size_hint();

        // They should all be equal
        assert_eq!(s_lo, p_lo);
        assert_eq!(s_hi, Some(s_lo));
        assert_eq!(p_hi, Some(p_lo));

        // Now we know there's a single size.
        // Use this as the hint to decide which algorithm to use.
        let size = s_lo;

        if size < 190 {
            crate::backend::straus_optional_multiscalar_mul(scalars, points)
        } else {
            crate::backend::pippenger_optional_multiscalar_mul(scalars, points)
        }
        </ORIGINAL CODE> */
        /* Uses Clone instead of by_ref() since Verus doesn't support &mut on iterators. */
        // Sanity-check lengths of input iterators (skipped by Verus, checked via requires clause)
        #[cfg(not(verus_keep_ghost))]
        {
            let (s_lo, s_hi) = scalars.clone().size_hint();
            let (p_lo, p_hi) = points.clone().size_hint();
            assert_eq!(s_lo, p_lo);
            assert_eq!(s_hi, Some(s_lo));
            assert_eq!(p_hi, Some(p_lo));
        }

        // Get size for algorithm dispatch
        let size = Self::iter_count(&scalars);

        if size < 190 {
            crate::backend::straus_optional_multiscalar_mul_verus(scalars, points)
        } else {
            crate::backend::pippenger_optional_multiscalar_mul_verus(scalars, points)
        }
    }

    /// Verus-compatible version of multiscalar_mul (constant-time).
    /// Uses Iterator instead of IntoIterator (Verus doesn't support I::Item projections).
    /// Dispatches to Straus algorithm (constant-time).
    #[cfg(feature = "alloc")]
    pub fn multiscalar_mul_verus<S, P, I, J>(scalars: I, points: J) -> (result: EdwardsPoint) where
        S: Borrow<Scalar>,
        P: Borrow<EdwardsPoint>,
        I: Iterator<Item = S> + Clone,
        J: Iterator<Item = P> + Clone,

        requires
    // Same number of scalars and points

            spec_scalars_from_iter::<S, I>(scalars).len() == spec_points_from_iter::<P, J>(
                points,
            ).len(),
            // All input points must be well-formed
            forall|i: int|
                0 <= i < spec_points_from_iter::<P, J>(points).len()
                    ==> is_well_formed_edwards_point(
                    #[trigger] spec_points_from_iter::<P, J>(points)[i],
                ),
        ensures
    // Result is a well-formed Edwards point

            is_well_formed_edwards_point(result),
            // Semantic correctness: result = sum(scalars[i] * points[i])
            edwards_point_as_affine(result) == sum_of_scalar_muls(
                spec_scalars_from_iter::<S, I>(scalars),
                spec_points_from_iter::<P, J>(points),
            ),
    {
        /* <ORIGINAL CODE>
        // Sanity-check lengths of input iterators
        let mut scalars = scalars.into_iter();
        let mut points = points.into_iter();

        // Lower and upper bounds on iterators
        let (s_lo, s_hi) = scalars.by_ref().size_hint();
        let (p_lo, p_hi) = points.by_ref().size_hint();

        // They should all be equal
        assert_eq!(s_lo, p_lo);
        assert_eq!(s_hi, Some(s_lo));
        assert_eq!(p_hi, Some(p_lo));

        // Now we know there's a single size.  When we do
        // size-dependent algorithm dispatch, use this as the hint.
        let _size = s_lo;

        crate::backend::straus_multiscalar_mul(scalars, points)
        </ORIGINAL CODE> */
        /* Uses Clone instead of by_ref() since Verus doesn't support &mut on iterators. */
        // Sanity-check lengths of input iterators (skipped by Verus, checked via requires clause)
        #[cfg(not(verus_keep_ghost))]
        {
            let (s_lo, s_hi) = scalars.clone().size_hint();
            let (p_lo, p_hi) = points.clone().size_hint();
            assert_eq!(s_lo, p_lo);
            assert_eq!(s_hi, Some(s_lo));
            assert_eq!(p_hi, Some(p_lo));
        }

        // Dispatch to Straus (constant-time)
        crate::backend::straus_multiscalar_mul_verus(scalars, points)
    }
}

} // verus!
/* VERIFICATION NOTE: Removed unused impl_basepoint_table! macro since EdwardsBasepointTable
(radix-16) was manually expanded. */
// The number of additions required is ceil(256/w) where w is the radix representation.
/* VERIFICATION NOTE: Manually expanded impl_basepoint_table! macro for radix-16 (EdwardsBasepointTable).
   Removed macro invocations for radix-32, 64, 128, 256 variants to focus verification
   on the primary radix-16 implementation used as a constructor for consts.

   Original macro invocation:
   impl_basepoint_table! {
       Name = EdwardsBasepointTable,
       LookupTable = LookupTableRadix16,
       Point = EdwardsPoint,
       Radix = 4,
       Additions = 64
   }
*/
cfg_if! {
    if #[cfg(feature = "precomputed-tables")] {

verus! {

/// A precomputed table of multiples of a basepoint, for accelerating
/// fixed-base scalar multiplication.  One table, for the Ed25519
/// basepoint, is provided in the [`constants`] module.
///
/// The basepoint tables are reasonably large, so they should probably be boxed.
///
/// The sizes for the tables and the number of additions required for one scalar
/// multiplication are as follows:
///
/// * [`EdwardsBasepointTableRadix16`]: 30KB, 64A
///   (this is the default size, and is used for
///   [`constants::ED25519_BASEPOINT_TABLE`])
/// * [`EdwardsBasepointTableRadix64`]: 120KB, 43A
/// * [`EdwardsBasepointTableRadix128`]: 240KB, 37A
/// * [`EdwardsBasepointTableRadix256`]: 480KB, 33A
///
/// # Why 33 additions for radix-256?
///
/// Normally, the radix-256 tables would allow for only 32 additions per scalar
/// multiplication.  However, due to the fact that standardised definitions of
/// legacy protocols—such as x25519—require allowing unreduced 255-bit scalars
/// invariants, when converting such an unreduced scalar's representation to
/// radix-\\(2^{8}\\), we cannot guarantee the carry bit will fit in the last
/// coefficient (the coefficients are `i8`s).  When, \\(w\\), the power-of-2 of
/// the radix, is \\(w < 8\\), we can fold the final carry onto the last
/// coefficient, \\(d\\), because \\(d < 2^{w/2}\\), so
/// $$
///     d + carry \cdot 2^{w} = d + 1 \cdot 2^{w} < 2^{w+1} < 2^{8}
/// $$
/// When \\(w = 8\\), we can't fit \\(carry \cdot 2^{w}\\) into an `i8`, so we
/// add the carry bit onto an additional coefficient.
#[repr(transparent)]
pub struct EdwardsBasepointTable(pub [LookupTableRadix16<AffineNielsPoint>; 32]);

// Manual Clone implementation to avoid array clone issues in Verus
impl Clone for EdwardsBasepointTable {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        EdwardsBasepointTable(self.0)
    }
}

impl BasepointTable for EdwardsBasepointTable {
    type Point = EdwardsPoint;

    /// Create a table of precomputed multiples of `basepoint`.
    ///
    /// Constructs 32 LookupTables where table.0[i] = [1·(16²)^i·B, ..., 8·(16²)^i·B]
    fn create(basepoint: &EdwardsPoint) -> (result: EdwardsBasepointTable)
        requires
            is_well_formed_edwards_point(*basepoint),
        ensures
            is_valid_edwards_basepoint_table(result, edwards_point_as_affine(*basepoint)),
    {
        // XXX use init_with
        let mut table = EdwardsBasepointTable([LookupTableRadix16::default();32]);
        let mut P = *basepoint;
        let ghost basepoint_affine = edwards_point_as_affine(*basepoint);

        // Prove initialization: P = basepoint = pow256(0) * basepoint
        proof {
            // Show that pow256(0) == 1
            assert(pow256(0) == pow2(8 * 0)) by {
                reveal(pow256);
            }
            assert(pow256(0) == pow2(0));
            // Prove pow2(0) == 1 using vstd lemmas
            assert(pow2(0) == 1) by {
                reveal(pow2);
                vstd::arithmetic::power::lemma_pow0(2);
            }
            assert(pow256(0) == 1);
            // edwards_scalar_mul(P, 1) = P by definition
            reveal_with_fuel(edwards_scalar_mul, 2);
            // Establish the invariant
            assert(edwards_scalar_mul(basepoint_affine, pow256(0)) == edwards_scalar_mul(
                basepoint_affine,
                1,
            ));
            assert(edwards_scalar_mul(basepoint_affine, 1) == basepoint_affine);
            assert(edwards_point_as_affine(P) == basepoint_affine);
        }

        for i in 0..32
            invariant
                is_well_formed_edwards_point(*basepoint),
                is_well_formed_edwards_point(P),
                // Track that P equals pow256(i) * basepoint at iteration i
                edwards_point_as_affine(P) == edwards_scalar_mul(
                    edwards_point_as_affine(*basepoint),
                    pow256(i as nat),
                ),
                // All table entries filled so far (indices 0..i) are correct
                // (affine coords are correct scalar multiples)
                forall|j: int|
                    #![trigger table.0[j as int]]
                    0 <= j < i ==> is_valid_lookup_table_affine_coords(
                        table.0[j as int].0,
                        edwards_scalar_mul(edwards_point_as_affine(*basepoint), pow256(j as nat)),
                        8,
                    ),
                // All table entries filled so far have bounded limbs
                forall|j: int|
                    #![trigger table.0[j as int]]
                    0 <= j < i ==> lookup_table_affine_limbs_bounded(table.0[j as int].0),
        {
            // P = (16²)^i * basepoint
            table.0[i] = LookupTableRadix16::from(&P);

            proof {
                // From LookupTableRadix16::from postcondition, we have:
                // is_valid_lookup_table_affine_coords(table.0[i].0, edwards_point_as_affine(P), 8)
                // lookup_table_affine_limbs_bounded(table.0[i].0)
                //
                // From loop invariant, we know:
                // edwards_point_as_affine(P) == edwards_scalar_mul(basepoint_affine, pow256(i))
                //
                // Therefore, table[i] is correct for index i
                assert(is_valid_lookup_table_affine_coords(
                    table.0[i as int].0,
                    edwards_scalar_mul(edwards_point_as_affine(*basepoint), pow256(i as nat)),
                    8,
                ));
                // Limb bounds from postcondition
                assert(lookup_table_affine_limbs_bounded(table.0[i as int].0));
            }

            P = P.mul_by_pow_2(4 + 4);  // P = P * 2^8 = P * 256 = P * 16²

            proof {
                // scalar_mul(scalar_mul(B, pow256(i)), pow2(8)) == scalar_mul(B, pow256(i+1))
                assert(edwards_scalar_mul(
                    edwards_scalar_mul(edwards_point_as_affine(*basepoint), pow256(i as nat)),
                    pow2(8),
                ) == edwards_scalar_mul(
                    edwards_point_as_affine(*basepoint),
                    pow256((i + 1) as nat),
                )) by {
                    assert(8 * ((i + 1) as nat) == 8 * (i as nat) + 8);
                    vstd::arithmetic::power2::lemma_pow2_adds(8 * (i as nat), 8);
                    lemma_edwards_scalar_mul_composition(
                        edwards_point_as_affine(*basepoint),
                        pow256(i as nat),
                        pow2(8),
                    );
                };
            }
        }
        proof {
            // Loop invariant at i=32 gives the postcondition
            assert(is_valid_edwards_basepoint_table(table, edwards_point_as_affine(*basepoint)));
        }
        table
    }

    /// Get the basepoint for this table as an `EdwardsPoint`.
    fn basepoint(&self) -> (result: EdwardsPoint)
        requires
            is_valid_edwards_basepoint_table(*self, spec_ed25519_basepoint()),
        ensures
            is_well_formed_edwards_point(result),
            // The result is the Ed25519 basepoint B
            edwards_point_as_affine(result) == spec_ed25519_basepoint(),
    {
        // self.0[0].select(1) = 1*(16^2)^0*B
        // but as an `AffineNielsPoint`, so add identity to convert to extended.
        let identity = EdwardsPoint::identity();
        proof {
            reveal(is_valid_edwards_basepoint_table);
            assert(lookup_table_affine_limbs_bounded((*self).0[0int].0));
        }
        let selected = self.0[0].select(1);
        proof {
            assert(is_well_formed_edwards_point(identity));
            assert(fe51_limbs_bounded(&identity.Z, 52));
            assert(sum_of_limbs_bounded(&identity.Z, &identity.Z, u64::MAX)) by {
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&identity.Z, &identity.Z, 52);
            }
            // Validity: select returns a valid AffineNielsPoint (from select postcondition)
            assert(is_valid_affine_niels_point(selected));
        }
        let completed = &identity + &selected;
        proof {
            assert(fe51_limbs_bounded(&completed.X, 54));
            assert(fe51_limbs_bounded(&completed.Y, 54));
            assert(fe51_limbs_bounded(&completed.Z, 54));
            assert(fe51_limbs_bounded(&completed.T, 54));
        }
        let result = completed.as_extended();
        proof {
            assert(is_well_formed_edwards_point(result));

            let B = spec_ed25519_basepoint();

            assert(pow256(0) == 1) by {
                reveal(pow256);
                reveal(pow2);
                vstd::arithmetic::power::lemma_pow0(2);
            }
            assert(edwards_scalar_mul(B, 1) == B) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }

            // Table validity: table[0] contains multiples of B
            assert(is_valid_lookup_table_affine_coords((*self).0[0int].0, B, 8));
            assert(affine_niels_point_as_affine_edwards((*self).0[0int].0[0int]) == B);
            assert(selected == (*self).0[0int].0[0int]);
            assert(affine_niels_point_as_affine_edwards(selected) == B);

            // Identity has affine coords (0, 1)
            assert(is_identity_edwards_point(identity));
            assert(edwards_point_as_affine(identity) == (0nat, 1nat)) by {
                lemma_identity_affine_coords(identity);
            }

            // Add: identity + B = B
            assert(completed_point_as_affine_edwards(completed) == edwards_add(
                0nat,
                1nat,
                B.0,
                B.1,
            ));
            assert(edwards_add(0nat, 1nat, B.0, B.1) == (B.0 % p(), B.1 % p())) by {
                lemma_edwards_add_identity_left(B.0, B.1);
            }

            // B is canonical, so B % p == B
            assert(B.0 < p() && B.1 < p()) by {
                axiom_ed25519_basepoint_canonical();
            }
            assert(B.0 % p() == B.0 && B.1 % p() == B.1) by {
                vstd::arithmetic::div_mod::lemma_small_mod(B.0, p());
                vstd::arithmetic::div_mod::lemma_small_mod(B.1, p());
            }

            assert(edwards_point_as_affine(result) == completed_point_as_affine_edwards(completed));
            assert(edwards_point_as_affine(result) == B);
        }
        result
    }

    /// The computation uses Pippenger's algorithm, as described for the
    /// specific case of radix-16 on page 13 of the Ed25519 paper.
    ///
    /// # Pippenger's Algorithm Generalised
    ///
    /// Write the scalar \\(a\\) in radix-\\(w\\), where \\(w\\) is a power of
    /// 2, with coefficients in \\([\frac{-w}{2},\frac{w}{2})\\), i.e.,
    /// $$
    ///     a = a\_0 + a\_1 w\^1 + \cdots + a\_{x} w\^{x},
    /// $$
    /// with
    /// $$
    /// \begin{aligned}
    ///     \frac{-w}{2} \leq a_i < \frac{w}{2}
    ///     &&\cdots&&
    ///     \frac{-w}{2} \leq a\_{x} \leq \frac{w}{2}
    /// \end{aligned}
    /// $$
    /// and the number of additions, \\(x\\), is given by
    /// \\(x = \lceil \frac{256}{w} \rceil\\). Then
    /// $$
    ///     a B = a\_0 B + a\_1 w\^1 B + \cdots + a\_{x-1} w\^{x-1} B.
    /// $$
    /// Grouping even and odd coefficients gives
    /// $$
    /// \begin{aligned}
    ///     a B = \quad a\_0 w\^0 B +& a\_2 w\^2 B + \cdots + a\_{x-2} w\^{x-2} B    \\\\
    ///               + a\_1 w\^1 B +& a\_3 w\^3 B + \cdots + a\_{x-1} w\^{x-1} B    \\\\
    ///         = \quad(a\_0 w\^0 B +& a\_2 w\^2 B + \cdots + a\_{x-2} w\^{x-2} B)   \\\\
    ///             + w(a\_1 w\^0 B +& a\_3 w\^2 B + \cdots + a\_{x-1} w\^{x-2} B).  \\\\
    /// \end{aligned}
    /// $$
    /// For each \\(i = 0 \ldots 31\\), we create a lookup table of
    /// $$
    /// [w\^{2i} B, \ldots, \frac{w}{2}\cdot w\^{2i} B],
    /// $$
    /// and use it to select \\( y \cdot w\^{2i} \cdot B \\) in constant time.
    ///
    /// The radix-\\(w\\) representation requires that the scalar is bounded
    /// by \\(2\^{255}\\), which is always the case.
    ///
    /// The above algorithm is trivially generalised to other powers-of-2 radices.
    fn mul_base(&self, scalar: &Scalar) -> (result: EdwardsPoint)
        requires
            scalar.bytes[31] <= 127,
            is_valid_edwards_basepoint_table(*self, spec_ed25519_basepoint()),
        ensures
            is_well_formed_edwards_point(result),
            // Functional correctness: result = [scalar] * B
            edwards_point_as_affine(result) == edwards_scalar_mul(
                spec_ed25519_basepoint(),
                scalar_as_nat(scalar),
            ),
    {
        let a = scalar.as_radix_2w(4);

        let tables = &self.0;
        let mut P = EdwardsPoint::identity();

        proof {
            // From `identity()` postcondition.
            assert(is_well_formed_edwards_point(P));
            // From `as_radix_2w(4)` postcondition: the digits are a valid radix-16 representation.
            assert(is_valid_radix_2w(&a, 4, 64));
            assert(is_valid_radix_16(&a));
            assert(radix_16_all_bounded(&a)) by {
                lemma_valid_radix_16_implies_all_bounded(a);
            }

            // Initial invariant: identity == odd_sum_up_to(digits, 0, B)
            assert(edwards_point_as_affine(P) == math_edwards_identity()) by {
                lemma_identity_affine_coords(P);
            }
            // odd_sum_up_to(_, 0, _) = math_edwards_identity() = (0, 1) by definition
            reveal(odd_sum_up_to);
            assert(odd_sum_up_to(a@, 0, spec_ed25519_basepoint()) == math_edwards_identity());
        }

        // ORIGINAL CODE (doesn't work with Verus - .filter() not supported in ghost for loops):
        // for i in (0..64).filter(|x| x % 2 == 1) {
        //     P = (&P + &tables[i / 2].select(a[i])).as_extended();
        // }
        let ghost B = spec_ed25519_basepoint();
        for i in 0..64
            invariant
                is_well_formed_edwards_point(P),
                radix_16_all_bounded(&a),
                is_valid_edwards_basepoint_table(*self, spec_ed25519_basepoint()),
                tables == &self.0,  // track tables alias
                B == spec_ed25519_basepoint(),  // track ghost variable
                // Functional correctness: P = odd_sum_up_to(a, i, B)
                edwards_point_as_affine(P) == odd_sum_up_to(a@, i as int, B),
        {
            if i % 2 == 1 {
                // ORIGINAL CODE: need to add intermediate variables for pre and post conditions
                //     P = (&P + &tables[i / 2].select(a[i])).as_extended();
                proof {
                    // Preconditions for `select`.
                    assert(-8 <= a[i as int] && a[i as int] <= 8);

                    // Table limb bounds come from `is_valid_edwards_basepoint_table`.
                    let ti: int = (i / 2) as int;
                    assert(0 <= ti < 32);
                    // Establish select precondition via the table validity.
                    assert(lookup_table_affine_limbs_bounded(tables[ti].0)) by {
                        reveal(is_valid_edwards_basepoint_table);
                    }
                }
                let selected = tables[i / 2].select(a[i]);
                proof {
                    // Preconditions for `&EdwardsPoint + &AffineNielsPoint`.
                    // - `P` is well-formed from the loop invariant.
                    // - Need `sum_of_limbs_bounded(P.Z, P.Z, u64::MAX)`; follows from 52-boundedness.
                    assert(edwards_point_limbs_bounded(P));
                    assert(sum_of_limbs_bounded(&P.Z, &P.Z, u64::MAX)) by {
                        lemma_sum_of_limbs_bounded_from_fe51_bounded(&P.Z, &P.Z, 52);
                    }
                    // - `selected` limb bounds are ensured by `select`.
                    assert(fe51_limbs_bounded(&selected.y_plus_x, 54));
                    assert(fe51_limbs_bounded(&selected.y_minus_x, 54));
                    assert(fe51_limbs_bounded(&selected.xy2d, 54));
                    // Validity: select returns a valid AffineNielsPoint (from select postcondition)
                    assert(is_valid_affine_niels_point(selected));
                }
                let ghost old_P = P;
                let ghost old_P_affine = edwards_point_as_affine(P);
                let tmp = &P + &selected;
                proof {
                    // `tmp.as_extended()` preconditions follow from `Add` postconditions.
                    assert(is_valid_completed_point(tmp));
                    assert(fe51_limbs_bounded(&tmp.X, 54));
                    assert(fe51_limbs_bounded(&tmp.Y, 54));
                    assert(fe51_limbs_bounded(&tmp.Z, 54));
                    assert(fe51_limbs_bounded(&tmp.T, 54));
                }
                P = tmp.as_extended();
                proof {
                    // Chain: edwards_point_as_affine(P) == completed_point_as_affine_edwards(tmp)
                    //        == edwards_add(old_P_affine, selected_affine)
                    let selected_affine = affine_niels_point_as_affine_edwards(selected);
                    assert(edwards_point_as_affine(P) == edwards_add(
                        old_P_affine.0,
                        old_P_affine.1,
                        selected_affine.0,
                        selected_affine.1,
                    ));

                    // 4. By loop invariant: old_P_affine == odd_sum_up_to(a@, i, B)
                    // 5. Get selected_affine from table validity
                    let table_idx = (i / 2) as int;
                    let table_base = edwards_scalar_mul(B, pow256(table_idx as nat));
                    lemma_basepoint_table_select(*self, a@, i as int, selected, B);
                    assert(selected_affine == edwards_scalar_mul_signed(
                        table_base,
                        a[i as int] as int,
                    ));

                    // 6. Unfold odd_sum_up_to(a@, i+1, B) - since i is odd, this includes term for i
                    reveal(odd_sum_up_to);
                    let term_i = edwards_scalar_mul_signed(table_base, a@[i as int] as int);
                    // odd_sum_up_to(a@, i+1, B) = edwards_add(odd_sum_up_to(a@, i, B), term_i)
                    // Since old_P_affine == odd_sum_up_to(a@, i, B) and selected_affine == term_i:
                    assert(edwards_point_as_affine(P) == odd_sum_up_to(a@, (i + 1) as int, B));
                }
            } else {
                proof {
                    // Even index: odd_sum_up_to skips this index, so invariant unchanged
                    reveal(odd_sum_up_to);
                    // odd_sum_up_to(a@, i+1, B) == odd_sum_up_to(a@, i, B) when i is even
                }
            }
        }

        // After loop 1: P = odd_sum_up_to(a@, 64, B)
        // mul_by_pow_2(4) multiplies by 16: P = 16 * odd_sum
        P = P.mul_by_pow_2(4);

        proof {
            // After mul_by_pow_2(4), P = edwards_scalar_mul(odd_sum, 16)
            // which equals pippenger_partial(a@, 0, B) since even_sum_up_to(_, 0, _) = identity
            assert(pow2(4) == 16) by {
                vstd::arithmetic::power2::lemma2_to64();
            }
            reveal(even_sum_up_to);
            reveal(pippenger_partial);

            // From loop 1 exit invariant: old_P = odd_sum_up_to(a@, 64, B)
            // From mul_by_pow_2 postcondition: P = edwards_scalar_mul(old_P, 16)
            let odd_sum = odd_sum_up_to(a@, 64, B);
            let scaled = edwards_scalar_mul(odd_sum, 16);
            // By mul_by_pow_2 postcondition:
            assert(edwards_point_as_affine(P) == scaled);

            // pippenger_partial(a@, 0, B) = edwards_add(scaled, even_sum_up_to(a@, 0, B))
            //                            = edwards_add(scaled, identity)
            //                            = scaled (by identity law)
            assert(even_sum_up_to(a@, 0, B) == math_edwards_identity());
            // scaled comes from edwards_scalar_mul, which produces canonical coordinates
            assert(edwards_add(scaled.0, scaled.1, 0, 1) == scaled) by {
                // First establish that the basepoint B is canonical
                axiom_ed25519_basepoint_canonical();
                // Then odd_sum is canonical (from lemma_odd_sum_up_to_canonical)
                lemma_odd_sum_up_to_canonical(a@, 64, B);
                lemma_edwards_scalar_mul_canonical(odd_sum, 16);
                lemma_edwards_add_identity_right_canonical(scaled);
            }
            assert(pippenger_partial(a@, 0, B) == scaled);
        }

        // ORIGINAL CODE (doesn't work with Verus - .filter() not supported in ghost for loops):
        // for i in (0..64).filter(|x| x % 2 == 0) {
        //     P = (&P + &tables[i / 2].select(a[i])).as_extended();
        // }
        for i in 0..64
            invariant
                is_well_formed_edwards_point(P),
                radix_16_all_bounded(&a),
                is_valid_edwards_basepoint_table(*self, spec_ed25519_basepoint()),
                tables == &self.0,  // track tables alias
                B == spec_ed25519_basepoint(),  // track ghost variable
                // Functional correctness: P = pippenger_partial(a, i, B)
                edwards_point_as_affine(P) == pippenger_partial(a@, i as int, B),
        {
            if i % 2 == 0 {
                // ORIGINAL CODE: need to add intermediate variables for pre and post conditions
                //     P = (&P + &tables[i / 2].select(a[i])).as_extended();
                proof {
                    // Preconditions for `select`.
                    assert(-8 <= a[i as int] && a[i as int] <= 8);

                    // Table limb bounds come from `is_valid_edwards_basepoint_table`.
                    let ti: int = (i / 2) as int;
                    assert(0 <= ti < 32);
                    // Establish select precondition via the table validity.
                    assert(lookup_table_affine_limbs_bounded(tables[ti].0)) by {
                        reveal(is_valid_edwards_basepoint_table);
                    }
                }
                let selected = tables[i / 2].select(a[i]);
                proof {
                    // Preconditions for `&EdwardsPoint + &AffineNielsPoint`.
                    assert(edwards_point_limbs_bounded(P));
                    assert(sum_of_limbs_bounded(&P.Z, &P.Z, u64::MAX)) by {
                        lemma_sum_of_limbs_bounded_from_fe51_bounded(&P.Z, &P.Z, 52);
                    }
                    assert(fe51_limbs_bounded(&selected.y_plus_x, 54));
                    assert(fe51_limbs_bounded(&selected.y_minus_x, 54));
                    assert(fe51_limbs_bounded(&selected.xy2d, 54));
                    // Validity: select returns a valid AffineNielsPoint (from select postcondition)
                    assert(is_valid_affine_niels_point(selected));
                }
                let ghost old_P2 = P;
                let ghost old_P2_affine = edwards_point_as_affine(P);
                let tmp = &P + &selected;
                proof {
                    // `tmp.as_extended()` preconditions follow from `Add` postconditions.
                    assert(is_valid_completed_point(tmp));
                    assert(fe51_limbs_bounded(&tmp.X, 54));
                    assert(fe51_limbs_bounded(&tmp.Y, 54));
                    assert(fe51_limbs_bounded(&tmp.Z, 54));
                    assert(fe51_limbs_bounded(&tmp.T, 54));
                }
                P = tmp.as_extended();
                proof {
                    // Chain: edwards_point_as_affine(P) == completed_point_as_affine_edwards(tmp)
                    //        == edwards_add(old_P2_affine, selected_affine)
                    let selected_affine = affine_niels_point_as_affine_edwards(selected);
                    assert(edwards_point_as_affine(P) == edwards_add(
                        old_P2_affine.0,
                        old_P2_affine.1,
                        selected_affine.0,
                        selected_affine.1,
                    ));

                    // Get selected_affine from table validity
                    let table_idx = (i / 2) as int;
                    let table_base = edwards_scalar_mul(B, pow256(table_idx as nat));
                    lemma_basepoint_table_select(*self, a@, i as int, selected, B);
                    assert(selected_affine == edwards_scalar_mul_signed(
                        table_base,
                        a[i as int] as int,
                    ));

                    let term_i = edwards_scalar_mul_signed(table_base, a[i as int] as int);
                    assert(selected_affine == term_i);

                    let p_i = pippenger_partial(a@, i as int, B);
                    assert(old_P2_affine == p_i);

                    // Update step for the spec-side loop state, isolated in a small lemma to avoid rlimit.
                    crate::lemmas::edwards_lemmas::mul_base_lemmas::lemma_pippenger_partial_step_even(
                    a@, i as int, B);
                    assert(edwards_add(p_i.0, p_i.1, term_i.0, term_i.1) == pippenger_partial(
                        a@,
                        (i + 1) as int,
                        B,
                    ));

                    // Our updated point is p_i + term_i, hence equals p_{i+1}.
                    assert(edwards_point_as_affine(P) == edwards_add(
                        p_i.0,
                        p_i.1,
                        term_i.0,
                        term_i.1,
                    ));
                    assert(edwards_point_as_affine(P) == pippenger_partial(a@, (i + 1) as int, B));
                }
            } else {
                proof {
                    // Odd index: pippenger_partial skips this index (even_sum_up_to skips odd)
                    crate::lemmas::edwards_lemmas::mul_base_lemmas::lemma_pippenger_partial_step_odd(
                    a@, i as int, B);
                }
            }
        }

        proof {
            // After loop 2: P = pippenger_partial(a@, 64, B)
            assert(edwards_point_as_affine(P) == pippenger_partial(a@, 64, B));

            // Now connect pippenger_partial to edwards_scalar_mul:
            // pippenger_partial(a@, 64, B) == edwards_scalar_mul(B, reconstruct_radix_16(a@))
            // And from as_radix_2w postcondition: reconstruct_radix_16(a@) == scalar_as_nat(scalar)
            assert(reconstruct_radix_2w(a@.take(64), 4) == scalar_as_nat(scalar) as int);
            assert(a@.take(64) =~= a@);
            reveal(reconstruct_radix_16);
            assert(reconstruct_radix_16(a@) == scalar_as_nat(scalar) as int);

            lemma_pippenger_sum_correct(a@, B, scalar_as_nat(scalar));
            assert(pippenger_partial(a@, 64, B) == edwards_scalar_mul(B, scalar_as_nat(scalar)));

            // Postconditions:
            assert(is_well_formed_edwards_point(P));
        }
        P
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a EdwardsBasepointTable {
    type Output = EdwardsPoint;

    /// Construct an `EdwardsPoint` from a `Scalar` \\(a\\) by
    /// computing the multiple \\(aB\\) of this basepoint \\(B\\).
    fn mul(self, scalar: &'b Scalar) -> (result:
        EdwardsPoint)/* requires clause in MulSpecImpl<&Scalar> for &EdwardsBasepointTable in arithm_trait_specs.rs:
        requires scalar.bytes[31] <= 127
    */

        ensures
            is_well_formed_edwards_point(result),
            // Functional correctness: result = [scalar] * B
            edwards_point_as_affine(result) == edwards_scalar_mul(
                spec_ed25519_basepoint(),
                scalar_as_nat(scalar),
            ),
    {
        self.mul_base(scalar)
    }
}

impl<'a, 'b> Mul<&'a EdwardsBasepointTable> for &'b Scalar {
    type Output = EdwardsPoint;

    /// Construct an `EdwardsPoint` from a `Scalar` \\(a\\) by
    /// computing the multiple \\(aB\\) of this basepoint \\(B\\).
    fn mul(self, basepoint_table: &'a EdwardsBasepointTable) -> (result:
        EdwardsPoint)/* requires clause in MulSpecImpl<&EdwardsBasepointTable> for &Scalar in arithm_trait_specs.rs:
        requires self.bytes[31] <= 127
    */

        ensures
            is_well_formed_edwards_point(result),
            // Functional correctness: result = [scalar] * B
            edwards_point_as_affine(result) == edwards_scalar_mul(
                spec_ed25519_basepoint(),
                scalar_as_nat(self),
            ),
    {
        basepoint_table * self
    }
}

} // verus!
impl Debug for EdwardsBasepointTable {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}([\n", stringify!(EdwardsBasepointTable))?;
        for i in 0..32 {
            write!(f, "\t{:?},\n", &self.0[i])?;
        }
        write!(f, "])")
    }
}

        /// A type-alias for [`EdwardsBasepointTable`] because the latter is
        /// used as a constructor in the [`constants`] module.
        //
        // Same as for `LookupTableRadix16`, we have to define `EdwardsBasepointTable`
        // first, because it's used as a constructor, and then provide a type alias for
        // it.
        pub type EdwardsBasepointTableRadix16 = EdwardsBasepointTable;
    }
}

/* VERIFICATION NOTE:
- removed unused impl_basepoint_table_conversions! macro definitions and invocations
since only radix-16 is kept and no conversions between radix sizes are needed.
*/

verus! {

impl EdwardsPoint {
    /// Multiply by the cofactor: return \\(\[8\]P\\).
    pub fn mul_by_cofactor(&self) -> (result: EdwardsPoint)
        requires
            is_well_formed_edwards_point(*self),
        ensures
            is_well_formed_edwards_point(result),
            // Functional correctness: result = [8]P
            edwards_point_as_affine(result) == edwards_scalar_mul(
                edwards_point_as_affine(*self),
                8,
            ),
    {
        let result = self.mul_by_pow_2(3);
        proof {
            // Prove 2^3 = 8
            // mul_by_pow_2 ensures: edwards_point_as_affine(result) == edwards_scalar_mul(..., pow2(3))
            // Combined with pow2(3) == 8, we get the postcondition
            assert(pow2(3) == 8) by {
                lemma2_to64();
            }
        }
        result
    }

    /// Compute \\([2\^k] P \\) by successive doublings. Requires \\( k > 0 \\).
    pub(crate) fn mul_by_pow_2(&self, k: u32) -> (result: EdwardsPoint)
        requires
            k > 0,
            is_well_formed_edwards_point(*self),
        ensures
            is_well_formed_edwards_point(result),
            // Functional correctness: result = [2^k]P
            edwards_point_as_affine(result) == edwards_scalar_mul(
                edwards_point_as_affine(*self),
                pow2(k as nat),
            ),
    {
        #[cfg(not(verus_keep_ghost))]
        debug_assert!(k > 0);
        let ghost point_affine = edwards_point_as_affine(*self);
        let mut r: CompletedPoint;
        let mut s = self.as_projective();

        proof {
            // Establish ProjectivePoint::double preconditions for the initial s.
            assert(sum_of_limbs_bounded(&s.X, &s.Y, u64::MAX)) by {
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&s.X, &s.Y, 52);
            }
            assert(is_valid_projective_point(s)) by {
                assert(is_valid_edwards_point(*self));
                // Bridge z % p() != 0 → z != 0 (z = fe51_as_canonical_nat < p)
                let z = fe51_as_canonical_nat(&self.Z);
                p_gt_2();
                lemma_mod_bound(fe51_as_nat(&self.Z) as int, p() as int);
                lemma_small_mod(z, p());
            }

            // Base case: pow2(0) == 1 and [1]P == P.
            assert(pow2(0) == 1) by {
                lemma2_to64();
            }
            reveal_with_fuel(edwards_scalar_mul, 1);
            // Add mul_basics lemmas for stability (1 * x == x inference)
            vstd::arithmetic::mul::lemma_mul_basics_3(1int);
            vstd::arithmetic::mul::lemma_mul_basics_4(1int);
            assert(projective_point_as_affine_edwards(s) == point_affine);
            assert(projective_point_as_affine_edwards(s) == edwards_scalar_mul(
                point_affine,
                pow2(0),
            ));
        }

        // ORIGINAL: for _ in 0..(k - 1) { ... }
        // Changed to track iteration index `i` for loop invariant
        for i in 0..(k - 1)
            invariant
                is_valid_projective_point(s),
                fe51_limbs_bounded(&s.X, 52),
                fe51_limbs_bounded(&s.Y, 52),
                fe51_limbs_bounded(&s.Z, 52),
                sum_of_limbs_bounded(&s.X, &s.Y, u64::MAX),
                projective_point_as_affine_edwards(s) == edwards_scalar_mul(
                    point_affine,
                    pow2(i as nat),
                ),
        {
            r = s.double();
            s = r.as_projective();

            proof {
                lemma_edwards_scalar_mul_pow2_succ(point_affine, i as nat);
            }
        }

        // Unroll last iteration to go directly to as_extended() (avoids extra as_projective conversion)
        // ORIGINAL: let result = s.double().as_extended();
        r = s.double();
        let result = r.as_extended();

        proof {
            lemma_edwards_scalar_mul_pow2_succ(point_affine, (k - 1) as nat);
        }

        result
    }

    /// Determine if this point is of small order.
    ///
    /// # Return
    ///
    /// * `true` if `self` is in the torsion subgroup \\( \mathcal E\[8\] \\);
    /// * `false` if `self` is not in the torsion subgroup \\( \mathcal E\[8\] \\).
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::constants;
    ///
    /// // Generator of the prime-order subgroup
    /// let P = constants::ED25519_BASEPOINT_POINT;
    /// // Generator of the torsion subgroup
    /// let Q = constants::EIGHT_TORSION[1];
    ///
    /// // P has large order
    /// assert_eq!(P.is_small_order(), false);
    ///
    /// // Q has small order
    /// assert_eq!(Q.is_small_order(), true);
    /// ```
    pub fn is_small_order(&self) -> (result: bool)
        requires
            is_well_formed_edwards_point(*self),
        ensures
    // A point has small order iff [8]P = O (identity)

            result == (edwards_scalar_mul(edwards_point_as_affine(*self), 8)
                == math_edwards_identity()),
    {
        /* ORIGINAL CODE: self.mul_by_cofactor().is_identity() */
        let cofactor_mul = self.mul_by_cofactor();
        // mul_by_cofactor ensures:
        //   edwards_point_as_affine(cofactor_mul) == edwards_scalar_mul(edwards_point_as_affine(*self), 8)
        let result = cofactor_mul.is_identity();
        // is_identity ensures: result == cofactor_mul.is_identity_spec()
        //   which equals: edwards_point_as_affine(cofactor_mul) == math_edwards_identity()
        // Combined with mul_by_cofactor's ensures:
        //   result == (edwards_scalar_mul(edwards_point_as_affine(*self), 8) == math_edwards_identity())
        result
    }

    /// Determine if this point is "torsion-free", i.e., is contained in
    /// the prime-order subgroup.
    ///
    /// # Return
    ///
    /// * `true` if `self` has zero torsion component and is in the
    /// prime-order subgroup;
    /// * `false` if `self` has a nonzero torsion component and is not
    /// in the prime-order subgroup.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::constants;
    ///
    /// // Generator of the prime-order subgroup
    /// let P = constants::ED25519_BASEPOINT_POINT;
    /// // Generator of the torsion subgroup
    /// let Q = constants::EIGHT_TORSION[1];
    ///
    /// // P is torsion-free
    /// assert_eq!(P.is_torsion_free(), true);
    ///
    /// // P + Q is not torsion-free
    /// assert_eq!((P+Q).is_torsion_free(), false);
    /// ```
    pub fn is_torsion_free(&self) -> (result: bool)
        requires
            is_well_formed_edwards_point(*self),
        ensures
    // A point is torsion-free iff [ℓ]P = O, where ℓ is the group order

            result == (edwards_scalar_mul(edwards_point_as_affine(*self), group_order())
                == math_edwards_identity()),
    {
        /* ORIGINAL CODE: (self * constants::BASEPOINT_ORDER_PRIVATE).is_identity() */
        let order_mul = self * constants::BASEPOINT_ORDER_PRIVATE;
        let result = order_mul.is_identity();
        proof {
            assert(edwards_point_as_affine(order_mul) == edwards_scalar_mul(
                edwards_point_as_affine(*self),
                group_order(),
            )) by {
                // BASEPOINT_ORDER_PRIVATE encodes ℓ in little-endian bytes.
                lemma_scalar_as_nat_basepoint_order_private_equals_group_order();
            }
        }
        result
    }
}

} // verus!
// ------------------------------------------------------------------------
// Debug traits
// ------------------------------------------------------------------------
impl Debug for EdwardsPoint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "EdwardsPoint{{\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?},\n\tT: {:?}\n}}",
            &self.X, &self.Y, &self.Z, &self.T
        )
    }
}

// ------------------------------------------------------------------------
// group traits
// ------------------------------------------------------------------------

// Use the full trait path to avoid Group::identity overlapping Identity::identity in the
// rest of the module (e.g. tests).
#[cfg(feature = "group")]
impl group::Group for EdwardsPoint {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        let mut repr = CompressedEdwardsY([0u8; 32]);
        loop {
            rng.fill_bytes(&mut repr.0);
            if let Some(p) = repr.decompress() {
                if !IsIdentity::is_identity(&p) {
                    break p;
                }
            }
        }
    }

    fn identity() -> Self {
        Identity::identity()
    }

    fn generator() -> Self {
        constants::ED25519_BASEPOINT_POINT
    }

    fn is_identity(&self) -> Choice {
        self.ct_eq(&Identity::identity())
    }

    fn double(&self) -> Self {
        self.double()
    }
}

#[cfg(feature = "group")]
impl GroupEncoding for EdwardsPoint {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let repr = CompressedEdwardsY(*bytes);
        let (is_valid_y_coord, X, Y, Z) = decompress::step_1(&repr);
        CtOption::new(decompress::step_2(&repr, X, Y, Z), is_valid_y_coord)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        // Just use the checked API; there are no checks we can skip.
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.compress().to_bytes()
    }
}

/// A `SubgroupPoint` represents a point on the Edwards form of Curve25519, that is
/// guaranteed to be in the prime-order subgroup.
#[cfg(feature = "group")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SubgroupPoint(EdwardsPoint);

#[cfg(feature = "group")]
impl From<SubgroupPoint> for EdwardsPoint {
    fn from(p: SubgroupPoint) -> Self {
        p.0
    }
}

#[cfg(feature = "group")]
impl Neg for SubgroupPoint {
    type Output = Self;

    fn neg(self) -> Self::Output {
        SubgroupPoint(-self.0)
    }
}

#[cfg(feature = "group")]
impl Add<&SubgroupPoint> for &SubgroupPoint {
    type Output = SubgroupPoint;
    fn add(self, other: &SubgroupPoint) -> SubgroupPoint {
        SubgroupPoint(self.0 + other.0)
    }
}

#[cfg(feature = "group")]
define_add_variants!(
    LHS = SubgroupPoint,
    RHS = SubgroupPoint,
    Output = SubgroupPoint
);

#[cfg(feature = "group")]
impl Add<&SubgroupPoint> for &EdwardsPoint {
    type Output = EdwardsPoint;
    fn add(self, other: &SubgroupPoint) -> EdwardsPoint {
        self + other.0
    }
}

#[cfg(feature = "group")]
define_add_variants!(
    LHS = EdwardsPoint,
    RHS = SubgroupPoint,
    Output = EdwardsPoint
);

#[cfg(feature = "group")]
impl AddAssign<&SubgroupPoint> for SubgroupPoint {
    fn add_assign(&mut self, rhs: &SubgroupPoint) {
        self.0 += rhs.0
    }
}

#[cfg(feature = "group")]
define_add_assign_variants!(LHS = SubgroupPoint, RHS = SubgroupPoint);

#[cfg(feature = "group")]
impl AddAssign<&SubgroupPoint> for EdwardsPoint {
    fn add_assign(&mut self, rhs: &SubgroupPoint) {
        *self += rhs.0
    }
}

#[cfg(feature = "group")]
define_add_assign_variants!(LHS = EdwardsPoint, RHS = SubgroupPoint);

#[cfg(feature = "group")]
impl Sub<&SubgroupPoint> for &SubgroupPoint {
    type Output = SubgroupPoint;
    fn sub(self, other: &SubgroupPoint) -> SubgroupPoint {
        SubgroupPoint(self.0 - other.0)
    }
}

#[cfg(feature = "group")]
define_sub_variants!(
    LHS = SubgroupPoint,
    RHS = SubgroupPoint,
    Output = SubgroupPoint
);

#[cfg(feature = "group")]
impl Sub<&SubgroupPoint> for &EdwardsPoint {
    type Output = EdwardsPoint;
    fn sub(self, other: &SubgroupPoint) -> EdwardsPoint {
        self - other.0
    }
}

#[cfg(feature = "group")]
define_sub_variants!(
    LHS = EdwardsPoint,
    RHS = SubgroupPoint,
    Output = EdwardsPoint
);

#[cfg(feature = "group")]
impl SubAssign<&SubgroupPoint> for SubgroupPoint {
    fn sub_assign(&mut self, rhs: &SubgroupPoint) {
        self.0 -= rhs.0;
    }
}

#[cfg(feature = "group")]
define_sub_assign_variants!(LHS = SubgroupPoint, RHS = SubgroupPoint);

#[cfg(feature = "group")]
impl SubAssign<&SubgroupPoint> for EdwardsPoint {
    fn sub_assign(&mut self, rhs: &SubgroupPoint) {
        *self -= rhs.0;
    }
}

#[cfg(feature = "group")]
define_sub_assign_variants!(LHS = EdwardsPoint, RHS = SubgroupPoint);

#[cfg(feature = "group")]
impl<T> Sum<T> for SubgroupPoint
where
    T: Borrow<SubgroupPoint>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        use group::Group;
        iter.fold(SubgroupPoint::identity(), |acc, item| acc + item.borrow())
    }
}

#[cfg(feature = "group")]
impl Mul<&Scalar> for &SubgroupPoint {
    type Output = SubgroupPoint;

    /// Scalar multiplication: compute `scalar * self`.
    ///
    /// For scalar multiplication of a basepoint,
    /// `EdwardsBasepointTable` is approximately 4x faster.
    fn mul(self, scalar: &Scalar) -> SubgroupPoint {
        SubgroupPoint(self.0 * scalar)
    }
}

#[cfg(feature = "group")]
define_mul_variants!(LHS = Scalar, RHS = SubgroupPoint, Output = SubgroupPoint);

#[cfg(feature = "group")]
impl Mul<&SubgroupPoint> for &Scalar {
    type Output = SubgroupPoint;

    /// Scalar multiplication: compute `scalar * self`.
    ///
    /// For scalar multiplication of a basepoint,
    /// `EdwardsBasepointTable` is approximately 4x faster.
    fn mul(self, point: &SubgroupPoint) -> SubgroupPoint {
        point * self
    }
}

#[cfg(feature = "group")]
define_mul_variants!(LHS = SubgroupPoint, RHS = Scalar, Output = SubgroupPoint);

#[cfg(feature = "group")]
impl MulAssign<&Scalar> for SubgroupPoint {
    fn mul_assign(&mut self, scalar: &Scalar) {
        self.0 *= scalar;
    }
}

#[cfg(feature = "group")]
define_mul_assign_variants!(LHS = SubgroupPoint, RHS = Scalar);

#[cfg(feature = "group")]
impl group::Group for SubgroupPoint {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        use group::ff::Field;

        // This will almost never loop, but `Group::random` is documented as returning a
        // non-identity element.
        let s = loop {
            let s: Scalar = Field::random(&mut rng);
            if !s.is_zero_vartime() {
                break s;
            }
        };

        // This gives an element of the prime-order subgroup.
        Self::generator() * s
    }

    fn identity() -> Self {
        SubgroupPoint(Identity::identity())
    }

    fn generator() -> Self {
        SubgroupPoint(EdwardsPoint::generator())
    }

    fn is_identity(&self) -> Choice {
        self.0.ct_eq(&Identity::identity())
    }

    fn double(&self) -> Self {
        SubgroupPoint(self.0.double())
    }
}

#[cfg(feature = "group")]
impl GroupEncoding for SubgroupPoint {
    type Repr = <EdwardsPoint as GroupEncoding>::Repr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        EdwardsPoint::from_bytes(bytes).and_then(|p| p.into_subgroup())
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        EdwardsPoint::from_bytes_unchecked(bytes).and_then(|p| p.into_subgroup())
    }

    fn to_bytes(&self) -> Self::Repr {
        self.0.compress().to_bytes()
    }
}

#[cfg(feature = "group")]
impl PrimeGroup for SubgroupPoint {}

/// Ristretto has a cofactor of 1.
#[cfg(feature = "group")]
impl CofactorGroup for EdwardsPoint {
    type Subgroup = SubgroupPoint;

    fn clear_cofactor(&self) -> Self::Subgroup {
        SubgroupPoint(self.mul_by_cofactor())
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(SubgroupPoint(self), CofactorGroup::is_torsion_free(&self))
    }

    fn is_torsion_free(&self) -> Choice {
        (self * constants::BASEPOINT_ORDER_PRIVATE).ct_eq(&Self::identity())
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test_sum {
    use super::*;

    #[test]
    #[cfg(all(feature = "alloc", feature = "rand_core"))]
    fn verus_equivalence_random_sum() {
        use rand_core::{OsRng, RngCore};

        let mut rng = OsRng;

        for iteration in 0..10 {
            let n = (rng.next_u32() % 65) as usize; // 0..=64
            let mut points: Vec<EdwardsPoint> = Vec::with_capacity(n);

            while points.len() < n {
                let mut bytes = [0u8; 32];
                rng.fill_bytes(&mut bytes);
                if let Some(p) = CompressedEdwardsY(bytes).decompress() {
                    points.push(p);
                }
            }

            let original = EdwardsPoint::sum_original(points.iter());
            let refactored: EdwardsPoint = points.iter().sum();

            assert_eq!(
                original.compress().as_bytes(),
                refactored.compress().as_bytes(),
                "Mismatch in iteration {} with {} points",
                iteration,
                n
            );
        }
    }
}

// #[cfg(test)]
// mod test {
//     use super::*;

//     // If `group` is set, then this is already imported in super
//     #[cfg(not(feature = "group"))]
//     use rand_core::RngCore;

//     #[cfg(feature = "alloc")]
//     use alloc::vec::Vec;

//     #[cfg(feature = "precomputed-tables")]
//     use crate::constants::ED25519_BASEPOINT_TABLE;

//     /// X coordinate of the basepoint.
//     /// = 15112221349535400772501151409588531511454012693041857206046113283949847762202
//     static BASE_X_COORD_BYTES: [u8; 32] = [
//         0x1a, 0xd5, 0x25, 0x8f, 0x60, 0x2d, 0x56, 0xc9, 0xb2, 0xa7, 0x25, 0x95, 0x60, 0xc7, 0x2c,
//         0x69, 0x5c, 0xdc, 0xd6, 0xfd, 0x31, 0xe2, 0xa4, 0xc0, 0xfe, 0x53, 0x6e, 0xcd, 0xd3, 0x36,
//         0x69, 0x21,
//     ];

//     /// Compressed Edwards Y form of 2*basepoint.
//     static BASE2_CMPRSSD: CompressedEdwardsY = CompressedEdwardsY([
//         0xc9, 0xa3, 0xf8, 0x6a, 0xae, 0x46, 0x5f, 0xe, 0x56, 0x51, 0x38, 0x64, 0x51, 0x0f, 0x39,
//         0x97, 0x56, 0x1f, 0xa2, 0xc9, 0xe8, 0x5e, 0xa2, 0x1d, 0xc2, 0x29, 0x23, 0x09, 0xf3, 0xcd,
//         0x60, 0x22,
//     ]);

//     /// Compressed Edwards Y form of 16*basepoint.
//     static BASE16_CMPRSSD: CompressedEdwardsY = CompressedEdwardsY([
//         0xeb, 0x27, 0x67, 0xc1, 0x37, 0xab, 0x7a, 0xd8, 0x27, 0x9c, 0x07, 0x8e, 0xff, 0x11, 0x6a,
//         0xb0, 0x78, 0x6e, 0xad, 0x3a, 0x2e, 0x0f, 0x98, 0x9f, 0x72, 0xc3, 0x7f, 0x82, 0xf2, 0x96,
//         0x96, 0x70,
//     ]);

//     /// 4493907448824000747700850167940867464579944529806937181821189941592931634714
//     pub static A_SCALAR: Scalar = Scalar {
//         bytes: [
//             0x1a, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d, 0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8,
//             0x26, 0x4d, 0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1, 0x58, 0x9e, 0x7b, 0x7f,
//             0x23, 0x76, 0xef, 0x09,
//         ],
//     };

//     /// 2506056684125797857694181776241676200180934651973138769173342316833279714961
//     pub static B_SCALAR: Scalar = Scalar {
//         bytes: [
//             0x91, 0x26, 0x7a, 0xcf, 0x25, 0xc2, 0x09, 0x1b, 0xa2, 0x17, 0x74, 0x7b, 0x66, 0xf0,
//             0xb3, 0x2e, 0x9d, 0xf2, 0xa5, 0x67, 0x41, 0xcf, 0xda, 0xc4, 0x56, 0xa7, 0xd4, 0xaa,
//             0xb8, 0x60, 0x8a, 0x05,
//         ],
//     };

//     /// A_SCALAR * basepoint, computed with ed25519.py
//     pub static A_TIMES_BASEPOINT: CompressedEdwardsY = CompressedEdwardsY([
//         0xea, 0x27, 0xe2, 0x60, 0x53, 0xdf, 0x1b, 0x59, 0x56, 0xf1, 0x4d, 0x5d, 0xec, 0x3c, 0x34,
//         0xc3, 0x84, 0xa2, 0x69, 0xb7, 0x4c, 0xc3, 0x80, 0x3e, 0xa8, 0xe2, 0xe7, 0xc9, 0x42, 0x5e,
//         0x40, 0xa5,
//     ]);

//     /// A_SCALAR * (A_TIMES_BASEPOINT) + B_SCALAR * BASEPOINT
//     /// computed with ed25519.py
//     static DOUBLE_SCALAR_MULT_RESULT: CompressedEdwardsY = CompressedEdwardsY([
//         0x7d, 0xfd, 0x6c, 0x45, 0xaf, 0x6d, 0x6e, 0x0e, 0xba, 0x20, 0x37, 0x1a, 0x23, 0x64, 0x59,
//         0xc4, 0xc0, 0x46, 0x83, 0x43, 0xde, 0x70, 0x4b, 0x85, 0x09, 0x6f, 0xfe, 0x35, 0x4f, 0x13,
//         0x2b, 0x42,
//     ]);

//     /// Test round-trip decompression for the basepoint.
//     #[test]
//     fn basepoint_decompression_compression() {
//         let base_X = FieldElement::from_bytes(&BASE_X_COORD_BYTES);
//         let bp = constants::ED25519_BASEPOINT_COMPRESSED
//             .decompress()
//             .unwrap();
//         assert!(bp.is_valid());
//         // Check that decompression actually gives the correct X coordinate
//         assert_eq!(base_X, bp.X);
//         assert_eq!(bp.compress(), constants::ED25519_BASEPOINT_COMPRESSED);
//     }

//     /// Test sign handling in decompression
//     #[test]
//     fn decompression_sign_handling() {
//         // Manually set the high bit of the last byte to flip the sign
//         let mut minus_basepoint_bytes = *constants::ED25519_BASEPOINT_COMPRESSED.as_bytes();
//         minus_basepoint_bytes[31] |= 1 << 7;
//         let minus_basepoint = CompressedEdwardsY(minus_basepoint_bytes)
//             .decompress()
//             .unwrap();
//         // Test projective coordinates exactly since we know they should
//         // only differ by a flipped sign.
//         assert_eq!(minus_basepoint.X, -(&constants::ED25519_BASEPOINT_POINT.X));
//         assert_eq!(minus_basepoint.Y, constants::ED25519_BASEPOINT_POINT.Y);
//         assert_eq!(minus_basepoint.Z, constants::ED25519_BASEPOINT_POINT.Z);
//         assert_eq!(minus_basepoint.T, -(&constants::ED25519_BASEPOINT_POINT.T));
//     }

//     /// Test that computing 1*basepoint gives the correct basepoint.
//     #[cfg(feature = "precomputed-tables")]
//     #[test]
//     fn basepoint_mult_one_vs_basepoint() {
//         let bp = ED25519_BASEPOINT_TABLE * &Scalar::ONE;
//         let compressed = bp.compress();
//         assert_eq!(compressed, constants::ED25519_BASEPOINT_COMPRESSED);
//     }

//     /// Test that `EdwardsBasepointTable::basepoint()` gives the correct basepoint.
//     #[cfg(feature = "precomputed-tables")]
//     #[test]
//     fn basepoint_table_basepoint_function_correct() {
//         let bp = ED25519_BASEPOINT_TABLE.basepoint();
//         assert_eq!(bp.compress(), constants::ED25519_BASEPOINT_COMPRESSED);
//     }

//     /// Test `impl Add<EdwardsPoint> for EdwardsPoint`
//     /// using basepoint + basepoint versus the 2*basepoint constant.
//     #[test]
//     fn basepoint_plus_basepoint_vs_basepoint2() {
//         let bp = constants::ED25519_BASEPOINT_POINT;
//         let bp_added = bp + bp;
//         assert_eq!(bp_added.compress(), BASE2_CMPRSSD);
//     }

//     /// Test `impl Add<ProjectiveNielsPoint> for EdwardsPoint`
//     /// using the basepoint, basepoint2 constants
//     #[test]
//     fn basepoint_plus_basepoint_projective_niels_vs_basepoint2() {
//         let bp = constants::ED25519_BASEPOINT_POINT;
//         let bp_added = (&bp + &bp.as_projective_niels()).as_extended();
//         assert_eq!(bp_added.compress(), BASE2_CMPRSSD);
//     }

//     /// Test `impl Add<AffineNielsPoint> for EdwardsPoint`
//     /// using the basepoint, basepoint2 constants
//     #[test]
//     fn basepoint_plus_basepoint_affine_niels_vs_basepoint2() {
//         let bp = constants::ED25519_BASEPOINT_POINT;
//         let bp_affine_niels = bp.as_affine_niels();
//         let bp_added = (&bp + &bp_affine_niels).as_extended();
//         assert_eq!(bp_added.compress(), BASE2_CMPRSSD);
//     }

//     /// Check that equality of `EdwardsPoints` handles projective
//     /// coordinates correctly.
//     #[test]
//     fn extended_point_equality_handles_scaling() {
//         let mut two_bytes = [0u8; 32];
//         two_bytes[0] = 2;
//         let id1 = EdwardsPoint::identity();
//         let id2 = EdwardsPoint {
//             X: FieldElement::ZERO,
//             Y: FieldElement::from_bytes(&two_bytes),
//             Z: FieldElement::from_bytes(&two_bytes),
//             T: FieldElement::ZERO,
//         };
//         assert!(bool::from(id1.ct_eq(&id2)));
//     }

//     /// Sanity check for conversion to precomputed points
//     #[cfg(feature = "precomputed-tables")]
//     #[test]
//     fn to_affine_niels_clears_denominators() {
//         // construct a point as aB so it has denominators (ie. Z != 1)
//         let aB = ED25519_BASEPOINT_TABLE * &A_SCALAR;
//         let aB_affine_niels = aB.as_affine_niels();
//         let also_aB = (&EdwardsPoint::identity() + &aB_affine_niels).as_extended();
//         assert_eq!(aB.compress(), also_aB.compress());
//     }

//     /// Test mul_base versus a known scalar multiple from ed25519.py
//     #[test]
//     fn basepoint_mult_vs_ed25519py() {
//         let aB = EdwardsPoint::mul_base(&A_SCALAR);
//         assert_eq!(aB.compress(), A_TIMES_BASEPOINT);
//     }

//     /// Test that multiplication by the basepoint order kills the basepoint
//     #[test]
//     fn basepoint_mult_by_basepoint_order() {
//         let should_be_id = EdwardsPoint::mul_base(&constants::BASEPOINT_ORDER_PRIVATE);
//         assert!(should_be_id.is_identity());
//     }

//     /// Test precomputed basepoint mult
//     #[cfg(feature = "precomputed-tables")]
//     #[test]
//     fn test_precomputed_basepoint_mult() {
//         let aB_1 = ED25519_BASEPOINT_TABLE * &A_SCALAR;
//         let aB_2 = constants::ED25519_BASEPOINT_POINT * A_SCALAR;
//         assert_eq!(aB_1.compress(), aB_2.compress());
//     }

//     /// Test scalar_mul versus a known scalar multiple from ed25519.py
//     #[test]
//     fn scalar_mul_vs_ed25519py() {
//         let aB = constants::ED25519_BASEPOINT_POINT * A_SCALAR;
//         assert_eq!(aB.compress(), A_TIMES_BASEPOINT);
//     }

//     /// Test basepoint.double() versus the 2*basepoint constant.
//     #[test]
//     fn basepoint_double_vs_basepoint2() {
//         assert_eq!(
//             constants::ED25519_BASEPOINT_POINT.double().compress(),
//             BASE2_CMPRSSD
//         );
//     }

//     /// Test that computing 2*basepoint is the same as basepoint.double()
//     #[test]
//     fn basepoint_mult_two_vs_basepoint2() {
//         let two = Scalar::from(2u64);
//         let bp2 = EdwardsPoint::mul_base(&two);
//         assert_eq!(bp2.compress(), BASE2_CMPRSSD);
//     }

//     /// Test that all the basepoint table types compute the same results.
//     #[cfg(feature = "precomputed-tables")]
//     #[test]
//     fn basepoint_tables() {
//         let P = &constants::ED25519_BASEPOINT_POINT;
//         let a = A_SCALAR;

//         let table_radix16 = EdwardsBasepointTableRadix16::create(P);
//         let table_radix32 = EdwardsBasepointTableRadix32::create(P);
//         let table_radix64 = EdwardsBasepointTableRadix64::create(P);
//         let table_radix128 = EdwardsBasepointTableRadix128::create(P);
//         let table_radix256 = EdwardsBasepointTableRadix256::create(P);

//         let aP = (ED25519_BASEPOINT_TABLE * &a).compress();
//         let aP16 = (&table_radix16 * &a).compress();
//         let aP32 = (&table_radix32 * &a).compress();
//         let aP64 = (&table_radix64 * &a).compress();
//         let aP128 = (&table_radix128 * &a).compress();
//         let aP256 = (&table_radix256 * &a).compress();

//         assert_eq!(aP, aP16);
//         assert_eq!(aP16, aP32);
//         assert_eq!(aP32, aP64);
//         assert_eq!(aP64, aP128);
//         assert_eq!(aP128, aP256);
//     }

//     /// Check unreduced scalar multiplication by the basepoint tables is the same no matter what
//     /// radix the table is.
//     #[cfg(feature = "precomputed-tables")]
//     #[test]
//     fn basepoint_tables_unreduced_scalar() {
//         let P = &constants::ED25519_BASEPOINT_POINT;
//         let a = crate::scalar::test::LARGEST_UNREDUCED_SCALAR;

//         let table_radix16 = EdwardsBasepointTableRadix16::create(P);
//         let table_radix32 = EdwardsBasepointTableRadix32::create(P);
//         let table_radix64 = EdwardsBasepointTableRadix64::create(P);
//         let table_radix128 = EdwardsBasepointTableRadix128::create(P);
//         let table_radix256 = EdwardsBasepointTableRadix256::create(P);

//         let aP = (ED25519_BASEPOINT_TABLE * &a).compress();
//         let aP16 = (&table_radix16 * &a).compress();
//         let aP32 = (&table_radix32 * &a).compress();
//         let aP64 = (&table_radix64 * &a).compress();
//         let aP128 = (&table_radix128 * &a).compress();
//         let aP256 = (&table_radix256 * &a).compress();

//         assert_eq!(aP, aP16);
//         assert_eq!(aP16, aP32);
//         assert_eq!(aP32, aP64);
//         assert_eq!(aP64, aP128);
//         assert_eq!(aP128, aP256);
//     }

//     /// Check that converting to projective and then back to extended round-trips.
//     #[test]
//     fn basepoint_projective_extended_round_trip() {
//         assert_eq!(
//             constants::ED25519_BASEPOINT_POINT
//                 .as_projective()
//                 .as_extended()
//                 .compress(),
//             constants::ED25519_BASEPOINT_COMPRESSED
//         );
//     }

//     /// Test computing 16*basepoint vs mul_by_pow_2(4)
//     #[test]
//     fn basepoint16_vs_mul_by_pow_2_4() {
//         let bp16 = constants::ED25519_BASEPOINT_POINT.mul_by_pow_2(4);
//         assert_eq!(bp16.compress(), BASE16_CMPRSSD);
//     }

//     /// Check that mul_base_clamped and mul_clamped agree
//     #[test]
//     fn mul_base_clamped() {
//         let mut csprng = rand_core::OsRng;

//         // Make a random curve point in the curve. Give it torsion to make things interesting.
//         #[cfg(feature = "precomputed-tables")]
//         let random_point = {
//             let mut b = [0u8; 32];
//             csprng.fill_bytes(&mut b);
//             EdwardsPoint::mul_base_clamped(b) + constants::EIGHT_TORSION[1]
//         };
//         // Make a basepoint table from the random point. We'll use this with mul_base_clamped
//         #[cfg(feature = "precomputed-tables")]
//         let random_table = EdwardsBasepointTableRadix256::create(&random_point);

//         // Now test scalar mult. agreement on the default basepoint as well as random_point

//         // Test that mul_base_clamped and mul_clamped agree on a large integer. Even after
//         // clamping, this integer is not reduced mod l.
//         let a_bytes = [0xff; 32];
//         assert_eq!(
//             EdwardsPoint::mul_base_clamped(a_bytes),
//             constants::ED25519_BASEPOINT_POINT.mul_clamped(a_bytes)
//         );
//         #[cfg(feature = "precomputed-tables")]
//         assert_eq!(
//             random_table.mul_base_clamped(a_bytes),
//             random_point.mul_clamped(a_bytes)
//         );

//         // Test agreement on random integers
//         for _ in 0..100 {
//             // This will be reduced mod l with probability l / 2^256 ≈ 6.25%
//             let mut a_bytes = [0u8; 32];
//             csprng.fill_bytes(&mut a_bytes);

//             assert_eq!(
//                 EdwardsPoint::mul_base_clamped(a_bytes),
//                 constants::ED25519_BASEPOINT_POINT.mul_clamped(a_bytes)
//             );
//             #[cfg(feature = "precomputed-tables")]
//             assert_eq!(
//                 random_table.mul_base_clamped(a_bytes),
//                 random_point.mul_clamped(a_bytes)
//             );
//         }
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn impl_sum() {
//         // Test that sum works for non-empty iterators
//         let BASE = constants::ED25519_BASEPOINT_POINT;

//         let s1 = Scalar::from(999u64);
//         let P1 = BASE * s1;

//         let s2 = Scalar::from(333u64);
//         let P2 = BASE * s2;

//         let vec = vec![P1, P2];
//         let sum: EdwardsPoint = vec.iter().sum();

//         assert_eq!(sum, P1 + P2);

//         // Test that sum works for the empty iterator
//         let empty_vector: Vec<EdwardsPoint> = vec![];
//         let sum: EdwardsPoint = empty_vector.iter().sum();

//         assert_eq!(sum, EdwardsPoint::identity());

//         // Test that sum works on owning iterators
//         let s = Scalar::from(2u64);
//         let mapped = vec.iter().map(|x| x * s);
//         let sum: EdwardsPoint = mapped.sum();

//         assert_eq!(sum, P1 * s + P2 * s);
//     }

//     /// Test that the conditional assignment trait works for AffineNielsPoints.
//     #[test]
//     fn conditional_assign_for_affine_niels_point() {
//         let id = AffineNielsPoint::identity();
//         let mut p1 = AffineNielsPoint::identity();
//         let bp = constants::ED25519_BASEPOINT_POINT.as_affine_niels();

//         p1.conditional_assign(&bp, Choice::from(0));
//         assert_eq!(p1, id);
//         p1.conditional_assign(&bp, Choice::from(1));
//         assert_eq!(p1, bp);
//     }

//     #[test]
//     fn is_small_order() {
//         // The basepoint has large prime order
//         assert!(!constants::ED25519_BASEPOINT_POINT.is_small_order());
//         // constants::EIGHT_TORSION has all points of small order.
//         for torsion_point in &constants::EIGHT_TORSION {
//             assert!(torsion_point.is_small_order());
//         }
//     }

//     #[test]
//     fn compressed_identity() {
//         assert_eq!(
//             EdwardsPoint::identity().compress(),
//             CompressedEdwardsY::identity()
//         );
//     }

//     #[test]
//     fn is_identity() {
//         assert!(EdwardsPoint::identity().is_identity());
//         assert!(!constants::ED25519_BASEPOINT_POINT.is_identity());
//     }

//     /// Rust's debug builds have overflow and underflow trapping,
//     /// and enable `debug_assert!()`.  This performs many scalar
//     /// multiplications to attempt to trigger possible overflows etc.
//     ///
//     /// For instance, the `u64` `Mul` implementation for
//     /// `FieldElements` requires the input `Limb`s to be bounded by
//     /// 2^54, but we cannot enforce this dynamically at runtime, or
//     /// statically at compile time (until Rust gets type-level
//     /// integers, at which point we can encode "bits of headroom" into
//     /// the type system and prove correctness).
//     #[test]
//     fn monte_carlo_overflow_underflow_debug_assert_test() {
//         let mut P = constants::ED25519_BASEPOINT_POINT;
//         // N.B. each scalar_mul does 1407 field mults, 1024 field squarings,
//         // so this does ~ 1M of each operation.
//         for _ in 0..1_000 {
//             P *= &A_SCALAR;
//         }
//     }

//     #[test]
//     fn scalarmult_extended_point_works_both_ways() {
//         let G: EdwardsPoint = constants::ED25519_BASEPOINT_POINT;
//         let s: Scalar = A_SCALAR;

//         let P1 = G * s;
//         let P2 = s * G;

//         assert!(P1.compress().to_bytes() == P2.compress().to_bytes());
//     }

//     // A single iteration of a consistency check for MSM.
//     #[cfg(feature = "alloc")]
//     fn multiscalar_consistency_iter(n: usize) {
//         let mut rng = rand::thread_rng();

//         // Construct random coefficients x0, ..., x_{n-1},
//         // followed by some extra hardcoded ones.
//         let xs = (0..n).map(|_| Scalar::random(&mut rng)).collect::<Vec<_>>();
//         let check = xs.iter().map(|xi| xi * xi).sum::<Scalar>();

//         // Construct points G_i = x_i * B
//         let Gs = xs.iter().map(EdwardsPoint::mul_base).collect::<Vec<_>>();

//         // Compute H1 = <xs, Gs> (consttime)
//         let H1 = EdwardsPoint::multiscalar_mul(&xs, &Gs);
//         // Compute H2 = <xs, Gs> (vartime)
//         let H2 = EdwardsPoint::vartime_multiscalar_mul(&xs, &Gs);
//         // Compute H3 = <xs, Gs> = sum(xi^2) * B
//         let H3 = EdwardsPoint::mul_base(&check);

//         assert_eq!(H1, H3);
//         assert_eq!(H2, H3);
//     }

//     // Use different multiscalar sizes to hit different internal
//     // parameters.

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn multiscalar_consistency_n_100() {
//         let iters = 50;
//         for _ in 0..iters {
//             multiscalar_consistency_iter(100);
//         }
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn multiscalar_consistency_n_250() {
//         let iters = 50;
//         for _ in 0..iters {
//             multiscalar_consistency_iter(250);
//         }
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn multiscalar_consistency_n_500() {
//         let iters = 50;
//         for _ in 0..iters {
//             multiscalar_consistency_iter(500);
//         }
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn multiscalar_consistency_n_1000() {
//         let iters = 50;
//         for _ in 0..iters {
//             multiscalar_consistency_iter(1000);
//         }
//     }

//     #[test]
//     #[cfg(feature = "alloc")]
//     fn vartime_precomputed_vs_nonprecomputed_multiscalar() {
//         let mut rng = rand::thread_rng();

//         let static_scalars = (0..128)
//             .map(|_| Scalar::random(&mut rng))
//             .collect::<Vec<_>>();

//         let dynamic_scalars = (0..128)
//             .map(|_| Scalar::random(&mut rng))
//             .collect::<Vec<_>>();

//         let check_scalar: Scalar = static_scalars
//             .iter()
//             .chain(dynamic_scalars.iter())
//             .map(|s| s * s)
//             .sum();

//         let static_points = static_scalars
//             .iter()
//             .map(EdwardsPoint::mul_base)
//             .collect::<Vec<_>>();
//         let dynamic_points = dynamic_scalars
//             .iter()
//             .map(EdwardsPoint::mul_base)
//             .collect::<Vec<_>>();

//         let precomputation = VartimeEdwardsPrecomputation::new(static_points.iter());

//         let P = precomputation.vartime_mixed_multiscalar_mul(
//             &static_scalars,
//             &dynamic_scalars,
//             &dynamic_points,
//         );

//         use crate::traits::VartimeMultiscalarMul;
//         let Q = EdwardsPoint::vartime_multiscalar_mul(
//             static_scalars.iter().chain(dynamic_scalars.iter()),
//             static_points.iter().chain(dynamic_points.iter()),
//         );

//         let R = EdwardsPoint::mul_base(&check_scalar);

//         assert_eq!(P.compress(), R.compress());
//         assert_eq!(Q.compress(), R.compress());
//     }

//     mod vartime {
//         use super::super::*;
//         use super::{A_SCALAR, A_TIMES_BASEPOINT, B_SCALAR, DOUBLE_SCALAR_MULT_RESULT};

//         /// Test double_scalar_mul_vartime vs ed25519.py
//         #[test]
//         fn double_scalar_mul_basepoint_vs_ed25519py() {
//             let A = A_TIMES_BASEPOINT.decompress().unwrap();
//             let result =
//                 EdwardsPoint::vartime_double_scalar_mul_basepoint(&A_SCALAR, &A, &B_SCALAR);
//             assert_eq!(result.compress(), DOUBLE_SCALAR_MULT_RESULT);
//         }

//         #[test]
//         #[cfg(feature = "alloc")]
//         fn multiscalar_mul_vs_ed25519py() {
//             let A = A_TIMES_BASEPOINT.decompress().unwrap();
//             let result = EdwardsPoint::vartime_multiscalar_mul(
//                 &[A_SCALAR, B_SCALAR],
//                 &[A, constants::ED25519_BASEPOINT_POINT],
//             );
//             assert_eq!(result.compress(), DOUBLE_SCALAR_MULT_RESULT);
//         }

//         #[test]
//         #[cfg(feature = "alloc")]
//         fn multiscalar_mul_vartime_vs_consttime() {
//             let A = A_TIMES_BASEPOINT.decompress().unwrap();
//             let result_vartime = EdwardsPoint::vartime_multiscalar_mul(
//                 &[A_SCALAR, B_SCALAR],
//                 &[A, constants::ED25519_BASEPOINT_POINT],
//             );
//             let result_consttime = EdwardsPoint::multiscalar_mul(
//                 &[A_SCALAR, B_SCALAR],
//                 &[A, constants::ED25519_BASEPOINT_POINT],
//             );

//             assert_eq!(result_vartime.compress(), result_consttime.compress());
//         }
//     }

//     #[test]
//     #[cfg(feature = "serde")]
//     fn serde_bincode_basepoint_roundtrip() {
//         use bincode;

//         let encoded = bincode::serialize(&constants::ED25519_BASEPOINT_POINT).unwrap();
//         let enc_compressed = bincode::serialize(&constants::ED25519_BASEPOINT_COMPRESSED).unwrap();
//         assert_eq!(encoded, enc_compressed);

//         // Check that the encoding is 32 bytes exactly
//         assert_eq!(encoded.len(), 32);

//         let dec_uncompressed: EdwardsPoint = bincode::deserialize(&encoded).unwrap();
//         let dec_compressed: CompressedEdwardsY = bincode::deserialize(&encoded).unwrap();

//         assert_eq!(dec_uncompressed, constants::ED25519_BASEPOINT_POINT);
//         assert_eq!(dec_compressed, constants::ED25519_BASEPOINT_COMPRESSED);

//         // Check that the encoding itself matches the usual one
//         let raw_bytes = constants::ED25519_BASEPOINT_COMPRESSED.as_bytes();
//         let bp: EdwardsPoint = bincode::deserialize(raw_bytes).unwrap();
//         assert_eq!(bp, constants::ED25519_BASEPOINT_POINT);
//     }

//     ////////////////////////////////////////////////////////////
//     // Signal tests from                                      //
//     //     https://github.com/signalapp/libsignal-protocol-c/ //
//     ////////////////////////////////////////////////////////////

//     #[cfg(all(feature = "alloc", feature = "digest"))]
//     fn test_vectors() -> Vec<Vec<&'static str>> {
//         vec![
//             vec![
//                 "214f306e1576f5a7577636fe303ca2c625b533319f52442b22a9fa3b7ede809f",
//                 "c95becf0f93595174633b9d4d6bbbeb88e16fa257176f877ce426e1424626052",
//             ],
//             vec![
//                 "2eb10d432702ea7f79207da95d206f82d5a3b374f5f89f17a199531f78d3bea6",
//                 "d8f8b508edffbb8b6dab0f602f86a9dd759f800fe18f782fdcac47c234883e7f",
//             ],
//             vec![
//                 "84cbe9accdd32b46f4a8ef51c85fd39d028711f77fb00e204a613fc235fd68b9",
//                 "93c73e0289afd1d1fc9e4e78a505d5d1b2642fbdf91a1eff7d281930654b1453",
//             ],
//             vec![
//                 "c85165952490dc1839cb69012a3d9f2cc4b02343613263ab93a26dc89fd58267",
//                 "43cbe8685fd3c90665b91835debb89ff1477f906f5170f38a192f6a199556537",
//             ],
//             vec![
//                 "26e7fc4a78d863b1a4ccb2ce0951fbcd021e106350730ee4157bacb4502e1b76",
//                 "b6fc3d738c2c40719479b2f23818180cdafa72a14254d4016bbed8f0b788a835",
//             ],
//             vec![
//                 "1618c08ef0233f94f0f163f9435ec7457cd7a8cd4bb6b160315d15818c30f7a2",
//                 "da0b703593b29dbcd28ebd6e7baea17b6f61971f3641cae774f6a5137a12294c",
//             ],
//             vec![
//                 "48b73039db6fcdcb6030c4a38e8be80b6390d8ae46890e77e623f87254ef149c",
//                 "ca11b25acbc80566603eabeb9364ebd50e0306424c61049e1ce9385d9f349966",
//             ],
//             vec![
//                 "a744d582b3a34d14d311b7629da06d003045ae77cebceeb4e0e72734d63bd07d",
//                 "fad25a5ea15d4541258af8785acaf697a886c1b872c793790e60a6837b1adbc0",
//             ],
//             vec![
//                 "80a6ff33494c471c5eff7efb9febfbcf30a946fe6535b3451cda79f2154a7095",
//                 "57ac03913309b3f8cd3c3d4c49d878bb21f4d97dc74a1eaccbe5c601f7f06f47",
//             ],
//             vec![
//                 "f06fc939bc10551a0fd415aebf107ef0b9c4ee1ef9a164157bdd089127782617",
//                 "785b2a6a00a5579cc9da1ff997ce8339b6f9fb46c6f10cf7a12ff2986341a6e0",
//             ],
//         ]
//     }

//     #[test]
//     #[allow(deprecated)]
//     #[cfg(all(feature = "alloc", feature = "digest"))]
//     fn elligator_signal_test_vectors() {
//         for vector in test_vectors().iter() {
//             let input = hex::decode(vector[0]).unwrap();
//             let output = hex::decode(vector[1]).unwrap();

//             let point = EdwardsPoint::nonspec_map_to_curve::<sha2::Sha512>(&input);
//             assert_eq!(point.compress().to_bytes(), output[..]);
//         }
//     }
// }
