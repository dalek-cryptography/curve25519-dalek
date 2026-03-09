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
//! Code for fixed- and sliding-window functionality
#![allow(non_snake_case)]

use core::fmt::Debug;

use cfg_if::cfg_if;

use subtle::Choice;
use subtle::ConditionallyNegatable;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

use crate::traits::Identity;

use crate::backend::serial::curve_models::AffineNielsPoint;
use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::backend::serial::u64::subtle_assumes::{
    conditional_assign_generic, conditional_negate_affine_niels, conditional_negate_generic,
    conditional_negate_projective_niels, ct_eq_u16,
};
use crate::edwards::EdwardsPoint;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::choice_is_true;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::{
    lemma_affine_niels_affine_equals_edwards_affine, lemma_edwards_add_commutative,
    lemma_edwards_scalar_mul_additive, lemma_edwards_scalar_mul_succ,
    lemma_identity_affine_niels_valid, lemma_identity_projective_niels_valid,
    lemma_negate_affine_niels_preserves_validity, lemma_negate_projective_niels_preserves_validity,
    lemma_projective_niels_affine_equals_edwards_affine,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::lemma_sum_of_limbs_bounded_from_fe51_bounded;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::edwards_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::field_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::window_specs::*;
use vstd::prelude::*;

/* VERIFICATION NOTE: Removed unused impl_lookup_table! macro since LookupTable
(radix-16) was manually expanded. */

verus! {

/* VERIFICATION NOTE: Manually expanded impl_lookup_table! macro for radix-16 (LookupTable).
   Removed macro invocations for radix-32, 64, 128, 256 variants to focus verification
   on the primary radix-16 implementation used as a constructor for consts.

   Original macro invocation:
impl_lookup_table! {
    Name = LookupTable,
    Size = 8,
    SizeNeg = -8,
    SizeRange = 1..9,
    ConversionRange = 0..7
   }
*/
/// A lookup table of precomputed multiples of a point \\(P\\), used to
/// compute \\( xP \\) for \\( -8 \leq x \leq 8 \\).
///
/// The computation of \\( xP \\) is done in constant time by the `select` function.
///
/// Since `LookupTable` does not implement `Index`, it's more difficult
/// to accidentally use the table directly.  Unfortunately the table is
/// only `pub(crate)` so that we can write hardcoded constants, so it's
/// still technically possible.  It would be nice to prevent direct
/// access to the table.
///
/* VERIFICATION NOTE: Changed from `pub(crate)` to `pub` to allow Verus verification of
 the `from` function's ensures clause, which must be verifiable from outside this crate.
 */
#[derive(Copy)]
pub struct LookupTable<T>(pub [T; 8]);

/* VERIFICATION NOTE: Replaced generic impl with two concrete implementations
 to allow type-specific ensures clauses in the `select` function.

 ORIGINAL CODE:
 impl<T> LookupTable<T>
 where
     T: Identity + ConditionallySelectable + ConditionallyNegatable,
 {
     pub fn select(&self, x: i8) -> (result: T)
         ensures
             (x > 0 ==> result == self.0[(x - 1) as int]),
             // Generic T prevented type-specific specs for x == 0 and x < 0
     {...}
 }

 The `From` implementations were already concrete (one for AffineNielsPoint,
 one for ProjectiveNielsPoint), so they were unaffected by this change.
 */

// Concrete implementation of select for AffineNielsPoint
impl LookupTable<AffineNielsPoint> {
    /// Given \\(-8 \leq x \leq 8\\), return \\(xP\\) in constant time.
    ///
    /// Where P is the base point that was used to create this lookup table.
    /// This table stores [P, 2P, 3P, ..., 8P] (for radix-16).
    pub fn select(&self, x: i8) -> (result: AffineNielsPoint)
        requires
            -8 <= x,
            x <= 8,
            lookup_table_affine_limbs_bounded(self.0),
            // Not derivable from limb bounds alone; each entry must correspond to some EdwardsPoint.
            forall|j: int| 0 <= j < 8 ==> is_valid_affine_niels_point(#[trigger] self.0[j]),
        ensures
    // Formal specification for all cases:

            (x > 0 ==> result == self.0[(x - 1) as int]),
            (x == 0 ==> result == identity_affine_niels()),
            (x < 0 ==> result == negate_affine_niels(self.0[((-x) - 1) as int])),
            // Limb bounds on result
            fe51_limbs_bounded(&result.y_plus_x, 54),
            fe51_limbs_bounded(&result.y_minus_x, 54),
            fe51_limbs_bounded(&result.xy2d, 54),
            // The result is a valid AffineNielsPoint
            is_valid_affine_niels_point(result),
    {
        // Debug assertions from original macro - ignored by Verus
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert!(x >= -8);
            debug_assert!(x <= 8);
        }

        // Compute xabs = |x|
        let xmask = x as i16 >> 7;
        proof {
            // xmask is 0 or -1, so x + xmask doesn't overflow i16
            assert((x as i16 >> 7u32) == 0i16 || (x as i16 >> 7u32) == -1i16) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
            ;
        }
        let xabs = (x as i16 + xmask) ^ xmask;

        proof {
            // Bit-vector facts about xmask, xabs
            // In Verus spec mode, i16 + i16 returns int (for overflow safety),
            // making `(x as i16 + xmask) ^ xmask` fail because int has no XOR.
            // Work around by binding the sum as i16 so XOR stays in bitvector land.
            let xsum: i16 = (x as i16 + xmask) as i16;
            assert(x >= 0i8 ==> xabs == x as i16) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
                    xsum == (x as i16 + xmask) as i16,
                    xabs == (xsum ^ xmask),
            ;
            assert(x < 0i8 ==> xabs == -(x as i16)) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
                    xsum == (x as i16 + xmask) as i16,
                    xabs == (xsum ^ xmask),
            ;
        }

        // Set t = 0 * P = identity
        let mut t = AffineNielsPoint::identity();
        proof {
            assert(1u64 < (1u64 << 54u64)) by (bit_vector);
            assert(is_valid_affine_niels_point(t)) by {
                lemma_identity_affine_niels_valid();
            }
        }

        for j in 1..9
            invariant
        // Constant-time scan state: t holds the right value based on progress

                (xabs > 0 && (xabs as int) < j) ==> t == self.0[(xabs - 1) as int],
                (xabs == 0 || (xabs as int) >= j) ==> t == identity_affine_niels(),
                // Limb bounds preserved
                fe51_limbs_bounded(&t.y_plus_x, 54),
                fe51_limbs_bounded(&t.y_minus_x, 54),
                fe51_limbs_bounded(&t.xy2d, 54),
                // Validity preserved
                is_valid_affine_niels_point(t),
                // Table state (from preconditions, carry through loop)
                lookup_table_affine_limbs_bounded(self.0),
                forall|k: int| 0 <= k < 8 ==> is_valid_affine_niels_point(#[trigger] self.0[k]),
        {
            // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
            /* ORIGINAL CODE: let c = (xabs as u16).ct_eq(&(j as u16)); */
            let c = ct_eq_u16(&(xabs as u16), &(j as u16));
            /* ORIGINAL CODE: t.conditional_assign(&self.0[j - 1], c); */
            conditional_assign_generic(&mut t, &self.0[j - 1], c);
        }
        // Now t == |x| * P.

        let ghost old_t = t;
        let neg_mask = Choice::from((xmask & 1) as u8);
        proof {
            assert(x < 0i8 ==> ((xmask & 1i16) as u8 == 1u8)) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
            ;
            assert(x >= 0i8 ==> ((xmask & 1i16) as u8 == 0u8)) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
            ;
        }
        /* ORIGINAL CODE: t.conditional_negate(neg_mask); */
        conditional_negate_affine_niels(&mut t, neg_mask);
        proof {
            if x < 0 {
                assert(is_valid_affine_niels_point(t)) by {
                    lemma_negate_affine_niels_preserves_validity(old_t);
                }
            }
        }
        // Now t == x * P.

        t
    }
}

// Concrete implementation of select for ProjectiveNielsPoint
impl LookupTable<ProjectiveNielsPoint> {
    /// Given \\(-8 \leq x \leq 8\\), return \\(xP\\) in constant time.
    ///
    /// Where P is the base point that was used to create this lookup table.
    /// This table stores [P, 2P, 3P, ..., 8P] (for radix-16).
    pub fn select(&self, x: i8) -> (result: ProjectiveNielsPoint)
        requires
            -8 <= x,
            x <= 8,
            // Table entries must have bounded limbs
            lookup_table_projective_limbs_bounded(self.0),
            // Each table entry must be a valid ProjectiveNielsPoint
            forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] self.0[j]),
        ensures
    // Formal specification for all cases:

            (x > 0 ==> result == self.0[(x - 1) as int]),
            (x == 0 ==> result == identity_projective_niels()),
            (x < 0 ==> result == negate_projective_niels(self.0[((-x) - 1) as int])),
            // Limb bounds for the result (derived from table bounds)
            fe51_limbs_bounded(&result.Y_plus_X, 54),
            fe51_limbs_bounded(&result.Y_minus_X, 54),
            fe51_limbs_bounded(&result.Z, 54),
            fe51_limbs_bounded(&result.T2d, 54),
            // The result is a valid ProjectiveNielsPoint
            is_valid_projective_niels_point(result),
    {
        /* ORIGINAL CODE: for generic type T, $name, $size, $neg, $range, and $conv_range.

            debug_assert!(x >= $neg);
            debug_assert!(x as i16 <= $size as i16); // XXX We have to convert to i16s here for the radix-256 case.. this is wrong.

            // Compute xabs = |x|
                let xmask = x as i16 >> 7;
                let xabs = (x as i16 + xmask) ^ xmask;

                // Set t = 0 * P = identity
                let mut t = T::identity();
                for j in $range {
                    // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
                    let c = (xabs as u16).ct_eq(&(j as u16));
                    t.conditional_assign(&self.0[j - 1], c);
                }
                // Now t == |x| * P.

                let neg_mask = Choice::from((xmask & 1) as u8);
                t.conditional_negate(neg_mask);
                // Now t == x * P.

                t
        In our instantiation we have T = ProjectiveNielsPoint, $name = LookupTable, $size = 8, $neg = -8, $range = 1..9, and $conv_range = 0..7.
         */
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert!(x >= -8);
            debug_assert!(x <= 8);
        }

        // Compute xabs = |x|
        let xmask = x as i16 >> 7;
        proof {
            assert((x as i16 >> 7u32) == 0i16 || (x as i16 >> 7u32) == -1i16) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
            ;
        }
        let xabs = (x as i16 + xmask) ^ xmask;

        proof {
            let xsum: i16 = (x as i16 + xmask) as i16;
            assert(x >= 0i8 ==> xabs == x as i16) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
                    xsum == (x as i16 + xmask) as i16,
                    xabs == (xsum ^ xmask),
            ;
            assert(x < 0i8 ==> xabs == -(x as i16)) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
                    xsum == (x as i16 + xmask) as i16,
                    xabs == (xsum ^ xmask),
            ;
        }

        // Set t = 0 * P = identity
        let mut t = ProjectiveNielsPoint::identity();
        proof {
            assert(1u64 < (1u64 << 54u64)) by (bit_vector);
            assert(is_valid_projective_niels_point(t)) by {
                lemma_identity_projective_niels_valid();
            }
        }

        for j in 1..9
            invariant
        // Constant-time scan state: t holds the right value based on progress

                (xabs > 0 && (xabs as int) < j) ==> t == self.0[(xabs - 1) as int],
                (xabs == 0 || (xabs as int) >= j) ==> t == identity_projective_niels(),
                // Limb bounds preserved
                fe51_limbs_bounded(&t.Y_plus_X, 54),
                fe51_limbs_bounded(&t.Y_minus_X, 54),
                fe51_limbs_bounded(&t.Z, 54),
                fe51_limbs_bounded(&t.T2d, 54),
                // Validity preserved
                is_valid_projective_niels_point(t),
                // Table state (from preconditions, carry through loop)
                lookup_table_projective_limbs_bounded(self.0),
                forall|k: int| 0 <= k < 8 ==> is_valid_projective_niels_point(#[trigger] self.0[k]),
        {
            // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
            /* ORIGINAL CODE: let c = (xabs as u16).ct_eq(&(j as u16)); */
            let c = ct_eq_u16(&(xabs as u16), &(j as u16));
            /* ORIGINAL CODE: t.conditional_assign(&self.0[j - 1], c); */
            conditional_assign_generic(&mut t, &self.0[j - 1], c);
        }
        // Now t == |x| * P.

        let ghost old_t = t;
        let neg_mask = Choice::from((xmask & 1) as u8);
        proof {
            assert(x < 0i8 ==> ((xmask & 1i16) as u8 == 1u8)) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
            ;
            assert(x >= 0i8 ==> ((xmask & 1i16) as u8 == 0u8)) by (bit_vector)
                requires
                    -8i8 <= x && x <= 8i8,
                    xmask == (x as i16 >> 7u32),
            ;
        }
        /* ORIGINAL CODE: t.conditional_negate(neg_mask); */
        conditional_negate_projective_niels(&mut t, neg_mask);
        proof {
            if x < 0 {
                assert(is_valid_projective_niels_point(t)) by {
                    lemma_negate_projective_niels_preserves_validity(old_t);
                }
            }
        }
        // Now t == x * P.

        t
    }
}

// Manual Clone implementation to avoid array clone issues in Verus
impl<T: Copy> Clone for LookupTable<T> {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        *self
    }
}

// Specialized Default implementation for AffineNielsPoint
impl Default for LookupTable<AffineNielsPoint> {
    fn default() -> (result: LookupTable<AffineNielsPoint>)
        ensures
    // All table entries are set to the identity point

            forall|i: int|
                0 <= i < 8 ==> result.0[i] == crate::specs::edwards_specs::identity_affine_niels(),
    {
        LookupTable([AffineNielsPoint::default();8])
    }
}

// Specialized Default implementation for ProjectiveNielsPoint
impl Default for LookupTable<ProjectiveNielsPoint> {
    fn default() -> (result: LookupTable<ProjectiveNielsPoint>)
        ensures
    // All table entries are set to the identity point

            forall|i: int|
                0 <= i < 8 ==> result.0[i]
                    == crate::specs::edwards_specs::identity_projective_niels(),
    {
        LookupTable([ProjectiveNielsPoint::default();8])
    }
}

/* ORIGINAL CODE: generic default implementation
impl<T: Copy + Default> Default for $name<T> {
    fn default() -> $name<T> {
        $name([T::default(); 8])
    }
*/

impl<T: Debug> Debug for LookupTable<T> {
    #[verifier::external_body]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}(", stringify!(LookupTable))?;

        for x in self.0.iter() {
            write!(f, "{:?}", x)?;
        }

        write!(f, ")")
    }
}

impl<'a> From<&'a EdwardsPoint> for LookupTable<ProjectiveNielsPoint> {
    /// Create a lookup table from an EdwardsPoint
    /// Constructs [P, 2P, 3P, ..., Size*P]
    fn from(P: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_lookup_table_projective(result.0, *P, 8 as nat),
            lookup_table_projective_limbs_bounded(result.0),
            forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] result.0[j]),
    {
        /* ORIGINAL CODE: for generic $name, $size, and conv_range.

         let mut points = [P.as_projective_niels(); $size];
                for j in $conv_range {
                    points[j + 1] = (P + &points[j]).as_extended().as_projective_niels();
                }
                $name(points)

        In our instantiation we have $name = LookupTable, $size = 8, and conv_range = 0..7.
        */
        proof {
            use_type_invariant(P);
            lemma_unfold_edwards(*P);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&P.Y, &P.X, 52);
        }

        let ghost P_affine = edwards_point_as_affine(*P);
        let mut points = [P.as_projective_niels();8];
        proof {
            // Base case: points[0] corresponds to 1*P
            assert(projective_niels_point_as_affine_edwards(points[0]) == P_affine) by {
                lemma_projective_niels_affine_equals_edwards_affine(points[0], *P);
            }
            assert(edwards_scalar_mul(P_affine, 1) == P_affine) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
        }
        for j in 0..7
            invariant
        // Limb bounds for all entries built so far

                forall|k: int|
                    0 <= k <= j ==> fe51_limbs_bounded(&(#[trigger] points[k]).Y_plus_X, 54)
                        && fe51_limbs_bounded(&points[k].Y_minus_X, 54) && fe51_limbs_bounded(
                        &points[k].Z,
                        54,
                    ) && fe51_limbs_bounded(&points[k].T2d, 54),
                // Validity for all entries built so far
                forall|k: int|
                    0 <= k <= j ==> is_valid_projective_niels_point(#[trigger] points[k]),
                // Mathematical correspondence: entry[k] represents (k+1)*P
                forall|k: int|
                    0 <= k <= j ==> projective_niels_point_as_affine_edwards(#[trigger] points[k])
                        == edwards_scalar_mul(P_affine, (k + 1) as nat),
                // P is well-formed (needed for add preconditions)
                is_well_formed_edwards_point(*P),
                edwards_point_limbs_bounded(*P),
                is_valid_edwards_point(*P),
                P_affine == edwards_point_as_affine(*P),
        {
            // ORIGINAL CODE: points[j + 1] = (P + &points[j]).as_extended().as_projective_niels();
            proof {
                use_type_invariant(P);
                lemma_unfold_edwards(*P);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&P.Y, &P.X, 52);
            }
            let sum = P + &points[j];
            let extended = sum.as_extended();
            proof {
                use_type_invariant(extended);
                lemma_unfold_edwards(extended);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&extended.Y, &extended.X, 52);
            }
            points[j + 1] = extended.as_projective_niels();
            proof {
                // Prove mathematical correspondence for points[j+1]
                // Chain: niels_affine(points[j+1]) == ep_affine(extended) == completed_affine(sum) == add(P, points[j])
                assert(projective_niels_point_as_affine_edwards(points[(j + 1) as int])
                    == edwards_point_as_affine(extended)) by {
                    lemma_projective_niels_affine_equals_edwards_affine(
                        points[(j + 1) as int],
                        extended,
                    );
                }
                // add(P, scalar_mul(P, j+1)) == scalar_mul(P, j+2) via commutativity + succ lemma
                let prev = edwards_scalar_mul(P_affine, (j + 1) as nat);
                assert(edwards_scalar_mul(P_affine, (j + 2) as nat) == edwards_add(
                    prev.0,
                    prev.1,
                    P_affine.0,
                    P_affine.1,
                )) by {
                    lemma_edwards_scalar_mul_succ(P_affine, (j + 1) as nat);
                }
                assert(edwards_add(P_affine.0, P_affine.1, prev.0, prev.1) == edwards_add(
                    prev.0,
                    prev.1,
                    P_affine.0,
                    P_affine.1,
                )) by {
                    lemma_edwards_add_commutative(P_affine.0, P_affine.1, prev.0, prev.1);
                }
            }
        }
        let result = LookupTable(points);
        proof {
            // All 8 entries are valid, bounded, and correspond to scalar multiples
            assert forall|j: int| 0 <= j < 8 implies is_valid_projective_niels_point(
                #[trigger] result.0[j],
            ) by {}
            assert forall|j: int| 0 <= j < 8 implies {
                let entry = #[trigger] result.0[j];
                fe51_limbs_bounded(&entry.Y_plus_X, 54) && fe51_limbs_bounded(&entry.Y_minus_X, 54)
                    && fe51_limbs_bounded(&entry.Z, 54) && fe51_limbs_bounded(&entry.T2d, 54)
            } by {}
            assert forall|j: int| 0 <= j < 8 implies projective_niels_point_as_affine_edwards(
                #[trigger] result.0[j],
            ) == edwards_scalar_mul(P_affine, (j + 1) as nat) by {}
        }
        result
    }
}

impl<'a> From<&'a EdwardsPoint> for LookupTable<AffineNielsPoint> {
    /// Create a lookup table from an EdwardsPoint (affine version)
    /// Constructs [P, 2P, 3P, ..., Size*P]
    fn from(P: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_lookup_table_affine(result.0, *P, 8 as nat),
            lookup_table_affine_limbs_bounded(result.0),
            forall|j: int| 0 <= j < 8 ==> is_valid_affine_niels_point(#[trigger] result.0[j]),
    {
        /* ORIGINAL CODE: for generic $name, $size, and conv_range.

         let mut points = [P.as_affine_niels(); $size];
                // XXX batch inversion would be good if perf mattered here
                for j in $conv_range {
                    points[j + 1] = (P + &points[j]).as_extended().as_affine_niels()
                }
                $name(points)

        In our instantiation we have $name = LookupTable, $size = 8, and conv_range = 0..7.
        */
        proof {
            use_type_invariant(P);
            lemma_unfold_edwards(*P);
        }

        let ghost P_affine = edwards_point_as_affine(*P);
        let mut points = [P.as_affine_niels();8];
        proof {
            assert(affine_niels_point_as_affine_edwards(points[0]) == P_affine) by {
                lemma_affine_niels_affine_equals_edwards_affine(points[0], *P);
            }
            assert(edwards_scalar_mul(P_affine, 1) == P_affine) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
        }
        for j in 0..7
            invariant
                forall|k: int|
                    0 <= k <= j ==> fe51_limbs_bounded(&(#[trigger] points[k]).y_plus_x, 54)
                        && fe51_limbs_bounded(&points[k].y_minus_x, 54) && fe51_limbs_bounded(
                        &points[k].xy2d,
                        54,
                    ),
                forall|k: int| 0 <= k <= j ==> is_valid_affine_niels_point(#[trigger] points[k]),
                forall|k: int|
                    0 <= k <= j ==> affine_niels_point_as_affine_edwards(#[trigger] points[k])
                        == edwards_scalar_mul(P_affine, (k + 1) as nat),
                is_well_formed_edwards_point(*P),
                edwards_point_limbs_bounded(*P),
                is_valid_edwards_point(*P),
                P_affine == edwards_point_as_affine(*P),
        {
            // ORIGINAL CODE: points[j + 1] = (P + &points[j]).as_extended().as_affine_niels();
            proof {
                use_type_invariant(P);
                lemma_unfold_edwards(*P);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&P.Z, &P.Z, 52);
            }
            let sum = P + &points[j];
            let extended = sum.as_extended();
            points[j + 1] = extended.as_affine_niels();
            proof {
                assert(affine_niels_point_as_affine_edwards(points[(j + 1) as int])
                    == edwards_point_as_affine(extended)) by {
                    lemma_affine_niels_affine_equals_edwards_affine(
                        points[(j + 1) as int],
                        extended,
                    );
                }
                let prev = edwards_scalar_mul(P_affine, (j + 1) as nat);
                assert(edwards_scalar_mul(P_affine, (j + 2) as nat) == edwards_add(
                    prev.0,
                    prev.1,
                    P_affine.0,
                    P_affine.1,
                )) by {
                    lemma_edwards_scalar_mul_succ(P_affine, (j + 1) as nat);
                }
                assert(edwards_add(P_affine.0, P_affine.1, prev.0, prev.1) == edwards_add(
                    prev.0,
                    prev.1,
                    P_affine.0,
                    P_affine.1,
                )) by {
                    lemma_edwards_add_commutative(P_affine.0, P_affine.1, prev.0, prev.1);
                }
            }
        }
        let result = LookupTable(points);
        proof {
            assert forall|j: int| 0 <= j < 8 implies is_valid_affine_niels_point(
                #[trigger] result.0[j],
            ) by {}
            assert forall|j: int| 0 <= j < 8 implies {
                let entry = #[trigger] result.0[j];
                fe51_limbs_bounded(&entry.y_plus_x, 54) && fe51_limbs_bounded(&entry.y_minus_x, 54)
                    && fe51_limbs_bounded(&entry.xy2d, 54)
            } by {}
            assert forall|j: int| 0 <= j < 8 implies affine_niels_point_as_affine_edwards(
                #[trigger] result.0[j],
            ) == edwards_scalar_mul(P_affine, (j + 1) as nat) by {}
        }
        result
    }
}

} // verus!
#[cfg(feature = "zeroize")]
impl<T> Zeroize for LookupTable<T>
where
    T: Copy + Default + Zeroize,
{
    fn zeroize(&mut self) {
        self.0.iter_mut().zeroize();
    }
}

cfg_if! {
    if #[cfg(feature = "precomputed-tables")] {
        // For homogeneity with other radix sizes, alias to "LookupTableRadix16".
        pub(crate) type LookupTableRadix16<T> = LookupTable<T>;
    }
}

verus! {

/// Holds odd multiples 1A, 3A, ..., 15A of a point A.
/* VERIFICATION NOTE:
   - Changed from pub(crate) to pub to allow Verus verification
     of requires/ensures clauses that reference self.0.
   - Removed Clone from #[derive(Copy, Clone)] because Verus does not support
     autoderive Clone for arrays. Manual Clone impl provided outside verus! macro.

   ORIGINAL CODE:
   #[derive(Copy, Clone)]
   pub(crate) struct NafLookupTable5<T>(pub(crate) [T; 8]);
*/
#[derive(Copy)]
pub struct NafLookupTable5<T>(pub [T; 8]);

/* VERIFICATION NOTE: Replaced generic NafLookupTable5<T>::select with concrete implementations
   to allow type-specific specs.

   ORIGINAL CODE:
   impl<T: Copy> NafLookupTable5<T> {
       pub fn select(&self, x: usize) -> T {
           debug_assert_eq!(x & 1, 1);
           debug_assert!(x < 16);
           self.0[x / 2]
       }
   }
*/

/// Concrete select implementation for NafLookupTable5<ProjectiveNielsPoint>
impl NafLookupTable5<ProjectiveNielsPoint> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^4 \\), return \\(xA\\).
    /// Table stores [1A, 3A, 5A, 7A, 9A, 11A, 13A, 15A], so table[x/2] = x*A.
    pub fn select(&self, x: usize) -> (result: ProjectiveNielsPoint)
        requires
            x & 1 == 1,  // x is odd
            x < 16,  // x in {1, 3, 5, 7, 9, 11, 13, 15}
            naf_lookup_table5_projective_limbs_bounded(self.0),
            forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] self.0[j]),
        ensures
            result == self.0[(x / 2) as int],
            fe51_limbs_bounded(&result.Y_plus_X, 54),
            fe51_limbs_bounded(&result.Y_minus_X, 54),
            fe51_limbs_bounded(&result.Z, 54),
            fe51_limbs_bounded(&result.T2d, 54),
            is_valid_projective_niels_point(result),
    {
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert_eq!(x & 1, 1);
            debug_assert!(x < 16);
        }
        self.0[x / 2]
    }
}

/// Concrete select implementation for NafLookupTable5<AffineNielsPoint>
impl NafLookupTable5<AffineNielsPoint> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^4 \\), return \\(xA\\).
    /// Table stores [1A, 3A, 5A, 7A, 9A, 11A, 13A, 15A], so table[x/2] = x*A.
    pub fn select(&self, x: usize) -> (result: AffineNielsPoint)
        requires
            x & 1 == 1,  // x is odd
            x < 16,  // x in {1, 3, 5, 7, 9, 11, 13, 15}
            naf_lookup_table5_affine_limbs_bounded(self.0),
        ensures
            result == self.0[(x / 2) as int],
            fe51_limbs_bounded(&result.y_plus_x, 54),
            fe51_limbs_bounded(&result.y_minus_x, 54),
            fe51_limbs_bounded(&result.xy2d, 54),
    {
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert_eq!(x & 1, 1);
            debug_assert!(x < 16);
        }
        self.0[x / 2]
    }
}

} // verus!
// Manual Clone impl since derive(Clone) is not supported inside verus macro for arrays
impl<T: Copy> Clone for NafLookupTable5<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Debug> Debug for NafLookupTable5<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NafLookupTable5({:?})", self.0)
    }
}

verus! {

impl<'a> From<&'a EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint> {
    /// Create a NAF lookup table from an EdwardsPoint
    /// Constructs [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A] (odd multiples)
    fn from(A: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_naf_lookup_table5_projective(result.0, *A),
            naf_lookup_table5_projective_limbs_bounded(result.0),
            forall|j: int| 0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] result.0[j]),
    {
        proof {
            use_type_invariant(A);
            lemma_unfold_edwards(*A);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&A.Y, &A.X, 52);
        }

        let ghost A_affine = edwards_point_as_affine(*A);
        let mut Ai = [A.as_projective_niels();8];
        let A2 = A.double();
        proof {
            // Base case: Ai[0] = A corresponds to 1*A = (2*0+1)*A
            assert(projective_niels_point_as_affine_edwards(Ai[0]) == A_affine) by {
                lemma_projective_niels_affine_equals_edwards_affine(Ai[0], *A);
            }
            assert(edwards_scalar_mul(A_affine, 1) == A_affine) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
            // A2 affine = scalar_mul(A, 2)
            assert(edwards_scalar_mul(A_affine, 2) == edwards_double(A_affine.0, A_affine.1)) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
        }
        for i in 0..7
            invariant
        // Limb bounds for all entries built so far

                forall|k: int|
                    0 <= k <= i ==> fe51_limbs_bounded(&(#[trigger] Ai[k]).Y_plus_X, 54)
                        && fe51_limbs_bounded(&Ai[k].Y_minus_X, 54) && fe51_limbs_bounded(
                        &Ai[k].Z,
                        54,
                    ) && fe51_limbs_bounded(&Ai[k].T2d, 54),
                // Validity for all entries built so far
                forall|k: int| 0 <= k <= i ==> is_valid_projective_niels_point(#[trigger] Ai[k]),
                // Mathematical correspondence: entry[k] represents (2*k+1)*A
                forall|k: int|
                    0 <= k <= i ==> projective_niels_point_as_affine_edwards(#[trigger] Ai[k])
                        == edwards_scalar_mul(A_affine, (2 * k + 1) as nat),
                // A2 = double(A) and its affine
                is_valid_edwards_point(A2),
                edwards_point_as_affine(A2) == edwards_double(A_affine.0, A_affine.1),
                edwards_scalar_mul(A_affine, 2) == edwards_double(A_affine.0, A_affine.1),
                A_affine == edwards_point_as_affine(*A),
        {
            // ORIGINAL CODE: Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_projective_niels();
            proof {
                use_type_invariant(A2);
                lemma_unfold_edwards(A2);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Y, &A2.X, 52);
            }
            let sum = &A2 + &Ai[i];
            let extended = sum.as_extended();
            proof {
                use_type_invariant(extended);
                lemma_unfold_edwards(extended);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&extended.Y, &extended.X, 52);
            }
            Ai[i + 1] = extended.as_projective_niels();
            proof {
                // Prove correspondence for Ai[i+1]: represents (2*(i+1)+1)*A = (2*i+3)*A
                assert(projective_niels_point_as_affine_edwards(Ai[(i + 1) as int])
                    == edwards_point_as_affine(extended)) by {
                    lemma_projective_niels_affine_equals_edwards_affine(
                        Ai[(i + 1) as int],
                        extended,
                    );
                }
                // add(scalar_mul(A, 2), scalar_mul(A, 2*i+1)) == scalar_mul(A, 2*i+3)
                assert(edwards_scalar_mul(A_affine, (2 * i + 3) as nat) == {
                    let p2 = edwards_scalar_mul(A_affine, 2);
                    let pk = edwards_scalar_mul(A_affine, (2 * i + 1) as nat);
                    edwards_add(p2.0, p2.1, pk.0, pk.1)
                }) by {
                    lemma_edwards_scalar_mul_additive(A_affine, 2, (2 * i + 1) as nat);
                }
            }
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        let result = NafLookupTable5(Ai);
        proof {
            assert forall|j: int| 0 <= j < 8 implies projective_niels_point_as_affine_edwards(
                #[trigger] result.0[j],
            ) == edwards_scalar_mul(A_affine, (2 * j + 1) as nat) by {}
            assert forall|j: int| 0 <= j < 8 implies {
                let entry = #[trigger] result.0[j];
                fe51_limbs_bounded(&entry.Y_plus_X, 54) && fe51_limbs_bounded(&entry.Y_minus_X, 54)
                    && fe51_limbs_bounded(&entry.Z, 54) && fe51_limbs_bounded(&entry.T2d, 54)
            } by {}
            assert forall|j: int| 0 <= j < 8 implies is_valid_projective_niels_point(
                #[trigger] result.0[j],
            ) by {}
        }
        result
    }
}

impl<'a> From<&'a EdwardsPoint> for NafLookupTable5<AffineNielsPoint> {
    /// Create a NAF lookup table from an EdwardsPoint
    /// Constructs [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A] (odd multiples)
    fn from(A: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_naf_lookup_table5_affine(result.0, *A),
            naf_lookup_table5_affine_limbs_bounded(result.0),
    {
        proof {
            use_type_invariant(A);
            lemma_unfold_edwards(*A);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&A.Y, &A.X, 52);
        }

        let ghost A_affine = edwards_point_as_affine(*A);
        let mut Ai = [A.as_affine_niels();8];
        let A2 = A.double();
        proof {
            assert(affine_niels_point_as_affine_edwards(Ai[0]) == A_affine) by {
                lemma_affine_niels_affine_equals_edwards_affine(Ai[0], *A);
            }
            assert(edwards_scalar_mul(A_affine, 1) == A_affine) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
            assert(edwards_scalar_mul(A_affine, 2) == edwards_double(A_affine.0, A_affine.1)) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
        }
        for i in 0..7
            invariant
                forall|k: int|
                    0 <= k <= i ==> fe51_limbs_bounded(&(#[trigger] Ai[k]).y_plus_x, 54)
                        && fe51_limbs_bounded(&Ai[k].y_minus_x, 54) && fe51_limbs_bounded(
                        &Ai[k].xy2d,
                        54,
                    ),
                forall|k: int| 0 <= k <= i ==> is_valid_affine_niels_point(#[trigger] Ai[k]),
                forall|k: int|
                    0 <= k <= i ==> affine_niels_point_as_affine_edwards(#[trigger] Ai[k])
                        == edwards_scalar_mul(A_affine, (2 * k + 1) as nat),
                is_valid_edwards_point(A2),
                edwards_point_as_affine(A2) == edwards_double(A_affine.0, A_affine.1),
                edwards_scalar_mul(A_affine, 2) == edwards_double(A_affine.0, A_affine.1),
                A_affine == edwards_point_as_affine(*A),
        {
            // ORIGINAL CODE: Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_affine_niels();
            proof {
                use_type_invariant(A2);
                lemma_unfold_edwards(A2);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Y, &A2.X, 52);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Z, &A2.Z, 52);
            }
            let sum = &A2 + &Ai[i];
            let extended = sum.as_extended();
            Ai[i + 1] = extended.as_affine_niels();
            proof {
                assert(affine_niels_point_as_affine_edwards(Ai[(i + 1) as int])
                    == edwards_point_as_affine(extended)) by {
                    lemma_affine_niels_affine_equals_edwards_affine(Ai[(i + 1) as int], extended);
                }
                assert(edwards_scalar_mul(A_affine, (2 * i + 3) as nat) == {
                    let p2 = edwards_scalar_mul(A_affine, 2);
                    let pk = edwards_scalar_mul(A_affine, (2 * i + 1) as nat);
                    edwards_add(p2.0, p2.1, pk.0, pk.1)
                }) by {
                    lemma_edwards_scalar_mul_additive(A_affine, 2, (2 * i + 1) as nat);
                }
            }
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        let result = NafLookupTable5(Ai);
        proof {
            assert forall|j: int| 0 <= j < 8 implies affine_niels_point_as_affine_edwards(
                #[trigger] result.0[j],
            ) == edwards_scalar_mul(A_affine, (2 * j + 1) as nat) by {}
            assert forall|j: int| 0 <= j < 8 implies {
                let entry = #[trigger] result.0[j];
                fe51_limbs_bounded(&entry.y_plus_x, 54) && fe51_limbs_bounded(&entry.y_minus_x, 54)
                    && fe51_limbs_bounded(&entry.xy2d, 54)
            } by {}
        }
        result
    }
}

} // verus!
verus! {

/// Holds stuff up to 8. The only time we use tables this big is for precomputed basepoint tables
/// and multiscalar multiplication (which requires alloc).
/* VERIFICATION NOTE:
   - Changed from pub(crate) to pub to allow Verus verification
     of requires/ensures clauses that reference self.0.
   - Removed Clone from #[derive(Copy, Clone)] because Verus does not support
     autoderive Clone for arrays. Manual Clone impl provided outside verus! macro.

   ORIGINAL CODE:
   #[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
   #[derive(Copy, Clone)]
   pub(crate) struct NafLookupTable8<T>(pub(crate) [T; 64]);
*/
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
#[derive(Copy)]
pub struct NafLookupTable8<T>(pub [T; 64]);

/* VERIFICATION NOTE: Replaced generic NafLookupTable8<T>::select with concrete implementations
   to allow type-specific specs.

   ORIGINAL CODE:
   impl<T: Copy> NafLookupTable8<T> {
       pub fn select(&self, x: usize) -> T {
           debug_assert_eq!(x & 1, 1);
           debug_assert!(x < 128);
           self.0[x / 2]
       }
   }
*/

/// Concrete select implementation for NafLookupTable8<ProjectiveNielsPoint>
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl NafLookupTable8<ProjectiveNielsPoint> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^7 \\), return \\(xA\\).
    /// Table stores [1A, 3A, 5A, ..., 127A], so table[x/2] = x*A.
    pub fn select(&self, x: usize) -> (result: ProjectiveNielsPoint)
        requires
            x & 1 == 1,  // x is odd
            x < 128,  // x in {1, 3, 5, ..., 127}
            naf_lookup_table8_projective_limbs_bounded(self.0),
        ensures
            result == self.0[(x / 2) as int],
            fe51_limbs_bounded(&result.Y_plus_X, 54),
            fe51_limbs_bounded(&result.Y_minus_X, 54),
            fe51_limbs_bounded(&result.Z, 54),
            fe51_limbs_bounded(&result.T2d, 54),
    {
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert_eq!(x & 1, 1);
            debug_assert!(x < 128);
        }
        self.0[x / 2]
    }
}

/// Concrete select implementation for NafLookupTable8<AffineNielsPoint>
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl NafLookupTable8<AffineNielsPoint> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^7 \\), return \\(xA\\).
    /// Table stores [1A, 3A, 5A, ..., 127A], so table[x/2] = x*A.
    pub fn select(&self, x: usize) -> (result: AffineNielsPoint)
        requires
            x & 1 == 1,  // x is odd
            x < 128,  // x in {1, 3, 5, ..., 127}
            naf_lookup_table8_affine_limbs_bounded(self.0),
            forall|j: int| 0 <= j < 64 ==> is_valid_affine_niels_point(#[trigger] self.0[j]),
        ensures
            result == self.0[(x / 2) as int],
            fe51_limbs_bounded(&result.y_plus_x, 54),
            fe51_limbs_bounded(&result.y_minus_x, 54),
            fe51_limbs_bounded(&result.xy2d, 54),
            is_valid_affine_niels_point(result),
    {
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert_eq!(x & 1, 1);
            debug_assert!(x < 128);
        }
        self.0[x / 2]
    }
}

} // verus!
// Manual Clone impl since derive(Clone) is not supported inside verus macro for arrays
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<T: Copy> Clone for NafLookupTable8<T> {
    fn clone(&self) -> Self {
        *self
    }
}

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<T: Debug> Debug for NafLookupTable8<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "NafLookupTable8([")?;
        for i in 0..64 {
            writeln!(f, "\t{:?},", &self.0[i])?;
        }
        write!(f, "])")
    }
}

verus! {

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<'a> From<&'a EdwardsPoint> for NafLookupTable8<ProjectiveNielsPoint> {
    /// Create a NAF lookup table from an EdwardsPoint
    /// Constructs [A, 3A, 5A, 7A, ..., 127A] (odd multiples)
    fn from(A: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_naf_lookup_table8_projective(result.0, *A),
            naf_lookup_table8_projective_limbs_bounded(result.0),
    {
        proof {
            use_type_invariant(A);
            lemma_unfold_edwards(*A);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&A.Y, &A.X, 52);
        }

        let ghost A_affine = edwards_point_as_affine(*A);
        let mut Ai = [A.as_projective_niels();64];
        let A2 = A.double();
        proof {
            assert(projective_niels_point_as_affine_edwards(Ai[0]) == A_affine) by {
                lemma_projective_niels_affine_equals_edwards_affine(Ai[0], *A);
            }
            assert(edwards_scalar_mul(A_affine, 1) == A_affine) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
            assert(edwards_scalar_mul(A_affine, 2) == edwards_double(A_affine.0, A_affine.1)) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
        }
        for i in 0..63
            invariant
                forall|k: int|
                    0 <= k <= i ==> fe51_limbs_bounded(&(#[trigger] Ai[k]).Y_plus_X, 54)
                        && fe51_limbs_bounded(&Ai[k].Y_minus_X, 54) && fe51_limbs_bounded(
                        &Ai[k].Z,
                        54,
                    ) && fe51_limbs_bounded(&Ai[k].T2d, 54),
                forall|k: int| 0 <= k <= i ==> is_valid_projective_niels_point(#[trigger] Ai[k]),
                forall|k: int|
                    0 <= k <= i ==> projective_niels_point_as_affine_edwards(#[trigger] Ai[k])
                        == edwards_scalar_mul(A_affine, (2 * k + 1) as nat),
                is_valid_edwards_point(A2),
                edwards_point_as_affine(A2) == edwards_double(A_affine.0, A_affine.1),
                edwards_scalar_mul(A_affine, 2) == edwards_double(A_affine.0, A_affine.1),
                A_affine == edwards_point_as_affine(*A),
        {
            // ORIGINAL CODE: Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_projective_niels();
            proof {
                use_type_invariant(A2);
                assert(is_well_formed_edwards_point(A2)) by {
                    lemma_unfold_edwards(A2);
                }
                assert(sum_of_limbs_bounded(&A2.X, &A2.Y, u64::MAX)) by {
                    lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Y, &A2.X, 52);
                }
            }
            let sum = &A2 + &Ai[i];
            let extended = sum.as_extended();
            proof {
                use_type_invariant(extended);
                assert(is_well_formed_edwards_point(extended)) by {
                    lemma_unfold_edwards(extended);
                }
                assert(sum_of_limbs_bounded(&extended.X, &extended.Y, u64::MAX)) by {
                    lemma_sum_of_limbs_bounded_from_fe51_bounded(&extended.Y, &extended.X, 52);
                }
            }
            Ai[i + 1] = extended.as_projective_niels();
            proof {
                assert(projective_niels_point_as_affine_edwards(Ai[(i + 1) as int])
                    == edwards_point_as_affine(extended)) by {
                    lemma_projective_niels_affine_equals_edwards_affine(
                        Ai[(i + 1) as int],
                        extended,
                    );
                }
                assert(edwards_scalar_mul(A_affine, (2 * i + 3) as nat) == {
                    let p2 = edwards_scalar_mul(A_affine, 2);
                    let pk = edwards_scalar_mul(A_affine, (2 * i + 1) as nat);
                    edwards_add(p2.0, p2.1, pk.0, pk.1)
                }) by {
                    lemma_edwards_scalar_mul_additive(A_affine, 2, (2 * i + 1) as nat);
                }
            }
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
        let result = NafLookupTable8(Ai);
        proof {
            assert forall|j: int| 0 <= j < 64 implies projective_niels_point_as_affine_edwards(
                #[trigger] result.0[j],
            ) == edwards_scalar_mul(A_affine, (2 * j + 1) as nat) by {}
            assert forall|j: int| 0 <= j < 64 implies {
                let entry = #[trigger] result.0[j];
                fe51_limbs_bounded(&entry.Y_plus_X, 54) && fe51_limbs_bounded(&entry.Y_minus_X, 54)
                    && fe51_limbs_bounded(&entry.Z, 54) && fe51_limbs_bounded(&entry.T2d, 54)
            } by {}
        }
        result
    }
}

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<'a> From<&'a EdwardsPoint> for NafLookupTable8<AffineNielsPoint> {
    /// Create a NAF lookup table from an EdwardsPoint
    /// Constructs [A, 3A, 5A, 7A, ..., 127A] (odd multiples)
    fn from(A: &'a EdwardsPoint) -> (result: Self)
        ensures
            is_valid_naf_lookup_table8_affine(result.0, *A),
            naf_lookup_table8_affine_limbs_bounded(result.0),
    {
        proof {
            use_type_invariant(A);
            lemma_unfold_edwards(*A);
            lemma_sum_of_limbs_bounded_from_fe51_bounded(&A.Y, &A.X, 52);
        }

        let ghost A_affine = edwards_point_as_affine(*A);
        let mut Ai = [A.as_affine_niels();64];
        let A2 = A.double();
        proof {
            assert(affine_niels_point_as_affine_edwards(Ai[0]) == A_affine) by {
                lemma_affine_niels_affine_equals_edwards_affine(Ai[0], *A);
            }
            assert(edwards_scalar_mul(A_affine, 1) == A_affine) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
            assert(edwards_scalar_mul(A_affine, 2) == edwards_double(A_affine.0, A_affine.1)) by {
                reveal_with_fuel(edwards_scalar_mul, 2);
            }
        }
        for i in 0..63
            invariant
                forall|k: int|
                    0 <= k <= i ==> fe51_limbs_bounded(&(#[trigger] Ai[k]).y_plus_x, 54)
                        && fe51_limbs_bounded(&Ai[k].y_minus_x, 54) && fe51_limbs_bounded(
                        &Ai[k].xy2d,
                        54,
                    ),
                forall|k: int| 0 <= k <= i ==> is_valid_affine_niels_point(#[trigger] Ai[k]),
                forall|k: int|
                    0 <= k <= i ==> affine_niels_point_as_affine_edwards(#[trigger] Ai[k])
                        == edwards_scalar_mul(A_affine, (2 * k + 1) as nat),
                is_valid_edwards_point(A2),
                edwards_point_as_affine(A2) == edwards_double(A_affine.0, A_affine.1),
                edwards_scalar_mul(A_affine, 2) == edwards_double(A_affine.0, A_affine.1),
                A_affine == edwards_point_as_affine(*A),
        {
            // ORIGINAL CODE: Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_affine_niels();
            proof {
                use_type_invariant(A2);
                lemma_unfold_edwards(A2);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Y, &A2.X, 52);
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&A2.Z, &A2.Z, 52);
            }
            let sum = &A2 + &Ai[i];
            let extended = sum.as_extended();
            Ai[i + 1] = extended.as_affine_niels();
            proof {
                assert(affine_niels_point_as_affine_edwards(Ai[(i + 1) as int])
                    == edwards_point_as_affine(extended)) by {
                    lemma_affine_niels_affine_equals_edwards_affine(Ai[(i + 1) as int], extended);
                }
                assert(edwards_scalar_mul(A_affine, (2 * i + 3) as nat) == {
                    let p2 = edwards_scalar_mul(A_affine, 2);
                    let pk = edwards_scalar_mul(A_affine, (2 * i + 1) as nat);
                    edwards_add(p2.0, p2.1, pk.0, pk.1)
                }) by {
                    lemma_edwards_scalar_mul_additive(A_affine, 2, (2 * i + 1) as nat);
                }
            }
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
        let result = NafLookupTable8(Ai);
        proof {
            assert forall|j: int| 0 <= j < 64 implies affine_niels_point_as_affine_edwards(
                #[trigger] result.0[j],
            ) == edwards_scalar_mul(A_affine, (2 * j + 1) as nat) by {}
            assert forall|j: int| 0 <= j < 64 implies {
                let entry = #[trigger] result.0[j];
                fe51_limbs_bounded(&entry.y_plus_x, 54) && fe51_limbs_bounded(&entry.y_minus_x, 54)
                    && fe51_limbs_bounded(&entry.xy2d, 54)
            } by {}
        }
        result
    }
}

} // verus!
