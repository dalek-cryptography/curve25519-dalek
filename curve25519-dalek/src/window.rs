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
    conditional_assign_generic, conditional_negate_generic, ct_eq_u16,
};
use crate::edwards::EdwardsPoint;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::edwards_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::field_specs::*;
use vstd::prelude::*;

/* VERIFICATION NOTE: Removed unused impl_lookup_table! macro since LookupTable
(radix-16) was manually expanded. */

verus! {

/// Spec: Check if a lookup table contains [P, 2P, 3P, ..., size*P] in ProjectiveNiels form
pub open spec fn is_valid_lookup_table_projective<const N: usize>(
    table: [ProjectiveNielsPoint; N],
    P: EdwardsPoint,
    size: nat,
) -> bool {
    &&& table.len() == size
    &&& forall|j: int|
        0 <= j < size ==> projective_niels_point_as_affine_edwards(#[trigger] table[j])
            == edwards_scalar_mul(edwards_point_as_affine(P), (j + 1) as nat)
}

/// Spec: All entries in a ProjectiveNiels lookup table have bounded limbs
pub open spec fn lookup_table_projective_limbs_bounded<const N: usize>(
    table: [ProjectiveNielsPoint; N],
) -> bool {
    forall|j: int|
        0 <= j < table.len() ==> {
            let entry = #[trigger] table[j];
            fe51_limbs_bounded(&entry.Y_plus_X, 54) && fe51_limbs_bounded(&entry.Y_minus_X, 54)
                && fe51_limbs_bounded(&entry.Z, 54) && fe51_limbs_bounded(&entry.T2d, 54)
        }
}

/// Spec: Check if a lookup table contains [P, 2P, 3P, ..., size*P] in AffineNiels form
/// where P is given as affine coordinates (nat, nat).
pub open spec fn is_valid_lookup_table_affine_coords<const N: usize>(
    table: [AffineNielsPoint; N],
    basepoint: (nat, nat),
    size: nat,
) -> bool {
    &&& table.len() == size
    &&& forall|j: int|
        #![trigger table[j]]
        0 <= j < size ==> affine_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (j + 1) as nat,
        )
}

/// Spec: Check if a lookup table contains [P, 2P, 3P, ..., size*P] in AffineNiels form
/// Wrapper that takes an EdwardsPoint and extracts affine coords.
pub open spec fn is_valid_lookup_table_affine<const N: usize>(
    table: [AffineNielsPoint; N],
    P: EdwardsPoint,
    size: nat,
) -> bool {
    is_valid_lookup_table_affine_coords(table, edwards_point_as_affine(P), size)
}

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
        ensures
    // Formal specification for all cases:

            (x > 0 ==> result == self.0[(x - 1) as int]),
            (x == 0 ==> result == identity_affine_niels()),
            (x < 0 ==> result == negate_affine_niels(self.0[((-x) - 1) as int])),
    {
        // Debug assertions from original macro - ignored by Verus
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert!(x >= -8);
            debug_assert!(x <= 8);
        }

        assume(false);

        // Compute xabs = |x|
        let xmask = x as i16 >> 7;
        let xabs = (x as i16 + xmask) ^ xmask;

        // Set t = 0 * P = identity
        let mut t = AffineNielsPoint::identity();
        for j in 1..9 {
            // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
            /* ORIGINAL CODE: let c = (xabs as u16).ct_eq(&(j as u16)); */
            let c = ct_eq_u16(&(xabs as u16), &(j as u16));
            /* ORIGINAL CODE: t.conditional_assign(&self.0[j - 1], c); */
            conditional_assign_generic(&mut t, &self.0[j - 1], c);
        }
        // Now t == |x| * P.

        let neg_mask = Choice::from((xmask & 1) as u8);
        /* ORIGINAL CODE: t.conditional_negate(neg_mask); */
        conditional_negate_generic(&mut t, neg_mask);
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

        assume(false);

        // Compute xabs = |x|
        let xmask = x as i16 >> 7;
        let xabs = (x as i16 + xmask) ^ xmask;

        // Set t = 0 * P = identity
        let mut t = ProjectiveNielsPoint::identity();
        for j in 1..9 {
            // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
            /* ORIGINAL CODE: let c = (xabs as u16).ct_eq(&(j as u16)); */
            let c = ct_eq_u16(&(xabs as u16), &(j as u16));
            /* ORIGINAL CODE: t.conditional_assign(&self.0[j - 1], c); */
            conditional_assign_generic(&mut t, &self.0[j - 1], c);
        }
        // Now t == |x| * P.

        let neg_mask = Choice::from((xmask & 1) as u8);
        /* ORIGINAL CODE: t.conditional_negate(neg_mask); */
        conditional_negate_generic(&mut t, neg_mask);
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

/// Spec for From<&EdwardsPoint> conversion for ProjectiveNiels lookup table
#[cfg(verus_keep_ghost)]
impl<'a> vstd::std_specs::convert::FromSpecImpl<&'a EdwardsPoint> for LookupTable<
    ProjectiveNielsPoint,
> {
    //impl<'a> vstd::std_specs::convert::FromSpecImpl<&'a EdwardsPoint> for LookupTable<ProjectiveNielsPoint> {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    /* VERIFICTATION NOTE: this not supported in Verus

    open spec fn from_req(P: &'a EdwardsPoint) -> bool {
        // Preconditions needed for table construction
        fe51_limbs_bounded(&P.X, 54) && fe51_limbs_bounded(&P.Y, 54) && fe51_limbs_bounded(&P.Z, 54)
            && fe51_limbs_bounded(&P.T, 54)
    }
*/
    open spec fn from_spec(P: &'a EdwardsPoint) -> Self {
        arbitrary()  // conditions specified in the ensures clause of the from function

    }
}

impl<'a> From<&'a EdwardsPoint> for LookupTable<ProjectiveNielsPoint> {
    /// Create a lookup table from an EdwardsPoint
    /// Constructs [P, 2P, 3P, ..., Size*P]
    fn from(P: &'a EdwardsPoint) -> (result:
        Self)/*
    VERIFICATION NOTE: similar to Add and Mul traits,
    we want from_req from above to apply here, but Verus does not yet support this
    */

        ensures
            is_valid_lookup_table_projective(result.0, *P, 8 as nat),
            // All table entries have bounded limbs for subsequent arithmetic
            lookup_table_projective_limbs_bounded(result.0),
    {
        /* ORIGINAL CODE: for generic $name, $size, and conv_range.

         let mut points = [P.as_projective_niels(); $size];
                for j in $conv_range {
                    points[j + 1] = (P + &points[j]).as_extended().as_projective_niels();
                }
                $name(points)

        In our instantiation we have $name = LookupTable, $size = 8, and conv_range = 0..7.
        */
        // Assume preconditions from FromSpecImpl::from_spec_req
        proof {
            assume(edwards_point_limbs_bounded(*P));
            assume(edwards_point_sum_bounded(*P));
        }

        let mut points = [P.as_projective_niels();8];
        for j in 0..7 {
            // ORIGINAL CODE: points[j + 1] = (P + &points[j]).as_extended().as_projective_niels();
            // NOTE: We must unroll this into intermediate variables (sum, extended) to add
            // assumes about their limb bounds.
            // We cannot directly put them in proof blocks because they are exec variables.
            proof {
                // Preconditions for P + &points[j]
                assume(is_well_formed_edwards_point(*P));
                assume(fe51_limbs_bounded(&&points[j as int].Y_plus_X, 54));
                assume(fe51_limbs_bounded(&&points[j as int].Y_minus_X, 54));
                assume(fe51_limbs_bounded(&&points[j as int].Z, 54));
                assume(fe51_limbs_bounded(&&points[j as int].T2d, 54));
            }
            let sum = P + &points[j];
            proof {
                // Preconditions for sum.as_extended()
                assume(fe51_limbs_bounded(&sum.X, 54));
                assume(fe51_limbs_bounded(&sum.Y, 54));
                assume(fe51_limbs_bounded(&sum.Z, 54));
                assume(fe51_limbs_bounded(&sum.T, 54));
            }
            let extended = sum.as_extended();
            proof {
                // Preconditions for extended.as_projective_niels()
                assume(edwards_point_limbs_bounded(extended));
                assume(edwards_point_sum_bounded(extended));
            }
            points[j + 1] = extended.as_projective_niels();
        }
        let result = LookupTable(points);
        proof {
            assume(is_valid_lookup_table_projective(result.0, *P, 8 as nat));
            assume(lookup_table_projective_limbs_bounded(result.0));
        }
        result
    }
}

/// Spec for From<&EdwardsPoint> conversion for AffineNiels lookup table
#[cfg(verus_keep_ghost)]
impl<'a> vstd::std_specs::convert::FromSpecImpl<&'a EdwardsPoint> for LookupTable<
    AffineNielsPoint,
> {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    /* VERIFICTATION NOTE: this not supported in Verus
    open spec fn from_req(P: &'a EdwardsPoint) -> bool {
        // Preconditions needed for table construction
        fe51_limbs_bounded(&P.X, 54) && fe51_limbs_bounded(&P.Y, 54) && fe51_limbs_bounded(&P.Z, 54)
            && fe51_limbs_bounded(&P.T, 54)
    }
*/
    open spec fn from_spec(P: &'a EdwardsPoint) -> Self {
        arbitrary()  // conditions specified in the ensures clause of the from function

    }
}

impl<'a> From<&'a EdwardsPoint> for LookupTable<AffineNielsPoint> {
    /// Create a lookup table from an EdwardsPoint (affine version)
    /// Constructs [P, 2P, 3P, ..., Size*P]
    fn from(P: &'a EdwardsPoint) -> (result:
        Self)/*
    VERIFICATION NOTE: similar to Add and Mul traits,
    we want from_req from above to apply here, but Verus does not yet support this
    */

        ensures
            is_valid_lookup_table_affine(result.0, *P, 8 as nat),
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
        // Assume preconditions from FromSpecImpl::from_spec_req
        proof {
            assume(edwards_point_limbs_bounded(*P));
        }

        let mut points = [P.as_affine_niels();8];
        // XXX batch inversion would be good if perf mattered here
        for j in 0..7 {
            // ORIGINAL CODE:
            // points[j + 1] = (P + &points[j]).as_extended().as_affine_niels()
            // For Verus: unroll to assume preconditions for intermediate operations
            proof {
                // Preconditions for P (left-hand side of addition)
                assume(is_well_formed_edwards_point(*P));
                assume(sum_of_limbs_bounded(&P.Z, &P.Z, u64::MAX));  // for Z2 = &P.Z + &P.Z in add
                // Preconditions for &points[j] (right-hand side - AffineNielsPoint)
                assume(fe51_limbs_bounded(&&points[j as int].y_plus_x, 54));
                assume(fe51_limbs_bounded(&&points[j as int].y_minus_x, 54));
                assume(fe51_limbs_bounded(&&points[j as int].xy2d, 54));
            }
            let sum = P + &points[j];
            proof {
                // Preconditions for sum.as_extended()
                assume(fe51_limbs_bounded(&sum.X, 54));
                assume(fe51_limbs_bounded(&sum.Y, 54));
                assume(fe51_limbs_bounded(&sum.Z, 54));
                assume(fe51_limbs_bounded(&sum.T, 54));
            }
            let extended = sum.as_extended();
            proof {
                // Preconditions for extended.as_affine_niels()
                assume(edwards_point_limbs_bounded(extended));
            }
            points[j + 1] = extended.as_affine_niels()
        }
        let result = LookupTable(points);
        proof {
            assume(is_valid_lookup_table_affine(result.0, *P, 8 as nat));
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

/// Holds odd multiples 1A, 3A, ..., 15A of a point A.
#[derive(Copy, Clone)]
pub(crate) struct NafLookupTable5<T>(pub(crate) [T; 8]);

impl<T: Copy> NafLookupTable5<T> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^4 \\), return \\(xA\\).
    pub fn select(&self, x: usize) -> T {
        debug_assert_eq!(x & 1, 1);
        debug_assert!(x < 16);

        self.0[x / 2]
    }
}

impl<T: Debug> Debug for NafLookupTable5<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NafLookupTable5({:?})", self.0)
    }
}

impl<'a> From<&'a EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.as_projective_niels(); 8];
        let A2 = A.double();
        for i in 0..7 {
            Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_projective_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        NafLookupTable5(Ai)
    }
}

impl<'a> From<&'a EdwardsPoint> for NafLookupTable5<AffineNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.as_affine_niels(); 8];
        let A2 = A.double();
        for i in 0..7 {
            Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_affine_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        NafLookupTable5(Ai)
    }
}

/// Holds stuff up to 8. The only time we use tables this big is for precomputed basepoint tables
/// and multiscalar multiplication (which requires alloc).
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
#[derive(Copy, Clone)]
pub(crate) struct NafLookupTable8<T>(pub(crate) [T; 64]);

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<T: Copy> NafLookupTable8<T> {
    pub fn select(&self, x: usize) -> T {
        debug_assert_eq!(x & 1, 1);
        debug_assert!(x < 128);

        self.0[x / 2]
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

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<'a> From<&'a EdwardsPoint> for NafLookupTable8<ProjectiveNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.as_projective_niels(); 64];
        let A2 = A.double();
        for i in 0..63 {
            Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_projective_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
        NafLookupTable8(Ai)
    }
}

#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
impl<'a> From<&'a EdwardsPoint> for NafLookupTable8<AffineNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.as_affine_niels(); 64];
        let A2 = A.double();
        for i in 0..63 {
            Ai[i + 1] = (&A2 + &Ai[i]).as_extended().as_affine_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A, ..., 127A]
        NafLookupTable8(Ai)
    }
}
