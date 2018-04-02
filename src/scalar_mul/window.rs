// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Code for fixed- and sliding-window functionality

#![allow(non_snake_case)]

use core::fmt::Debug;

use subtle::ConditionallyNegatable;
use subtle::ConditionallyAssignable;
use subtle::ConstantTimeEq;
use subtle::Choice;

use traits::Identity;

use edwards::EdwardsPoint;
use curve_models::ProjectiveNielsPoint;
use curve_models::AffineNielsPoint;

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
/// XXX make this generic with respect to table size
#[derive(Copy, Clone)]
pub struct LookupTable<T>(pub(crate) [T; 8]);

use clear_on_drop::clear::ZeroSafe;

/// This type isn't actually zeroable (all zero bytes are not valid
/// points), but we want to be able to use `clear_on_drop` to erase slices
/// of `LookupTable`.
///
/// Since the `ZeroSafe` trait is only used by `clear_on_drop`, the only
/// situation where this would be a problem is if code attempted to use
/// a `ClearOnDrop` to erase a `LookupTable` and then used the table
/// afterwards.
///
/// Normally this is not a problem, since the table's storage is usually
/// dropped too.
///
/// XXX is this a good compromise?
unsafe impl<T> ZeroSafe for LookupTable<T> {}

impl<T> LookupTable<T>
where
    T: Identity + ConditionallyAssignable + ConditionallyNegatable,
{
    /// Given \\(-8 \leq x \leq 8\\), return \\(xP\\) in constant time.
    pub fn select(&self, x: i8) -> T {
        debug_assert!(x >= -8);
        debug_assert!(x <= 8);

        // Compute xabs = |x|
        let xmask = x >> 7;
        let xabs = (x + xmask) ^ xmask;

        // Set t = 0 * P = identity
        let mut t = T::identity();
        for j in 1..9 {
            // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
            let c = (xabs as u8).ct_eq(&(j as u8));
            t.conditional_assign(&self.0[j - 1], c);
        }
        // Now t == |x| * P.

        let neg_mask = Choice::from((xmask & 1) as u8);
        t.conditional_negate(neg_mask);
        // Now t == x * P.

        t
    }
}

impl<T: Copy + Default> Default for LookupTable<T> {
    fn default() -> LookupTable<T> {
        LookupTable([T::default(); 8])
    }
}

impl<T: Debug> Debug for LookupTable<T> {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "LookupTable({:?})", self.0)
    }
}

impl<'a> From<&'a EdwardsPoint> for LookupTable<ProjectiveNielsPoint> {
    fn from(P: &'a EdwardsPoint) -> Self {
        let mut points = [P.to_projective_niels(); 8];
        for j in 0..7 {
            points[j + 1] = (P + &points[j]).to_extended().to_projective_niels();
        }
        LookupTable(points)
    }
}

impl<'a> From<&'a EdwardsPoint> for LookupTable<AffineNielsPoint> {
    fn from(P: &'a EdwardsPoint) -> Self {
        let mut points = [P.to_affine_niels(); 8];
        // XXX batch inversion would be good if perf mattered here
        for j in 0..7 {
            points[j + 1] = (P + &points[j]).to_extended().to_affine_niels()
        }
        LookupTable(points)
    }
}

/// Holds odd multiples 1A, 3A, ..., 15A of a point A.
#[derive(Copy, Clone)]
pub(crate) struct OddLookupTable<T>(pub(crate) [T; 8]);

impl<T: Copy> OddLookupTable<T> {
    /// Given public, odd \\( x \\) with \\( 0 < x < 2^4 \\), return \\(xA\\).
    pub fn select(&self, x: usize) -> T {
        debug_assert_eq!(x & 1, 1);
        debug_assert!(x < 16);

        self.0[x / 2]
    }
}

impl<T: Debug> Debug for OddLookupTable<T> {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "OddLookupTable({:?})", self.0)
    }
}

impl<'a> From<&'a EdwardsPoint> for OddLookupTable<ProjectiveNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.to_projective_niels(); 8];
        let A2 = A.double();
        for i in 0..7 {
            Ai[i + 1] = (&A2 + &Ai[i]).to_extended().to_projective_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        OddLookupTable(Ai)
    }
}

impl<'a> From<&'a EdwardsPoint> for OddLookupTable<AffineNielsPoint> {
    fn from(A: &'a EdwardsPoint) -> Self {
        let mut Ai = [A.to_affine_niels(); 8];
        let A2 = A.double();
        for i in 0..7 {
            Ai[i + 1] = (&A2 + &Ai[i]).to_extended().to_affine_niels();
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        OddLookupTable(Ai)
    }
}
