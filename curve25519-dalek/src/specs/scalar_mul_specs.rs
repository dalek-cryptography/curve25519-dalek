//! Verus specifications for scalar multiplication operations.
//!
//! Contains spec functions for reasoning about iterators and sequences
//! used in multiscalar multiplication algorithms.
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use core::borrow::Borrow;

use vstd::prelude::*;

#[allow(unused_imports)]
use crate::edwards::EdwardsPoint;
#[allow(unused_imports)]
use crate::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::{
    edwards_add, edwards_point_as_affine, edwards_scalar_mul, is_well_formed_edwards_point,
};
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::spec_scalar;

verus! {

/*
 * Iterator-to-sequence abstraction for Verus
 * ==========================================
 *
 * Verus cannot reason about Rust iterators directly. We introduce uninterpreted
 * spec functions that map iterators to Seq types representing their contents:
 *
 *   spec_scalars_from_iter         -> Seq<Scalar>
 *   spec_optional_points_from_iter -> Seq<Option<EdwardsPoint>>
 *   spec_points_from_iter          -> Seq<EdwardsPoint>
 *
 * Verus can reason about Seq (indexing, length, etc.), so requires/ensures
 * clauses use these sequences to express properties about scalars and points contained in the iterator.
 *
 * To work with iterator data in verified code, we need to collect elements into
 * a Vec. The collect_*_from_iter functions do this, consuming the iterator and
 * returning a Vec. They are marked external_body (unverified) with assumed
 * postconditions linking the Vec to the spec sequence:
 *
 *   ensures result@ == spec_*_from_iter(iter)
 *
 * This links the Seq view of the Vec (result@) to the abstract spec sequence,
 * allowing verified code to reason about the concrete Vec data.
 */
// ============================================================================
/// Spec function to convert an iterator of scalars to a sequence.
pub uninterp spec fn spec_scalars_from_iter<S, I>(iter: I) -> Seq<Scalar>;

/// Spec function to convert an iterator of optional points to a sequence.
pub uninterp spec fn spec_optional_points_from_iter<J>(iter: J) -> Seq<Option<EdwardsPoint>>;

/// Spec function to convert an iterator of points to a sequence.
pub uninterp spec fn spec_points_from_iter<P, J>(iter: J) -> Seq<EdwardsPoint>;

// ============================================================================
// Spec functions for optional point sequences
// ============================================================================
/// Check if all optional points in a sequence are Some.
pub open spec fn all_points_some(points: Seq<Option<EdwardsPoint>>) -> bool {
    forall|i: int| 0 <= i < points.len() ==> points[i].is_some()
}

/// Extract EdwardsPoints from an Option sequence (assumes all are Some).
pub open spec fn unwrap_points(points: Seq<Option<EdwardsPoint>>) -> Seq<EdwardsPoint>
    recommends
        all_points_some(points),
{
    points.map(|_i, opt: Option<EdwardsPoint>| opt.unwrap())
}

// ============================================================================
// Helper functions to collect iterators into Vecs (external_body)
// These bridge the gap between generic iterators and concrete Vec types
// ============================================================================
/// Collect an iterator of scalars into Vec<Scalar>.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn collect_scalars_from_iter<S, I>(iter: I) -> (result: Vec<Scalar>) where
    S: Borrow<Scalar>,
    I: Iterator<Item = S>,

    ensures
        result@ == spec_scalars_from_iter::<S, I>(iter),
{
    iter.map(|s| *s.borrow()).collect()
}

/// Collect an iterator of optional points into Vec<Option<EdwardsPoint>>.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn collect_optional_points_from_iter<J>(iter: J) -> (result: Vec<Option<EdwardsPoint>>) where
    J: Iterator<Item = Option<EdwardsPoint>>,

    ensures
        result@ == spec_optional_points_from_iter::<J>(iter),
{
    iter.collect()
}

/// Collect an iterator of points into Vec<EdwardsPoint>.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn collect_points_from_iter<P, J>(iter: J) -> (result: Vec<EdwardsPoint>) where
    P: Borrow<EdwardsPoint>,
    J: Iterator<Item = P>,

    ensures
        result@ == spec_points_from_iter::<P, J>(iter),
        // Assume all collected points are well-formed (trusted boundary)
        forall|i: int|
            0 <= i < result@.len() ==> is_well_formed_edwards_point(#[trigger] result@[i]),
{
    iter.map(|p| *p.borrow()).collect()
}

// ============================================================================
// Spec function for multiscalar multiplication result
// ============================================================================
/// Spec function to compute sum of scalar multiplications.
/// Returns the affine coordinates of sum(scalars[i] * points[i] for i in 0..min(len_s, len_p)).
pub open spec fn sum_of_scalar_muls(scalars: Seq<Scalar>, points: Seq<EdwardsPoint>) -> (nat, nat)
    decreases scalars.len(),
{
    let len = if scalars.len() <= points.len() {
        scalars.len()
    } else {
        points.len()
    };
    if len == 0 {
        // Identity point in affine coordinates: (0, 1)
        (0, 1)
    } else {
        let last = (len - 1) as int;
        let prev = sum_of_scalar_muls(scalars.subrange(0, last), points.subrange(0, last));
        let point_affine = edwards_point_as_affine(points[last]);
        let scalar_nat = spec_scalar(&scalars[last]);
        let scaled = edwards_scalar_mul(point_affine, scalar_nat);
        edwards_add(prev.0, prev.1, scaled.0, scaled.1)
    }
}

} // verus!
