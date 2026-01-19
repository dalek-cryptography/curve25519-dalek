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
use crate::ristretto::RistrettoPoint;
#[allow(unused_imports)]
use crate::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::{
    edwards_add, edwards_point_as_affine, is_well_formed_edwards_point, sum_of_points,
};

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
{
    iter.map(|p| *p.borrow()).collect()
}

/// Convert a Vec<EdwardsPoint> to an iterator.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn vec_to_edwards_iter(vec: Vec<EdwardsPoint>) -> (result: alloc::vec::IntoIter<EdwardsPoint>)
    requires
        forall|i: int| 0 <= i < vec@.len() ==> is_well_formed_edwards_point(#[trigger] vec@[i]),
    ensures
        spec_points_from_iter::<EdwardsPoint, alloc::vec::IntoIter<EdwardsPoint>>(result) == vec@,
{
    vec.into_iter()
}

/// Convert a Vec<Option<EdwardsPoint>> to an iterator.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn vec_to_optional_edwards_iter(vec: Vec<Option<EdwardsPoint>>) -> (result:
    alloc::vec::IntoIter<Option<EdwardsPoint>>)
    requires
        forall|i: int|
            0 <= i < vec@.len() && (#[trigger] vec@[i]).is_some() ==> is_well_formed_edwards_point(
                vec@[i].unwrap(),
            ),
    ensures
        spec_optional_points_from_iter::<alloc::vec::IntoIter<Option<EdwardsPoint>>>(result)
            == vec@,
{
    vec.into_iter()
}

/// Collect an iterator of RistrettoPoints into Vec<EdwardsPoint>.
/// Directly maps RistrettoPoint to EdwardsPoint via .0.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn collect_edwards_from_ristretto_iter<P, J>(iter: J) -> (result: Vec<EdwardsPoint>) where
    P: Borrow<RistrettoPoint>,
    J: Iterator<Item = P>,

    ensures
        result@ == spec_edwards_from_ristretto_iter::<P, J>(iter),
{
    iter.map(|p| p.borrow().0).collect()
}

/// Clone a RistrettoPoint iterator with spec guarantee.
/// Returns (original, clone) with the guarantee that both yield the same Edwards sequence.
#[verifier::external_body]
pub fn clone_ristretto_iter_with_spec<P, J>(iter: J) -> (result: (J, J)) where
    P: Borrow<RistrettoPoint>,
    J: Iterator<Item = P> + Clone,

    ensures
        spec_edwards_from_ristretto_iter::<P, J>(result.0) == spec_edwards_from_ristretto_iter::<
            P,
            J,
        >(iter),
        spec_edwards_from_ristretto_iter::<P, J>(result.1) == spec_edwards_from_ristretto_iter::<
            P,
            J,
        >(iter),
{
    let cloned = iter.clone();
    (iter, cloned)
}

/// Collect an iterator of RistrettoPoints into Vec<RistrettoPoint>.
/// Used by Sum<T> impl which needs to pass slice to sum_of_slice.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn collect_ristretto_points<P, J>(iter: J) -> (result: Vec<RistrettoPoint>) where
    P: Borrow<RistrettoPoint>,
    J: Iterator<Item = P>,

    ensures
        result@.len() == spec_edwards_from_ristretto_iter::<P, J>(iter).len(),
        forall|i: int|
            0 <= i < result@.len() ==> (#[trigger] result@[i]).0
                == spec_edwards_from_ristretto_iter::<P, J>(iter)[i],
{
    iter.map(|p| *p.borrow()).collect()
}

/// Collect an iterator of Option<RistrettoPoint> into Vec<Option<EdwardsPoint>>.
/// Directly maps RistrettoPoint to EdwardsPoint via .0.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn collect_optional_edwards_from_ristretto_iter<J>(iter: J) -> (result: Vec<
    Option<EdwardsPoint>,
>) where J: Iterator<Item = Option<RistrettoPoint>>
    ensures
        result@ == spec_optional_edwards_from_ristretto_iter::<J>(iter),
{
    iter.map(|opt| opt.map(|p| p.0)).collect()
}

/// Clone an optional RistrettoPoint iterator with spec guarantee.
/// Returns (original, clone) with the guarantee that both yield the same Edwards sequence.
#[verifier::external_body]
pub fn clone_optional_ristretto_iter_with_spec<J>(iter: J) -> (result: (J, J)) where
    J: Iterator<Item = Option<RistrettoPoint>> + Clone,

    ensures
        spec_optional_edwards_from_ristretto_iter::<J>(result.0)
            == spec_optional_edwards_from_ristretto_iter::<J>(iter),
        spec_optional_edwards_from_ristretto_iter::<J>(result.1)
            == spec_optional_edwards_from_ristretto_iter::<J>(iter),
{
    let cloned = iter.clone();
    (iter, cloned)
}

// ============================================================================
// RistrettoPoint iterator specs
// Specs extract Edwards points directly since RistrettoPoint just wraps EdwardsPoint.
// ============================================================================
/// Spec function to convert an iterator of RistrettoPoints directly to
/// a sequence of EdwardsPoints (extracting .0 from each).
pub uninterp spec fn spec_edwards_from_ristretto_iter<P, J>(iter: J) -> Seq<EdwardsPoint>;

/// Spec function to convert an iterator of Option<RistrettoPoint> directly to
/// a sequence of Option<EdwardsPoint> (extracting .0 from each Some).
pub uninterp spec fn spec_optional_edwards_from_ristretto_iter<J>(iter: J) -> Seq<
    Option<EdwardsPoint>,
>;

/// Spec function to compute sum of all RistrettoPoints in a sequence.
/// Returns the affine coordinates of the result.
pub open spec fn sum_of_ristretto_points(points: Seq<RistrettoPoint>) -> (nat, nat)
    decreases points.len(),
{
    if points.len() == 0 {
        // Identity point in affine coordinates: (0, 1)
        (0, 1)
    } else {
        let last = (points.len() - 1) as int;
        let prev = sum_of_ristretto_points(points.subrange(0, last));
        let point_affine = edwards_point_as_affine(points[last].0);
        edwards_add(prev.0, prev.1, point_affine.0, point_affine.1)
    }
}

/// Lemma: sum_of_ristretto_points equals sum_of_points when Edwards points are extracted.
/// This allows translating between Ristretto and Edwards sum specs.
pub proof fn lemma_sum_ristretto_edwards_equiv(ristretto_points: Seq<RistrettoPoint>)
    ensures
        sum_of_ristretto_points(ristretto_points) == sum_of_points(
            Seq::new(ristretto_points.len(), |i: int| ristretto_points[i].0),
        ),
    decreases ristretto_points.len(),
{
    let edwards_points = Seq::new(ristretto_points.len(), |i: int| ristretto_points[i].0);
    if ristretto_points.len() == 0 {
        // Base case: both return (0, 1)
    } else {
        let last = (ristretto_points.len() - 1) as int;
        // Inductive step
        lemma_sum_ristretto_edwards_equiv(ristretto_points.subrange(0, last));
        // Show subranges map correctly
        assert(Seq::new(
            ristretto_points.subrange(0, last).len(),
            |i: int| ristretto_points.subrange(0, last)[i].0,
        ) =~= edwards_points.subrange(0, last));
        assert(ristretto_points[last].0 == edwards_points[last]);
    }
}

} // verus!
