//! Probabilistic specifications and axioms for uniform distribution.
//!
//! This module collects all specifications related to uniform distribution,
//! which are cryptographic properties that cannot be proven in standard program logic.
//!
//! ## Overview
//!
//! The uniform distribution properties form a chain:
//! 1. `is_uniform_bytes` - uniform random bytes (from RNG or hash)
//! 2. `is_uniform_field_element` - uniform field element (from bytes via from_bytes)
//! 3. `is_uniform_over_elligator_image` - uniform over Elligator image (~half the group)
//! 4. `is_uniform_ristretto_point` - uniform over FULL Ristretto group (requires 2 Elligator + add)
//!
//! ## Axioms
//!
//! Each axiom corresponds to a cryptographic/mathematical fact:
//! - `axiom_uniform_bytes_split`: Splitting uniform bytes yields independent uniform halves
//! - `axiom_from_bytes_uniform`: Clearing bit 255 preserves uniformity (negligible bias)
//! - `axiom_uniform_elligator`: Elligator produces uniform over its IMAGE (not full group!)
//! - `axiom_uniform_elligator_sum`: Two independent Elligator outputs sum to FULL uniform
//! - `axiom_uniform_point_add`: Sum of *independent* uniform group elements is uniform
//! - `axiom_uniform_mod_reduction`: Reducing 512 uniform bits mod L produces uniform scalar
#[allow(unused_imports)]
use super::edwards_specs::*;
#[allow(unused_imports)]
use super::field_specs::*;
#[allow(unused_imports)]
use super::ristretto_specs::*;
#[allow(unused_imports)]
use crate::field::FieldElement;
#[allow(unused_imports)]
use crate::ristretto::RistrettoPoint;
#[allow(unused_imports)]
use crate::Scalar;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::core_specs::bytes_seq_as_nat;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::scalar52_specs::group_order;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::scalar_specs::scalar_as_nat;

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::core_specs::u8_32_as_nat;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::arithmetic::power2::pow2;

// =============================================================================
// Uninterpreted Spec Functions for Uniform Distribution
// =============================================================================
/// Uniform distribution predicate for a single byte.
pub uninterp spec fn is_uniform(x: u8) -> bool;

/// Uniform distribution predicate for a byte slice.
/// True if the bytes are uniformly distributed over their domain.
pub uninterp spec fn is_uniform_bytes(bytes: &[u8]) -> bool;

/// Uniform distribution predicate for a field element.
/// True if the field element is uniformly distributed over F_p.
pub uninterp spec fn is_uniform_field_element(fe: &FieldElement) -> bool;

/// Uniform distribution predicate for a scalar.
/// True if the scalar is uniformly distributed over [0, l) where l is the group order.
pub uninterp spec fn is_uniform_scalar(scalar: &Scalar) -> bool;

/// Uniform distribution predicate for a Ristretto point.
/// True if the point is uniformly distributed over the Ristretto group.
pub uninterp spec fn is_uniform_ristretto_point(point: &RistrettoPoint) -> bool;

/// Independence predicate for two 32-byte strings.
///
/// This is intended to be used together with `is_uniform_bytes(..)` to model
/// two *independent uniform* samples when needed.
pub uninterp spec fn is_independent_uniform_bytes32(first: &[u8; 32], second: &[u8; 32]) -> bool;

/// Independence predicate for two field elements.
///
/// This is intended to be used together with `is_uniform_field_element(..)` to
/// model two *independent uniform* samples when needed.
pub uninterp spec fn is_independent_uniform_field_elements(
    fe1: &FieldElement,
    fe2: &FieldElement,
) -> bool;

/// Independence predicate for two Ristretto points.
///
/// This captures that two points are sampled independently. It can be used for
/// either full-group-uniform samples (`is_uniform_ristretto_point(..)`) or for
/// other sampling distributions (e.g. Elligator-image samples).
pub uninterp spec fn is_independent_uniform_ristretto_points(
    p1: &RistrettoPoint,
    p2: &RistrettoPoint,
) -> bool;

/// Uniform distribution over the Elligator image (roughly half the Ristretto group).
///
/// A single Elligator call does NOT produce a uniform point over the full group.
/// It only reaches points with a certain Jacobi symbol - approximately half the group.
/// This predicate captures uniformity over that restricted image.
pub uninterp spec fn is_uniform_over_elligator_image(point: &RistrettoPoint) -> bool;

// =============================================================================
// Axiom 1: Splitting uniform bytes preserves uniformity
// =============================================================================
/// Axiom: Splitting uniform bytes preserves uniformity on each half.
///
/// Mathematical justification:
/// If X is uniform over [0, 2^512), then the first 256 bits and last 256 bits
/// are each uniform over [0, 2^256) (they are independent uniform samples).
pub proof fn axiom_uniform_bytes_split(bytes: &[u8; 64], first: &[u8; 32], second: &[u8; 32])
    requires
        first@ == bytes@.subrange(0, 32),
        second@ == bytes@.subrange(32, 64),
        is_uniform_bytes(bytes),
    ensures
        is_uniform_bytes(first),
        is_uniform_bytes(second),
        is_independent_uniform_bytes32(first, second),
{
    admit();
}

// =============================================================================
// Axiom 2: from_bytes preserves uniformity
// =============================================================================
/// Axiom: Clearing bit 255 of uniform bytes preserves uniform distribution.
///
/// Mathematical justification:
/// - If X is uniform over [0, 2^256), then X mod 2^255 is uniform over [0, 2^255)
/// - This is because the high bit is independent of the lower 255 bits
/// - The limb representation is a bijection from 255-bit values to FieldElement
///
/// Note: There's negligible bias (19/2^255 ≈ 5.4e-77) from values in [p, 2^255)
/// that wrap when used in field arithmetic, but this is cryptographically negligible.
pub proof fn axiom_from_bytes_uniform(bytes: &[u8; 32], fe: &FieldElement)
    requires
        fe51_as_nat(fe) == u8_32_as_nat(bytes) % pow2(255),
    ensures
        is_uniform_bytes(bytes) ==> is_uniform_field_element(fe),
{
    assume(is_uniform_bytes(bytes) ==> is_uniform_field_element(fe));
}

/// Axiom: `from_bytes` preserves independence.
///
/// If two 32-byte strings are sampled independently, then the corresponding
/// field elements produced by `from_bytes` are also sampled independently.
pub proof fn axiom_from_bytes_independent(
    bytes1: &[u8; 32],
    bytes2: &[u8; 32],
    fe1: &FieldElement,
    fe2: &FieldElement,
)
    requires
        fe51_as_nat(fe1) == u8_32_as_nat(bytes1) % pow2(255),
        fe51_as_nat(fe2) == u8_32_as_nat(bytes2) % pow2(255),
        is_independent_uniform_bytes32(bytes1, bytes2),
    ensures
        is_independent_uniform_field_elements(fe1, fe2),
{
    admit();
}

// =============================================================================
// Axiom 3: Elligator map produces uniform points over its IMAGE (not the full group)
// =============================================================================
/// Axiom: Elligator map on uniform field element produces uniform point
/// over the Elligator IMAGE (approximately half the Ristretto group).
///
/// IMPORTANT: A single Elligator call does NOT produce a uniform point over
/// the full Ristretto group. Elligator maps F_p to roughly half the curve points
/// (those with a certain Jacobi symbol). See:
/// - Bernstein et al., "Elligator: Elliptic-curve points indistinguishable from uniform random strings"
/// - https://ristretto.group/formulas/elligator.html
///
/// To get uniform distribution over the FULL group, use two independent Elligator
/// calls and add the results (see `axiom_uniform_elligator_sum`).
pub proof fn axiom_uniform_elligator(fe: &FieldElement, point: &RistrettoPoint)
    requires
        edwards_point_as_affine(point.0) == spec_elligator_ristretto_flavor(
            fe51_as_canonical_nat(fe),
        ),
        is_uniform_field_element(fe),
    ensures
        is_uniform_over_elligator_image(point),
{
    admit();
}

/// Axiom: Elligator preserves independence.
///
/// If two field elements are sampled independently, then applying the Elligator
/// map to each yields independently sampled points (over the Elligator image).
pub proof fn axiom_uniform_elligator_independent(
    fe1: &FieldElement,
    fe2: &FieldElement,
    p1: &RistrettoPoint,
    p2: &RistrettoPoint,
)
    requires
        edwards_point_as_affine(p1.0) == spec_elligator_ristretto_flavor(
            fe51_as_canonical_nat(fe1),
        ),
        edwards_point_as_affine(p2.0) == spec_elligator_ristretto_flavor(
            fe51_as_canonical_nat(fe2),
        ),
        is_independent_uniform_field_elements(fe1, fe2),
    ensures
        is_independent_uniform_ristretto_points(p1, p2),
{
    admit();
}

// =============================================================================
// Axiom 4: Two independent Elligator outputs sum to FULL uniform
// =============================================================================
/// Axiom: Sum of two *independent* uniform-over-Elligator-image points
/// produces a point uniform over the FULL Ristretto group.
///
/// Mathematical justification (Bernstein et al., ristretto.group):
/// - Elligator(fe1) is uniform over ~half the group (Elligator image)
/// - Elligator(fe2) is uniform over ~half the group (independent)
/// - p1 + p2 covers the full group uniformly
///
/// This is precisely why `from_uniform_bytes` uses TWO Elligator calls + addition.
pub proof fn axiom_uniform_elligator_sum(
    p1: &RistrettoPoint,
    p2: &RistrettoPoint,
    sum: &RistrettoPoint,
)
    requires
        edwards_point_as_affine(sum.0) == edwards_add(
            edwards_point_as_affine(p1.0).0,
            edwards_point_as_affine(p1.0).1,
            edwards_point_as_affine(p2.0).0,
            edwards_point_as_affine(p2.0).1,
        ),
        is_uniform_over_elligator_image(p1),
        is_uniform_over_elligator_image(p2),
        is_independent_uniform_ristretto_points(p1, p2),
    ensures
        is_uniform_ristretto_point(sum),
{
    admit();
}

// =============================================================================
// Axiom 5: Group addition preserves uniformity (for already-uniform points)
// =============================================================================
/// Axiom: Sum of two *independent* uniform points is uniform (group theory property).
///
/// Mathematical justification:
/// In a prime-order group G, if X and Y are independent uniform elements of G,
/// then X + Y is also uniform over G. Without independence this is false
/// (e.g. if Y = -X then X + Y is always the identity).
pub proof fn axiom_uniform_point_add(p1: &RistrettoPoint, p2: &RistrettoPoint, sum: &RistrettoPoint)
    requires
        edwards_point_as_affine(sum.0) == edwards_add(
            edwards_point_as_affine(p1.0).0,
            edwards_point_as_affine(p1.0).1,
            edwards_point_as_affine(p2.0).0,
            edwards_point_as_affine(p2.0).1,
        ),
        is_uniform_ristretto_point(p1),
        is_uniform_ristretto_point(p2),
        is_independent_uniform_ristretto_points(p1, p2),
    ensures
        is_uniform_ristretto_point(sum),
{
    admit();
}

// =============================================================================
// Axiom 6: Modular reduction preserves uniformity (for scalars)
// =============================================================================
/// Axiom: Reducing 512 uniform bits modulo L produces a nearly uniform scalar.
///
/// Mathematical justification:
/// - Input: 64 bytes = 512 bits, uniform over [0, 2^512)
/// - Output: reduced modulo L (group order ≈ 2^253)
/// - Each residue r ∈ [0, L) appears floor(2^512/L) or ceil(2^512/L) times
/// - Statistical distance from uniform: at most L/2^512 ≈ 2^-259 (cryptographically negligible)
pub proof fn axiom_uniform_mod_reduction(input: &[u8; 64], result: &Scalar)
    requires
// result is the reduction of input mod group_order

        scalar_as_nat(result) == bytes_seq_as_nat(input@) % group_order(),
    ensures
        is_uniform_bytes(input) ==> is_uniform_scalar(result),
{
    admit();
}

} // verus!
