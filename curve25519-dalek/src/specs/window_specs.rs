//! Verus specifications for window lookup tables.
//!
//! This module contains spec functions for verifying lookup table construction
//! and selection operations used in scalar multiplication.
use crate::backend::serial::curve_models::AffineNielsPoint;
use crate::backend::serial::curve_models::ProjectiveNielsPoint;
#[cfg(feature = "precomputed-tables")]
use crate::backend::serial::u64::constants::AFFINE_ODD_MULTIPLES_OF_BASEPOINT;
use crate::edwards::EdwardsPoint;
use crate::specs::edwards_specs::*;
use crate::specs::field_specs::*;
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
use crate::window::NafLookupTable8;
use crate::window::{LookupTable, NafLookupTable5};
use vstd::prelude::*;

verus! {

// ============================================================================
// LookupTable specs (radix-16, stores [P, 2P, 3P, ..., 8P])
// ============================================================================
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

// ============================================================================
// NafLookupTable5 specs (stores odd multiples [1A, 3A, 5A, ..., 15A])
// ============================================================================
/// Spec: All entries in a NafLookupTable5<ProjectiveNielsPoint> have bounded limbs
pub open spec fn naf_lookup_table5_projective_limbs_bounded(
    table: [ProjectiveNielsPoint; 8],
) -> bool {
    forall|j: int|
        0 <= j < 8 ==> {
            let entry = #[trigger] table[j];
            fe51_limbs_bounded(&entry.Y_plus_X, 54) && fe51_limbs_bounded(&entry.Y_minus_X, 54)
                && fe51_limbs_bounded(&entry.Z, 54) && fe51_limbs_bounded(&entry.T2d, 54)
        }
}

/// Spec: All entries in a NafLookupTable5<AffineNielsPoint> have bounded limbs
pub open spec fn naf_lookup_table5_affine_limbs_bounded(table: [AffineNielsPoint; 8]) -> bool {
    forall|j: int|
        0 <= j < 8 ==> {
            let entry = #[trigger] table[j];
            fe51_limbs_bounded(&entry.y_plus_x, 54) && fe51_limbs_bounded(&entry.y_minus_x, 54)
                && fe51_limbs_bounded(&entry.xy2d, 54)
        }
}

/// Spec: Check if a NafLookupTable5 contains odd multiples [1A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
/// in ProjectiveNiels form.
pub open spec fn is_valid_naf_lookup_table5_projective(
    table: [ProjectiveNielsPoint; 8],
    A: EdwardsPoint,
) -> bool {
    forall|j: int|
        0 <= j < 8 ==> projective_niels_point_as_affine_edwards(#[trigger] table[j])
            == edwards_scalar_mul(edwards_point_as_affine(A), (2 * j + 1) as nat)
}

/// Spec: Check if a NafLookupTable5 contains odd multiples [1A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
/// in AffineNiels form.
pub open spec fn is_valid_naf_lookup_table5_affine(
    table: [AffineNielsPoint; 8],
    A: EdwardsPoint,
) -> bool {
    forall|j: int|
        0 <= j < 8 ==> affine_niels_point_as_affine_edwards(#[trigger] table[j])
            == edwards_scalar_mul(edwards_point_as_affine(A), (2 * j + 1) as nat)
}

// ============================================================================
// NafLookupTable8 specs (stores odd multiples [1A, 3A, 5A, ..., 127A])
// ============================================================================
/// Spec: All entries in a NafLookupTable8<ProjectiveNielsPoint> have bounded limbs
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
pub open spec fn naf_lookup_table8_projective_limbs_bounded(
    table: [ProjectiveNielsPoint; 64],
) -> bool {
    forall|j: int|
        0 <= j < 64 ==> {
            let entry = #[trigger] table[j];
            fe51_limbs_bounded(&entry.Y_plus_X, 54) && fe51_limbs_bounded(&entry.Y_minus_X, 54)
                && fe51_limbs_bounded(&entry.Z, 54) && fe51_limbs_bounded(&entry.T2d, 54)
        }
}

/// Spec: All entries in a NafLookupTable8<AffineNielsPoint> have bounded limbs
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
pub open spec fn naf_lookup_table8_affine_limbs_bounded(table: [AffineNielsPoint; 64]) -> bool {
    forall|j: int|
        0 <= j < 64 ==> {
            let entry = #[trigger] table[j];
            fe51_limbs_bounded(&entry.y_plus_x, 54) && fe51_limbs_bounded(&entry.y_minus_x, 54)
                && fe51_limbs_bounded(&entry.xy2d, 54)
        }
}

/// Spec: Check if a NafLookupTable8 contains odd multiples [1A, 3A, 5A, ..., 127A]
/// in ProjectiveNiels form.
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
pub open spec fn is_valid_naf_lookup_table8_projective(
    table: [ProjectiveNielsPoint; 64],
    A: EdwardsPoint,
) -> bool {
    forall|j: int|
        0 <= j < 64 ==> projective_niels_point_as_affine_edwards(#[trigger] table[j])
            == edwards_scalar_mul(edwards_point_as_affine(A), (2 * j + 1) as nat)
}

/// Spec: Check if a NafLookupTable8 contains odd multiples [1A, 3A, 5A, ..., 127A]
/// in AffineNiels form.
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
pub open spec fn is_valid_naf_lookup_table8_affine(
    table: [AffineNielsPoint; 64],
    A: EdwardsPoint,
) -> bool {
    forall|j: int|
        0 <= j < 64 ==> affine_niels_point_as_affine_edwards(#[trigger] table[j])
            == edwards_scalar_mul(edwards_point_as_affine(A), (2 * j + 1) as nat)
}

/// Spec: Check if a NafLookupTable8 contains odd multiples [1A, 3A, 5A, ..., 127A]
/// in AffineNiels form, where A is given as affine coordinates (nat, nat).
#[cfg(any(feature = "precomputed-tables", feature = "alloc"))]
pub open spec fn is_valid_naf_lookup_table8_affine_coords(
    table: [AffineNielsPoint; 64],
    basepoint: (nat, nat),
) -> bool {
    forall|j: int|
        #![trigger table[j]]
        0 <= j < 64 ==> affine_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (2 * j + 1) as nat,
        )
}

// ============================================================================
// Axioms for precomputed constant tables
// ============================================================================
/// Axiom: AFFINE_ODD_MULTIPLES_OF_BASEPOINT is a valid NAF lookup table for the Ed25519 basepoint.
/// This connects the hardcoded constant to our specification.
///
/// The table contains odd multiples [1·B, 3·B, 5·B, ..., 127·B] where B is the Ed25519 basepoint.
#[cfg(feature = "precomputed-tables")]
pub proof fn axiom_affine_odd_multiples_of_basepoint_valid()
    ensures
        naf_lookup_table8_affine_limbs_bounded(AFFINE_ODD_MULTIPLES_OF_BASEPOINT.0),
        is_valid_naf_lookup_table8_affine_coords(
            AFFINE_ODD_MULTIPLES_OF_BASEPOINT.0,
            spec_ed25519_basepoint(),
        ),
{
    admit();  // Hardcoded table data verified by construction
}

// ============================================================================
// FromSpecImpl trait implementations for From<&EdwardsPoint> conversions
// ============================================================================
/* VERIFICATION NOTE: Verus does not yet support `from_req` (requires clause) in FromSpecImpl.
   Unlike AddSpecImpl which has `add_req`, the FromSpecImpl trait only provides:
   - obeys_from_spec(): whether to check from_spec postcondition
   - from_spec(): the specification for the return value

   Because we cannot specify preconditions through the trait, we:
   1. Set obeys_from_spec() to false (skip checking from_spec postcondition)
   2. Use assumes in the from() implementation body for preconditions
   3. Use ensures clause directly on from() for postconditions
*/

// --- LookupTable ---
/// Spec for From<&EdwardsPoint> conversion for LookupTable<ProjectiveNielsPoint>
#[cfg(verus_keep_ghost)]
impl<'a> vstd::std_specs::convert::FromSpecImpl<&'a EdwardsPoint> for LookupTable<
    ProjectiveNielsPoint,
> {
    open spec fn obeys_from_spec() -> bool {
        false  // Verus does not support from_req; use ensures on from() instead

    }

    /* Expected from_req (if Verus supported it):
    open spec fn from_req(P: &'a EdwardsPoint) -> bool {
        edwards_point_limbs_bounded(*P)
        && edwards_point_sum_bounded(*P)
    }
    */
    open spec fn from_spec(P: &'a EdwardsPoint) -> Self {
        arbitrary()  // postconditions specified in ensures clause of from()

    }
}

/// Spec for From<&EdwardsPoint> conversion for LookupTable<AffineNielsPoint>
#[cfg(verus_keep_ghost)]
impl<'a> vstd::std_specs::convert::FromSpecImpl<&'a EdwardsPoint> for LookupTable<
    AffineNielsPoint,
> {
    open spec fn obeys_from_spec() -> bool {
        false  // Verus does not support from_req; use ensures on from() instead

    }

    /* Expected from_req (if Verus supported it):
    open spec fn from_req(P: &'a EdwardsPoint) -> bool {
        edwards_point_limbs_bounded(*P)
    }
    */
    open spec fn from_spec(P: &'a EdwardsPoint) -> Self {
        arbitrary()  // postconditions specified in ensures clause of from()

    }
}

// --- NafLookupTable5 ---
/// Spec for From<&EdwardsPoint> conversion for NafLookupTable5<ProjectiveNielsPoint>
#[cfg(verus_keep_ghost)]
impl<'a> vstd::std_specs::convert::FromSpecImpl<&'a EdwardsPoint> for NafLookupTable5<
    ProjectiveNielsPoint,
> {
    open spec fn obeys_from_spec() -> bool {
        false  // Verus does not support from_req; use ensures on from() instead

    }

    /* Expected from_req (if Verus supported it):
    open spec fn from_req(A: &'a EdwardsPoint) -> bool {
        edwards_point_limbs_bounded(*A)
        && edwards_point_sum_bounded(*A)
        && is_valid_edwards_point(*A)
    }
    */
    open spec fn from_spec(A: &'a EdwardsPoint) -> Self {
        arbitrary()  // postconditions specified in ensures clause of from()

    }
}

/// Spec for From<&EdwardsPoint> conversion for NafLookupTable5<AffineNielsPoint>
#[cfg(verus_keep_ghost)]
impl<'a> vstd::std_specs::convert::FromSpecImpl<&'a EdwardsPoint> for NafLookupTable5<
    AffineNielsPoint,
> {
    open spec fn obeys_from_spec() -> bool {
        false  // Verus does not support from_req; use ensures on from() instead

    }

    /* Expected from_req (if Verus supported it):
    open spec fn from_req(A: &'a EdwardsPoint) -> bool {
        edwards_point_limbs_bounded(*A)
        && edwards_point_sum_bounded(*A)
        && is_valid_edwards_point(*A)
    }
    */
    open spec fn from_spec(A: &'a EdwardsPoint) -> Self {
        arbitrary()  // postconditions specified in ensures clause of from()

    }
}

// --- NafLookupTable8 ---
/// Spec for From<&EdwardsPoint> conversion for NafLookupTable8<ProjectiveNielsPoint>
#[cfg(all(verus_keep_ghost, any(feature = "precomputed-tables", feature = "alloc")))]
impl<'a> vstd::std_specs::convert::FromSpecImpl<&'a EdwardsPoint> for NafLookupTable8<
    ProjectiveNielsPoint,
> {
    open spec fn obeys_from_spec() -> bool {
        false  // Verus does not support from_req; use ensures on from() instead

    }

    /* Expected from_req (if Verus supported it):
    open spec fn from_req(A: &'a EdwardsPoint) -> bool {
        edwards_point_limbs_bounded(*A)
        && edwards_point_sum_bounded(*A)
        && is_valid_edwards_point(*A)
    }
    */
    open spec fn from_spec(A: &'a EdwardsPoint) -> Self {
        arbitrary()  // postconditions specified in ensures clause of from()

    }
}

/// Spec for From<&EdwardsPoint> conversion for NafLookupTable8<AffineNielsPoint>
#[cfg(all(verus_keep_ghost, any(feature = "precomputed-tables", feature = "alloc")))]
impl<'a> vstd::std_specs::convert::FromSpecImpl<&'a EdwardsPoint> for NafLookupTable8<
    AffineNielsPoint,
> {
    open spec fn obeys_from_spec() -> bool {
        false  // Verus does not support from_req; use ensures on from() instead

    }

    /* Expected from_req (if Verus supported it):
    open spec fn from_req(A: &'a EdwardsPoint) -> bool {
        edwards_point_limbs_bounded(*A)
        && edwards_point_sum_bounded(*A)
        && is_valid_edwards_point(*A)
    }
    */
    open spec fn from_spec(A: &'a EdwardsPoint) -> Self {
        arbitrary()  // postconditions specified in ensures clause of from()

    }
}

} // verus!
