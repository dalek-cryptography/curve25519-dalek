#[cfg(feature = "precomputed-tables")]
use crate::edwards::EdwardsBasepointTable;
use crate::specs::edwards_specs::*;
use crate::specs::montgomery_specs::*;
use crate::specs::scalar_specs::*;
use crate::{EdwardsPoint, MontgomeryPoint, Scalar};
use vstd::prelude::*;

/* VERIFICATION NOTE: this file contains
- inlined macro definitions for multiplicaitons between Scalar, EdwardsPoint, and MontgomeryPoint.
- their specifications as trait implementations MulSpecImpl.
*/
verus! {

// =============================================================================
// SECTION 1: EdwardsPoint * Scalar
// =============================================================================
// Specifications only - reference implementations (&EdwardsPoint * &Scalar) are in edwards.rs
/// Spec for &EdwardsPoint * &Scalar (reference implementation)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &EdwardsPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        rhs.bytes[31] <= 127 && is_well_formed_edwards_point(*self)
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for &EdwardsPoint * Scalar (owned scalar)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<Scalar> for &EdwardsPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: Scalar) -> bool {
        rhs.bytes[31] <= 127 && is_well_formed_edwards_point(*self)
    }

    open spec fn mul_spec(self, rhs: Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for EdwardsPoint * &Scalar (owned point)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for EdwardsPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        rhs.bytes[31] <= 127 && is_well_formed_edwards_point(self)
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for EdwardsPoint * Scalar (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<Scalar> for EdwardsPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: Scalar) -> bool {
        rhs.bytes[31] <= 127 && is_well_formed_edwards_point(self)
    }

    open spec fn mul_spec(self, rhs: Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 2: Scalar * EdwardsPoint
// =============================================================================
// NOTE: Manual implementations needed because macro-generated code is outside verus! blocks
// and cannot be used from inside verus! blocks (e.g., EdwardsPoint::mul_clamped).
/// Spec for &Scalar * &EdwardsPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&EdwardsPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &EdwardsPoint) -> bool {
        self.bytes[31] <= 127 && is_well_formed_edwards_point(*rhs)
    }

    open spec fn mul_spec(self, rhs: &EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for Scalar * &EdwardsPoint (owned scalar)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&EdwardsPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &EdwardsPoint) -> bool {
        self.bytes[31] <= 127 && is_well_formed_edwards_point(*rhs)
    }

    open spec fn mul_spec(self, rhs: &EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for &Scalar * EdwardsPoint (owned point)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<EdwardsPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: EdwardsPoint) -> bool {
        self.bytes[31] <= 127 && is_well_formed_edwards_point(rhs)
    }

    open spec fn mul_spec(self, rhs: EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for Scalar * EdwardsPoint (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<EdwardsPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: EdwardsPoint) -> bool {
        self.bytes[31] <= 127 && is_well_formed_edwards_point(rhs)
    }

    open spec fn mul_spec(self, rhs: EdwardsPoint) -> EdwardsPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 3: MontgomeryPoint * Scalar
// =============================================================================
// Specifications only - implementations are in montgomery.rs
// Requires: MontgomeryPoint must be valid
/// Spec for &MontgomeryPoint * &Scalar (reference implementation)
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

// =============================================================================
// SECTION 4: Scalar * MontgomeryPoint
// =============================================================================
// Specifications only - implementations are in montgomery.rs
// Requires: MontgomeryPoint must be valid
/// Spec for &Scalar * &MontgomeryPoint (reference implementation)
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

/// Spec for Scalar * &MontgomeryPoint (owned scalar)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&MontgomeryPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &MontgomeryPoint) -> bool {
        is_valid_montgomery_point(*rhs)
    }

    open spec fn mul_spec(self, rhs: &MontgomeryPoint) -> MontgomeryPoint {
        arbitrary()
    }
}

/// Spec for &Scalar * MontgomeryPoint (owned point)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<MontgomeryPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: MontgomeryPoint) -> bool {
        is_valid_montgomery_point(rhs)
    }

    open spec fn mul_spec(self, rhs: MontgomeryPoint) -> MontgomeryPoint {
        arbitrary()
    }
}

/// Spec for Scalar * MontgomeryPoint (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<MontgomeryPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: MontgomeryPoint) -> bool {
        is_valid_montgomery_point(rhs)
    }

    open spec fn mul_spec(self, rhs: MontgomeryPoint) -> MontgomeryPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 5: EdwardsBasepointTable * Scalar
// =============================================================================
// Specifications for basepoint table scalar multiplication
/// Spec for &EdwardsBasepointTable * &Scalar
#[cfg(feature = "precomputed-tables")]
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &EdwardsBasepointTable {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        rhs.bytes[31] <= 127
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> EdwardsPoint {
        arbitrary()
    }
}

/// Spec for &Scalar * &EdwardsBasepointTable
#[cfg(feature = "precomputed-tables")]
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&EdwardsBasepointTable> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &EdwardsBasepointTable) -> bool {
        self.bytes[31] <= 127
    }

    open spec fn mul_spec(self, rhs: &EdwardsBasepointTable) -> EdwardsPoint {
        arbitrary()
    }
}

} // verus!
