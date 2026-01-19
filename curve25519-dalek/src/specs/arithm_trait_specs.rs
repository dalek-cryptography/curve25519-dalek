//! Arithmetic trait specifications for Verus verification.
//!
//! This file contains specifications for arithmetic operations (Add, Sub, Mul)
//! as trait implementations (AddSpecImpl, SubSpecImpl, MulSpecImpl).
//!
//! The actual implementations are in their respective files (edwards.rs, ristretto.rs, etc.).
//! These specs define preconditions (via *_req) that Verus uses for verification.
#[cfg(feature = "precomputed-tables")]
#[allow(unused_imports)]
use crate::edwards::EdwardsBasepointTable;
#[cfg(feature = "precomputed-tables")]
#[allow(unused_imports)]
use crate::ristretto::RistrettoBasepointTable;
#[allow(unused_imports)]
use crate::ristretto::RistrettoPoint;
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::montgomery_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[allow(unused_imports)]
use crate::{EdwardsPoint, MontgomeryPoint, Scalar};
use vstd::prelude::*;

verus! {

// =============================================================================
// SECTION 1: RistrettoPoint + RistrettoPoint (AddSpecImpl)
// =============================================================================
// Requires: both RistrettoPoints have well-formed underlying EdwardsPoints
/// Spec for &RistrettoPoint + &RistrettoPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl<&RistrettoPoint> for &RistrettoPoint {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: &RistrettoPoint) -> bool {
        is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn add_spec(self, rhs: &RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for RistrettoPoint + RistrettoPoint (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl<RistrettoPoint> for RistrettoPoint {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: RistrettoPoint) -> bool {
        is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn add_spec(self, rhs: RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for RistrettoPoint + &RistrettoPoint (owned lhs)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl<&RistrettoPoint> for RistrettoPoint {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: &RistrettoPoint) -> bool {
        is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn add_spec(self, rhs: &RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for &RistrettoPoint + RistrettoPoint (owned rhs)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl<RistrettoPoint> for &RistrettoPoint {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: RistrettoPoint) -> bool {
        is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn add_spec(self, rhs: RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 2: RistrettoPoint - RistrettoPoint (SubSpecImpl)
// =============================================================================
// Requires: both RistrettoPoints have well-formed underlying EdwardsPoints
/// Spec for &RistrettoPoint - &RistrettoPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::SubSpecImpl<&RistrettoPoint> for &RistrettoPoint {
    open spec fn obeys_sub_spec() -> bool {
        false
    }

    open spec fn sub_req(self, rhs: &RistrettoPoint) -> bool {
        is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn sub_spec(self, rhs: &RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for RistrettoPoint - RistrettoPoint (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::SubSpecImpl<RistrettoPoint> for RistrettoPoint {
    open spec fn obeys_sub_spec() -> bool {
        false
    }

    open spec fn sub_req(self, rhs: RistrettoPoint) -> bool {
        is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn sub_spec(self, rhs: RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for RistrettoPoint - &RistrettoPoint (owned lhs)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::SubSpecImpl<&RistrettoPoint> for RistrettoPoint {
    open spec fn obeys_sub_spec() -> bool {
        false
    }

    open spec fn sub_req(self, rhs: &RistrettoPoint) -> bool {
        is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn sub_spec(self, rhs: &RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for &RistrettoPoint - RistrettoPoint (owned rhs)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::SubSpecImpl<RistrettoPoint> for &RistrettoPoint {
    open spec fn obeys_sub_spec() -> bool {
        false
    }

    open spec fn sub_req(self, rhs: RistrettoPoint) -> bool {
        is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn sub_spec(self, rhs: RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 3: EdwardsPoint * Scalar (MulSpecImpl)
// =============================================================================
// Requires: scalar.bytes[31] <= 127, EdwardsPoint is well-formed
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
// SECTION 4: Scalar * EdwardsPoint (MulSpecImpl)
// =============================================================================
// Requires: scalar.bytes[31] <= 127, EdwardsPoint is well-formed
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
// SECTION 5: MontgomeryPoint * Scalar (MulSpecImpl)
// =============================================================================
// Requires: MontgomeryPoint is valid
/// Spec for &MontgomeryPoint * &Scalar (reference implementation)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &MontgomeryPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        is_valid_montgomery_point(*self)
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> MontgomeryPoint {
        arbitrary()
    }
}

/// Spec for MontgomeryPoint * &Scalar (owned point)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for MontgomeryPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        is_valid_montgomery_point(self)
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> MontgomeryPoint {
        arbitrary()
    }
}

/// Spec for &MontgomeryPoint * Scalar (owned scalar)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<Scalar> for &MontgomeryPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: Scalar) -> bool {
        is_valid_montgomery_point(*self)
    }

    open spec fn mul_spec(self, rhs: Scalar) -> MontgomeryPoint {
        arbitrary()
    }
}

/// Spec for MontgomeryPoint * Scalar (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<Scalar> for MontgomeryPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: Scalar) -> bool {
        is_valid_montgomery_point(self)
    }

    open spec fn mul_spec(self, rhs: Scalar) -> MontgomeryPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 6: Scalar * MontgomeryPoint (MulSpecImpl)
// =============================================================================
// Requires: MontgomeryPoint is valid
/// Spec for &Scalar * &MontgomeryPoint (reference implementation)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&MontgomeryPoint> for &Scalar {
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
// SECTION 7: EdwardsBasepointTable * Scalar (MulSpecImpl)
// =============================================================================
// Requires: scalar.bytes[31] <= 127
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

// =============================================================================
// SECTION 8: RistrettoBasepointTable * Scalar (MulSpecImpl)
// =============================================================================
// Requires: scalar.bytes[31] <= 127
/// Spec for &RistrettoBasepointTable * &Scalar
#[cfg(feature = "precomputed-tables")]
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &RistrettoBasepointTable {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        rhs.bytes[31] <= 127
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for &Scalar * &RistrettoBasepointTable
#[cfg(feature = "precomputed-tables")]
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&RistrettoBasepointTable> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &RistrettoBasepointTable) -> bool {
        self.bytes[31] <= 127
    }

    open spec fn mul_spec(self, rhs: &RistrettoBasepointTable) -> RistrettoPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 9: RistrettoPoint * Scalar (MulSpecImpl)
// =============================================================================
// Requires: scalar.bytes[31] <= 127, RistrettoPoint has well-formed EdwardsPoint
/// Spec for &RistrettoPoint * &Scalar (reference implementation)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &RistrettoPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        rhs.bytes[31] <= 127 && is_well_formed_edwards_point(self.0)
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for &RistrettoPoint * Scalar (owned scalar)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<Scalar> for &RistrettoPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: Scalar) -> bool {
        rhs.bytes[31] <= 127 && is_well_formed_edwards_point(self.0)
    }

    open spec fn mul_spec(self, rhs: Scalar) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for RistrettoPoint * &Scalar (owned point)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for RistrettoPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        rhs.bytes[31] <= 127 && is_well_formed_edwards_point(self.0)
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for RistrettoPoint * Scalar (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<Scalar> for RistrettoPoint {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: Scalar) -> bool {
        rhs.bytes[31] <= 127 && is_well_formed_edwards_point(self.0)
    }

    open spec fn mul_spec(self, rhs: Scalar) -> RistrettoPoint {
        arbitrary()
    }
}

// =============================================================================
// SECTION 10: Scalar * RistrettoPoint (MulSpecImpl)
// =============================================================================
// Requires: scalar.bytes[31] <= 127, RistrettoPoint has well-formed EdwardsPoint
/// Spec for &Scalar * &RistrettoPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&RistrettoPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &RistrettoPoint) -> bool {
        self.bytes[31] <= 127 && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn mul_spec(self, rhs: &RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for Scalar * &RistrettoPoint (owned scalar)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&RistrettoPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: &RistrettoPoint) -> bool {
        self.bytes[31] <= 127 && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn mul_spec(self, rhs: &RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for &Scalar * RistrettoPoint (owned point)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<RistrettoPoint> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: RistrettoPoint) -> bool {
        self.bytes[31] <= 127 && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn mul_spec(self, rhs: RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

/// Spec for Scalar * RistrettoPoint (both owned)
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<RistrettoPoint> for Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false
    }

    open spec fn mul_req(self, rhs: RistrettoPoint) -> bool {
        self.bytes[31] <= 127 && is_well_formed_edwards_point(rhs.0)
    }

    open spec fn mul_spec(self, rhs: RistrettoPoint) -> RistrettoPoint {
        arbitrary()
    }
}

} // verus!
