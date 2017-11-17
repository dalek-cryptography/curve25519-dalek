// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Module for common traits.

use core::ops::Neg;

use subtle;
use subtle::ConditionallyAssignable;
use subtle::ConditionallyNegatable;

// ------------------------------------------------------------------------
// Public Traits
// ------------------------------------------------------------------------

/// Trait for getting the identity element of a point type.
pub trait Identity {
    /// Returns the identity element of the curve.
    /// Can be used as a constructor.
    fn identity() -> Self;
}

/// Trait for testing if a curve point is equivalent to the identity point.
pub trait IsIdentity {
    /// Return true if this element is the identity element of the curve.
    fn is_identity(&self) -> bool;
}

/// Implement generic identity equality testing for a point representations
/// which have constant-time equality testing and a defined identity
/// constructor.
impl<T> IsIdentity for T where T: subtle::Equal + Identity {
    fn is_identity(&self) -> bool {
        self.ct_eq(&T::identity()) == 1u8
    }
}

// ------------------------------------------------------------------------
// Private Traits
// ------------------------------------------------------------------------

/// Trait for checking whether a point is on the curve.
///
/// This trait is only for debugging/testing, since it should be
/// impossible for a `curve25519-dalek` user to construct an invalid
/// point.
pub(crate) trait ValidityCheck {
    /// Checks whether the point is on the curve. Not CT.
    fn is_valid(&self) -> bool;
}

// This isn't a trait, but it is fully generic...

/// Given precomputed points `[P, 2P, 3P, ..., 8P]`, as well as `-8 ≤
/// x ≤ 8`, compute `x * B` in constant time, i.e., without branching
/// on x or using it as an array index.
pub(crate) fn select_precomputed_point<T>(x: i8, points: &[T; 8]) -> T
    where T: Identity + ConditionallyAssignable, for<'a> &'a T: Neg<Output=T>
{
    debug_assert!(x >= -8); debug_assert!(x <= 8);

    // Compute xabs = |x|
    let xmask = x >> 7;
    let xabs  = (x + xmask) ^ xmask;

    // Set t = 0 * P = identity
    let mut t = T::identity();
    for j in 1..9 {
        // Copy `points[j-1] == j*P` onto `t` in constant time if `|x| == j`.
        t.conditional_assign(&points[j-1],
                             subtle::bytes_equal(xabs as u8, j as u8));
    }
    // Now t == |x| * P.

    let neg_mask = (xmask & 1) as u8;
    t.conditional_negate(neg_mask);
    // Now t == x * P.

    t
}
