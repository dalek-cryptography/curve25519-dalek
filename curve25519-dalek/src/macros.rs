// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis agora lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
//! Internal macros.
/// Define borrow and non-borrow variants of `Add`.
///
use vstd::prelude::*;

macro_rules! define_add_variants {
    (LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
        impl<'b> Add<&'b $rhs> for $lhs {
            type Output = $out;
            fn add(self, rhs: &'b $rhs) -> $out {
                &self + rhs
            }
        }

        impl<'a> Add<$rhs> for &'a $lhs {
            type Output = $out;
            fn add(self, rhs: $rhs) -> $out {
                self + &rhs
            }
        }

        impl Add<$rhs> for $lhs {
            type Output = $out;
            fn add(self, rhs: $rhs) -> $out {
                &self + &rhs
            }
        }
    };
}

/// Define Add variants for RistrettoPoint inside verus! block.
/// Includes well-formedness and functional correctness (edwards_add).
macro_rules! define_ristretto_add_variants {
    () => {
        verus! {
        impl<'b> Add<&'b RistrettoPoint> for RistrettoPoint {
            type Output = RistrettoPoint;
            fn add(self, rhs: &'b RistrettoPoint) -> (result: RistrettoPoint)
                ensures
                    is_well_formed_edwards_point(result.0),
                    edwards_point_as_affine(result.0) == edwards_add(
                        edwards_point_as_affine(self.0).0,
                        edwards_point_as_affine(self.0).1,
                        edwards_point_as_affine(rhs.0).0,
                        edwards_point_as_affine(rhs.0).1,
                    ),
            {
                &self + rhs
            }
        }

        impl<'a> Add<RistrettoPoint> for &'a RistrettoPoint {
            type Output = RistrettoPoint;
            fn add(self, rhs: RistrettoPoint) -> (result: RistrettoPoint)
                ensures
                    is_well_formed_edwards_point(result.0),
                    edwards_point_as_affine(result.0) == edwards_add(
                        edwards_point_as_affine(self.0).0,
                        edwards_point_as_affine(self.0).1,
                        edwards_point_as_affine(rhs.0).0,
                        edwards_point_as_affine(rhs.0).1,
                    ),
            {
                self + &rhs
            }
        }

        impl Add<RistrettoPoint> for RistrettoPoint {
            type Output = RistrettoPoint;
            fn add(self, rhs: RistrettoPoint) -> (result: RistrettoPoint)
                ensures
                    is_well_formed_edwards_point(result.0),
                    edwards_point_as_affine(result.0) == edwards_add(
                        edwards_point_as_affine(self.0).0,
                        edwards_point_as_affine(self.0).1,
                        edwards_point_as_affine(rhs.0).0,
                        edwards_point_as_affine(rhs.0).1,
                    ),
            {
                &self + &rhs
            }
        }
        }
    };
}

/// Define non-borrow variants of `AddAssign`.
macro_rules! define_add_assign_variants {
    (LHS = $lhs:ty, RHS = $rhs:ty) => {
        impl AddAssign<$rhs> for $lhs {
            fn add_assign(&mut self, rhs: $rhs) {
                *self += &rhs;
            }
        }
    };
}

/// Define borrow and non-borrow variants of `Sub`.
macro_rules! define_sub_variants {
    (LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
        impl<'b> Sub<&'b $rhs> for $lhs {
            type Output = $out;
            fn sub(self, rhs: &'b $rhs) -> $out {
                &self - rhs
            }
        }

        impl<'a> Sub<$rhs> for &'a $lhs {
            type Output = $out;
            fn sub(self, rhs: $rhs) -> $out {
                self - &rhs
            }
        }

        impl Sub<$rhs> for $lhs {
            type Output = $out;
            fn sub(self, rhs: $rhs) -> $out {
                &self - &rhs
            }
        }
    };
}

/// Define Sub variants for RistrettoPoint inside verus! block.
/// Includes well-formedness and functional correctness (edwards_sub).
macro_rules! define_ristretto_sub_variants {
    () => {
        verus! {
        impl<'b> Sub<&'b RistrettoPoint> for RistrettoPoint {
            type Output = RistrettoPoint;
            fn sub(self, rhs: &'b RistrettoPoint) -> (result: RistrettoPoint)
                ensures
                    is_well_formed_edwards_point(result.0),
                    edwards_point_as_affine(result.0) == edwards_sub(
                        edwards_point_as_affine(self.0).0,
                        edwards_point_as_affine(self.0).1,
                        edwards_point_as_affine(rhs.0).0,
                        edwards_point_as_affine(rhs.0).1,
                    ),
            {
                &self - rhs
            }
        }

        impl<'a> Sub<RistrettoPoint> for &'a RistrettoPoint {
            type Output = RistrettoPoint;
            fn sub(self, rhs: RistrettoPoint) -> (result: RistrettoPoint)
                ensures
                    is_well_formed_edwards_point(result.0),
                    edwards_point_as_affine(result.0) == edwards_sub(
                        edwards_point_as_affine(self.0).0,
                        edwards_point_as_affine(self.0).1,
                        edwards_point_as_affine(rhs.0).0,
                        edwards_point_as_affine(rhs.0).1,
                    ),
            {
                self - &rhs
            }
        }

        impl Sub<RistrettoPoint> for RistrettoPoint {
            type Output = RistrettoPoint;
            fn sub(self, rhs: RistrettoPoint) -> (result: RistrettoPoint)
                ensures
                    is_well_formed_edwards_point(result.0),
                    edwards_point_as_affine(result.0) == edwards_sub(
                        edwards_point_as_affine(self.0).0,
                        edwards_point_as_affine(self.0).1,
                        edwards_point_as_affine(rhs.0).0,
                        edwards_point_as_affine(rhs.0).1,
                    ),
            {
                &self - &rhs
            }
        }
        }
    };
}

/// Define non-borrow variants of `SubAssign`.
macro_rules! define_sub_assign_variants {
    (LHS = $lhs:ty, RHS = $rhs:ty) => {
        impl SubAssign<$rhs> for $lhs {
            fn sub_assign(&mut self, rhs: $rhs) {
                *self -= &rhs;
            }
        }
    };
}

/// Define borrow and non-borrow variants of `Mul`.
macro_rules! define_mul_variants {
    (LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
        impl<'b> Mul<&'b $rhs> for $lhs {
            type Output = $out;
            fn mul(self, rhs: &'b $rhs) -> $out {
                &self * rhs
            }
        }

        impl<'a> Mul<$rhs> for &'a $lhs {
            type Output = $out;
            fn mul(self, rhs: $rhs) -> $out {
                self * &rhs
            }
        }

        impl Mul<$rhs> for $lhs {
            type Output = $out;
            fn mul(self, rhs: $rhs) -> $out {
                &self * &rhs
            }
        }
    };
}

/// Define borrow and non-borrow variants of `Mul` inside verus! block.
/// Use this when the macro-generated functions are called from within verus! blocks.
macro_rules! define_mul_variants_verus {
    (LHS = $lhs:ty, RHS = $rhs:ty, Output = $out:ty) => {
        verus! {
        impl<'b> Mul<&'b $rhs> for $lhs {
            type Output = $out;
            fn mul(self, rhs: &'b $rhs) -> $out {
                &self * rhs
            }
        }

        impl<'a> Mul<$rhs> for &'a $lhs {
            type Output = $out;
            fn mul(self, rhs: $rhs) -> $out {
                self * &rhs
            }
        }

        impl Mul<$rhs> for $lhs {
            type Output = $out;
            fn mul(self, rhs: $rhs) -> $out {
                &self * &rhs
            }
        }
        }
    };
}

/// Define wrapper variants for `EdwardsPoint * Scalar` with functional-correctness postconditions.
///
/// Exec-wise, this is equivalent to what
/// `define_mul_variants_verus!(LHS = EdwardsPoint, RHS = Scalar, Output = EdwardsPoint)`
/// would generate (each impl forwards to a borrowed-argument multiplication).
///
/// We write it as a specialized macro so we can attach `ensures` postconditions to
/// the wrapper variants, instead of only having specs on `&EdwardsPoint * &Scalar`.
macro_rules! define_edwards_scalar_mul_variants_verus {
    () => {
        verus! {
        impl<'b> core::ops::Mul<&'b $crate::scalar::Scalar> for $crate::edwards::EdwardsPoint {
            type Output = $crate::edwards::EdwardsPoint;

            fn mul(self, scalar: &'b $crate::scalar::Scalar) -> (result: $crate::edwards::EdwardsPoint)
                ensures
                    $crate::specs::edwards_specs::is_well_formed_edwards_point(result),
                    $crate::specs::edwards_specs::edwards_point_as_affine(result)
                        == $crate::specs::edwards_specs::edwards_scalar_mul(
                        $crate::specs::edwards_specs::edwards_point_as_affine(self),
                        $crate::specs::scalar_specs::scalar_to_nat(scalar),
                    ),
            {
                // Calls &EdwardsPoint * &Scalar (the verified implementation)
                &self * scalar
            }
        }

        impl<'a> core::ops::Mul<$crate::scalar::Scalar> for &'a $crate::edwards::EdwardsPoint {
            type Output = $crate::edwards::EdwardsPoint;

            fn mul(self, scalar: $crate::scalar::Scalar) -> (result: $crate::edwards::EdwardsPoint)
                ensures
                    $crate::specs::edwards_specs::is_well_formed_edwards_point(result),
                    $crate::specs::edwards_specs::edwards_point_as_affine(result)
                        == $crate::specs::edwards_specs::edwards_scalar_mul(
                        $crate::specs::edwards_specs::edwards_point_as_affine(*self),
                        $crate::specs::scalar_specs::scalar_to_nat(&scalar),
                    ),
            {
                // Calls &EdwardsPoint * &Scalar (the verified implementation)
                self * &scalar
            }
        }

        impl core::ops::Mul<$crate::scalar::Scalar> for $crate::edwards::EdwardsPoint {
            type Output = $crate::edwards::EdwardsPoint;

            fn mul(self, scalar: $crate::scalar::Scalar) -> (result: $crate::edwards::EdwardsPoint)
                ensures
                    $crate::specs::edwards_specs::is_well_formed_edwards_point(result),
                    $crate::specs::edwards_specs::edwards_point_as_affine(result)
                        == $crate::specs::edwards_specs::edwards_scalar_mul(
                        $crate::specs::edwards_specs::edwards_point_as_affine(self),
                        $crate::specs::scalar_specs::scalar_to_nat(&scalar),
                    ),
            {
                // Calls &EdwardsPoint * &Scalar (the verified implementation)
                &self * &scalar
            }
        }
        }
    };
}

/// Define non-borrow variants of `MulAssign`.
macro_rules! define_mul_assign_variants {
    (LHS = $lhs:ty, RHS = $rhs:ty) => {
        impl MulAssign<$rhs> for $lhs {
            fn mul_assign(&mut self, rhs: $rhs) {
                *self *= &rhs;
            }
        }
    };
}
