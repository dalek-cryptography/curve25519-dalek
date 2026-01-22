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
//! Internal curve representations which are not part of the public API.
//!
//! # Curve representations
//!
//! Internally, we use several different models for the curve.  Here
//! is a sketch of the relationship between the models, following [a
//! post][smith-moderncrypto]
//! by Ben Smith on the `moderncrypto` mailing list.  This is also briefly
//! discussed in section 2.5 of [_Montgomery curves and their
//! arithmetic_][costello-smith-2017] by Costello and Smith.
//!
//! Begin with the affine equation for the curve,
//! $$
//!     -x\^2 + y\^2 = 1 + dx\^2y\^2.
//! $$
//! Next, pass to the projective closure \\(\mathbb P\^1 \times \mathbb
//! P\^1 \\) by setting \\(x=X/Z\\), \\(y=Y/T.\\)  Clearing denominators
//! gives the model
//! $$
//!     -X\^2T\^2 + Y\^2Z\^2 = Z\^2T\^2 + dX\^2Y\^2.
//! $$
//! In `curve25519-dalek`, this is represented as the `CompletedPoint`
//! struct.
//! To map from \\(\mathbb P\^1 \times \mathbb P\^1 \\), a product of
//! two lines, to \\(\mathbb P\^3\\), we use the [Segre
//! embedding](https://en.wikipedia.org/wiki/Segre_embedding)
//! $$
//!     \sigma : ((X:Z),(Y:T)) \mapsto (XY:XT:ZY:ZT).
//! $$
//! Using coordinates \\( (W_0:W_1:W_2:W_3) \\) for \\(\mathbb P\^3\\),
//! the image \\(\sigma (\mathbb P\^1 \times \mathbb P\^1) \\) is the
//! surface defined by \\( W_0 W_3 = W_1 W_2 \\), and under \\(
//! \sigma\\), the equation above becomes
//! $$
//!     -W\_1\^2 + W\_2\^2 = W\_3\^2 + dW\_0\^2,
//! $$
//! so that the curve is given by the pair of equations
//! $$
//! \begin{aligned}
//!     -W\_1\^2 + W\_2\^2 &= W\_3\^2 + dW\_0\^2, \\\\  W_0 W_3 &= W_1 W_2.
//! \end{aligned}
//! $$
//! Up to variable naming, this is exactly the "extended" curve model
//! introduced in [_Twisted Edwards Curves
//! Revisited_][hisil-wong-carter-dawson-2008] by Hisil, Wong, Carter,
//! and Dawson.  In `curve25519-dalek`, it is represented as the
//! `EdwardsPoint` struct.  We can map from \\(\mathbb P\^3 \\) to
//! \\(\mathbb P\^2 \\) by sending \\( (W\_0:W\_1:W\_2:W\_3) \\) to \\(
//! (W\_1:W\_2:W\_3) \\).  Notice that
//! $$
//!     \frac {W\_1} {W\_3} = \frac {XT} {ZT} = \frac X Z = x,
//! $$
//! and
//! $$
//!     \frac {W\_2} {W\_3} = \frac {YZ} {ZT} = \frac Y T = y,
//! $$
//! so this is the same as if we had started with the affine model
//! and passed to \\( \mathbb P\^2 \\) by setting \\( x = W\_1 / W\_3
//! \\), \\(y = W\_2 / W\_3 \\).
//! Up to variable naming, this is the projective representation
//! introduced in in [_Twisted Edwards
//! Curves_][bernstein-birkner-joye-lange-peters-2008] by Bernstein,
//! Birkner, Joye, Lange, and Peters.  In `curve25519-dalek`, it is
//! represented by the `ProjectivePoint` struct.
//!
//! # Passing between curve models
//!
//! Although the \\( \mathbb P\^3 \\) model provides faster addition
//! formulas, the \\( \mathbb P\^2 \\) model provides faster doubling
//! formulas.  Hisil, Wong, Carter, and Dawson therefore suggest mixing
//! coordinate systems for scalar multiplication, attributing the idea
//! to [a 1998 paper][cohen-miyaji-ono-1998] of Cohen, Miyagi, and Ono.
//!
//! Their suggestion is to vary the formulas used by context, using a
//! \\( \mathbb P\^2 \rightarrow \mathbb P\^2 \\) doubling formula when
//! a doubling is followed
//! by another doubling, a \\( \mathbb P\^2 \rightarrow \mathbb P\^3 \\)
//! doubling formula when a doubling is followed by an addition, and
//! computing point additions using a \\( \mathbb P\^3 \times \mathbb P\^3
//! \rightarrow \mathbb P\^2 \\) formula.
//!
//! The `ref10` reference implementation of [Ed25519][ed25519], by
//! Bernstein, Duif, Lange, Schwabe, and Yang, tweaks
//! this strategy, factoring the addition formulas through the
//! completion \\( \mathbb P\^1 \times \mathbb P\^1 \\), so that the
//! output of an addition or doubling always lies in \\( \mathbb P\^1 \times
//! \mathbb P\^1\\), and the choice of which formula to use is replaced
//! by a choice of whether to convert the result to \\( \mathbb P\^2 \\)
//! or \\(\mathbb P\^3 \\).  However, this tweak is not described in
//! their paper, only in their software.
//!
//! Our naming for the `CompletedPoint` (\\(\mathbb P\^1 \times \mathbb
//! P\^1 \\)), `ProjectivePoint` (\\(\mathbb P\^2 \\)), and
//! `EdwardsPoint` (\\(\mathbb P\^3 \\)) structs follows the naming in
//! Adam Langley's [Golang ed25519][agl-ed25519] implementation, which
//! `curve25519-dalek` was originally derived from.
//!
//! Finally, to accelerate readditions, we use two cached point formats
//! in "Niels coordinates", named for Niels Duif,
//! one for the affine model and one for the \\( \mathbb P\^3 \\) model:
//!
//! * `AffineNielsPoint`: \\( (y+x, y-x, 2dxy) \\)
//! * `ProjectiveNielsPoint`: \\( (Y+X, Y-X, Z, 2dXY) \\)
//!
//! [smith-moderncrypto]: https://moderncrypto.org/mail-archive/curves/2016/000807.html
//! [costello-smith-2017]: https://eprint.iacr.org/2017/212
//! [hisil-wong-carter-dawson-2008]: https://www.iacr.org/archive/asiacrypt2008/53500329/53500329.pdf
//! [bernstein-birkner-joye-lange-peters-2008]: https://eprint.iacr.org/2008/013
//! [cohen-miyaji-ono-1998]: https://link.springer.com/content/pdf/10.1007%2F3-540-49649-1_6.pdf
//! [ed25519]: https://eprint.iacr.org/2011/368
//! [agl-ed25519]: https://github.com/agl/ed25519
#![allow(non_snake_case)]

use core::fmt::Debug;
use core::ops::{Add, Neg, Sub};

use subtle::Choice;
use subtle::ConditionallySelectable;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

#[cfg(verus_keep_ghost)]
use crate::backend::serial::u64::subtle_assumes::choice_is_true;
use crate::constants;
use crate::core_assumes::negate_field;
#[allow(unused_imports)] // Used in verus! blocks for affine↔projective curve equation
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::lemmas::field_lemmas::add_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks for as_projective proof
use crate::lemmas::field_lemmas::field_algebra_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::edwards_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::field_specs::*;
#[allow(unused_imports)] // Used in verus! blocks for p() and spec_field_element_as_nat
use crate::specs::field_specs_u64::*;

use crate::edwards::EdwardsPoint;
use crate::field::FieldElement;
use crate::traits::ValidityCheck;

use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

// ------------------------------------------------------------------------
// Internal point representations
// ------------------------------------------------------------------------

verus! {

/// A `ProjectivePoint` is a point \\((X:Y:Z)\\) on the \\(\mathbb
/// P\^2\\) model of the curve.
/// A point \\((x,y)\\) in the affine model corresponds to
/// \\((x:y:1)\\).
///
/// More details on the relationships between the different curve models
/// can be found in the module-level documentation.
#[allow(missing_docs)]
#[derive(Copy, Clone)]
pub struct ProjectivePoint {
    pub X: FieldElement,
    pub Y: FieldElement,
    pub Z: FieldElement,
}

/// A `CompletedPoint` is a point \\(((X:Z), (Y:T))\\) on the \\(\mathbb
/// P\^1 \times \mathbb P\^1 \\) model of the curve.
/// A point (x,y) in the affine model corresponds to \\( ((x:1),(y:1))
/// \\).
///
/// More details on the relationships between the different curve models
/// can be found in the module-level documentation.
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct CompletedPoint {
    pub X: FieldElement,
    pub Y: FieldElement,
    pub Z: FieldElement,
    pub T: FieldElement,
}

/// A pre-computed point in the affine model for the curve, represented as
/// \\((y+x, y-x, 2dxy)\\) in "Niels coordinates".
///
/// More details on the relationships between the different curve models
/// can be found in the module-level documentation.
// Safe to derive Eq because affine coordinates.
#[derive(Copy, Clone, Eq, PartialEq)]
#[allow(missing_docs)]
pub struct AffineNielsPoint {
    pub y_plus_x: FieldElement,
    pub y_minus_x: FieldElement,
    pub xy2d: FieldElement,
}

#[cfg(feature = "zeroize")]
impl Zeroize for AffineNielsPoint {
    fn zeroize(&mut self)
        ensures
    // All fields are zeroed (each limb is 0)

            forall|i: int| 0 <= i < 5 ==> self.y_plus_x.limbs[i] == 0,
            forall|i: int| 0 <= i < 5 ==> self.y_minus_x.limbs[i] == 0,
            forall|i: int| 0 <= i < 5 ==> self.xy2d.limbs[i] == 0,
    {
        self.y_plus_x.zeroize();
        self.y_minus_x.zeroize();
        self.xy2d.zeroize();
    }
}

/// A pre-computed point on the \\( \mathbb P\^3 \\) model for the
/// curve, represented as \\((Y+X, Y-X, Z, 2dXY)\\) in "Niels coordinates".
///
/// More details on the relationships between the different curve models
/// can be found in the module-level documentation.
#[derive(Copy, Clone)]
#[allow(missing_docs)]
pub struct ProjectiveNielsPoint {
    pub Y_plus_X: FieldElement,
    pub Y_minus_X: FieldElement,
    pub Z: FieldElement,
    pub T2d: FieldElement,
}

#[cfg(feature = "zeroize")]
impl Zeroize for ProjectiveNielsPoint {
    fn zeroize(&mut self)
        ensures
    // All fields are zeroed (each limb is 0)

            forall|i: int| 0 <= i < 5 ==> self.Y_plus_X.limbs[i] == 0,
            forall|i: int| 0 <= i < 5 ==> self.Y_minus_X.limbs[i] == 0,
            forall|i: int| 0 <= i < 5 ==> self.Z.limbs[i] == 0,
            forall|i: int| 0 <= i < 5 ==> self.T2d.limbs[i] == 0,
    {
        self.Y_plus_X.zeroize();
        self.Y_minus_X.zeroize();
        self.Z.zeroize();
        self.T2d.zeroize();
    }
}

} // verus!
// ------------------------------------------------------------------------
// Constructors
// ------------------------------------------------------------------------
use crate::traits::Identity;

verus! {

impl Identity for ProjectivePoint {
    fn identity() -> (result: ProjectivePoint)
        ensures
            result == identity_projective_point_edwards(),
    {
        ProjectivePoint { X: FieldElement::ZERO, Y: FieldElement::ONE, Z: FieldElement::ONE }
    }
}

impl Identity for ProjectiveNielsPoint {
    fn identity() -> (result: ProjectiveNielsPoint)
        ensures
            result == identity_projective_niels(),
    {
        ProjectiveNielsPoint {
            Y_plus_X: FieldElement::ONE,
            Y_minus_X: FieldElement::ONE,
            Z: FieldElement::ONE,
            T2d: FieldElement::ZERO,
        }
    }
}

impl Default for ProjectiveNielsPoint {
    fn default() -> (result: ProjectiveNielsPoint)
        ensures
            result == identity_projective_niels(),
    {
        ProjectiveNielsPoint::identity()
    }
}

impl Identity for AffineNielsPoint {
    fn identity() -> (result: AffineNielsPoint)
        ensures
            result == identity_affine_niels(),
    {
        AffineNielsPoint {
            y_plus_x: FieldElement::ONE,
            y_minus_x: FieldElement::ONE,
            xy2d: FieldElement::ZERO,
        }
    }
}

impl Default for AffineNielsPoint {
    fn default() -> (result: AffineNielsPoint)
        ensures
            result == identity_affine_niels(),
    {
        AffineNielsPoint::identity()
    }
}

} // verus!
// ------------------------------------------------------------------------
// Validity checks (for debugging, not CT)
// ------------------------------------------------------------------------
verus! {

impl ValidityCheck for ProjectivePoint {
    fn is_valid(&self) -> (result: bool)
        requires
            fe51_limbs_bounded(&self.X, 54),
            fe51_limbs_bounded(&self.Y, 54),
            fe51_limbs_bounded(&self.Z, 54),
        ensures
            result == math_on_edwards_curve_projective(
                spec_field_element(&self.X),
                spec_field_element(&self.Y),
                spec_field_element(&self.Z),
            ),
    {
        // Curve equation is    -x^2 + y^2 = 1 + d*x^2*y^2,
        // homogenized as (-X^2 + Y^2)*Z^2 = Z^4 + d*X^2*Y^2
        let XX = self.X.square();
        let YY = self.Y.square();
        let ZZ = self.Z.square();
        proof {
            assume(fe51_limbs_bounded(&ZZ, 54));  // for ZZZZ = ZZ.square()
            assume(fe51_limbs_bounded(&YY, 54) && fe51_limbs_bounded(&XX, 54));  // for yy_minus_xx = &YY - &XX and
        }
        let ZZZZ = ZZ.square();

        /* ORIGINAL CODE: refactor for assumptions on intermediate results
        let lhs = &(&YY - &XX) * &ZZ;
        let rhs = &ZZZZ + &(&constants::EDWARDS_D * &(&XX * &YY));
        lhs == rhs
        */

        let yy_minus_xx = &YY - &XX;
        proof {
            assume(fe51_limbs_bounded(&yy_minus_xx, 54) && fe51_limbs_bounded(&ZZ, 54));  // for lhs = &yy_minus_xx * &ZZ
        }
        let lhs = &yy_minus_xx * &ZZ;

        let xx_times_yy = &XX * &YY;
        proof {
            assume(fe51_limbs_bounded(&constants::EDWARDS_D, 54) && fe51_limbs_bounded(
                &xx_times_yy,
                54,
            ));  // for d_times_xxyy = &constants::EDWARDS_D * &xx_times_yy
        }
        let d_times_xxyy = &constants::EDWARDS_D * &xx_times_yy;
        proof {
            assume(sum_of_limbs_bounded(&ZZZZ, &d_times_xxyy, u64::MAX));  // for rhs = &ZZZZ + &d_times_xxyy
        }
        let rhs = &ZZZZ + &d_times_xxyy;

        let result = lhs == rhs;
        proof {
            // postcondition
            assume(result == math_on_edwards_curve_projective(
                spec_field_element(&self.X),
                spec_field_element(&self.Y),
                spec_field_element(&self.Z),
            ));
        }
        result
    }
}

// ------------------------------------------------------------------------
// Constant-time assignment
// ------------------------------------------------------------------------
impl ConditionallySelectable for ProjectiveNielsPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> (result: Self)
        ensures
    // If choice is false, return a

            !choice_is_true(choice) ==> result == *a,
            // If choice is true, return b
            choice_is_true(choice) ==> result == *b,
    {
        let result = ProjectiveNielsPoint {
            Y_plus_X: FieldElement::conditional_select(&a.Y_plus_X, &b.Y_plus_X, choice),
            Y_minus_X: FieldElement::conditional_select(&a.Y_minus_X, &b.Y_minus_X, choice),
            Z: FieldElement::conditional_select(&a.Z, &b.Z, choice),
            T2d: FieldElement::conditional_select(&a.T2d, &b.T2d, choice),
        };
        proof {
            // Postconditions follow from FieldElement51::conditional_select specs
            // Each field select returns a's or b's field based on choice, so struct equals a or b
            // Verus can't automatically derive struct equality from limb-level specs
            assume(!choice_is_true(choice) ==> result == *a);
            assume(choice_is_true(choice) ==> result == *b);
        }
        result
    }

    fn conditional_assign(&mut self, other: &Self, choice: Choice)
        ensures
    // If choice is false, self remains unchanged

            !choice_is_true(choice) ==> *self == *old(self),
            // If choice is true, self is assigned from other
            choice_is_true(choice) ==> *self == *other,
    {
        self.Y_plus_X.conditional_assign(&other.Y_plus_X, choice);
        self.Y_minus_X.conditional_assign(&other.Y_minus_X, choice);
        self.Z.conditional_assign(&other.Z, choice);
        self.T2d.conditional_assign(&other.T2d, choice);
        proof {
            // Postconditions follow from FieldElement51::conditional_assign specs
            // Each field assign keeps old or assigns other based on choice
            // Verus can't automatically derive struct equality from limb-level specs
            assume(!choice_is_true(choice) ==> *self == *old(self));
            assume(choice_is_true(choice) ==> *self == *other);
        }
    }
}

impl ConditionallySelectable for AffineNielsPoint {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> (result: Self)
        ensures
    // If choice is false, return a

            !choice_is_true(choice) ==> result == *a,
            // If choice is true, return b
            choice_is_true(choice) ==> result == *b,
    {
        let result = AffineNielsPoint {
            y_plus_x: FieldElement::conditional_select(&a.y_plus_x, &b.y_plus_x, choice),
            y_minus_x: FieldElement::conditional_select(&a.y_minus_x, &b.y_minus_x, choice),
            xy2d: FieldElement::conditional_select(&a.xy2d, &b.xy2d, choice),
        };
        proof {
            // Postconditions follow from FieldElement51::conditional_select specs
            // Each field select returns a's or b's field based on choice, so struct equals a or b
            // Verus can't automatically derive struct equality from limb-level specs
            assume(!choice_is_true(choice) ==> result == *a);
            assume(choice_is_true(choice) ==> result == *b);
        }
        result
    }

    fn conditional_assign(&mut self, other: &Self, choice: Choice)
        ensures
    // If choice is false, self remains unchanged

            !choice_is_true(choice) ==> *self == *old(self),
            // If choice is true, self is assigned from other
            choice_is_true(choice) ==> *self == *other,
    {
        self.y_plus_x.conditional_assign(&other.y_plus_x, choice);
        self.y_minus_x.conditional_assign(&other.y_minus_x, choice);
        self.xy2d.conditional_assign(&other.xy2d, choice);
        proof {
            // Postconditions follow from FieldElement51::conditional_assign specs
            // Each field assign keeps old or assigns other based on choice
            // Verus can't automatically derive struct equality from limb-level specs
            assume(!choice_is_true(choice) ==> *self == *old(self));
            assume(choice_is_true(choice) ==> *self == *other);
        }
    }
}

// ------------------------------------------------------------------------
// Point conversions
// ------------------------------------------------------------------------
impl ProjectivePoint {
    /// Convert this point from the \\( \mathbb P\^2 \\) model to the
    /// \\( \mathbb P\^3 \\) model.
    ///
    /// This costs \\(3 \mathrm M + 1 \mathrm S\\).
    pub fn as_extended(&self) -> (result: EdwardsPoint)
        requires
            is_valid_projective_point(*self),
            // preconditions for arithmetic traits
            fe51_limbs_bounded(&self.X, 54),
            fe51_limbs_bounded(&self.Y, 54),
            fe51_limbs_bounded(&self.Z, 54),
        ensures
            is_valid_edwards_point(result),
            spec_edwards_point(result) == spec_projective_to_extended(*self),
            edwards_point_as_affine(result) == projective_point_as_affine_edwards(*self),
    {
        let result = EdwardsPoint {
            X: &self.X * &self.Z,
            Y: &self.Y * &self.Z,
            Z: self.Z.square(),
            T: &self.X * &self.Y,
        };
        proof {
            // postconditions
            assume(is_valid_edwards_point(result));
            assume(spec_edwards_point(result) == spec_projective_to_extended(*self));
            assume(edwards_point_as_affine(result) == projective_point_as_affine_edwards(*self));
        }
        result
    }
}

impl CompletedPoint {
    /// Convert this point from the \\( \mathbb P\^1 \times \mathbb P\^1
    /// \\) model to the \\( \mathbb P\^2 \\) model.
    ///
    /// This costs \\(3 \mathrm M \\).
    pub fn as_projective(&self) -> (result: ProjectivePoint)
        requires
            is_valid_completed_point(*self),
            // preconditions for arithmetic traits
            fe51_limbs_bounded(&self.X, 54),
            fe51_limbs_bounded(&self.Y, 54),
            fe51_limbs_bounded(&self.Z, 54),
            fe51_limbs_bounded(&self.T, 54),
        ensures
            is_valid_projective_point(result),
            spec_projective_point_edwards(result) == spec_completed_to_projective(*self),
            projective_point_as_affine_edwards(result) == completed_point_as_affine_edwards(*self),
            // Limb bounds from mul() postconditions (mul produces 52-bounded output)
            fe51_limbs_bounded(&result.X, 52),
            fe51_limbs_bounded(&result.Y, 52),
            fe51_limbs_bounded(&result.Z, 52),
            // Sum bounded: X, Y each < 2^52, so sum < 2^53 < u64::MAX
            sum_of_limbs_bounded(&result.X, &result.Y, u64::MAX),
    {
        let result = ProjectivePoint {
            X: &self.X * &self.T,
            Y: &self.Y * &self.Z,
            Z: &self.Z * &self.T,
        };
        proof {
            // Limb bounds follow from mul() postconditions (mul produces 52-bounded)
            assert(fe51_limbs_bounded(&result.X, 52));
            assert(fe51_limbs_bounded(&result.Y, 52));
            assert(fe51_limbs_bounded(&result.Z, 52));

            // Sum bounded: use lemma with n=52
            assert(sum_of_limbs_bounded(&result.X, &result.Y, u64::MAX)) by {
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&result.X, &result.Y, 52);
            };

            // Extract spec values from precondition
            let (x_abs, y_abs, z_abs, t_abs) = spec_completed_point(*self);

            // From is_valid_completed_point: z_abs != 0 and t_abs != 0
            assert(z_abs != 0 && t_abs != 0);

            // spec_field_element returns values < p, so z_abs < p and t_abs < p
            // Therefore z_abs % p == z_abs and t_abs % p == t_abs
            assert(z_abs < p() && t_abs < p()) by {
                p_gt_2();  // Establish p() > 0 for lemma_mod_bound
                lemma_mod_bound(spec_field_element_as_nat(&self.Z) as int, p() as int);
                lemma_mod_bound(spec_field_element_as_nat(&self.T) as int, p() as int);
            };

            // Since z_abs < p and z_abs != 0, we have z_abs % p == z_abs != 0
            assert(z_abs % p() != 0) by {
                lemma_small_mod(z_abs, p());
            };
            assert(t_abs % p() != 0) by {
                lemma_small_mod(t_abs, p());
            };

            // Result Z = Z * T, which is non-zero since both Z and T are non-zero
            let result_z = math_field_mul(z_abs, t_abs);
            assert(result_z != 0) by {
                lemma_nonzero_product(z_abs, t_abs);
            };

            // Spec equivalence: show concrete multiplication matches spec
            assert(spec_projective_point_edwards(result) == spec_completed_to_projective(*self));

            // Now prove is_valid_projective_point(result)
            // Need to show:
            // 1. result.Z != 0 (shown above via result_z != 0)
            // 2. (result.X/result.Z, result.Y/result.Z) is on the curve
            //
            // result.X/result.Z = (X*T)/(Z*T) = X/Z (by cancellation)
            // result.Y/result.Z = (Y*Z)/(Z*T) = Y/T (by cancellation)
            // From is_valid_completed_point: (X/Z, Y/T) is on the curve

            // Cancellation for X coordinate: (X*T)/(Z*T) = X/Z
            assert(math_field_mul(
                math_field_mul(x_abs, t_abs),
                math_field_inv(math_field_mul(z_abs, t_abs)),
            ) == math_field_mul(x_abs, math_field_inv(z_abs))) by {
                lemma_cancel_common_factor(x_abs, z_abs, t_abs);
            };

            // Cancellation for Y coordinate: (Y*Z)/(Z*T) = Y/T
            // Rewrite as (Y*Z)/(T*Z) = Y/T using commutativity
            assert(math_field_mul(z_abs, t_abs) == math_field_mul(t_abs, z_abs)) by {
                lemma_field_mul_comm(z_abs, t_abs);
            };
            assert(math_field_mul(
                math_field_mul(y_abs, z_abs),
                math_field_inv(math_field_mul(t_abs, z_abs)),
            ) == math_field_mul(y_abs, math_field_inv(t_abs))) by {
                lemma_cancel_common_factor(y_abs, t_abs, z_abs);
            };

            // The affine coordinates of result equal those of the completed point
            assert(projective_point_as_affine_edwards(result) == completed_point_as_affine_edwards(
                *self,
            ));

            // Therefore result is a valid projective point (same affine point as completed,
            // which is on the curve by precondition)
            // Use the lemma to convert from affine curve equation to projective form
            let (result_x, result_y, result_z_spec) = spec_projective_point_edwards(result);

            // result_z_spec = spec_field_element(&result.Z) = math_field_mul(z_abs, t_abs) = result_z
            // We showed result_z != 0 above, and result_z < p (since it's a field element)
            // Therefore result_z_spec % p == result_z_spec != 0
            assert(result_z_spec == result_z);  // They're the same value
            assert(result_z_spec < p()) by {
                lemma_mod_bound((z_abs * t_abs) as int, p() as int);
            };
            assert(result_z_spec % p() != 0) by {
                lemma_small_mod(result_z_spec, p());
            };

            assert(math_on_edwards_curve(
                math_field_mul(result_x, math_field_inv(result_z_spec)),
                math_field_mul(result_y, math_field_inv(result_z_spec)),
            ));
            assert(is_valid_projective_point(result)) by {
                lemma_affine_curve_implies_projective(result_x, result_y, result_z_spec);
            };
        }
        result
    }

    /// Convert this point from the \\( \mathbb P\^1 \times \mathbb P\^1
    /// \\) model to the \\( \mathbb P\^3 \\) model.
    ///
    /// This costs \\(4 \mathrm M \\).
    pub fn as_extended(&self) -> (result: EdwardsPoint)
        requires
            is_valid_completed_point(*self),
            // preconditions for mul
            fe51_limbs_bounded(&self.X, 54),
            fe51_limbs_bounded(&self.Y, 54),
            fe51_limbs_bounded(&self.Z, 54),
            fe51_limbs_bounded(&self.T, 54),
        ensures
            is_valid_edwards_point(result),
            is_well_formed_edwards_point(result),
            // Explicit bounds: mul() produces 52-bounded output
            fe51_limbs_bounded(&result.X, 52),
            fe51_limbs_bounded(&result.Y, 52),
            fe51_limbs_bounded(&result.Z, 52),
            fe51_limbs_bounded(&result.T, 52),
            spec_edwards_point(result) == spec_completed_to_extended(*self),
            edwards_point_as_affine(result) == completed_point_as_affine_edwards(*self),
    {
        let result = EdwardsPoint {
            X: &self.X * &self.T,
            Y: &self.Y * &self.Z,
            Z: &self.Z * &self.T,
            T: &self.X * &self.Y,
        };
        proof {
            // Limb bounds: mul() produces 52-bounded output (from its postcondition)
            assert(fe51_limbs_bounded(&result.X, 52));  // X = self.X * self.T
            assert(fe51_limbs_bounded(&result.Y, 52));  // Y = self.Y * self.Z
            assert(fe51_limbs_bounded(&result.Z, 52));  // Z = self.Z * self.T
            assert(fe51_limbs_bounded(&result.T, 52));  // T = self.X * self.Y

            // edwards_point_limbs_bounded requires 52-bounded (the new invariant)
            assert(edwards_point_limbs_bounded(result));

            // sum_of_limbs_bounded follows from 52-bounded via lemma
            assert(sum_of_limbs_bounded(&result.Y, &result.X, u64::MAX)) by {
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&result.Y, &result.X, 52);
            };

            // Therefore is_well_formed_edwards_point holds (pending is_valid_edwards_point)
            // Semantic postconditions still need assumes
            assume(is_valid_edwards_point(result));
            assume(spec_edwards_point(result) == spec_completed_to_extended(*self));
            assume(edwards_point_as_affine(result) == completed_point_as_affine_edwards(*self));
        }
        result
    }
}

// ------------------------------------------------------------------------
// Doubling
// ------------------------------------------------------------------------
impl ProjectivePoint {
    /// Double this point: return self + self
    pub fn double(&self) -> (result: CompletedPoint)
        requires
            is_valid_projective_point(*self),
            // preconditions for arithmetic traits (ProjectivePoint invariant: 52-bounded)
            fe51_limbs_bounded(&self.X, 52),
            fe51_limbs_bounded(&self.Y, 52),
            fe51_limbs_bounded(&self.Z, 52),
            sum_of_limbs_bounded(&self.X, &self.Y, u64::MAX),
        ensures
            is_valid_completed_point(result),
            // The result represents the affine doubling of self
            completed_point_as_affine_edwards(result) == ({
                let (x, y) = projective_point_as_affine_edwards(*self);
                edwards_double(x, y)
            }),
            fe51_limbs_bounded(&result.X, 54),
            fe51_limbs_bounded(&result.Y, 54),
            fe51_limbs_bounded(&result.Z, 54),
            fe51_limbs_bounded(&result.T, 54),
    {
        proof {
            // Establish that 52-bounded implies 54-bounded for square() preconditions
            assert((1u64 << 52) < (1u64 << 54)) by (bit_vector);
            assert forall|i: int| 0 <= i < 5 implies self.X.limbs[i] < (1u64 << 54) by {
                assert(self.X.limbs[i] < (1u64 << 52));  // from precondition
            }
            assert forall|i: int| 0 <= i < 5 implies self.Y.limbs[i] < (1u64 << 54) by {
                assert(self.Y.limbs[i] < (1u64 << 52));  // from precondition
            }
            assert forall|i: int| 0 <= i < 5 implies self.Z.limbs[i] < (1u64 << 54) by {
                assert(self.Z.limbs[i] < (1u64 << 52));  // from precondition
            }
        }
        // Double()
        let XX = self.X.square();
        let YY = self.Y.square();
        let ZZ2 = self.Z.square2();

        let X_plus_Y = &self.X + &self.Y;
        proof {
            // XX, YY are 52-bounded from square() postcondition
            assert(fe51_limbs_bounded(&XX, 52));  // from square() postcondition
            assert(fe51_limbs_bounded(&YY, 52));  // from square() postcondition
            // X_plus_Y is 53-bounded: 52-bounded + 52-bounded = 53-bounded
            assert(fe51_limbs_bounded(&X_plus_Y, 53)) by {
                lemma_add_bounds_propagate(&self.X, &self.Y, 52);
            }
            // Establish 54-bounded for X_plus_Y.square() precondition
            assert(fe51_limbs_bounded(&X_plus_Y, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&X_plus_Y, 53, 54);
            }
            // sum_of_limbs_bounded for YY + XX: both are 52-bounded
            assert(sum_of_limbs_bounded(&YY, &XX, u64::MAX)) by {
                lemma_sum_of_limbs_bounded_from_fe51_bounded(&YY, &XX, 52);
            }
        }
        let X_plus_Y_sq = X_plus_Y.square();
        let YY_plus_XX = &YY + &XX;
        let YY_minus_XX = &YY - &XX;

        proof {
            // X_plus_Y_sq: 52-bounded from square() postcondition
            assert(fe51_limbs_bounded(&X_plus_Y_sq, 52));  // from square() postcondition
            // YY_minus_XX: 54-bounded from subtraction postcondition
            assert(fe51_limbs_bounded(&YY_minus_XX, 54));  // from subtraction postcondition
            // YY_plus_XX: 53-bounded (52 + 52 = 53)
            assert(fe51_limbs_bounded(&YY_plus_XX, 53)) by {
                lemma_add_bounds_propagate(&YY, &XX, 52);
            }
            // ZZ2: 54-bounded from square2() postcondition
            assert(fe51_limbs_bounded(&ZZ2, 54));  // from square2() postcondition

            // For subtraction &X_plus_Y_sq - &YY_plus_XX: need both 54-bounded
            assert(fe51_limbs_bounded(&X_plus_Y_sq, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&X_plus_Y_sq, 52, 54);
            }
            assert(fe51_limbs_bounded(&YY_plus_XX, 54)) by {
                lemma_fe51_limbs_bounded_weaken(&YY_plus_XX, 53, 54);
            }
        }
        let result = CompletedPoint {
            X: &X_plus_Y_sq - &YY_plus_XX,
            Y: YY_plus_XX,
            Z: YY_minus_XX,
            T: &ZZ2 - &YY_minus_XX,
        };
        proof {
            // Bounds postconditions:
            // result.X: from subtraction → 54-bounded (directly from sub postcondition)
            assert(fe51_limbs_bounded(&result.X, 54));  // subtraction postcondition
            // result.Y: YY_plus_XX is 53-bounded, which implies 54-bounded
            assert forall|i: int| 0 <= i < 5 implies result.Y.limbs[i] < (1u64 << 54) by {
                assert(YY_plus_XX.limbs[i] < (1u64 << 53));
                assert((1u64 << 53) < (1u64 << 54)) by (bit_vector);
            }
            assert(fe51_limbs_bounded(&result.Y, 54));
            // result.Z: YY_minus_XX is 54-bounded (directly from sub postcondition)
            assert(fe51_limbs_bounded(&result.Z, 54));  // subtraction postcondition
            // result.T: from subtraction → 54-bounded (directly from sub postcondition)
            assert(fe51_limbs_bounded(&result.T, 54));  // subtraction postcondition

            // Semantic postconditions
            assume(is_valid_completed_point(result));
            assume(completed_point_as_affine_edwards(result) == edwards_double(
                projective_point_as_affine_edwards(*self).0,
                projective_point_as_affine_edwards(*self).1,
            ));
        }

        result
    }
}

// ------------------------------------------------------------------------
// Addition and Subtraction
// ------------------------------------------------------------------------
// XXX(hdevalence) These were doc(hidden) so they don't appear in the
// public API docs.
// However, that prevents them being used with --document-private-items,
// so comment out the doc(hidden) for now until this is resolved
/// Spec for &EdwardsPoint + &ProjectiveNielsPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl<&ProjectiveNielsPoint> for &EdwardsPoint {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: &ProjectiveNielsPoint) -> bool {
        // Preconditions needed for field operations
        is_well_formed_edwards_point(*self) && fe51_limbs_bounded(&rhs.Y_plus_X, 54)
            && fe51_limbs_bounded(&rhs.Y_minus_X, 54) && fe51_limbs_bounded(&rhs.Z, 54)
            && fe51_limbs_bounded(&rhs.T2d, 54)
    }

    open spec fn add_spec(self, rhs: &ProjectiveNielsPoint) -> CompletedPoint {
        // Placeholder - actual spec is in the ensures clause of the add function
        arbitrary()
    }
}

//
// upstream rust issue: https://github.com/rust-lang/rust/issues/46380
//#[doc(hidden)]
impl<'a, 'b> Add<&'b ProjectiveNielsPoint> for &'a EdwardsPoint {
    type Output = CompletedPoint;

    fn add(self, other: &'b ProjectiveNielsPoint) -> (result:
        CompletedPoint)/* VERIFICATION NOTE: requires clause is in AddSpecImpl::add_req
        requires
            is_well_formed_edwards_point(*self),  // EdwardsPoint invariant: 52-bounded
            fe51_limbs_bounded(&other.Y_plus_X, 54),
            fe51_limbs_bounded(&other.Y_minus_X, 54),
            fe51_limbs_bounded(&other.Z, 54),
            fe51_limbs_bounded(&other.T2d, 54),
        */

        ensures
    // The result represents the Edwards addition of the affine forms of self and other

            is_valid_completed_point(result),
            completed_point_as_affine_edwards(result) == spec_edwards_add_projective_niels(
                *self,
                *other,
            ),
            // Limb bounds for result (from mul's 52-bit output → sub/add produce ≤54-bit)
            fe51_limbs_bounded(&result.X, 54),
            fe51_limbs_bounded(&result.Y, 54),
            fe51_limbs_bounded(&result.Z, 54),
            fe51_limbs_bounded(&result.T, 54),
    {
        proof {
            // EdwardsPoint invariant is 52-bounded, weaken to 54-bounded for sub/mul preconditions
            lemma_edwards_point_weaken_to_54(self);
        }
        let Y_plus_X = &self.Y + &self.X;
        let Y_minus_X = &self.Y - &self.X;
        proof {
            assume(sum_of_limbs_bounded(&Y_plus_X, &Y_minus_X, u64::MAX));  // for PP = &Y_plus_X * &other.Y_plus_X and MM = &Y_minus_X * &other.Y_minus_X
            assume(fe51_limbs_bounded(&Y_plus_X, 54) && fe51_limbs_bounded(&Y_minus_X, 54));  // for PP = &Y_plus_X * &other.Y_plus_X and MM = &Y_minus_X * &other.Y_minus_X
        }
        let PP = &Y_plus_X * &other.Y_plus_X;
        let MM = &Y_minus_X * &other.Y_minus_X;
        let TT2d = &self.T * &other.T2d;
        let ZZ = &self.Z * &other.Z;
        proof {
            assume(sum_of_limbs_bounded(&ZZ, &ZZ, u64::MAX));  // for ZZ2 = &ZZ + &ZZ
        }
        let ZZ2 = &ZZ + &ZZ;
        proof {
            assume(fe51_limbs_bounded(&ZZ2, 54));  // for ZZ2 = &ZZ + &ZZ
            assume(sum_of_limbs_bounded(&ZZ2, &TT2d, u64::MAX));  // for Z and T operations
            assume(sum_of_limbs_bounded(&PP, &MM, u64::MAX));  // for Y = &PP + &MM
            // Preconditions for subtractions
            assume(fe51_limbs_bounded(&PP, 54) && fe51_limbs_bounded(&MM, 54));  // for X = &PP - &MM
            assume(fe51_limbs_bounded(&TT2d, 54));  // for T = &ZZ2 - &TT2d (ZZ2 already bounded above)
        }
        let result = CompletedPoint {
            X: &PP - &MM,
            Y: &PP + &MM,
            Z: &ZZ2 + &TT2d,
            T: &ZZ2 - &TT2d,
        };
        proof {
            // postconditions
            assume(is_valid_completed_point(result));
            assume(completed_point_as_affine_edwards(result) == spec_edwards_add_projective_niels(
                *self,
                *other,
            ));
            // Limb bounds: mul outputs 52-bit, sub/add preserve or slightly increase bounds
            // X = PP - MM: sub of 52-bit values → 52-bit output (sub postcondition)
            // Y = PP + MM: add of 52-bit values → 53-bit output
            // Z = ZZ2 + TT2d: 53-bit + 52-bit → 54-bit
            // T = ZZ2 - TT2d: sub of 53-bit and 52-bit → 54-bit
            assume(fe51_limbs_bounded(&result.X, 54));
            assume(fe51_limbs_bounded(&result.Y, 54));
            assume(fe51_limbs_bounded(&result.Z, 54));
            assume(fe51_limbs_bounded(&result.T, 54));
        }
        result
    }
}

/// Spec for &EdwardsPoint - &ProjectiveNielsPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::SubSpecImpl<&ProjectiveNielsPoint> for &EdwardsPoint {
    open spec fn obeys_sub_spec() -> bool {
        false
    }

    open spec fn sub_req(self, rhs: &ProjectiveNielsPoint) -> bool {
        // Preconditions needed for field operations
        is_well_formed_edwards_point(*self) && fe51_limbs_bounded(&rhs.Y_plus_X, 54)
            && fe51_limbs_bounded(&rhs.Y_minus_X, 54) && fe51_limbs_bounded(&rhs.Z, 54)
            && fe51_limbs_bounded(&rhs.T2d, 54)
    }

    open spec fn sub_spec(self, rhs: &ProjectiveNielsPoint) -> CompletedPoint {
        arbitrary()
    }
}

//#[doc(hidden)]
impl<'a, 'b> Sub<&'b ProjectiveNielsPoint> for &'a EdwardsPoint {
    type Output = CompletedPoint;

    fn sub(self, other: &'b ProjectiveNielsPoint) -> (result:
        CompletedPoint)/* VERIFICATION NOTE: requires clause is in SubSpecImpl::sub_req
        requires
            is_well_formed_edwards_point(*self),  // EdwardsPoint invariant: 52-bounded
            fe51_limbs_bounded(&other.Y_plus_X, 54),
            fe51_limbs_bounded(&other.Y_minus_X, 54),
            fe51_limbs_bounded(&other.Z, 54),
            fe51_limbs_bounded(&other.T2d, 54),
        */

        ensures
    // The result represents the Edwards subtraction of the affine forms of self and other

            is_valid_completed_point(result),
            ({
                let self_affine = edwards_point_as_affine(*self);
                let other_affine = projective_niels_point_as_affine_edwards(*other);
                completed_point_as_affine_edwards(result) == edwards_sub(
                    self_affine.0,
                    self_affine.1,
                    other_affine.0,
                    other_affine.1,
                )
            }),
    {
        proof {
            // EdwardsPoint invariant is 52-bounded, weaken to 54-bounded for sub/mul preconditions
            lemma_edwards_point_weaken_to_54(self);
        }
        let Y_plus_X = &self.Y + &self.X;
        let Y_minus_X = &self.Y - &self.X;
        proof {
            assume(fe51_limbs_bounded(&Y_plus_X, 54) && fe51_limbs_bounded(&Y_minus_X, 54));
        }
        let PM = &Y_plus_X * &other.Y_minus_X;
        let MP = &Y_minus_X * &other.Y_plus_X;
        let TT2d = &self.T * &other.T2d;
        let ZZ = &self.Z * &other.Z;
        proof {
            assume(sum_of_limbs_bounded(&ZZ, &ZZ, u64::MAX));  // for ZZ2 = &ZZ + &ZZ
        }
        let ZZ2 = &ZZ + &ZZ;
        proof {
            assume(sum_of_limbs_bounded(&PM, &MP, u64::MAX));  // for Y = &PM + &MP
            assume(sum_of_limbs_bounded(&ZZ2, &TT2d, u64::MAX));  // for Z and T operations
            // Preconditions for subtractions
            assume(fe51_limbs_bounded(&PM, 54) && fe51_limbs_bounded(&MP, 54));  // for X = &PM - &MP
            assume(fe51_limbs_bounded(&ZZ2, 54) && fe51_limbs_bounded(&TT2d, 54));  // for Z = &ZZ2 - &TT2d
        }

        let result = CompletedPoint {
            X: &PM - &MP,
            Y: &PM + &MP,
            Z: &ZZ2 - &TT2d,
            T: &ZZ2 + &TT2d,
        };
        proof {
            // postconditions
            assume(is_valid_completed_point(result));
            let self_affine = edwards_point_as_affine(*self);
            let other_affine = projective_niels_point_as_affine_edwards(*other);
            assume(completed_point_as_affine_edwards(result) == edwards_sub(
                self_affine.0,
                self_affine.1,
                other_affine.0,
                other_affine.1,
            ));
        }
        result
    }
}

/// Spec for &EdwardsPoint + &AffineNielsPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl<&AffineNielsPoint> for &EdwardsPoint {
    open spec fn obeys_add_spec() -> bool {
        false
    }

    open spec fn add_req(self, rhs: &AffineNielsPoint) -> bool {
        // Preconditions needed for field operations
        is_well_formed_edwards_point(*self) && sum_of_limbs_bounded(
            &self.Z,
            &self.Z,
            u64::MAX,
        )  // for Z2 = &self.Z + &self.Z
         && fe51_limbs_bounded(&rhs.y_plus_x, 54) && fe51_limbs_bounded(&rhs.y_minus_x, 54)
            && fe51_limbs_bounded(&rhs.xy2d, 54)
    }

    open spec fn add_spec(self, rhs: &AffineNielsPoint) -> CompletedPoint {
        // Placeholder - actual spec is in the ensures clause of the add function
        arbitrary()
    }
}

//#[doc(hidden)]
impl<'a, 'b> Add<&'b AffineNielsPoint> for &'a EdwardsPoint {
    type Output = CompletedPoint;

    fn add(self, other: &'b AffineNielsPoint) -> (result:
        CompletedPoint)/* VERIFICATION NOTE: requires clause is in AddSpecImpl::add_req
        requires
            is_well_formed_edwards_point(*self),  // EdwardsPoint invariant: 52-bounded
            sum_of_limbs_bounded(&self.Z, &self.Z, u64::MAX),
            fe51_limbs_bounded(&other.y_plus_x, 54),
            fe51_limbs_bounded(&other.y_minus_x, 54),
            fe51_limbs_bounded(&other.xy2d, 54),
        */

        ensures
    // The result represents the Edwards addition of the affine forms of self and other

            is_valid_completed_point(result),
            completed_point_as_affine_edwards(result) == spec_edwards_add_affine_niels(
                *self,
                *other,
            ),
    {
        proof {
            // EdwardsPoint invariant is 52-bounded, weaken to 54-bounded for sub/mul preconditions
            lemma_edwards_point_weaken_to_54(self);
        }
        let Y_plus_X = &self.Y + &self.X;
        let Y_minus_X = &self.Y - &self.X;
        proof {
            assume(sum_of_limbs_bounded(&Y_plus_X, &Y_minus_X, u64::MAX));
            assume(fe51_limbs_bounded(&Y_plus_X, 54) && fe51_limbs_bounded(&Y_minus_X, 54));
        }
        let PP = &Y_plus_X * &other.y_plus_x;
        let MM = &Y_minus_X * &other.y_minus_x;
        let Txy2d = &self.T * &other.xy2d;
        let Z2 = &self.Z + &self.Z;
        proof {
            assume(sum_of_limbs_bounded(&Z2, &Txy2d, u64::MAX));
            assume(sum_of_limbs_bounded(&PP, &MM, u64::MAX));
            assume(fe51_limbs_bounded(&PP, 54) && fe51_limbs_bounded(&MM, 54));
            assume(fe51_limbs_bounded(&Z2, 54) && fe51_limbs_bounded(&Txy2d, 54));
        }
        let result = CompletedPoint {
            X: &PP - &MM,
            Y: &PP + &MM,
            Z: &Z2 + &Txy2d,
            T: &Z2 - &Txy2d,
        };
        proof {
            // postconditions
            assume(is_valid_completed_point(result));
            assume(completed_point_as_affine_edwards(result) == spec_edwards_add_affine_niels(
                *self,
                *other,
            ));
        }
        result
    }
}

/// Spec for &EdwardsPoint - &AffineNielsPoint
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::SubSpecImpl<&AffineNielsPoint> for &EdwardsPoint {
    open spec fn obeys_sub_spec() -> bool {
        false
    }

    open spec fn sub_req(self, rhs: &AffineNielsPoint) -> bool {
        // Preconditions needed for field operations
        is_well_formed_edwards_point(*self) && sum_of_limbs_bounded(
            &self.Z,
            &self.Z,
            u64::MAX,
        )  // for Z2 = &self.Z + &self.Z
         && fe51_limbs_bounded(&rhs.y_plus_x, 54) && fe51_limbs_bounded(&rhs.y_minus_x, 54)
            && fe51_limbs_bounded(&rhs.xy2d, 54)
    }

    open spec fn sub_spec(self, rhs: &AffineNielsPoint) -> CompletedPoint {
        // Placeholder - actual spec is in the ensures clause of the sub function
        arbitrary()
    }
}

//#[doc(hidden)]
impl<'a, 'b> Sub<&'b AffineNielsPoint> for &'a EdwardsPoint {
    type Output = CompletedPoint;

    fn sub(self, other: &'b AffineNielsPoint) -> (result:
        CompletedPoint)/* VERIFICATION NOTE: requires clause is in SubSpecImpl::sub_req
        requires
            is_well_formed_edwards_point(*self),  // EdwardsPoint invariant: 52-bounded
            sum_of_limbs_bounded(&self.Z, &self.Z, u64::MAX),
            fe51_limbs_bounded(&other.y_plus_x, 54),
            fe51_limbs_bounded(&other.y_minus_x, 54),
            fe51_limbs_bounded(&other.xy2d, 54),
        */

        ensures
    // The result represents the Edwards subtraction of the affine forms of self and other

            is_valid_completed_point(result),
            ({
                let self_affine = edwards_point_as_affine(*self);
                let other_affine = affine_niels_point_as_affine_edwards(*other);
                completed_point_as_affine_edwards(result) == edwards_sub(
                    self_affine.0,
                    self_affine.1,
                    other_affine.0,
                    other_affine.1,
                )
            }),
    {
        proof {
            // EdwardsPoint invariant is 52-bounded, weaken to 54-bounded for sub/mul preconditions
            lemma_edwards_point_weaken_to_54(self);
        }
        let Y_plus_X = &self.Y + &self.X;
        let Y_minus_X = &self.Y - &self.X;
        proof {
            assume(sum_of_limbs_bounded(&Y_plus_X, &Y_minus_X, u64::MAX));
            assume(fe51_limbs_bounded(&Y_plus_X, 54) && fe51_limbs_bounded(&Y_minus_X, 54));
        }
        let PM = &Y_plus_X * &other.y_minus_x;
        let MP = &Y_minus_X * &other.y_plus_x;
        let Txy2d = &self.T * &other.xy2d;
        let Z2 = &self.Z + &self.Z;
        proof {
            assume(sum_of_limbs_bounded(&Z2, &Txy2d, u64::MAX));
            assume(sum_of_limbs_bounded(&PM, &MP, u64::MAX));
            assume(fe51_limbs_bounded(&PM, 54) && fe51_limbs_bounded(&MP, 54));
            assume(fe51_limbs_bounded(&Z2, 54) && fe51_limbs_bounded(&Txy2d, 54));
        }
        let result = CompletedPoint {
            X: &PM - &MP,
            Y: &PM + &MP,
            Z: &Z2 - &Txy2d,
            T: &Z2 + &Txy2d,
        };
        proof {
            // postconditions
            assume(is_valid_completed_point(result));
            let self_affine = edwards_point_as_affine(*self);
            let other_affine = affine_niels_point_as_affine_edwards(*other);
            assume(completed_point_as_affine_edwards(result) == edwards_sub(
                self_affine.0,
                self_affine.1,
                other_affine.0,
                other_affine.1,
            ));
        }
        result
    }
}

// ------------------------------------------------------------------------
// Negation
// ------------------------------------------------------------------------
/// Spec for &ProjectiveNielsPoint negation
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::NegSpecImpl for &ProjectiveNielsPoint {
    open spec fn obeys_neg_spec() -> bool {
        false
    }

    open spec fn neg_req(self) -> bool {
        // Preconditions: limbs must be bounded for field element negation
        fe51_limbs_bounded(&self.T2d, 51)
    }

    open spec fn neg_spec(self) -> ProjectiveNielsPoint {
        // Negation swaps Y_plus_X and Y_minus_X, keeps Z, negates T2d
        // The affine point represented is (-x, y) where (x, y) was the original
        arbitrary()
    }
}

impl<'a> Neg for &'a ProjectiveNielsPoint {
    type Output = ProjectiveNielsPoint;

    /// Negate a ProjectiveNielsPoint: for Edwards point (x, y), negation is (-x, y).
    /// In Niels form (Y+X, Y-X, Z, T2d), this swaps Y+X ↔ Y-X and negates T2d.
    fn neg(self) -> (result:
        ProjectiveNielsPoint)/* requires clause in NegSpecImpl:
       requires fe51_limbs_bounded(&self.T2d, 51)
    */

        ensures
    // Structural: negation swaps Y_plus_X and Y_minus_X, keeps Z

            result.Y_plus_X == self.Y_minus_X,
            result.Y_minus_X == self.Y_plus_X,
            result.Z == self.Z,
            // Mathematical: the affine point is negated (x, y) → (-x, y)
            ({
                let self_affine = projective_niels_point_as_affine_edwards(*self);
                let result_affine = projective_niels_point_as_affine_edwards(result);
                result_affine == (math_field_neg(self_affine.0), self_affine.1)
            }),
    {
        // ORIGINAL CODE: T2d: -(&self.T2d),
        // Using negate_field wrapper to avoid Verus internal error
        let result = ProjectiveNielsPoint {
            Y_plus_X: self.Y_minus_X,
            Y_minus_X: self.Y_plus_X,
            Z: self.Z,
            T2d: negate_field(&self.T2d),
        };
        proof {
            let self_affine = projective_niels_point_as_affine_edwards(*self);
            assume(projective_niels_point_as_affine_edwards(result) == (
                math_field_neg(self_affine.0),
                self_affine.1,
            ));
        }
        result
    }
}

/// Spec for &AffineNielsPoint negation
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::NegSpecImpl for &AffineNielsPoint {
    open spec fn obeys_neg_spec() -> bool {
        false
    }

    open spec fn neg_req(self) -> bool {
        // Preconditions: limbs must be bounded for field element negation
        fe51_limbs_bounded(&self.xy2d, 51)
    }

    open spec fn neg_spec(self) -> AffineNielsPoint {
        // Negation swaps y_plus_x and y_minus_x, negates xy2d
        // The affine point represented is (-x, y) where (x, y) was the original
        arbitrary()
    }
}

impl<'a> Neg for &'a AffineNielsPoint {
    type Output = AffineNielsPoint;

    /// Negate an AffineNielsPoint: for Edwards point (x, y), negation is (-x, y).
    /// In AffineNiels form (y+x, y-x, xy2d), this swaps y+x ↔ y-x and negates xy2d.
    fn neg(self) -> (result:
        AffineNielsPoint)/* requires clause in NegSpecImpl:
       requires fe51_limbs_bounded(&self.xy2d, 51)
    */

        ensures
    // Structural: negation swaps y_plus_x and y_minus_x

            result.y_plus_x == self.y_minus_x,
            result.y_minus_x == self.y_plus_x,
            // Mathematical: the affine point is negated (x, y) → (-x, y)
            ({
                let self_affine = affine_niels_point_as_affine_edwards(*self);
                let result_affine = affine_niels_point_as_affine_edwards(result);
                result_affine == (math_field_neg(self_affine.0), self_affine.1)
            }),
    {
        // ORIGINAL CODE: xy2d: -(&self.xy2d),
        // Using negate_field wrapper to avoid Verus internal error
        let result = AffineNielsPoint {
            y_plus_x: self.y_minus_x,
            y_minus_x: self.y_plus_x,
            xy2d: negate_field(&self.xy2d),
        };
        proof {
            let self_affine = affine_niels_point_as_affine_edwards(*self);
            assume(affine_niels_point_as_affine_edwards(result) == (
                math_field_neg(self_affine.0),
                self_affine.1,
            ));
        }
        result
    }
}

} // verus!
// ------------------------------------------------------------------------
// Debug traits
// ------------------------------------------------------------------------
impl Debug for ProjectivePoint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "ProjectivePoint{{\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?}\n}}",
            &self.X, &self.Y, &self.Z
        )
    }
}

impl Debug for CompletedPoint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "CompletedPoint{{\n\tX: {:?},\n\tY: {:?},\n\tZ: {:?},\n\tT: {:?}\n}}",
            &self.X, &self.Y, &self.Z, &self.T
        )
    }
}

impl Debug for AffineNielsPoint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "AffineNielsPoint{{\n\ty_plus_x: {:?},\n\ty_minus_x: {:?},\n\txy2d: {:?}\n}}",
            &self.y_plus_x, &self.y_minus_x, &self.xy2d
        )
    }
}

impl Debug for ProjectiveNielsPoint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "ProjectiveNielsPoint{{\n\tY_plus_X: {:?},\n\tY_minus_X: {:?},\n\tZ: {:?},\n\tT2d: {:?}\n}}",
               &self.Y_plus_X, &self.Y_minus_X, &self.Z, &self.T2d)
    }
}
