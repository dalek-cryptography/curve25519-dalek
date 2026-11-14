/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Coords.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
public section

/-! # Twisted Edwards models: Niels coordinates

The two Niels forms of curve25519-dalek's `curve_models.rs` (Hisil–Wong–Carter–Dawson 2008),
alongside the projective, extended and completed coordinates of
`EllipticCurve.TwistedEdwards.Coords.Defs`:

* `E.ProjectiveNiels`: `(Y + X : Y - X : Z : 2 d T)` of an extended point;
* `E.AffineNiels`: `(y + x, y - x, 2 d x y)` of an affine point.

Each is a plain structure of field elements, as in the library, with

* an exposed validity predicate `OnCurve`, stated with the affine point, restated without
  division by `onCurve_iff_homogeneous` (away from `2`), and decided through that form;
* a total hidden `toPoint` into `E.Point`: the affine point when `OnCurve`, and `(0, 1)`
  otherwise (the neutral element `0` when `E` is complete); characterised by `toPoint_x`,
  `toPoint_y`, `toPoint_of_not_onCurve`, `toPoint_eq_zero_of_not_onCurve`, for any model.

The conversions into them (`Extended.toProjectiveNiels`, `Extended.toAffineNiels`,
`Point.toAffineNiels`), the identities and the negations are the exposed formulas the code
computes; their `onCurve_*` and `toPoint_*`
lemmas are in `Curve25519.Models.TwistedEdwards.Coords.Lemmas`. The mixed additions with Niels
points are in `Curve25519.Models.TwistedEdwards.Formulas.*`. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F)

/-! ### The coordinate systems -/

/-- Projective Niels coordinates `(Y + X : Y - X : Z : 2 d T)` of an extended point
(curve25519-dalek's `ProjectiveNielsPoint`). -/
@[ext] structure ProjectiveNiels (E : TwistedEdwardsModel F) where
  /-- `Y + X`. -/
  YPlusX : F
  /-- `Y - X`. -/
  YMinusX : F
  /-- The `Z`-coordinate. -/
  Z : F
  /-- `2 d T`. -/
  T2d : F
  deriving DecidableEq

/-- Affine Niels coordinates `(y + x, y - x, 2 d x y)` of an affine point (curve25519-dalek's
`AffineNielsPoint`). -/
@[ext] structure AffineNiels (E : TwistedEdwardsModel F) where
  /-- `y + x`. -/
  yPlusX : F
  /-- `y - x`. -/
  yMinusX : F
  /-- `2 d x y`. -/
  xy2d : F
  deriving DecidableEq

variable {E}

/-! ### From extended coordinates -/

namespace Extended

/-- The projective Niels form `(Y + X : Y - X : Z : T (2 d))`
(`EdwardsPoint::as_projective_niels`, with `EDWARDS_D2 = 2 d`). -/
@[expose] def toProjectiveNiels (P : E.Extended) : E.ProjectiveNiels :=
  ⟨P.Y + P.X, P.Y - P.X, P.Z, P.T * (2 * E.d)⟩

/-- The affine Niels form, through the inverse of `Z` (`EdwardsPoint::as_affine_niels`):
`x = X Z⁻¹`, `y = Y Z⁻¹`, result `(y + x, y - x, x y (2 d))`. -/
@[expose] def toAffineNiels (P : E.Extended) : E.AffineNiels :=
  let recip := P.Z⁻¹
  let x := P.X * recip
  let y := P.Y * recip
  ⟨y + x, y - x, x * y * (2 * E.d)⟩

end Extended

/-! ### Projective Niels coordinates -/

namespace ProjectiveNiels

/-- The `X`-coordinate `((Y + X) - (Y - X)) / 2` recovered from the Niels form. -/
@[expose] def X (P : E.ProjectiveNiels) : F :=
  (P.YPlusX - P.YMinusX) / 2

/-- The `Y`-coordinate `((Y + X) + (Y - X)) / 2` recovered from the Niels form. -/
@[expose] def Y (P : E.ProjectiveNiels) : F :=
  (P.YPlusX + P.YMinusX) / 2

/-- `(Y + X : Y - X : Z : T2d)` represents a point of `E`: `Z ≠ 0`, `(X / Z, Y / Z)` satisfies
the equation (`X`, `Y` recovered from the Niels form), and `T2d Z = 2 d X Y`. -/
@[expose] def OnCurve (P : E.ProjectiveNiels) : Prop :=
  P.Z ≠ 0 ∧ E.Equation (P.X / P.Z) (P.Y / P.Z) ∧ P.T2d * P.Z = 2 * E.d * P.X * P.Y

/-- `OnCurve` without division, in terms of `X' = 2 X = (Y + X) - (Y - X)` and
`Y' = 2 Y = (Y + X) + (Y - X)` (in characteristic `≠ 2`):
`4 a X'² Z² + 4 Y'² Z² = 16 Z⁴ + d X'² Y'²` and `2 T2d Z = d X' Y'`. -/
theorem onCurve_iff_homogeneous [NeZero (2 : F)] (P : E.ProjectiveNiels) :
    P.OnCurve ↔ P.Z ≠ 0 ∧
      4 * E.a * (P.YPlusX - P.YMinusX) ^ 2 * P.Z ^ 2 + 4 * (P.YPlusX + P.YMinusX) ^ 2 * P.Z ^ 2 =
        16 * P.Z ^ 4 + E.d * (P.YPlusX - P.YMinusX) ^ 2 * (P.YPlusX + P.YMinusX) ^ 2 ∧
      2 * P.T2d * P.Z = E.d * (P.YPlusX - P.YMinusX) * (P.YPlusX + P.YMinusX) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 * 2 * 2 * 2 by norm_num]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2
  have hX : P.YPlusX - P.YMinusX = 2 * P.X := (mul_div_cancel₀ _ h2).symm
  have hY : P.YPlusX + P.YMinusX = 2 * P.Y := (mul_div_cancel₀ _ h2).symm
  rw [hX, hY]
  unfold OnCurve
  constructor
  · rintro ⟨hZ, h, hT⟩
    rw [equation_div_iff E hZ hZ] at h
    exact ⟨hZ, by linear_combination 16 * h, by linear_combination 2 * hT⟩
  · rintro ⟨hZ, h, hT⟩
    refine ⟨hZ, (E.equation_div_iff hZ hZ).mpr ?_, ?_⟩
    · apply mul_left_cancel₀ h16
      linear_combination h
    · apply mul_left_cancel₀ h2
      linear_combination hT

/-- `OnCurve` is decidable away from `2` through its form without division
(`onCurve_iff_homogeneous`), so that the kernel can evaluate it. -/
instance instDecidableOnCurve [DecidableEq F] [NeZero (2 : F)] (P : E.ProjectiveNiels) :
    Decidable P.OnCurve :=
  decidable_of_iff _ (onCurve_iff_homogeneous P).symm

open scoped Classical in
/-- The point represented by `(Y + X : Y - X : Z : T2d)`: `(X / Z, Y / Z)` when `OnCurve`, and
`(0, 1)` otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`,
`toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.ProjectiveNiels) : E.Point :=
  if h : P.OnCurve then ⟨P.X / P.Z, P.Y / P.Z, h.2.1⟩ else ⟨0, 1, E.equation_zero_one⟩

/-- The `x`-coordinate of the point represented by a projective Niels point is `X / Z`. -/
theorem toPoint_x {P : E.ProjectiveNiels} (h : P.OnCurve) : P.toPoint.x = P.X / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by a projective Niels point is `Y / Z`. -/
theorem toPoint_y {P : E.ProjectiveNiels} (h : P.OnCurve) : P.toPoint.y = P.Y / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `(0, 1)`. -/
theorem toPoint_of_not_onCurve {P : E.ProjectiveNiels} (h : ¬ P.OnCurve) :
    P.toPoint = ⟨0, 1, E.equation_zero_one⟩ := by
  unfold toPoint
  rw [dite_eq_right h]

/-- Off the curve, `toPoint` is `0` on a complete model. -/
theorem toPoint_eq_zero_of_not_onCurve [E.IsComplete] {P : E.ProjectiveNiels}
    (h : ¬ P.OnCurve) : P.toPoint = 0 := by
  rw [toPoint_of_not_onCurve h, zero_eq_mk]

/-- The identity `(1 : 1 : 1 : 0)` (`ProjectiveNielsPoint::identity`). -/
@[expose] def identity : E.ProjectiveNiels :=
  ⟨1, 1, 1, 0⟩

/-- Negation: swap `Y + X` and `Y - X`, negate `T2d` (`Neg for ProjectiveNielsPoint`). -/
@[expose] def neg (P : E.ProjectiveNiels) : E.ProjectiveNiels :=
  ⟨P.YMinusX, P.YPlusX, P.Z, -P.T2d⟩

end ProjectiveNiels

/-! ### Affine Niels coordinates -/

namespace AffineNiels

/-- The `x`-coordinate `((y + x) - (y - x)) / 2` recovered from the Niels form. -/
@[expose] def x (P : E.AffineNiels) : F :=
  (P.yPlusX - P.yMinusX) / 2

/-- The `y`-coordinate `((y + x) + (y - x)) / 2` recovered from the Niels form. -/
@[expose] def y (P : E.AffineNiels) : F :=
  (P.yPlusX + P.yMinusX) / 2

/-- `(y + x, y - x, xy2d)` represents a point of `E`: `(x, y)` satisfies the equation (`x`, `y`
recovered from the Niels form) and `xy2d = 2 d x y`. -/
@[expose] def OnCurve (P : E.AffineNiels) : Prop :=
  E.Equation P.x P.y ∧ P.xy2d = 2 * E.d * P.x * P.y

/-- `OnCurve` without division, in terms of `x' = 2 x = (y + x) - (y - x)` and
`y' = 2 y = (y + x) + (y - x)` (in characteristic `≠ 2`): `4 a x'² + 4 y'² = 16 + d x'² y'²`
and `2 xy2d = d x' y'`. -/
theorem onCurve_iff_homogeneous [NeZero (2 : F)] (P : E.AffineNiels) :
    P.OnCurve ↔
      4 * E.a * (P.yPlusX - P.yMinusX) ^ 2 + 4 * (P.yPlusX + P.yMinusX) ^ 2 =
        16 + E.d * (P.yPlusX - P.yMinusX) ^ 2 * (P.yPlusX + P.yMinusX) ^ 2 ∧
      2 * P.xy2d = E.d * (P.yPlusX - P.yMinusX) * (P.yPlusX + P.yMinusX) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 * 2 * 2 * 2 by norm_num]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2
  have hx : P.yPlusX - P.yMinusX = 2 * P.x := (mul_div_cancel₀ _ h2).symm
  have hy : P.yPlusX + P.yMinusX = 2 * P.y := (mul_div_cancel₀ _ h2).symm
  rw [hx, hy]
  unfold OnCurve Equation
  constructor
  · rintro ⟨h, hT⟩
    exact ⟨by linear_combination 16 * h, by linear_combination 2 * hT⟩
  · rintro ⟨h, hT⟩
    refine ⟨?_, ?_⟩
    · apply mul_left_cancel₀ h16
      linear_combination h
    · apply mul_left_cancel₀ h2
      linear_combination hT

/-- `OnCurve` is decidable away from `2` through its form without division
(`onCurve_iff_homogeneous`), so that the kernel can evaluate it. -/
instance instDecidableOnCurve [DecidableEq F] [NeZero (2 : F)] (P : E.AffineNiels) :
    Decidable P.OnCurve :=
  decidable_of_iff _ (onCurve_iff_homogeneous P).symm

open scoped Classical in
/-- The point represented by `(y + x, y - x, xy2d)`: `(x, y)` when `OnCurve`, and `(0, 1)`
otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.AffineNiels) : E.Point :=
  if h : P.OnCurve then ⟨P.x, P.y, h.1⟩ else ⟨0, 1, E.equation_zero_one⟩

/-- The `x`-coordinate of the point represented by an affine Niels point is `x`. -/
theorem toPoint_x {P : E.AffineNiels} (h : P.OnCurve) : P.toPoint.x = P.x := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by an affine Niels point is `y`. -/
theorem toPoint_y {P : E.AffineNiels} (h : P.OnCurve) : P.toPoint.y = P.y := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `(0, 1)`. -/
theorem toPoint_of_not_onCurve {P : E.AffineNiels} (h : ¬ P.OnCurve) :
    P.toPoint = ⟨0, 1, E.equation_zero_one⟩ := by
  unfold toPoint
  rw [dite_eq_right h]

/-- Off the curve, `toPoint` is `0` on a complete model. -/
theorem toPoint_eq_zero_of_not_onCurve [E.IsComplete] {P : E.AffineNiels} (h : ¬ P.OnCurve) :
    P.toPoint = 0 := by
  rw [toPoint_of_not_onCurve h, zero_eq_mk]

/-- The identity `(1, 1, 0)` (`AffineNielsPoint::identity`). -/
@[expose] def identity : E.AffineNiels :=
  ⟨1, 1, 0⟩

/-- Negation: swap `y + x` and `y - x`, negate `xy2d` (`Neg for AffineNielsPoint`). -/
@[expose] def neg (P : E.AffineNiels) : E.AffineNiels :=
  ⟨P.yMinusX, P.yPlusX, -P.xy2d⟩

end AffineNiels

/-! ### From affine points -/

namespace Point

/-- Affine Niels coordinates `(y + x, y - x, x y (2 d))` of an affine point. -/
@[expose] def toAffineNiels (P : E.Point) : E.AffineNiels :=
  ⟨P.y + P.x, P.y - P.x, P.x * P.y * (2 * E.d)⟩

end Point

end TwistedEdwardsModel
