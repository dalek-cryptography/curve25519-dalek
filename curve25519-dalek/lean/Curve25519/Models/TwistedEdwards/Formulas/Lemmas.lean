/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Models.TwistedEdwards.Formulas.Defs
public import EllipticCurve.TwistedEdwards.Formulas.Lemmas
import Curve25519.Models.TwistedEdwards.Coords.Lemmas
import Mathlib.Tactic.Ring
public section

/-! # Twisted Edwards models: mixed additions with Niels points, correctness

The audited statements about the mixed additions of
`Curve25519.Models.TwistedEdwards.Formulas.Defs`, on a complete model with `a = -1`
(`ha : E.a = -1`): each sends points on the curve to points on the curve
(`addProjectiveNiels_onCurve`, …) and represents the sum or difference of the represented points
(`toPoint_addProjectiveNiels`, …).

Each formula produces, in terms of the represented points, a nonzero multiple of the completed
sum, which `Completed.onCurve_and_toPoint_eq_add` of
`EllipticCurve.TwistedEdwards.Formulas.Lemmas` recognises; the coordinates of the inputs are
eliminated through `X_eq_toPoint_x_mul_Z`, `YPlusX_eq`, …
(`Curve25519.Models.TwistedEdwards.Coords.Lemmas`), after which each identity is polynomial
(`ring`). -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] [NeZero (6 : F)] {E : TwistedEdwardsModel F} [E.IsComplete]

namespace Extended

/-! ### Mixed additions (`a = -1`) -/

variable {P : E.Extended}

private theorem addProjectiveNiels_spec (ha : E.a = -1) {Q : E.ProjectiveNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.addProjectiveNiels Q).OnCurve ∧
      (P.addProjectiveNiels Q).toPoint = P.toPoint + Q.toPoint := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  refine Completed.onCurve_and_toPoint_eq_add (mul_ne_zero (mul_ne_zero h2 hP.1) hQ.1) P.toPoint
    Q.toPoint ?_ ?_ ?_ ?_ <;>
  · simp only [addProjectiveNiels, X_eq_toPoint_x_mul_Z hP, Y_eq_toPoint_y_mul_Z hP,
      T_eq_toPoint_x_mul_y_mul_Z hP, ProjectiveNiels.YPlusX_eq hQ, ProjectiveNiels.YMinusX_eq hQ,
      ProjectiveNiels.T2d_eq hQ, addDen₁, addDen₂, ha]
    ring

/-- `EdwardsPoint + ProjectiveNielsPoint` sends points on the curve to points on the curve
(`a = -1`). -/
theorem addProjectiveNiels_onCurve (ha : E.a = -1) {Q : E.ProjectiveNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.addProjectiveNiels Q).OnCurve :=
  (addProjectiveNiels_spec ha hP hQ).1

/-- `EdwardsPoint + ProjectiveNielsPoint` adds the represented points (`a = -1`). -/
theorem toPoint_addProjectiveNiels (ha : E.a = -1) {Q : E.ProjectiveNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.addProjectiveNiels Q).toPoint = P.toPoint + Q.toPoint :=
  (addProjectiveNiels_spec ha hP hQ).2

private theorem subProjectiveNiels_spec (ha : E.a = -1) {Q : E.ProjectiveNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.subProjectiveNiels Q).OnCurve ∧
      (P.subProjectiveNiels Q).toPoint = P.toPoint - Q.toPoint := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  rw [sub_eq_add_neg]
  refine Completed.onCurve_and_toPoint_eq_add (mul_ne_zero (mul_ne_zero h2 hP.1) hQ.1) P.toPoint
    (-Q.toPoint) ?_ ?_ ?_ ?_ <;>
  · simp only [subProjectiveNiels, X_eq_toPoint_x_mul_Z hP, Y_eq_toPoint_y_mul_Z hP,
      T_eq_toPoint_x_mul_y_mul_Z hP, ProjectiveNiels.YPlusX_eq hQ, ProjectiveNiels.YMinusX_eq hQ,
      ProjectiveNiels.T2d_eq hQ, addDen₁, addDen₂, ha, neg_x, neg_y]
    ring

/-- `EdwardsPoint - ProjectiveNielsPoint` sends points on the curve to points on the curve
(`a = -1`). -/
theorem subProjectiveNiels_onCurve (ha : E.a = -1) {Q : E.ProjectiveNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.subProjectiveNiels Q).OnCurve :=
  (subProjectiveNiels_spec ha hP hQ).1

/-- `EdwardsPoint - ProjectiveNielsPoint` subtracts the represented points (`a = -1`). -/
theorem toPoint_subProjectiveNiels (ha : E.a = -1) {Q : E.ProjectiveNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.subProjectiveNiels Q).toPoint = P.toPoint - Q.toPoint :=
  (subProjectiveNiels_spec ha hP hQ).2

private theorem addAffineNiels_spec (ha : E.a = -1) {Q : E.AffineNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.addAffineNiels Q).OnCurve ∧
      (P.addAffineNiels Q).toPoint = P.toPoint + Q.toPoint := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  refine Completed.onCurve_and_toPoint_eq_add (mul_ne_zero h2 hP.1) P.toPoint Q.toPoint
    ?_ ?_ ?_ ?_ <;>
  · simp only [addAffineNiels, X_eq_toPoint_x_mul_Z hP, Y_eq_toPoint_y_mul_Z hP,
      T_eq_toPoint_x_mul_y_mul_Z hP, AffineNiels.yPlusX_eq hQ, AffineNiels.yMinusX_eq hQ,
      AffineNiels.xy2d_eq hQ, addDen₁, addDen₂, ha]
    ring

/-- `EdwardsPoint + AffineNielsPoint` sends points on the curve to points on the curve
(`a = -1`). -/
theorem addAffineNiels_onCurve (ha : E.a = -1) {Q : E.AffineNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.addAffineNiels Q).OnCurve :=
  (addAffineNiels_spec ha hP hQ).1

/-- `EdwardsPoint + AffineNielsPoint` adds the represented points (`a = -1`). -/
theorem toPoint_addAffineNiels (ha : E.a = -1) {Q : E.AffineNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.addAffineNiels Q).toPoint = P.toPoint + Q.toPoint :=
  (addAffineNiels_spec ha hP hQ).2

private theorem subAffineNiels_spec (ha : E.a = -1) {Q : E.AffineNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.subAffineNiels Q).OnCurve ∧
      (P.subAffineNiels Q).toPoint = P.toPoint - Q.toPoint := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  rw [sub_eq_add_neg]
  refine Completed.onCurve_and_toPoint_eq_add (mul_ne_zero h2 hP.1) P.toPoint (-Q.toPoint)
    ?_ ?_ ?_ ?_ <;>
  · simp only [subAffineNiels, X_eq_toPoint_x_mul_Z hP, Y_eq_toPoint_y_mul_Z hP,
      T_eq_toPoint_x_mul_y_mul_Z hP, AffineNiels.yPlusX_eq hQ, AffineNiels.yMinusX_eq hQ,
      AffineNiels.xy2d_eq hQ, addDen₁, addDen₂, ha, neg_x, neg_y]
    ring

/-- `EdwardsPoint - AffineNielsPoint` sends points on the curve to points on the curve
(`a = -1`). -/
theorem subAffineNiels_onCurve (ha : E.a = -1) {Q : E.AffineNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.subAffineNiels Q).OnCurve :=
  (subAffineNiels_spec ha hP hQ).1

/-- `EdwardsPoint - AffineNielsPoint` subtracts the represented points (`a = -1`). -/
theorem toPoint_subAffineNiels (ha : E.a = -1) {Q : E.AffineNiels} (hP : P.OnCurve)
    (hQ : Q.OnCurve) : (P.subAffineNiels Q).toPoint = P.toPoint - Q.toPoint :=
  (subAffineNiels_spec ha hP hQ).2

end Extended

end TwistedEdwardsModel
