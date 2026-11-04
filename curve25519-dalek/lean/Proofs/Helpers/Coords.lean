/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Edwards
public import Defs.Montgomery
public import Proofs.Helpers.ToField2625
public section

/-! # The coordinate lemmas of the math library on the dalek structures

For each point structure of `Defs.CurveModels`, `Defs.Edwards` and `Defs.Montgomery`:
`OnCurve` on the limbs' values (`onCurve_iff_equation`, `onCurve_iff_homogeneous`), the
coordinates of `toPoint` (`toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`), and projective
equality as point equality (`projEq_iff_toPoint_eq`). Everything is the corresponding lemma of
`EllipticCurve.TwistedEdwards.Coords` (projective, extended, completed) or
`Curve25519.Models.TwistedEdwards.Coords` (Niels) rewritten through the `_def` lemmas. -/

open curve25519 TwistedEdwardsModel

namespace Curve25519Dalek

/-! ### `curve_models.rs` (`x86_64-tables`) -/

namespace backend.serial.curve_models

namespace ProjectivePoint.«x86_64-tables»

theorem onCurve_iff (self : ProjectivePoint.«x86_64-tables») :
    self.OnCurve ↔ self.toProjective.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the equation. -/
theorem onCurve_iff_equation (self : ProjectivePoint.«x86_64-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toProjective_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : ProjectivePoint.«x86_64-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Projective.onCurve_iff_homogeneous, toProjective_def, edwards_a, edwards_d]

theorem toPoint_x {self : ProjectivePoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_x h, toProjective_def]

theorem toPoint_y {self : ProjectivePoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_y h, toProjective_def]

theorem toPoint_of_not_onCurve {self : ProjectivePoint.«x86_64-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Projective.toPoint_eq_zero_of_not_onCurve h]

theorem projEq_iff_toPoint_eq {self other : ProjectivePoint.«x86_64-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) :
    self.toProjective.ProjEq other.toProjective ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Projective.projEq_iff_toPoint_eq hP hQ

end ProjectivePoint.«x86_64-tables»

namespace ProjectivePoint.«i686-tables»

theorem onCurve_iff (self : ProjectivePoint.«i686-tables») :
    self.OnCurve ↔ self.toProjective.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the equation. -/
theorem onCurve_iff_equation (self : ProjectivePoint.«i686-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toProjective_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : ProjectivePoint.«i686-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Projective.onCurve_iff_homogeneous, toProjective_def, edwards_a, edwards_d]

theorem toPoint_x {self : ProjectivePoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_x h, toProjective_def]

theorem toPoint_y {self : ProjectivePoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_y h, toProjective_def]

theorem toPoint_of_not_onCurve {self : ProjectivePoint.«i686-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Projective.toPoint_eq_zero_of_not_onCurve h]

theorem projEq_iff_toPoint_eq {self other : ProjectivePoint.«i686-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) :
    self.toProjective.ProjEq other.toProjective ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Projective.projEq_iff_toPoint_eq hP hQ

end ProjectivePoint.«i686-tables»

namespace CompletedPoint.«x86_64-tables»

theorem onCurve_iff (self : CompletedPoint.«x86_64-tables») :
    self.OnCurve ↔ self.toCompleted.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : CompletedPoint.«x86_64-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.T.toField) := by
  rw [onCurve_iff, toCompleted_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : CompletedPoint.«x86_64-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.T.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 2 * self.T.toField ^ 2 +
          d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Completed.onCurve_iff_homogeneous, toCompleted_def, edwards_a, edwards_d]

theorem toPoint_x {self : CompletedPoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Completed.toPoint_x h, toCompleted_def]

theorem toPoint_y {self : CompletedPoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.T.toField := by
  rw [toPoint_def, Completed.toPoint_y h, toCompleted_def]

theorem toPoint_of_not_onCurve {self : CompletedPoint.«x86_64-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Completed.toPoint_eq_zero_of_not_onCurve h]

end CompletedPoint.«x86_64-tables»

namespace CompletedPoint.«i686-tables»

theorem onCurve_iff (self : CompletedPoint.«i686-tables») :
    self.OnCurve ↔ self.toCompleted.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : CompletedPoint.«i686-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.T.toField) := by
  rw [onCurve_iff, toCompleted_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : CompletedPoint.«i686-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.T.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 2 * self.T.toField ^ 2 +
          d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Completed.onCurve_iff_homogeneous, toCompleted_def, edwards_a, edwards_d]

theorem toPoint_x {self : CompletedPoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Completed.toPoint_x h, toCompleted_def]

theorem toPoint_y {self : CompletedPoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.T.toField := by
  rw [toPoint_def, Completed.toPoint_y h, toCompleted_def]

theorem toPoint_of_not_onCurve {self : CompletedPoint.«i686-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Completed.toPoint_eq_zero_of_not_onCurve h]

end CompletedPoint.«i686-tables»

namespace AffineNielsPoint.«x86_64-tables»

theorem onCurve_iff (self : AffineNielsPoint.«x86_64-tables») :
    self.OnCurve ↔ self.toAffineNiels.OnCurve :=
  Iff.rfl

/-- The `x`-coordinate recovered from the Niels form, `((y + x) - (y - x)) / 2`. -/
theorem toAffineNiels_x (self : AffineNielsPoint.«x86_64-tables») :
    self.toAffineNiels.x = (self.y_plus_x.toField - self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- The `y`-coordinate recovered from the Niels form, `((y + x) + (y - x)) / 2`. -/
theorem toAffineNiels_y (self : AffineNielsPoint.«x86_64-tables») :
    self.toAffineNiels.y = (self.y_plus_x.toField + self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : AffineNielsPoint.«x86_64-tables») :
    self.OnCurve ↔ edwards.Equation self.toAffineNiels.x self.toAffineNiels.y ∧
      self.xy2d.toField = 2 * d * self.toAffineNiels.x * self.toAffineNiels.y := by
  rw [onCurve_iff, ← edwards_d]
  have h : self.toAffineNiels.xy2d = self.xy2d.toField := by rw [toAffineNiels_def]
  rw [← h]
  exact Iff.rfl

theorem toPoint_x {self : AffineNielsPoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toAffineNiels.x := by
  rw [toPoint_def, AffineNiels.toPoint_x h]

theorem toPoint_y {self : AffineNielsPoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toAffineNiels.y := by
  rw [toPoint_def, AffineNiels.toPoint_y h]

theorem toPoint_of_not_onCurve {self : AffineNielsPoint.«x86_64-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, AffineNiels.toPoint_eq_zero_of_not_onCurve h]

end AffineNielsPoint.«x86_64-tables»

namespace AffineNielsPoint.«i686-tables»

theorem onCurve_iff (self : AffineNielsPoint.«i686-tables») :
    self.OnCurve ↔ self.toAffineNiels.OnCurve :=
  Iff.rfl

/-- The `x`-coordinate recovered from the Niels form, `((y + x) - (y - x)) / 2`. -/
theorem toAffineNiels_x (self : AffineNielsPoint.«i686-tables») :
    self.toAffineNiels.x = (self.y_plus_x.toField - self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- The `y`-coordinate recovered from the Niels form, `((y + x) + (y - x)) / 2`. -/
theorem toAffineNiels_y (self : AffineNielsPoint.«i686-tables») :
    self.toAffineNiels.y = (self.y_plus_x.toField + self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : AffineNielsPoint.«i686-tables») :
    self.OnCurve ↔ edwards.Equation self.toAffineNiels.x self.toAffineNiels.y ∧
      self.xy2d.toField = 2 * d * self.toAffineNiels.x * self.toAffineNiels.y := by
  rw [onCurve_iff, ← edwards_d]
  have h : self.toAffineNiels.xy2d = self.xy2d.toField := by rw [toAffineNiels_def]
  rw [← h]
  exact Iff.rfl

theorem toPoint_x {self : AffineNielsPoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toAffineNiels.x := by
  rw [toPoint_def, AffineNiels.toPoint_x h]

theorem toPoint_y {self : AffineNielsPoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toAffineNiels.y := by
  rw [toPoint_def, AffineNiels.toPoint_y h]

theorem toPoint_of_not_onCurve {self : AffineNielsPoint.«i686-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, AffineNiels.toPoint_eq_zero_of_not_onCurve h]

end AffineNielsPoint.«i686-tables»

namespace ProjectiveNielsPoint.«x86_64-tables»

theorem onCurve_iff (self : ProjectiveNielsPoint.«x86_64-tables») :
    self.OnCurve ↔ self.toProjectiveNiels.OnCurve :=
  Iff.rfl

/-- The `X`-coordinate recovered from the Niels form, `((Y + X) - (Y - X)) / 2`. -/
theorem toProjectiveNiels_X (self : ProjectiveNielsPoint.«x86_64-tables») :
    self.toProjectiveNiels.X = (self.Y_plus_X.toField - self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- The `Y`-coordinate recovered from the Niels form, `((Y + X) + (Y - X)) / 2`. -/
theorem toProjectiveNiels_Y (self : ProjectiveNielsPoint.«x86_64-tables») :
    self.toProjectiveNiels.Y = (self.Y_plus_X.toField + self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : ProjectiveNielsPoint.«x86_64-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.toProjectiveNiels.X / self.Z.toField)
        (self.toProjectiveNiels.Y / self.Z.toField) ∧
      self.T2d.toField * self.Z.toField =
        2 * d * self.toProjectiveNiels.X * self.toProjectiveNiels.Y := by
  rw [onCurve_iff, ← edwards_d]
  have hZ : self.toProjectiveNiels.Z = self.Z.toField := by rw [toProjectiveNiels_def]
  have hT : self.toProjectiveNiels.T2d = self.T2d.toField := by rw [toProjectiveNiels_def]
  rw [← hZ, ← hT]
  exact Iff.rfl

theorem toPoint_x {self : ProjectiveNielsPoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toProjectiveNiels.X / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_x h, toProjectiveNiels_def]

theorem toPoint_y {self : ProjectiveNielsPoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toProjectiveNiels.Y / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_y h, toProjectiveNiels_def]

theorem toPoint_of_not_onCurve {self : ProjectiveNielsPoint.«x86_64-tables»}
    (h : ¬ self.OnCurve) : self.toPoint = 0 := by
  rw [toPoint_def, ProjectiveNiels.toPoint_eq_zero_of_not_onCurve h]

end ProjectiveNielsPoint.«x86_64-tables»

namespace ProjectiveNielsPoint.«i686-tables»

theorem onCurve_iff (self : ProjectiveNielsPoint.«i686-tables») :
    self.OnCurve ↔ self.toProjectiveNiels.OnCurve :=
  Iff.rfl

/-- The `X`-coordinate recovered from the Niels form, `((Y + X) - (Y - X)) / 2`. -/
theorem toProjectiveNiels_X (self : ProjectiveNielsPoint.«i686-tables») :
    self.toProjectiveNiels.X = (self.Y_plus_X.toField - self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- The `Y`-coordinate recovered from the Niels form, `((Y + X) + (Y - X)) / 2`. -/
theorem toProjectiveNiels_Y (self : ProjectiveNielsPoint.«i686-tables») :
    self.toProjectiveNiels.Y = (self.Y_plus_X.toField + self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : ProjectiveNielsPoint.«i686-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.toProjectiveNiels.X / self.Z.toField)
        (self.toProjectiveNiels.Y / self.Z.toField) ∧
      self.T2d.toField * self.Z.toField =
        2 * d * self.toProjectiveNiels.X * self.toProjectiveNiels.Y := by
  rw [onCurve_iff, ← edwards_d]
  have hZ : self.toProjectiveNiels.Z = self.Z.toField := by rw [toProjectiveNiels_def]
  have hT : self.toProjectiveNiels.T2d = self.T2d.toField := by rw [toProjectiveNiels_def]
  rw [← hZ, ← hT]
  exact Iff.rfl

theorem toPoint_x {self : ProjectiveNielsPoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toProjectiveNiels.X / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_x h, toProjectiveNiels_def]

theorem toPoint_y {self : ProjectiveNielsPoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toProjectiveNiels.Y / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_y h, toProjectiveNiels_def]

theorem toPoint_of_not_onCurve {self : ProjectiveNielsPoint.«i686-tables»}
    (h : ¬ self.OnCurve) : self.toPoint = 0 := by
  rw [toPoint_def, ProjectiveNiels.toPoint_eq_zero_of_not_onCurve h]

end ProjectiveNielsPoint.«i686-tables»

end backend.serial.curve_models

/-! ### `edwards.rs` (`x86_64-tables`) -/

namespace edwards.EdwardsPoint.«x86_64-tables»

theorem onCurve_iff (self : EdwardsPoint.«x86_64-tables») :
    self.OnCurve ↔ self.toExtended.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : EdwardsPoint.«x86_64-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toExtended_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : EdwardsPoint.«x86_64-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Extended.onCurve_iff_homogeneous, toExtended_def, edwards_a, edwards_d]

theorem toPoint_x {self : EdwardsPoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_x h, toExtended_def]

theorem toPoint_y {self : EdwardsPoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_y h, toExtended_def]

theorem toPoint_of_not_onCurve {self : EdwardsPoint.«x86_64-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Extended.toPoint_eq_zero_of_not_onCurve h]

/-- `ProjEq` on the limbs' values: `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁`. -/
theorem projEq_iff (self other : EdwardsPoint.«x86_64-tables») :
    self.ProjEq other ↔ self.X.toField * other.Z.toField = other.X.toField * self.Z.toField ∧
      self.Y.toField * other.Z.toField = other.Y.toField * self.Z.toField := by
  change self.toExtended.ProjEq other.toExtended ↔ _
  rw [toExtended_def, toExtended_def]
  exact Iff.rfl

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {self other : EdwardsPoint.«x86_64-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) : self.ProjEq other ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Extended.projEq_iff_toPoint_eq hP hQ

end edwards.EdwardsPoint.«x86_64-tables»

namespace edwards.EdwardsPoint.«i686-tables»

theorem onCurve_iff (self : EdwardsPoint.«i686-tables») :
    self.OnCurve ↔ self.toExtended.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : EdwardsPoint.«i686-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toExtended_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : EdwardsPoint.«i686-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Extended.onCurve_iff_homogeneous, toExtended_def, edwards_a, edwards_d]

theorem toPoint_x {self : EdwardsPoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_x h, toExtended_def]

theorem toPoint_y {self : EdwardsPoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_y h, toExtended_def]

theorem toPoint_of_not_onCurve {self : EdwardsPoint.«i686-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Extended.toPoint_eq_zero_of_not_onCurve h]

/-- `ProjEq` on the limbs' values: `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁`. -/
theorem projEq_iff (self other : EdwardsPoint.«i686-tables») :
    self.ProjEq other ↔ self.X.toField * other.Z.toField = other.X.toField * self.Z.toField ∧
      self.Y.toField * other.Z.toField = other.Y.toField * self.Z.toField := by
  change self.toExtended.ProjEq other.toExtended ↔ _
  rw [toExtended_def, toExtended_def]
  exact Iff.rfl

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {self other : EdwardsPoint.«i686-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) : self.ProjEq other ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Extended.projEq_iff_toPoint_eq hP hQ

end edwards.EdwardsPoint.«i686-tables»

namespace edwards.affine.AffinePoint.«x86_64-tables»

theorem onCurve_iff (self : AffinePoint.«x86_64-tables») :
    self.OnCurve ↔ edwards.Equation self.x.toField self.y.toField :=
  Iff.rfl

theorem toPoint_eq_mk {self : AffinePoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint = ⟨self.x.toField, self.y.toField, h⟩ := by
  rw [toPoint_def, dite_eq_left h]

theorem toPoint_x {self : AffinePoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.x.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_y {self : AffinePoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.y.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_of_not_onCurve {self : AffinePoint.«x86_64-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, dite_eq_right h]

/-- The affine point and the extended coordinates `(x : y : 1 : x y)` of `to_edwards`. -/
theorem toExtended_toPoint {self : AffinePoint.«x86_64-tables»} (h : self.OnCurve) :
    self.toPoint.toExtended =
      ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ := by
  rw [toPoint_eq_mk h]
  rfl

end edwards.affine.AffinePoint.«x86_64-tables»

namespace edwards.affine.AffinePoint.«i686-tables»

theorem onCurve_iff (self : AffinePoint.«i686-tables») :
    self.OnCurve ↔ edwards.Equation self.x.toField self.y.toField :=
  Iff.rfl

theorem toPoint_eq_mk {self : AffinePoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint = ⟨self.x.toField, self.y.toField, h⟩ := by
  rw [toPoint_def, dite_eq_left h]

theorem toPoint_x {self : AffinePoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.x.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_y {self : AffinePoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.y.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_of_not_onCurve {self : AffinePoint.«i686-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, dite_eq_right h]

/-- The affine point and the extended coordinates `(x : y : 1 : x y)` of `to_edwards`. -/
theorem toExtended_toPoint {self : AffinePoint.«i686-tables»} (h : self.OnCurve) :
    self.toPoint.toExtended =
      ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ := by
  rw [toPoint_eq_mk h]
  rfl

end edwards.affine.AffinePoint.«i686-tables»

/-! ### `montgomery.rs` (`x86_64-tables`) -/

namespace montgomery.ProjectivePoint.«x86_64-tables»

/-- The affine `u`-coordinate `U / W` (`0` at `W = 0`), what `as_affine` computes. -/
theorem toXZ_toU (self : ProjectivePoint.«x86_64-tables») :
    self.toXZ.toU = self.U.toField / self.W.toField := by
  rw [toXZ_def]
  rfl

end montgomery.ProjectivePoint.«x86_64-tables»

namespace montgomery.ProjectivePoint.«i686-tables»

/-- The affine `u`-coordinate `U / W` (`0` at `W = 0`), what `as_affine` computes. -/
theorem toXZ_toU (self : ProjectivePoint.«i686-tables») :
    self.toXZ.toU = self.U.toField / self.W.toField := by
  rw [toXZ_def]
  rfl

end montgomery.ProjectivePoint.«i686-tables»

/-! ### `curve_models.rs` (`x86_64-no-tables`) -/

namespace backend.serial.curve_models

namespace ProjectivePoint.«x86_64-no-tables»

theorem onCurve_iff (self : ProjectivePoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.toProjective.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the equation. -/
theorem onCurve_iff_equation (self : ProjectivePoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toProjective_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : ProjectivePoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Projective.onCurve_iff_homogeneous, toProjective_def, edwards_a, edwards_d]

theorem toPoint_x {self : ProjectivePoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_x h, toProjective_def]

theorem toPoint_y {self : ProjectivePoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_y h, toProjective_def]

theorem toPoint_of_not_onCurve {self : ProjectivePoint.«x86_64-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Projective.toPoint_eq_zero_of_not_onCurve h]

theorem projEq_iff_toPoint_eq {self other : ProjectivePoint.«x86_64-no-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) :
    self.toProjective.ProjEq other.toProjective ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Projective.projEq_iff_toPoint_eq hP hQ

end ProjectivePoint.«x86_64-no-tables»

namespace ProjectivePoint.«i686-no-tables»

theorem onCurve_iff (self : ProjectivePoint.«i686-no-tables») :
    self.OnCurve ↔ self.toProjective.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the equation. -/
theorem onCurve_iff_equation (self : ProjectivePoint.«i686-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toProjective_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : ProjectivePoint.«i686-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Projective.onCurve_iff_homogeneous, toProjective_def, edwards_a, edwards_d]

theorem toPoint_x {self : ProjectivePoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_x h, toProjective_def]

theorem toPoint_y {self : ProjectivePoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_y h, toProjective_def]

theorem toPoint_of_not_onCurve {self : ProjectivePoint.«i686-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Projective.toPoint_eq_zero_of_not_onCurve h]

theorem projEq_iff_toPoint_eq {self other : ProjectivePoint.«i686-no-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) :
    self.toProjective.ProjEq other.toProjective ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Projective.projEq_iff_toPoint_eq hP hQ

end ProjectivePoint.«i686-no-tables»

namespace CompletedPoint.«x86_64-no-tables»

theorem onCurve_iff (self : CompletedPoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.toCompleted.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : CompletedPoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.T.toField) := by
  rw [onCurve_iff, toCompleted_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : CompletedPoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.T.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 2 * self.T.toField ^ 2 +
          d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Completed.onCurve_iff_homogeneous, toCompleted_def, edwards_a, edwards_d]

theorem toPoint_x {self : CompletedPoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Completed.toPoint_x h, toCompleted_def]

theorem toPoint_y {self : CompletedPoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.T.toField := by
  rw [toPoint_def, Completed.toPoint_y h, toCompleted_def]

theorem toPoint_of_not_onCurve {self : CompletedPoint.«x86_64-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Completed.toPoint_eq_zero_of_not_onCurve h]

end CompletedPoint.«x86_64-no-tables»

namespace CompletedPoint.«i686-no-tables»

theorem onCurve_iff (self : CompletedPoint.«i686-no-tables») :
    self.OnCurve ↔ self.toCompleted.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : CompletedPoint.«i686-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.T.toField) := by
  rw [onCurve_iff, toCompleted_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : CompletedPoint.«i686-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.T.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 2 * self.T.toField ^ 2 +
          d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Completed.onCurve_iff_homogeneous, toCompleted_def, edwards_a, edwards_d]

theorem toPoint_x {self : CompletedPoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Completed.toPoint_x h, toCompleted_def]

theorem toPoint_y {self : CompletedPoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.T.toField := by
  rw [toPoint_def, Completed.toPoint_y h, toCompleted_def]

theorem toPoint_of_not_onCurve {self : CompletedPoint.«i686-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Completed.toPoint_eq_zero_of_not_onCurve h]

end CompletedPoint.«i686-no-tables»

/-- The coordinates of an i686 completed point are below `3 · 2^26`, the input bound of `mul`
(`Z` is a sum `2 Z + T`, so `LimbsLt 27` is too weak). -/
@[expose] def CompletedPoint.«i686-tables».MulBounded
    (self : CompletedPoint.«i686-tables») : Prop :=
  self.X.MulBounded ∧ self.Y.MulBounded ∧ self.Z.MulBounded ∧ self.T.MulBounded

/-- The coordinates of an i686 completed point are below `3 · 2^26`, the input bound of `mul`
(`Z` is a sum `2 Z + T`, so `LimbsLt 27` is too weak). -/
@[expose] def CompletedPoint.«i686-no-tables».MulBounded
    (self : CompletedPoint.«i686-no-tables») : Prop :=
  self.X.MulBounded ∧ self.Y.MulBounded ∧ self.Z.MulBounded ∧ self.T.MulBounded

namespace AffineNielsPoint.«x86_64-no-tables»

theorem onCurve_iff (self : AffineNielsPoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.toAffineNiels.OnCurve :=
  Iff.rfl

/-- The `x`-coordinate recovered from the Niels form, `((y + x) - (y - x)) / 2`. -/
theorem toAffineNiels_x (self : AffineNielsPoint.«x86_64-no-tables») :
    self.toAffineNiels.x = (self.y_plus_x.toField - self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- The `y`-coordinate recovered from the Niels form, `((y + x) + (y - x)) / 2`. -/
theorem toAffineNiels_y (self : AffineNielsPoint.«x86_64-no-tables») :
    self.toAffineNiels.y = (self.y_plus_x.toField + self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : AffineNielsPoint.«x86_64-no-tables») :
    self.OnCurve ↔ edwards.Equation self.toAffineNiels.x self.toAffineNiels.y ∧
      self.xy2d.toField = 2 * d * self.toAffineNiels.x * self.toAffineNiels.y := by
  rw [onCurve_iff, ← edwards_d]
  have h : self.toAffineNiels.xy2d = self.xy2d.toField := by rw [toAffineNiels_def]
  rw [← h]
  exact Iff.rfl

theorem toPoint_x {self : AffineNielsPoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toAffineNiels.x := by
  rw [toPoint_def, AffineNiels.toPoint_x h]

theorem toPoint_y {self : AffineNielsPoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toAffineNiels.y := by
  rw [toPoint_def, AffineNiels.toPoint_y h]

theorem toPoint_of_not_onCurve {self : AffineNielsPoint.«x86_64-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, AffineNiels.toPoint_eq_zero_of_not_onCurve h]

end AffineNielsPoint.«x86_64-no-tables»

namespace AffineNielsPoint.«i686-no-tables»

theorem onCurve_iff (self : AffineNielsPoint.«i686-no-tables») :
    self.OnCurve ↔ self.toAffineNiels.OnCurve :=
  Iff.rfl

/-- The `x`-coordinate recovered from the Niels form, `((y + x) - (y - x)) / 2`. -/
theorem toAffineNiels_x (self : AffineNielsPoint.«i686-no-tables») :
    self.toAffineNiels.x = (self.y_plus_x.toField - self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- The `y`-coordinate recovered from the Niels form, `((y + x) + (y - x)) / 2`. -/
theorem toAffineNiels_y (self : AffineNielsPoint.«i686-no-tables») :
    self.toAffineNiels.y = (self.y_plus_x.toField + self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : AffineNielsPoint.«i686-no-tables») :
    self.OnCurve ↔ edwards.Equation self.toAffineNiels.x self.toAffineNiels.y ∧
      self.xy2d.toField = 2 * d * self.toAffineNiels.x * self.toAffineNiels.y := by
  rw [onCurve_iff, ← edwards_d]
  have h : self.toAffineNiels.xy2d = self.xy2d.toField := by rw [toAffineNiels_def]
  rw [← h]
  exact Iff.rfl

theorem toPoint_x {self : AffineNielsPoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toAffineNiels.x := by
  rw [toPoint_def, AffineNiels.toPoint_x h]

theorem toPoint_y {self : AffineNielsPoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toAffineNiels.y := by
  rw [toPoint_def, AffineNiels.toPoint_y h]

theorem toPoint_of_not_onCurve {self : AffineNielsPoint.«i686-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, AffineNiels.toPoint_eq_zero_of_not_onCurve h]

end AffineNielsPoint.«i686-no-tables»

namespace ProjectiveNielsPoint.«x86_64-no-tables»

theorem onCurve_iff (self : ProjectiveNielsPoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.toProjectiveNiels.OnCurve :=
  Iff.rfl

/-- The `X`-coordinate recovered from the Niels form, `((Y + X) - (Y - X)) / 2`. -/
theorem toProjectiveNiels_X (self : ProjectiveNielsPoint.«x86_64-no-tables») :
    self.toProjectiveNiels.X = (self.Y_plus_X.toField - self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- The `Y`-coordinate recovered from the Niels form, `((Y + X) + (Y - X)) / 2`. -/
theorem toProjectiveNiels_Y (self : ProjectiveNielsPoint.«x86_64-no-tables») :
    self.toProjectiveNiels.Y = (self.Y_plus_X.toField + self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : ProjectiveNielsPoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.toProjectiveNiels.X / self.Z.toField)
        (self.toProjectiveNiels.Y / self.Z.toField) ∧
      self.T2d.toField * self.Z.toField =
        2 * d * self.toProjectiveNiels.X * self.toProjectiveNiels.Y := by
  rw [onCurve_iff, ← edwards_d]
  have hZ : self.toProjectiveNiels.Z = self.Z.toField := by rw [toProjectiveNiels_def]
  have hT : self.toProjectiveNiels.T2d = self.T2d.toField := by rw [toProjectiveNiels_def]
  rw [← hZ, ← hT]
  exact Iff.rfl

theorem toPoint_x {self : ProjectiveNielsPoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toProjectiveNiels.X / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_x h, toProjectiveNiels_def]

theorem toPoint_y {self : ProjectiveNielsPoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toProjectiveNiels.Y / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_y h, toProjectiveNiels_def]

theorem toPoint_of_not_onCurve {self : ProjectiveNielsPoint.«x86_64-no-tables»}
    (h : ¬ self.OnCurve) : self.toPoint = 0 := by
  rw [toPoint_def, ProjectiveNiels.toPoint_eq_zero_of_not_onCurve h]

end ProjectiveNielsPoint.«x86_64-no-tables»

namespace ProjectiveNielsPoint.«i686-no-tables»

theorem onCurve_iff (self : ProjectiveNielsPoint.«i686-no-tables») :
    self.OnCurve ↔ self.toProjectiveNiels.OnCurve :=
  Iff.rfl

/-- The `X`-coordinate recovered from the Niels form, `((Y + X) - (Y - X)) / 2`. -/
theorem toProjectiveNiels_X (self : ProjectiveNielsPoint.«i686-no-tables») :
    self.toProjectiveNiels.X = (self.Y_plus_X.toField - self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- The `Y`-coordinate recovered from the Niels form, `((Y + X) + (Y - X)) / 2`. -/
theorem toProjectiveNiels_Y (self : ProjectiveNielsPoint.«i686-no-tables») :
    self.toProjectiveNiels.Y = (self.Y_plus_X.toField + self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : ProjectiveNielsPoint.«i686-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.toProjectiveNiels.X / self.Z.toField)
        (self.toProjectiveNiels.Y / self.Z.toField) ∧
      self.T2d.toField * self.Z.toField =
        2 * d * self.toProjectiveNiels.X * self.toProjectiveNiels.Y := by
  rw [onCurve_iff, ← edwards_d]
  have hZ : self.toProjectiveNiels.Z = self.Z.toField := by rw [toProjectiveNiels_def]
  have hT : self.toProjectiveNiels.T2d = self.T2d.toField := by rw [toProjectiveNiels_def]
  rw [← hZ, ← hT]
  exact Iff.rfl

theorem toPoint_x {self : ProjectiveNielsPoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toProjectiveNiels.X / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_x h, toProjectiveNiels_def]

theorem toPoint_y {self : ProjectiveNielsPoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toProjectiveNiels.Y / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_y h, toProjectiveNiels_def]

theorem toPoint_of_not_onCurve {self : ProjectiveNielsPoint.«i686-no-tables»}
    (h : ¬ self.OnCurve) : self.toPoint = 0 := by
  rw [toPoint_def, ProjectiveNiels.toPoint_eq_zero_of_not_onCurve h]

end ProjectiveNielsPoint.«i686-no-tables»

end backend.serial.curve_models

/-! ### `edwards.rs` (`x86_64-no-tables`) -/

namespace edwards.EdwardsPoint.«x86_64-no-tables»

theorem onCurve_iff (self : EdwardsPoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.toExtended.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : EdwardsPoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toExtended_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : EdwardsPoint.«x86_64-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Extended.onCurve_iff_homogeneous, toExtended_def, edwards_a, edwards_d]

theorem toPoint_x {self : EdwardsPoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_x h, toExtended_def]

theorem toPoint_y {self : EdwardsPoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_y h, toExtended_def]

theorem toPoint_of_not_onCurve {self : EdwardsPoint.«x86_64-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Extended.toPoint_eq_zero_of_not_onCurve h]

/-- `ProjEq` on the limbs' values: `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁`. -/
theorem projEq_iff (self other : EdwardsPoint.«x86_64-no-tables») :
    self.ProjEq other ↔ self.X.toField * other.Z.toField = other.X.toField * self.Z.toField ∧
      self.Y.toField * other.Z.toField = other.Y.toField * self.Z.toField := by
  change self.toExtended.ProjEq other.toExtended ↔ _
  rw [toExtended_def, toExtended_def]
  exact Iff.rfl

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {self other : EdwardsPoint.«x86_64-no-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) : self.ProjEq other ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Extended.projEq_iff_toPoint_eq hP hQ

end edwards.EdwardsPoint.«x86_64-no-tables»

namespace edwards.EdwardsPoint.«i686-no-tables»

theorem onCurve_iff (self : EdwardsPoint.«i686-no-tables») :
    self.OnCurve ↔ self.toExtended.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : EdwardsPoint.«i686-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toExtended_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : EdwardsPoint.«i686-no-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Extended.onCurve_iff_homogeneous, toExtended_def, edwards_a, edwards_d]

theorem toPoint_x {self : EdwardsPoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_x h, toExtended_def]

theorem toPoint_y {self : EdwardsPoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_y h, toExtended_def]

theorem toPoint_of_not_onCurve {self : EdwardsPoint.«i686-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Extended.toPoint_eq_zero_of_not_onCurve h]

/-- `ProjEq` on the limbs' values: `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁`. -/
theorem projEq_iff (self other : EdwardsPoint.«i686-no-tables») :
    self.ProjEq other ↔ self.X.toField * other.Z.toField = other.X.toField * self.Z.toField ∧
      self.Y.toField * other.Z.toField = other.Y.toField * self.Z.toField := by
  change self.toExtended.ProjEq other.toExtended ↔ _
  rw [toExtended_def, toExtended_def]
  exact Iff.rfl

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {self other : EdwardsPoint.«i686-no-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) : self.ProjEq other ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Extended.projEq_iff_toPoint_eq hP hQ

end edwards.EdwardsPoint.«i686-no-tables»

namespace edwards.affine.AffinePoint.«x86_64-no-tables»

theorem onCurve_iff (self : AffinePoint.«x86_64-no-tables») :
    self.OnCurve ↔ edwards.Equation self.x.toField self.y.toField :=
  Iff.rfl

theorem toPoint_eq_mk {self : AffinePoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint = ⟨self.x.toField, self.y.toField, h⟩ := by
  rw [toPoint_def, dite_eq_left h]

theorem toPoint_x {self : AffinePoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.x.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_y {self : AffinePoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.y.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_of_not_onCurve {self : AffinePoint.«x86_64-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, dite_eq_right h]

/-- The affine point and the extended coordinates `(x : y : 1 : x y)` of `to_edwards`. -/
theorem toExtended_toPoint {self : AffinePoint.«x86_64-no-tables»} (h : self.OnCurve) :
    self.toPoint.toExtended =
      ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ := by
  rw [toPoint_eq_mk h]
  rfl

end edwards.affine.AffinePoint.«x86_64-no-tables»

namespace edwards.affine.AffinePoint.«i686-no-tables»

theorem onCurve_iff (self : AffinePoint.«i686-no-tables») :
    self.OnCurve ↔ edwards.Equation self.x.toField self.y.toField :=
  Iff.rfl

theorem toPoint_eq_mk {self : AffinePoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint = ⟨self.x.toField, self.y.toField, h⟩ := by
  rw [toPoint_def, dite_eq_left h]

theorem toPoint_x {self : AffinePoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.x.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_y {self : AffinePoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.y.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_of_not_onCurve {self : AffinePoint.«i686-no-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, dite_eq_right h]

/-- The affine point and the extended coordinates `(x : y : 1 : x y)` of `to_edwards`. -/
theorem toExtended_toPoint {self : AffinePoint.«i686-no-tables»} (h : self.OnCurve) :
    self.toPoint.toExtended =
      ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ := by
  rw [toPoint_eq_mk h]
  rfl

end edwards.affine.AffinePoint.«i686-no-tables»

/-! ### `montgomery.rs` (`x86_64-no-tables`) -/

namespace montgomery.ProjectivePoint.«x86_64-no-tables»

/-- The affine `u`-coordinate `U / W` (`0` at `W = 0`), what `as_affine` computes. -/
theorem toXZ_toU (self : ProjectivePoint.«x86_64-no-tables») :
    self.toXZ.toU = self.U.toField / self.W.toField := by
  rw [toXZ_def]
  rfl

end montgomery.ProjectivePoint.«x86_64-no-tables»

namespace montgomery.ProjectivePoint.«i686-no-tables»

/-- The affine `u`-coordinate `U / W` (`0` at `W = 0`), what `as_affine` computes. -/
theorem toXZ_toU (self : ProjectivePoint.«i686-no-tables») :
    self.toXZ.toU = self.U.toField / self.W.toField := by
  rw [toXZ_def]
  rfl

end montgomery.ProjectivePoint.«i686-no-tables»

end Curve25519Dalek
