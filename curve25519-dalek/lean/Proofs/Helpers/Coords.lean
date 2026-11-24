module
public import Proofs.Representation.Edwards
public import Proofs.Representation.Montgomery
public import Proofs.Helpers.ToField2625
public section

/-! # The coordinate lemmas of the math library on the dalek structures

For each point structure of `Proofs.Representation.CurveModels`,
`Proofs.Representation.Edwards` and `Proofs.Representation.Montgomery`: `OnCurve`
on the limbs' values (`onCurve_iff_equation`, `onCurve_iff_homogeneous`), the coordinates of
`toPoint` (`toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`), and projective equality as point
equality (`projEq_iff_toPoint_eq`). Everything is the corresponding lemma of
`EllipticCurve.TwistedEdwards.Coords` (projective, extended, completed) or
`Proofs.Curve25519.Models.TwistedEdwards.Coords` (Niels) rewritten through the `_def` lemmas. -/

open curve25519 TwistedEdwardsModel

namespace Curve25519Dalek

/-! ### `curve_models.rs` (`64bit-tables`) -/

namespace backend.serial.curve_models

namespace ProjectivePoint.«64bit-tables»

theorem onCurve_iff (self : ProjectivePoint.«64bit-tables») :
    self.OnCurve ↔ self.toProjective.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the equation. -/
theorem onCurve_iff_equation (self : ProjectivePoint.«64bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toProjective_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : ProjectivePoint.«64bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Projective.onCurve_iff_homogeneous, toProjective_def, edwards_a, edwards_d]

theorem toPoint_x {self : ProjectivePoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_x h, toProjective_def]

theorem toPoint_y {self : ProjectivePoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_y h, toProjective_def]

theorem toPoint_of_not_onCurve {self : ProjectivePoint.«64bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Projective.toPoint_eq_zero_of_not_onCurve h]

theorem projEq_iff_toPoint_eq {self other : ProjectivePoint.«64bit-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) :
    self.toProjective.ProjEq other.toProjective ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Projective.projEq_iff_toPoint_eq hP hQ

end ProjectivePoint.«64bit-tables»

namespace ProjectivePoint.«32bit-tables»

theorem onCurve_iff (self : ProjectivePoint.«32bit-tables») :
    self.OnCurve ↔ self.toProjective.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the equation. -/
theorem onCurve_iff_equation (self : ProjectivePoint.«32bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toProjective_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : ProjectivePoint.«32bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Projective.onCurve_iff_homogeneous, toProjective_def, edwards_a, edwards_d]

theorem toPoint_x {self : ProjectivePoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_x h, toProjective_def]

theorem toPoint_y {self : ProjectivePoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_y h, toProjective_def]

theorem toPoint_of_not_onCurve {self : ProjectivePoint.«32bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Projective.toPoint_eq_zero_of_not_onCurve h]

theorem projEq_iff_toPoint_eq {self other : ProjectivePoint.«32bit-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) :
    self.toProjective.ProjEq other.toProjective ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Projective.projEq_iff_toPoint_eq hP hQ

end ProjectivePoint.«32bit-tables»

namespace CompletedPoint.«64bit-tables»

theorem onCurve_iff (self : CompletedPoint.«64bit-tables») :
    self.OnCurve ↔ self.toCompleted.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : CompletedPoint.«64bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.T.toField) := by
  rw [onCurve_iff, toCompleted_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : CompletedPoint.«64bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.T.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 2 * self.T.toField ^ 2 +
          d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Completed.onCurve_iff_homogeneous, toCompleted_def, edwards_a, edwards_d]

theorem toPoint_x {self : CompletedPoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Completed.toPoint_x h, toCompleted_def]

theorem toPoint_y {self : CompletedPoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.T.toField := by
  rw [toPoint_def, Completed.toPoint_y h, toCompleted_def]

theorem toPoint_of_not_onCurve {self : CompletedPoint.«64bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Completed.toPoint_eq_zero_of_not_onCurve h]

end CompletedPoint.«64bit-tables»

namespace CompletedPoint.«32bit-tables»

theorem onCurve_iff (self : CompletedPoint.«32bit-tables») :
    self.OnCurve ↔ self.toCompleted.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : CompletedPoint.«32bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.T.toField) := by
  rw [onCurve_iff, toCompleted_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : CompletedPoint.«32bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.T.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 2 * self.T.toField ^ 2 +
          d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Completed.onCurve_iff_homogeneous, toCompleted_def, edwards_a, edwards_d]

theorem toPoint_x {self : CompletedPoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Completed.toPoint_x h, toCompleted_def]

theorem toPoint_y {self : CompletedPoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.T.toField := by
  rw [toPoint_def, Completed.toPoint_y h, toCompleted_def]

theorem toPoint_of_not_onCurve {self : CompletedPoint.«32bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Completed.toPoint_eq_zero_of_not_onCurve h]

end CompletedPoint.«32bit-tables»

namespace AffineNielsPoint.«64bit-tables»

theorem onCurve_iff (self : AffineNielsPoint.«64bit-tables») :
    self.OnCurve ↔ self.toAffineNiels.OnCurve :=
  Iff.rfl

/-- The `x`-coordinate recovered from the Niels form, `((y + x) - (y - x)) / 2`. -/
theorem toAffineNiels_x (self : AffineNielsPoint.«64bit-tables») :
    self.toAffineNiels.x = (self.y_plus_x.toField - self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- The `y`-coordinate recovered from the Niels form, `((y + x) + (y - x)) / 2`. -/
theorem toAffineNiels_y (self : AffineNielsPoint.«64bit-tables») :
    self.toAffineNiels.y = (self.y_plus_x.toField + self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : AffineNielsPoint.«64bit-tables») :
    self.OnCurve ↔ edwards.Equation self.toAffineNiels.x self.toAffineNiels.y ∧
      self.xy2d.toField = 2 * d * self.toAffineNiels.x * self.toAffineNiels.y := by
  rw [onCurve_iff, ← edwards_d]
  have h : self.toAffineNiels.xy2d = self.xy2d.toField := by rw [toAffineNiels_def]
  rw [← h]
  exact Iff.rfl

theorem toPoint_x {self : AffineNielsPoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toAffineNiels.x := by
  rw [toPoint_def, AffineNiels.toPoint_x h]

theorem toPoint_y {self : AffineNielsPoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toAffineNiels.y := by
  rw [toPoint_def, AffineNiels.toPoint_y h]

theorem toPoint_of_not_onCurve {self : AffineNielsPoint.«64bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, AffineNiels.toPoint_eq_zero_of_not_onCurve h]

end AffineNielsPoint.«64bit-tables»

namespace AffineNielsPoint.«32bit-tables»

theorem onCurve_iff (self : AffineNielsPoint.«32bit-tables») :
    self.OnCurve ↔ self.toAffineNiels.OnCurve :=
  Iff.rfl

/-- The `x`-coordinate recovered from the Niels form, `((y + x) - (y - x)) / 2`. -/
theorem toAffineNiels_x (self : AffineNielsPoint.«32bit-tables») :
    self.toAffineNiels.x = (self.y_plus_x.toField - self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- The `y`-coordinate recovered from the Niels form, `((y + x) + (y - x)) / 2`. -/
theorem toAffineNiels_y (self : AffineNielsPoint.«32bit-tables») :
    self.toAffineNiels.y = (self.y_plus_x.toField + self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : AffineNielsPoint.«32bit-tables») :
    self.OnCurve ↔ edwards.Equation self.toAffineNiels.x self.toAffineNiels.y ∧
      self.xy2d.toField = 2 * d * self.toAffineNiels.x * self.toAffineNiels.y := by
  rw [onCurve_iff, ← edwards_d]
  have h : self.toAffineNiels.xy2d = self.xy2d.toField := by rw [toAffineNiels_def]
  rw [← h]
  exact Iff.rfl

theorem toPoint_x {self : AffineNielsPoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toAffineNiels.x := by
  rw [toPoint_def, AffineNiels.toPoint_x h]

theorem toPoint_y {self : AffineNielsPoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toAffineNiels.y := by
  rw [toPoint_def, AffineNiels.toPoint_y h]

theorem toPoint_of_not_onCurve {self : AffineNielsPoint.«32bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, AffineNiels.toPoint_eq_zero_of_not_onCurve h]

end AffineNielsPoint.«32bit-tables»

namespace ProjectiveNielsPoint.«64bit-tables»

theorem onCurve_iff (self : ProjectiveNielsPoint.«64bit-tables») :
    self.OnCurve ↔ self.toProjectiveNiels.OnCurve :=
  Iff.rfl

/-- The `X`-coordinate recovered from the Niels form, `((Y + X) - (Y - X)) / 2`. -/
theorem toProjectiveNiels_X (self : ProjectiveNielsPoint.«64bit-tables») :
    self.toProjectiveNiels.X = (self.Y_plus_X.toField - self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- The `Y`-coordinate recovered from the Niels form, `((Y + X) + (Y - X)) / 2`. -/
theorem toProjectiveNiels_Y (self : ProjectiveNielsPoint.«64bit-tables») :
    self.toProjectiveNiels.Y = (self.Y_plus_X.toField + self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : ProjectiveNielsPoint.«64bit-tables») :
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

theorem toPoint_x {self : ProjectiveNielsPoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toProjectiveNiels.X / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_x h, toProjectiveNiels_def]

theorem toPoint_y {self : ProjectiveNielsPoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toProjectiveNiels.Y / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_y h, toProjectiveNiels_def]

theorem toPoint_of_not_onCurve {self : ProjectiveNielsPoint.«64bit-tables»}
    (h : ¬ self.OnCurve) : self.toPoint = 0 := by
  rw [toPoint_def, ProjectiveNiels.toPoint_eq_zero_of_not_onCurve h]

end ProjectiveNielsPoint.«64bit-tables»

namespace ProjectiveNielsPoint.«32bit-tables»

theorem onCurve_iff (self : ProjectiveNielsPoint.«32bit-tables») :
    self.OnCurve ↔ self.toProjectiveNiels.OnCurve :=
  Iff.rfl

/-- The `X`-coordinate recovered from the Niels form, `((Y + X) - (Y - X)) / 2`. -/
theorem toProjectiveNiels_X (self : ProjectiveNielsPoint.«32bit-tables») :
    self.toProjectiveNiels.X = (self.Y_plus_X.toField - self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- The `Y`-coordinate recovered from the Niels form, `((Y + X) + (Y - X)) / 2`. -/
theorem toProjectiveNiels_Y (self : ProjectiveNielsPoint.«32bit-tables») :
    self.toProjectiveNiels.Y = (self.Y_plus_X.toField + self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : ProjectiveNielsPoint.«32bit-tables») :
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

theorem toPoint_x {self : ProjectiveNielsPoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.toProjectiveNiels.X / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_x h, toProjectiveNiels_def]

theorem toPoint_y {self : ProjectiveNielsPoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.toProjectiveNiels.Y / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_y h, toProjectiveNiels_def]

theorem toPoint_of_not_onCurve {self : ProjectiveNielsPoint.«32bit-tables»}
    (h : ¬ self.OnCurve) : self.toPoint = 0 := by
  rw [toPoint_def, ProjectiveNiels.toPoint_eq_zero_of_not_onCurve h]

end ProjectiveNielsPoint.«32bit-tables»

end backend.serial.curve_models

/-! ### `edwards.rs` (`64bit-tables`) -/

namespace edwards.EdwardsPoint.«64bit-tables»

theorem onCurve_iff (self : EdwardsPoint.«64bit-tables») :
    self.OnCurve ↔ self.toExtended.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : EdwardsPoint.«64bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toExtended_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : EdwardsPoint.«64bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Extended.onCurve_iff_homogeneous, toExtended_def, edwards_a, edwards_d]

theorem toPoint_x {self : EdwardsPoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_x h, toExtended_def]

theorem toPoint_y {self : EdwardsPoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_y h, toExtended_def]

theorem toPoint_of_not_onCurve {self : EdwardsPoint.«64bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Extended.toPoint_eq_zero_of_not_onCurve h]

/-- `ProjEq` on the limbs' values: `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁`. -/
theorem projEq_iff (self other : EdwardsPoint.«64bit-tables») :
    self.ProjEq other ↔ self.X.toField * other.Z.toField = other.X.toField * self.Z.toField ∧
      self.Y.toField * other.Z.toField = other.Y.toField * self.Z.toField := by
  change self.toExtended.ProjEq other.toExtended ↔ _
  rw [toExtended_def, toExtended_def]
  exact Iff.rfl

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {self other : EdwardsPoint.«64bit-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) : self.ProjEq other ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Extended.projEq_iff_toPoint_eq hP hQ

end edwards.EdwardsPoint.«64bit-tables»

namespace edwards.EdwardsPoint.«32bit-tables»

theorem onCurve_iff (self : EdwardsPoint.«32bit-tables») :
    self.OnCurve ↔ self.toExtended.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : EdwardsPoint.«32bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toExtended_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : EdwardsPoint.«32bit-tables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Extended.onCurve_iff_homogeneous, toExtended_def, edwards_a, edwards_d]

theorem toPoint_x {self : EdwardsPoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_x h, toExtended_def]

theorem toPoint_y {self : EdwardsPoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_y h, toExtended_def]

theorem toPoint_of_not_onCurve {self : EdwardsPoint.«32bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Extended.toPoint_eq_zero_of_not_onCurve h]

/-- `ProjEq` on the limbs' values: `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁`. -/
theorem projEq_iff (self other : EdwardsPoint.«32bit-tables») :
    self.ProjEq other ↔ self.X.toField * other.Z.toField = other.X.toField * self.Z.toField ∧
      self.Y.toField * other.Z.toField = other.Y.toField * self.Z.toField := by
  change self.toExtended.ProjEq other.toExtended ↔ _
  rw [toExtended_def, toExtended_def]
  exact Iff.rfl

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {self other : EdwardsPoint.«32bit-tables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) : self.ProjEq other ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Extended.projEq_iff_toPoint_eq hP hQ

end edwards.EdwardsPoint.«32bit-tables»

namespace edwards.affine.AffinePoint.«64bit-tables»

theorem onCurve_iff (self : AffinePoint.«64bit-tables») :
    self.OnCurve ↔ edwards.Equation self.x.toField self.y.toField :=
  Iff.rfl

theorem toPoint_eq_mk {self : AffinePoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint = ⟨self.x.toField, self.y.toField, h⟩ := by
  rw [toPoint_def, dite_eq_left h]

theorem toPoint_x {self : AffinePoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.x.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_y {self : AffinePoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.y.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_of_not_onCurve {self : AffinePoint.«64bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, dite_eq_right h]

/-- The affine point and the extended coordinates `(x : y : 1 : x y)` of `to_edwards`. -/
theorem toExtended_toPoint {self : AffinePoint.«64bit-tables»} (h : self.OnCurve) :
    self.toPoint.toExtended =
      ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ := by
  rw [toPoint_eq_mk h]
  rfl

end edwards.affine.AffinePoint.«64bit-tables»

namespace edwards.affine.AffinePoint.«32bit-tables»

theorem onCurve_iff (self : AffinePoint.«32bit-tables») :
    self.OnCurve ↔ edwards.Equation self.x.toField self.y.toField :=
  Iff.rfl

theorem toPoint_eq_mk {self : AffinePoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint = ⟨self.x.toField, self.y.toField, h⟩ := by
  rw [toPoint_def, dite_eq_left h]

theorem toPoint_x {self : AffinePoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.x = self.x.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_y {self : AffinePoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.y = self.y.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_of_not_onCurve {self : AffinePoint.«32bit-tables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, dite_eq_right h]

/-- The affine point and the extended coordinates `(x : y : 1 : x y)` of `to_edwards`. -/
theorem toExtended_toPoint {self : AffinePoint.«32bit-tables»} (h : self.OnCurve) :
    self.toPoint.toExtended =
      ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ := by
  rw [toPoint_eq_mk h]
  rfl

end edwards.affine.AffinePoint.«32bit-tables»

/-! ### `montgomery.rs` (`64bit-tables`) -/

namespace montgomery.ProjectivePoint.«64bit-tables»

/-- The affine `u`-coordinate `U / W` (`0` at `W = 0`), what `as_affine` computes. -/
theorem toXZ_toU (self : ProjectivePoint.«64bit-tables») :
    self.toXZ.toU = self.U.toField / self.W.toField := by
  rw [toXZ_def]
  rfl

end montgomery.ProjectivePoint.«64bit-tables»

namespace montgomery.ProjectivePoint.«32bit-tables»

/-- The affine `u`-coordinate `U / W` (`0` at `W = 0`), what `as_affine` computes. -/
theorem toXZ_toU (self : ProjectivePoint.«32bit-tables») :
    self.toXZ.toU = self.U.toField / self.W.toField := by
  rw [toXZ_def]
  rfl

end montgomery.ProjectivePoint.«32bit-tables»

/-! ### `curve_models.rs` (`64bit-notables`) -/

namespace backend.serial.curve_models

namespace ProjectivePoint.«64bit-notables»

theorem onCurve_iff (self : ProjectivePoint.«64bit-notables») :
    self.OnCurve ↔ self.toProjective.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the equation. -/
theorem onCurve_iff_equation (self : ProjectivePoint.«64bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toProjective_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : ProjectivePoint.«64bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Projective.onCurve_iff_homogeneous, toProjective_def, edwards_a, edwards_d]

theorem toPoint_x {self : ProjectivePoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_x h, toProjective_def]

theorem toPoint_y {self : ProjectivePoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_y h, toProjective_def]

theorem toPoint_of_not_onCurve {self : ProjectivePoint.«64bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Projective.toPoint_eq_zero_of_not_onCurve h]

theorem projEq_iff_toPoint_eq {self other : ProjectivePoint.«64bit-notables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) :
    self.toProjective.ProjEq other.toProjective ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Projective.projEq_iff_toPoint_eq hP hQ

end ProjectivePoint.«64bit-notables»

namespace ProjectivePoint.«32bit-notables»

theorem onCurve_iff (self : ProjectivePoint.«32bit-notables») :
    self.OnCurve ↔ self.toProjective.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the equation. -/
theorem onCurve_iff_equation (self : ProjectivePoint.«32bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toProjective_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : ProjectivePoint.«32bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Projective.onCurve_iff_homogeneous, toProjective_def, edwards_a, edwards_d]

theorem toPoint_x {self : ProjectivePoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_x h, toProjective_def]

theorem toPoint_y {self : ProjectivePoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Projective.toPoint_y h, toProjective_def]

theorem toPoint_of_not_onCurve {self : ProjectivePoint.«32bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Projective.toPoint_eq_zero_of_not_onCurve h]

theorem projEq_iff_toPoint_eq {self other : ProjectivePoint.«32bit-notables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) :
    self.toProjective.ProjEq other.toProjective ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Projective.projEq_iff_toPoint_eq hP hQ

end ProjectivePoint.«32bit-notables»

namespace CompletedPoint.«64bit-notables»

theorem onCurve_iff (self : CompletedPoint.«64bit-notables») :
    self.OnCurve ↔ self.toCompleted.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : CompletedPoint.«64bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.T.toField) := by
  rw [onCurve_iff, toCompleted_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : CompletedPoint.«64bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.T.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 2 * self.T.toField ^ 2 +
          d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Completed.onCurve_iff_homogeneous, toCompleted_def, edwards_a, edwards_d]

theorem toPoint_x {self : CompletedPoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Completed.toPoint_x h, toCompleted_def]

theorem toPoint_y {self : CompletedPoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.T.toField := by
  rw [toPoint_def, Completed.toPoint_y h, toCompleted_def]

theorem toPoint_of_not_onCurve {self : CompletedPoint.«64bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Completed.toPoint_eq_zero_of_not_onCurve h]

end CompletedPoint.«64bit-notables»

namespace CompletedPoint.«32bit-notables»

theorem onCurve_iff (self : CompletedPoint.«32bit-notables») :
    self.OnCurve ↔ self.toCompleted.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : CompletedPoint.«32bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.T.toField) := by
  rw [onCurve_iff, toCompleted_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : CompletedPoint.«32bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧ self.T.toField ≠ 0 ∧
      a * self.X.toField ^ 2 * self.T.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 2 * self.T.toField ^ 2 +
          d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Completed.onCurve_iff_homogeneous, toCompleted_def, edwards_a, edwards_d]

theorem toPoint_x {self : CompletedPoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Completed.toPoint_x h, toCompleted_def]

theorem toPoint_y {self : CompletedPoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.T.toField := by
  rw [toPoint_def, Completed.toPoint_y h, toCompleted_def]

theorem toPoint_of_not_onCurve {self : CompletedPoint.«32bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Completed.toPoint_eq_zero_of_not_onCurve h]

end CompletedPoint.«32bit-notables»

/-- The coordinates of a 32-bit completed point are below `3 · 2^26`, the input bound of `mul`
(`Z` is a sum `2 Z + T`, so `LimbsLt 27` is too weak). -/
@[expose] def CompletedPoint.«32bit-tables».MulBounded
    (self : CompletedPoint.«32bit-tables») : Prop :=
  self.X.MulBounded ∧ self.Y.MulBounded ∧ self.Z.MulBounded ∧ self.T.MulBounded

/-- The coordinates of a 32-bit completed point are below `3 · 2^26`, the input bound of `mul`
(`Z` is a sum `2 Z + T`, so `LimbsLt 27` is too weak). -/
@[expose] def CompletedPoint.«32bit-notables».MulBounded
    (self : CompletedPoint.«32bit-notables») : Prop :=
  self.X.MulBounded ∧ self.Y.MulBounded ∧ self.Z.MulBounded ∧ self.T.MulBounded

namespace AffineNielsPoint.«64bit-notables»

theorem onCurve_iff (self : AffineNielsPoint.«64bit-notables») :
    self.OnCurve ↔ self.toAffineNiels.OnCurve :=
  Iff.rfl

/-- The `x`-coordinate recovered from the Niels form, `((y + x) - (y - x)) / 2`. -/
theorem toAffineNiels_x (self : AffineNielsPoint.«64bit-notables») :
    self.toAffineNiels.x = (self.y_plus_x.toField - self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- The `y`-coordinate recovered from the Niels form, `((y + x) + (y - x)) / 2`. -/
theorem toAffineNiels_y (self : AffineNielsPoint.«64bit-notables») :
    self.toAffineNiels.y = (self.y_plus_x.toField + self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : AffineNielsPoint.«64bit-notables») :
    self.OnCurve ↔ edwards.Equation self.toAffineNiels.x self.toAffineNiels.y ∧
      self.xy2d.toField = 2 * d * self.toAffineNiels.x * self.toAffineNiels.y := by
  rw [onCurve_iff, ← edwards_d]
  have h : self.toAffineNiels.xy2d = self.xy2d.toField := by rw [toAffineNiels_def]
  rw [← h]
  exact Iff.rfl

theorem toPoint_x {self : AffineNielsPoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.toAffineNiels.x := by
  rw [toPoint_def, AffineNiels.toPoint_x h]

theorem toPoint_y {self : AffineNielsPoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.toAffineNiels.y := by
  rw [toPoint_def, AffineNiels.toPoint_y h]

theorem toPoint_of_not_onCurve {self : AffineNielsPoint.«64bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, AffineNiels.toPoint_eq_zero_of_not_onCurve h]

end AffineNielsPoint.«64bit-notables»

namespace AffineNielsPoint.«32bit-notables»

theorem onCurve_iff (self : AffineNielsPoint.«32bit-notables») :
    self.OnCurve ↔ self.toAffineNiels.OnCurve :=
  Iff.rfl

/-- The `x`-coordinate recovered from the Niels form, `((y + x) - (y - x)) / 2`. -/
theorem toAffineNiels_x (self : AffineNielsPoint.«32bit-notables») :
    self.toAffineNiels.x = (self.y_plus_x.toField - self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- The `y`-coordinate recovered from the Niels form, `((y + x) + (y - x)) / 2`. -/
theorem toAffineNiels_y (self : AffineNielsPoint.«32bit-notables») :
    self.toAffineNiels.y = (self.y_plus_x.toField + self.y_minus_x.toField) / 2 := by
  rw [toAffineNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : AffineNielsPoint.«32bit-notables») :
    self.OnCurve ↔ edwards.Equation self.toAffineNiels.x self.toAffineNiels.y ∧
      self.xy2d.toField = 2 * d * self.toAffineNiels.x * self.toAffineNiels.y := by
  rw [onCurve_iff, ← edwards_d]
  have h : self.toAffineNiels.xy2d = self.xy2d.toField := by rw [toAffineNiels_def]
  rw [← h]
  exact Iff.rfl

theorem toPoint_x {self : AffineNielsPoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.toAffineNiels.x := by
  rw [toPoint_def, AffineNiels.toPoint_x h]

theorem toPoint_y {self : AffineNielsPoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.toAffineNiels.y := by
  rw [toPoint_def, AffineNiels.toPoint_y h]

theorem toPoint_of_not_onCurve {self : AffineNielsPoint.«32bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, AffineNiels.toPoint_eq_zero_of_not_onCurve h]

end AffineNielsPoint.«32bit-notables»

namespace ProjectiveNielsPoint.«64bit-notables»

theorem onCurve_iff (self : ProjectiveNielsPoint.«64bit-notables») :
    self.OnCurve ↔ self.toProjectiveNiels.OnCurve :=
  Iff.rfl

/-- The `X`-coordinate recovered from the Niels form, `((Y + X) - (Y - X)) / 2`. -/
theorem toProjectiveNiels_X (self : ProjectiveNielsPoint.«64bit-notables») :
    self.toProjectiveNiels.X = (self.Y_plus_X.toField - self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- The `Y`-coordinate recovered from the Niels form, `((Y + X) + (Y - X)) / 2`. -/
theorem toProjectiveNiels_Y (self : ProjectiveNielsPoint.«64bit-notables») :
    self.toProjectiveNiels.Y = (self.Y_plus_X.toField + self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : ProjectiveNielsPoint.«64bit-notables») :
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

theorem toPoint_x {self : ProjectiveNielsPoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.toProjectiveNiels.X / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_x h, toProjectiveNiels_def]

theorem toPoint_y {self : ProjectiveNielsPoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.toProjectiveNiels.Y / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_y h, toProjectiveNiels_def]

theorem toPoint_of_not_onCurve {self : ProjectiveNielsPoint.«64bit-notables»}
    (h : ¬ self.OnCurve) : self.toPoint = 0 := by
  rw [toPoint_def, ProjectiveNiels.toPoint_eq_zero_of_not_onCurve h]

end ProjectiveNielsPoint.«64bit-notables»

namespace ProjectiveNielsPoint.«32bit-notables»

theorem onCurve_iff (self : ProjectiveNielsPoint.«32bit-notables») :
    self.OnCurve ↔ self.toProjectiveNiels.OnCurve :=
  Iff.rfl

/-- The `X`-coordinate recovered from the Niels form, `((Y + X) - (Y - X)) / 2`. -/
theorem toProjectiveNiels_X (self : ProjectiveNielsPoint.«32bit-notables») :
    self.toProjectiveNiels.X = (self.Y_plus_X.toField - self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- The `Y`-coordinate recovered from the Niels form, `((Y + X) + (Y - X)) / 2`. -/
theorem toProjectiveNiels_Y (self : ProjectiveNielsPoint.«32bit-notables») :
    self.toProjectiveNiels.Y = (self.Y_plus_X.toField + self.Y_minus_X.toField) / 2 := by
  rw [toProjectiveNiels_def]
  rfl

/-- `OnCurve` on the limbs' values. -/
theorem onCurve_iff_equation (self : ProjectiveNielsPoint.«32bit-notables») :
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

theorem toPoint_x {self : ProjectiveNielsPoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.toProjectiveNiels.X / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_x h, toProjectiveNiels_def]

theorem toPoint_y {self : ProjectiveNielsPoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.toProjectiveNiels.Y / self.Z.toField := by
  rw [toPoint_def, ProjectiveNiels.toPoint_y h, toProjectiveNiels_def]

theorem toPoint_of_not_onCurve {self : ProjectiveNielsPoint.«32bit-notables»}
    (h : ¬ self.OnCurve) : self.toPoint = 0 := by
  rw [toPoint_def, ProjectiveNiels.toPoint_eq_zero_of_not_onCurve h]

end ProjectiveNielsPoint.«32bit-notables»

end backend.serial.curve_models

/-! ### `edwards.rs` (`64bit-notables`) -/

namespace edwards.EdwardsPoint.«64bit-notables»

theorem onCurve_iff (self : EdwardsPoint.«64bit-notables») :
    self.OnCurve ↔ self.toExtended.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : EdwardsPoint.«64bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toExtended_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : EdwardsPoint.«64bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Extended.onCurve_iff_homogeneous, toExtended_def, edwards_a, edwards_d]

theorem toPoint_x {self : EdwardsPoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_x h, toExtended_def]

theorem toPoint_y {self : EdwardsPoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_y h, toExtended_def]

theorem toPoint_of_not_onCurve {self : EdwardsPoint.«64bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Extended.toPoint_eq_zero_of_not_onCurve h]

/-- `ProjEq` on the limbs' values: `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁`. -/
theorem projEq_iff (self other : EdwardsPoint.«64bit-notables») :
    self.ProjEq other ↔ self.X.toField * other.Z.toField = other.X.toField * self.Z.toField ∧
      self.Y.toField * other.Z.toField = other.Y.toField * self.Z.toField := by
  change self.toExtended.ProjEq other.toExtended ↔ _
  rw [toExtended_def, toExtended_def]
  exact Iff.rfl

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {self other : EdwardsPoint.«64bit-notables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) : self.ProjEq other ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Extended.projEq_iff_toPoint_eq hP hQ

end edwards.EdwardsPoint.«64bit-notables»

namespace edwards.EdwardsPoint.«32bit-notables»

theorem onCurve_iff (self : EdwardsPoint.«32bit-notables») :
    self.OnCurve ↔ self.toExtended.OnCurve :=
  Iff.rfl

/-- `OnCurve` on the limbs' values: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` satisfies the
equation. -/
theorem onCurve_iff_equation (self : EdwardsPoint.«32bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      edwards.Equation (self.X.toField / self.Z.toField) (self.Y.toField / self.Z.toField) := by
  rw [onCurve_iff, toExtended_def]
  exact Iff.rfl

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (self : EdwardsPoint.«32bit-notables») :
    self.OnCurve ↔ self.Z.toField ≠ 0 ∧
      self.X.toField * self.Y.toField = self.Z.toField * self.T.toField ∧
      a * self.X.toField ^ 2 * self.Z.toField ^ 2 + self.Y.toField ^ 2 * self.Z.toField ^ 2 =
        self.Z.toField ^ 4 + d * self.X.toField ^ 2 * self.Y.toField ^ 2 := by
  rw [onCurve_iff, Extended.onCurve_iff_homogeneous, toExtended_def, edwards_a, edwards_d]

theorem toPoint_x {self : EdwardsPoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.X.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_x h, toExtended_def]

theorem toPoint_y {self : EdwardsPoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.Y.toField / self.Z.toField := by
  rw [toPoint_def, Extended.toPoint_y h, toExtended_def]

theorem toPoint_of_not_onCurve {self : EdwardsPoint.«32bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, Extended.toPoint_eq_zero_of_not_onCurve h]

/-- `ProjEq` on the limbs' values: `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁`. -/
theorem projEq_iff (self other : EdwardsPoint.«32bit-notables») :
    self.ProjEq other ↔ self.X.toField * other.Z.toField = other.X.toField * self.Z.toField ∧
      self.Y.toField * other.Z.toField = other.Y.toField * self.Z.toField := by
  change self.toExtended.ProjEq other.toExtended ↔ _
  rw [toExtended_def, toExtended_def]
  exact Iff.rfl

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {self other : EdwardsPoint.«32bit-notables»} (hP : self.OnCurve)
    (hQ : other.OnCurve) : self.ProjEq other ↔ self.toPoint = other.toPoint := by
  rw [toPoint_def, toPoint_def]
  exact Extended.projEq_iff_toPoint_eq hP hQ

end edwards.EdwardsPoint.«32bit-notables»

namespace edwards.affine.AffinePoint.«64bit-notables»

theorem onCurve_iff (self : AffinePoint.«64bit-notables») :
    self.OnCurve ↔ edwards.Equation self.x.toField self.y.toField :=
  Iff.rfl

theorem toPoint_eq_mk {self : AffinePoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint = ⟨self.x.toField, self.y.toField, h⟩ := by
  rw [toPoint_def, dite_eq_left h]

theorem toPoint_x {self : AffinePoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.x.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_y {self : AffinePoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.y.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_of_not_onCurve {self : AffinePoint.«64bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, dite_eq_right h]

/-- The affine point and the extended coordinates `(x : y : 1 : x y)` of `to_edwards`. -/
theorem toExtended_toPoint {self : AffinePoint.«64bit-notables»} (h : self.OnCurve) :
    self.toPoint.toExtended =
      ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ := by
  rw [toPoint_eq_mk h]
  rfl

end edwards.affine.AffinePoint.«64bit-notables»

namespace edwards.affine.AffinePoint.«32bit-notables»

theorem onCurve_iff (self : AffinePoint.«32bit-notables») :
    self.OnCurve ↔ edwards.Equation self.x.toField self.y.toField :=
  Iff.rfl

theorem toPoint_eq_mk {self : AffinePoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint = ⟨self.x.toField, self.y.toField, h⟩ := by
  rw [toPoint_def, dite_eq_left h]

theorem toPoint_x {self : AffinePoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.x = self.x.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_y {self : AffinePoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.y = self.y.toField := by
  rw [toPoint_eq_mk h]

theorem toPoint_of_not_onCurve {self : AffinePoint.«32bit-notables»} (h : ¬ self.OnCurve) :
    self.toPoint = 0 := by
  rw [toPoint_def, dite_eq_right h]

/-- The affine point and the extended coordinates `(x : y : 1 : x y)` of `to_edwards`. -/
theorem toExtended_toPoint {self : AffinePoint.«32bit-notables»} (h : self.OnCurve) :
    self.toPoint.toExtended =
      ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ := by
  rw [toPoint_eq_mk h]
  rfl

end edwards.affine.AffinePoint.«32bit-notables»

/-! ### `montgomery.rs` (`64bit-notables`) -/

namespace montgomery.ProjectivePoint.«64bit-notables»

/-- The affine `u`-coordinate `U / W` (`0` at `W = 0`), what `as_affine` computes. -/
theorem toXZ_toU (self : ProjectivePoint.«64bit-notables») :
    self.toXZ.toU = self.U.toField / self.W.toField := by
  rw [toXZ_def]
  rfl

end montgomery.ProjectivePoint.«64bit-notables»

namespace montgomery.ProjectivePoint.«32bit-notables»

/-- The affine `u`-coordinate `U / W` (`0` at `W = 0`), what `as_affine` computes. -/
theorem toXZ_toU (self : ProjectivePoint.«32bit-notables») :
    self.toXZ.toU = self.U.toField / self.W.toField := by
  rw [toXZ_def]
  rfl

end montgomery.ProjectivePoint.«32bit-notables»

end Curve25519Dalek
