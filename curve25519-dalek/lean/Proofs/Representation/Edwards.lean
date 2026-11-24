module
public import ForHumans.Specs.Representation
import all ForHumans.Specs.Representation.Edwards
import all ForHumans.Specs.Representation.Edwards.Bits32Tables
import all ForHumans.Specs.Representation.Edwards.Bits64NoTables
import all ForHumans.Specs.Representation.Edwards.Bits32NoTables
public import Proofs.Representation.Window
public import Proofs.Representation.Array
public section

open Aeneas Aeneas.Std
open curve25519 (p)
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.edwards

/-! ### `EdwardsPoint` (`64bit-tables`) -/

namespace EdwardsPoint.«64bit-tables»

theorem toExtended_def (self : EdwardsPoint.«64bit-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

theorem toPoint_def (self : EdwardsPoint.«64bit-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«64bit-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

end EdwardsPoint.«64bit-tables»

namespace EdwardsPoint.«32bit-tables»

theorem toExtended_def (self : EdwardsPoint.«32bit-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

theorem toPoint_def (self : EdwardsPoint.«32bit-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«32bit-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

end EdwardsPoint.«32bit-tables»

/-! ### `AffinePoint` (`64bit-tables`) -/

namespace affine.AffinePoint.«64bit-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«64bit-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«64bit-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«64bit-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«64bit-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«64bit-tables»

namespace affine.AffinePoint.«32bit-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«32bit-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«32bit-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«32bit-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«32bit-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«32bit-tables»

/-! ### `EdwardsPoint` (`64bit-notables`) -/

namespace EdwardsPoint.«64bit-notables»

theorem toExtended_def (self : EdwardsPoint.«64bit-notables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

theorem toPoint_def (self : EdwardsPoint.«64bit-notables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«64bit-notables») : Prop :=
  self.toExtended.ProjEq other.toExtended

end EdwardsPoint.«64bit-notables»

namespace EdwardsPoint.«32bit-notables»

theorem toExtended_def (self : EdwardsPoint.«32bit-notables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

theorem toPoint_def (self : EdwardsPoint.«32bit-notables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«32bit-notables») : Prop :=
  self.toExtended.ProjEq other.toExtended

end EdwardsPoint.«32bit-notables»

/-! ### `AffinePoint` (`64bit-notables`) -/

namespace affine.AffinePoint.«64bit-notables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«64bit-notables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«64bit-notables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«64bit-notables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«64bit-notables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«64bit-notables»

namespace affine.AffinePoint.«32bit-notables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«32bit-notables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«32bit-notables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«32bit-notables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«32bit-notables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«32bit-notables»

end Curve25519Dalek.edwards
