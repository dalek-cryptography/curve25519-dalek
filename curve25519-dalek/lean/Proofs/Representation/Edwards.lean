/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Representation
import all ForHumans.Specs.Representation.Edwards
import all ForHumans.Specs.Representation.Edwards.I686Tables
import all ForHumans.Specs.Representation.Edwards.X86_64NoTables
import all ForHumans.Specs.Representation.Edwards.I686NoTables
public import Proofs.Representation.Window
public import Proofs.Representation.Array
public section

/-! # `edwards.rs`: the unfolding lemmas of the point, and `AffinePoint`

The definitions of `EdwardsPoint` (`toExtended`, `OnCurve`, `toPoint`, `LimbsLt`, `IsBounded`)
and of the basepoint tables (`point`, `IsTable`, `LimbsLt`, `IsBounded`) are in
`ForHumans/Specs/Representation/Edwards.lean`; this file has the unfolding lemmas of the hidden
ones, and the definitions that the statements do not use:

- `EdwardsPoint.ProjEq` (exposed), the projective equality that `ct_eq` computes;
- `AffinePoint` (`edwards/affine.rs`), the affine point itself: `OnCurve` is the curve equation,
  `toPoint` the point (`0` off the curve), `LimbsLt n` as for `EdwardsPoint`. -/

open Aeneas Aeneas.Std
open curve25519 (p)
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.edwards

/-! ### `EdwardsPoint` (`x86_64-tables`) -/

namespace EdwardsPoint.«x86_64-tables»

theorem toExtended_def (self : EdwardsPoint.«x86_64-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

theorem toPoint_def (self : EdwardsPoint.«x86_64-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«x86_64-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

end EdwardsPoint.«x86_64-tables»

namespace EdwardsPoint.«i686-tables»

theorem toExtended_def (self : EdwardsPoint.«i686-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

theorem toPoint_def (self : EdwardsPoint.«i686-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«i686-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

end EdwardsPoint.«i686-tables»

/-! ### `AffinePoint` (`x86_64-tables`) -/

namespace affine.AffinePoint.«x86_64-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«x86_64-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«x86_64-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«x86_64-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«x86_64-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«x86_64-tables»

namespace affine.AffinePoint.«i686-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«i686-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«i686-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«i686-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«i686-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«i686-tables»

/-! ### `EdwardsPoint` (`x86_64-no-tables`) -/

namespace EdwardsPoint.«x86_64-no-tables»

theorem toExtended_def (self : EdwardsPoint.«x86_64-no-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

theorem toPoint_def (self : EdwardsPoint.«x86_64-no-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«x86_64-no-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

end EdwardsPoint.«x86_64-no-tables»

namespace EdwardsPoint.«i686-no-tables»

theorem toExtended_def (self : EdwardsPoint.«i686-no-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

theorem toPoint_def (self : EdwardsPoint.«i686-no-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«i686-no-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

end EdwardsPoint.«i686-no-tables»

/-! ### `AffinePoint` (`x86_64-no-tables`) -/

namespace affine.AffinePoint.«x86_64-no-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«x86_64-no-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«x86_64-no-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«x86_64-no-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«x86_64-no-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«x86_64-no-tables»

namespace affine.AffinePoint.«i686-no-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«i686-no-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«i686-no-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«i686-no-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«i686-no-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«i686-no-tables»

end Curve25519Dalek.edwards
