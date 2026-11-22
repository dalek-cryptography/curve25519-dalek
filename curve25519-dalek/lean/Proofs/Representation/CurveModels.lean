/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Curve25519.Edwards.Basic
public import Proofs.Representation.FieldElement2625
public import Proofs.Representation.FieldElement51
public import ForHumans.Specs.Representation
import all ForHumans.Specs.Representation.CurveModels
import all ForHumans.Specs.Representation.CurveModels.Bits32Tables
import all ForHumans.Specs.Representation.CurveModels.Bits64NoTables
import all ForHumans.Specs.Representation.CurveModels.Bits32NoTables
public section

/-! # The point structures of `curve_models.rs` (audited)

`ProjectivePoint`, `CompletedPoint`, `AffineNielsPoint` and `ProjectiveNielsPoint` of
`backend/serial/curve_models.rs` implement the coordinate systems `Projective`, `Completed`,
`AffineNiels` and `ProjectiveNiels` of the Edwards model `curve25519.edwards` on
radix-`2^51` limbs (64-bit, `FieldElement51`) or radix-`2^25.5` limbs (32-bit,
`FieldElement2625`). Each structure `S` gets:

- `S.toX : S → curve25519.edwards.X`, its coordinates as field elements (hidden, `toX_def`);
- `S.OnCurve := (toX self).OnCurve`, the algebraic validity (exposed);
- `S.toPoint := (toX self).toPoint`, the point represented, `0` off the curve (hidden,
  `toPoint_def`);
- `S.LimbsLt n`: every limb is `< 2^n` (exposed). The 64-bit specs use `LimbsLt 52` for
  `ProjectivePoint` and `LimbsLt 54` for the three others.

The definitions for `AffineNielsPoint`, the entries of the precomputed tables, are in
`ForHumans/Specs/Representation/CurveModels.lean`; this file has their unfolding lemmas.

The four configurations (`«64bit-tables»`, `«64bit-notables»`, `«32bit-tables»`,
`«32bit-notables»`) have distinct structures with identical bodies, so every definition appears
four times. -/

open Aeneas Aeneas.Std
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.curve_models

/-! ### `ProjectivePoint` (`64bit-tables`) -/

namespace ProjectivePoint.«64bit-tables»

/-- The projective coordinates `(X : Y : Z)` as field elements. -/
noncomputable def toProjective (self : ProjectivePoint.«64bit-tables») :
    curve25519.edwards.Projective :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField⟩

theorem toProjective_def (self : ProjectivePoint.«64bit-tables») :
    self.toProjective = ⟨self.X.toField, self.Y.toField, self.Z.toField⟩ := by
  unfold toProjective
  rfl

/-- `self` represents a point: `Z ≠ 0` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : ProjectivePoint.«64bit-tables») : Prop :=
  self.toProjective.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectivePoint.«64bit-tables») :
    curve25519.edwards.Point :=
  self.toProjective.toPoint

theorem toPoint_def (self : ProjectivePoint.«64bit-tables») :
    self.toPoint = self.toProjective.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«64bit-tables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n

end ProjectivePoint.«64bit-tables»

namespace ProjectivePoint.«32bit-tables»

/-- The projective coordinates `(X : Y : Z)` as field elements. -/
noncomputable def toProjective (self : ProjectivePoint.«32bit-tables») :
    curve25519.edwards.Projective :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField⟩

theorem toProjective_def (self : ProjectivePoint.«32bit-tables») :
    self.toProjective = ⟨self.X.toField, self.Y.toField, self.Z.toField⟩ := by
  unfold toProjective
  rfl

/-- `self` represents a point: `Z ≠ 0` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : ProjectivePoint.«32bit-tables») : Prop :=
  self.toProjective.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectivePoint.«32bit-tables») :
    curve25519.edwards.Point :=
  self.toProjective.toPoint

theorem toPoint_def (self : ProjectivePoint.«32bit-tables») :
    self.toPoint = self.toProjective.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«32bit-tables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n

end ProjectivePoint.«32bit-tables»

/-! ### `CompletedPoint` (`64bit-tables`) -/

namespace CompletedPoint.«64bit-tables»

/-- The completed coordinates `((X : Z), (Y : T))` as field elements. -/
noncomputable def toCompleted (self : CompletedPoint.«64bit-tables») :
    curve25519.edwards.Completed :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toCompleted_def (self : CompletedPoint.«64bit-tables») :
    self.toCompleted = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toCompleted
  rfl

/-- `self` represents a point: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` is on the curve. -/
@[expose] def OnCurve (self : CompletedPoint.«64bit-tables») : Prop :=
  self.toCompleted.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : CompletedPoint.«64bit-tables») :
    curve25519.edwards.Point :=
  self.toCompleted.toPoint

theorem toPoint_def (self : CompletedPoint.«64bit-tables») :
    self.toPoint = self.toCompleted.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `CompletedPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : CompletedPoint.«64bit-tables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T.LimbsLt n

end CompletedPoint.«64bit-tables»

namespace CompletedPoint.«32bit-tables»

/-- The completed coordinates `((X : Z), (Y : T))` as field elements. -/
noncomputable def toCompleted (self : CompletedPoint.«32bit-tables») :
    curve25519.edwards.Completed :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toCompleted_def (self : CompletedPoint.«32bit-tables») :
    self.toCompleted = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toCompleted
  rfl

/-- `self` represents a point: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` is on the curve. -/
@[expose] def OnCurve (self : CompletedPoint.«32bit-tables») : Prop :=
  self.toCompleted.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : CompletedPoint.«32bit-tables») :
    curve25519.edwards.Point :=
  self.toCompleted.toPoint

theorem toPoint_def (self : CompletedPoint.«32bit-tables») :
    self.toPoint = self.toCompleted.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `CompletedPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : CompletedPoint.«32bit-tables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T.LimbsLt n

end CompletedPoint.«32bit-tables»

/-! ### `AffineNielsPoint` (`64bit-tables`) -/

namespace AffineNielsPoint.«64bit-tables»

theorem toAffineNiels_def (self : AffineNielsPoint.«64bit-tables») :
    self.toAffineNiels =
      ⟨self.y_plus_x.toField, self.y_minus_x.toField, self.xy2d.toField⟩ := by
  unfold toAffineNiels
  rfl

theorem toPoint_def (self : AffineNielsPoint.«64bit-tables») :
    self.toPoint = self.toAffineNiels.toPoint := by
  unfold toPoint
  rfl

end AffineNielsPoint.«64bit-tables»

namespace AffineNielsPoint.«32bit-tables»

theorem toAffineNiels_def (self : AffineNielsPoint.«32bit-tables») :
    self.toAffineNiels =
      ⟨self.y_plus_x.toField, self.y_minus_x.toField, self.xy2d.toField⟩ := by
  unfold toAffineNiels
  rfl

theorem toPoint_def (self : AffineNielsPoint.«32bit-tables») :
    self.toPoint = self.toAffineNiels.toPoint := by
  unfold toPoint
  rfl

end AffineNielsPoint.«32bit-tables»

/-! ### `ProjectiveNielsPoint` (`64bit-tables`) -/

namespace ProjectiveNielsPoint.«64bit-tables»

/-- The projective Niels coordinates `(Y + X : Y - X : Z : 2 d T)` as field elements. -/
noncomputable def toProjectiveNiels (self : ProjectiveNielsPoint.«64bit-tables») :
    curve25519.edwards.ProjectiveNiels :=
  ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩

theorem toProjectiveNiels_def (self : ProjectiveNielsPoint.«64bit-tables») :
    self.toProjectiveNiels =
      ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩ := by
  unfold toProjectiveNiels
  rfl

/-- `self` represents a point: `Z ≠ 0`, and with `X := ((Y + X) - (Y - X)) / 2` and
`Y := ((Y + X) + (Y - X)) / 2`, `(X / Z, Y / Z)` is on the curve and `T2d Z = 2 d X Y`. -/
@[expose] def OnCurve (self : ProjectiveNielsPoint.«64bit-tables») : Prop :=
  self.toProjectiveNiels.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectiveNielsPoint.«64bit-tables») :
    curve25519.edwards.Point :=
  self.toProjectiveNiels.toPoint

theorem toPoint_def (self : ProjectiveNielsPoint.«64bit-tables») :
    self.toPoint = self.toProjectiveNiels.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `ProjectiveNielsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectiveNielsPoint.«64bit-tables») : Prop :=
  self.Y_plus_X.LimbsLt n ∧ self.Y_minus_X.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T2d.LimbsLt n

/-- Needed for `t[j]!` on tables of `ProjectiveNielsPoint`s; the default is never observed for
in-range indices. -/
instance instInhabited : Inhabited (ProjectiveNielsPoint.«64bit-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end ProjectiveNielsPoint.«64bit-tables»

namespace ProjectiveNielsPoint.«32bit-tables»

/-- The projective Niels coordinates `(Y + X : Y - X : Z : 2 d T)` as field elements. -/
noncomputable def toProjectiveNiels (self : ProjectiveNielsPoint.«32bit-tables») :
    curve25519.edwards.ProjectiveNiels :=
  ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩

theorem toProjectiveNiels_def (self : ProjectiveNielsPoint.«32bit-tables») :
    self.toProjectiveNiels =
      ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩ := by
  unfold toProjectiveNiels
  rfl

/-- `self` represents a point: `Z ≠ 0`, and with `X := ((Y + X) - (Y - X)) / 2` and
`Y := ((Y + X) + (Y - X)) / 2`, `(X / Z, Y / Z)` is on the curve and `T2d Z = 2 d X Y`. -/
@[expose] def OnCurve (self : ProjectiveNielsPoint.«32bit-tables») : Prop :=
  self.toProjectiveNiels.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectiveNielsPoint.«32bit-tables») :
    curve25519.edwards.Point :=
  self.toProjectiveNiels.toPoint

theorem toPoint_def (self : ProjectiveNielsPoint.«32bit-tables») :
    self.toPoint = self.toProjectiveNiels.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `ProjectiveNielsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectiveNielsPoint.«32bit-tables») : Prop :=
  self.Y_plus_X.LimbsLt n ∧ self.Y_minus_X.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T2d.LimbsLt n

/-- Needed for `t[j]!` on tables of `ProjectiveNielsPoint`s; the default is never observed for
in-range indices. -/
instance instInhabited : Inhabited (ProjectiveNielsPoint.«32bit-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end ProjectiveNielsPoint.«32bit-tables»

/-! ### `ProjectivePoint` (`64bit-notables`) -/

namespace ProjectivePoint.«64bit-notables»

/-- The projective coordinates `(X : Y : Z)` as field elements. -/
noncomputable def toProjective (self : ProjectivePoint.«64bit-notables») :
    curve25519.edwards.Projective :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField⟩

theorem toProjective_def (self : ProjectivePoint.«64bit-notables») :
    self.toProjective = ⟨self.X.toField, self.Y.toField, self.Z.toField⟩ := by
  unfold toProjective
  rfl

/-- `self` represents a point: `Z ≠ 0` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : ProjectivePoint.«64bit-notables») : Prop :=
  self.toProjective.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectivePoint.«64bit-notables») :
    curve25519.edwards.Point :=
  self.toProjective.toPoint

theorem toPoint_def (self : ProjectivePoint.«64bit-notables») :
    self.toPoint = self.toProjective.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«64bit-notables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n

end ProjectivePoint.«64bit-notables»

namespace ProjectivePoint.«32bit-notables»

/-- The projective coordinates `(X : Y : Z)` as field elements. -/
noncomputable def toProjective (self : ProjectivePoint.«32bit-notables») :
    curve25519.edwards.Projective :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField⟩

theorem toProjective_def (self : ProjectivePoint.«32bit-notables») :
    self.toProjective = ⟨self.X.toField, self.Y.toField, self.Z.toField⟩ := by
  unfold toProjective
  rfl

/-- `self` represents a point: `Z ≠ 0` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : ProjectivePoint.«32bit-notables») : Prop :=
  self.toProjective.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectivePoint.«32bit-notables») :
    curve25519.edwards.Point :=
  self.toProjective.toPoint

theorem toPoint_def (self : ProjectivePoint.«32bit-notables») :
    self.toPoint = self.toProjective.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `ProjectivePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectivePoint.«32bit-notables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n

end ProjectivePoint.«32bit-notables»

/-! ### `CompletedPoint` (`64bit-notables`) -/

namespace CompletedPoint.«64bit-notables»

/-- The completed coordinates `((X : Z), (Y : T))` as field elements. -/
noncomputable def toCompleted (self : CompletedPoint.«64bit-notables») :
    curve25519.edwards.Completed :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toCompleted_def (self : CompletedPoint.«64bit-notables») :
    self.toCompleted = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toCompleted
  rfl

/-- `self` represents a point: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` is on the curve. -/
@[expose] def OnCurve (self : CompletedPoint.«64bit-notables») : Prop :=
  self.toCompleted.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : CompletedPoint.«64bit-notables») :
    curve25519.edwards.Point :=
  self.toCompleted.toPoint

theorem toPoint_def (self : CompletedPoint.«64bit-notables») :
    self.toPoint = self.toCompleted.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `CompletedPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : CompletedPoint.«64bit-notables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T.LimbsLt n

end CompletedPoint.«64bit-notables»

namespace CompletedPoint.«32bit-notables»

/-- The completed coordinates `((X : Z), (Y : T))` as field elements. -/
noncomputable def toCompleted (self : CompletedPoint.«32bit-notables») :
    curve25519.edwards.Completed :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toCompleted_def (self : CompletedPoint.«32bit-notables») :
    self.toCompleted = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toCompleted
  rfl

/-- `self` represents a point: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)` is on the curve. -/
@[expose] def OnCurve (self : CompletedPoint.«32bit-notables») : Prop :=
  self.toCompleted.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : CompletedPoint.«32bit-notables») :
    curve25519.edwards.Point :=
  self.toCompleted.toPoint

theorem toPoint_def (self : CompletedPoint.«32bit-notables») :
    self.toPoint = self.toCompleted.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `CompletedPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : CompletedPoint.«32bit-notables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T.LimbsLt n

end CompletedPoint.«32bit-notables»

/-! ### `AffineNielsPoint` (`64bit-notables`) -/

namespace AffineNielsPoint.«64bit-notables»

theorem toAffineNiels_def (self : AffineNielsPoint.«64bit-notables») :
    self.toAffineNiels =
      ⟨self.y_plus_x.toField, self.y_minus_x.toField, self.xy2d.toField⟩ := by
  unfold toAffineNiels
  rfl

theorem toPoint_def (self : AffineNielsPoint.«64bit-notables») :
    self.toPoint = self.toAffineNiels.toPoint := by
  unfold toPoint
  rfl

end AffineNielsPoint.«64bit-notables»

namespace AffineNielsPoint.«32bit-notables»

theorem toAffineNiels_def (self : AffineNielsPoint.«32bit-notables») :
    self.toAffineNiels =
      ⟨self.y_plus_x.toField, self.y_minus_x.toField, self.xy2d.toField⟩ := by
  unfold toAffineNiels
  rfl

theorem toPoint_def (self : AffineNielsPoint.«32bit-notables») :
    self.toPoint = self.toAffineNiels.toPoint := by
  unfold toPoint
  rfl

end AffineNielsPoint.«32bit-notables»

/-! ### `ProjectiveNielsPoint` (`64bit-notables`) -/

namespace ProjectiveNielsPoint.«64bit-notables»

/-- The projective Niels coordinates `(Y + X : Y - X : Z : 2 d T)` as field elements. -/
noncomputable def toProjectiveNiels (self : ProjectiveNielsPoint.«64bit-notables») :
    curve25519.edwards.ProjectiveNiels :=
  ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩

theorem toProjectiveNiels_def (self : ProjectiveNielsPoint.«64bit-notables») :
    self.toProjectiveNiels =
      ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩ := by
  unfold toProjectiveNiels
  rfl

/-- `self` represents a point: `Z ≠ 0`, and with `X := ((Y + X) - (Y - X)) / 2` and
`Y := ((Y + X) + (Y - X)) / 2`, `(X / Z, Y / Z)` is on the curve and `T2d Z = 2 d X Y`. -/
@[expose] def OnCurve (self : ProjectiveNielsPoint.«64bit-notables») : Prop :=
  self.toProjectiveNiels.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectiveNielsPoint.«64bit-notables») :
    curve25519.edwards.Point :=
  self.toProjectiveNiels.toPoint

theorem toPoint_def (self : ProjectiveNielsPoint.«64bit-notables») :
    self.toPoint = self.toProjectiveNiels.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `ProjectiveNielsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectiveNielsPoint.«64bit-notables») : Prop :=
  self.Y_plus_X.LimbsLt n ∧ self.Y_minus_X.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T2d.LimbsLt n

/-- Needed for `t[j]!` on tables of `ProjectiveNielsPoint`s; the default is never observed for
in-range indices. -/
instance instInhabited : Inhabited (ProjectiveNielsPoint.«64bit-notables») :=
  ⟨⟨default, default, default, default⟩⟩

end ProjectiveNielsPoint.«64bit-notables»

namespace ProjectiveNielsPoint.«32bit-notables»

/-- The projective Niels coordinates `(Y + X : Y - X : Z : 2 d T)` as field elements. -/
noncomputable def toProjectiveNiels (self : ProjectiveNielsPoint.«32bit-notables») :
    curve25519.edwards.ProjectiveNiels :=
  ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩

theorem toProjectiveNiels_def (self : ProjectiveNielsPoint.«32bit-notables») :
    self.toProjectiveNiels =
      ⟨self.Y_plus_X.toField, self.Y_minus_X.toField, self.Z.toField, self.T2d.toField⟩ := by
  unfold toProjectiveNiels
  rfl

/-- `self` represents a point: `Z ≠ 0`, and with `X := ((Y + X) - (Y - X)) / 2` and
`Y := ((Y + X) + (Y - X)) / 2`, `(X / Z, Y / Z)` is on the curve and `T2d Z = 2 d X Y`. -/
@[expose] def OnCurve (self : ProjectiveNielsPoint.«32bit-notables») : Prop :=
  self.toProjectiveNiels.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : ProjectiveNielsPoint.«32bit-notables») :
    curve25519.edwards.Point :=
  self.toProjectiveNiels.toPoint

theorem toPoint_def (self : ProjectiveNielsPoint.«32bit-notables») :
    self.toPoint = self.toProjectiveNiels.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of a `ProjectiveNielsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : ProjectiveNielsPoint.«32bit-notables») : Prop :=
  self.Y_plus_X.LimbsLt n ∧ self.Y_minus_X.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T2d.LimbsLt n

/-- Needed for `t[j]!` on tables of `ProjectiveNielsPoint`s; the default is never observed for
in-range indices. -/
instance instInhabited : Inhabited (ProjectiveNielsPoint.«32bit-notables») :=
  ⟨⟨default, default, default, default⟩⟩

end ProjectiveNielsPoint.«32bit-notables»

end Curve25519Dalek.backend.serial.curve_models
