/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Curves
public import ForHumans.Specs.Models
public import ForHumans.Specs.Representation.FieldElement51
public import ForHumans.Specs.Representation.Window
public section

/-! # The point an `AffineNielsPoint` represents

The precomputed tables store affine Niels points (`backend/serial/curve_models.rs`): three field
elements `(y + x, y - x, 2 d x y)` of an affine point `(x, y)` (`AffineNiels` in
`ForHumans.Specs.Models`). `OnCurve` says that the three are those of a point, `toPoint` is that
point (`0` otherwise), and `LimbsLt n` that every limb is `< 2^n`; the instance `PointRepr`
(`Representation/Window.lean`) makes them those of a table entry.

The definitions are written for `x86_64-tables`; `scripts/gen-config-specs.py` generates the
other configurations' copies in `Representation/CurveModels/`. -/

open Aeneas Aeneas.Std

-- BEGIN PER-CONFIG

namespace Curve25519Dalek.backend.serial.curve_models.AffineNielsPoint.«x86_64-tables»

/-- The affine Niels coordinates `(y + x, y - x, 2 d x y)` as field elements. -/
noncomputable def toAffineNiels (self : AffineNielsPoint.«x86_64-tables») :
    curve25519.edwards.AffineNiels :=
  ⟨self.y_plus_x.toField, self.y_minus_x.toField, self.xy2d.toField⟩

/-- `self` represents a point: with `x := ((y + x) - (y - x)) / 2` and
`y := ((y + x) + (y - x)) / 2`, `(x, y)` is on the curve and `xy2d = 2 d x y`. -/
@[expose] def OnCurve (self : AffineNielsPoint.«x86_64-tables») : Prop :=
  self.toAffineNiels.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffineNielsPoint.«x86_64-tables») :
    curve25519.edwards.Point :=
  self.toAffineNiels.toPoint

/-- Every limb of an `AffineNielsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffineNielsPoint.«x86_64-tables») : Prop :=
  self.y_plus_x.LimbsLt n ∧ self.y_minus_x.LimbsLt n ∧ self.xy2d.LimbsLt n

/-- Needed for `t[j]!` on tables of `AffineNielsPoint`s; the default is never observed for
in-range indices. -/
instance instInhabited : Inhabited (AffineNielsPoint.«x86_64-tables») :=
  ⟨⟨default, default, default⟩⟩

noncomputable instance instPointRepr : PointRepr AffineNielsPoint.«x86_64-tables» where
  OnCurve := OnCurve
  toPoint := toPoint
  LimbsLt := LimbsLt

end Curve25519Dalek.backend.serial.curve_models.AffineNielsPoint.«x86_64-tables»

-- END PER-CONFIG
