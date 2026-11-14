/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Curves
public import ForHumans.Specs.Representation.FieldElement51
public section

/-! # The point an `EdwardsPoint` represents

An `EdwardsPoint` holds extended coordinates `(X : Y : Z : T)`, field elements with `x = X / Z`,
`y = Y / Z` and `X Y = Z T`. `toPoint` is that point of edwards25519, or `0` when the coordinates
are not those of a point (`OnCurve`; both from the `EllipticCurve` library).

The definitions are written for `x86_64-tables`; `scripts/gen-config-specs.py` generates the
other configurations' copies in `Representation/Edwards/`. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek.edwards

/-- Needed for `v[i]!` on vectors and arrays of compressed points; the default is never
observed for in-range indices. -/
instance CompressedEdwardsY.instInhabited : Inhabited CompressedEdwardsY :=
  inferInstanceAs (Inhabited (Array U8 32#usize))

end Curve25519Dalek.edwards

-- BEGIN PER-CONFIG

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables»

/-- The extended coordinates `(X : Y : Z : T)` as field elements. -/
noncomputable def toExtended (self : EdwardsPoint.«x86_64-tables») :
    curve25519.edwards.Extended :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

/-- `self` represents a point: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : EdwardsPoint.«x86_64-tables») : Prop :=
  self.toExtended.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : EdwardsPoint.«x86_64-tables») : curve25519.edwards.Point :=
  self.toExtended.toPoint

/-- Needed for `a[i]!` on arrays of points; the default is never observed for in-range
indices. -/
instance instInhabited : Inhabited (EdwardsPoint.«x86_64-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables»

-- END PER-CONFIG
