/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Curves
public import Curve25519Dalek.Types
public section

/-! # The limbs of the lookup tables of `window.rs`

A lookup table is an array of entries (`LookupTable T = Array T 8`, `LookupTableRadix32/64/128/256
T = Array T 16/32/64/128`, `NafLookupTable5 T = Array T 8`, `NafLookupTable8 T = Array T 64`), for
any entry type `T` with a `PointRepr`: whether an entry represents a point, the point it
represents, and the bounds on its limbs. The entry types are the affine Niels points
(`Representation/CurveModels.lean`) and, in the proofs, the projective Niels points.
`….LimbsLt n t` says that every limb of every entry is `< 2^n`. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

/-- A dalek point structure that can be a table entry: whether it represents a point, the point
it represents, and its limb bounds. -/
class PointRepr (T : Type) where
  /-- The entry represents a point (`OnCurve` of its structure). -/
  OnCurve : T → Prop
  /-- The point represented (`toPoint` of its structure). -/
  toPoint : T → curve25519.edwards.Point
  /-- Every limb is `< 2^n` (`LimbsLt` of its structure). -/
  LimbsLt : ℕ → T → Prop

end Curve25519Dalek

namespace Curve25519Dalek.window

variable {T : Type} [Inhabited T] [PointRepr T]

/-- Every limb of every entry of `t` is `< 2^n`. -/
@[expose] def LookupTable.LimbsLt (n : ℕ) (t : LookupTable T) : Prop :=
  ∀ j < 8, PointRepr.LimbsLt n t[j]!

/-- Every limb of every entry of `t` is `< 2^n`. -/
@[expose] def LookupTableRadix32.LimbsLt (n : ℕ) (t : LookupTableRadix32 T) : Prop :=
  ∀ j < 16, PointRepr.LimbsLt n t[j]!

/-- Every limb of every entry of `t` is `< 2^n`. -/
@[expose] def LookupTableRadix64.LimbsLt (n : ℕ) (t : LookupTableRadix64 T) : Prop :=
  ∀ j < 32, PointRepr.LimbsLt n t[j]!

/-- Every limb of every entry of `t` is `< 2^n`. -/
@[expose] def LookupTableRadix128.LimbsLt (n : ℕ) (t : LookupTableRadix128 T) : Prop :=
  ∀ j < 64, PointRepr.LimbsLt n t[j]!

/-- Every limb of every entry of `t` is `< 2^n`. -/
@[expose] def LookupTableRadix256.LimbsLt (n : ℕ) (t : LookupTableRadix256 T) : Prop :=
  ∀ j < 128, PointRepr.LimbsLt n t[j]!

/-- Every limb of every entry of `t` is `< 2^n`. -/
@[expose] def NafLookupTable5.LimbsLt (n : ℕ) (t : NafLookupTable5 T) : Prop :=
  ∀ k < 8, PointRepr.LimbsLt n t[k]!

/-- Every limb of every entry of `t` is `< 2^n`. -/
@[expose] def NafLookupTable8.LimbsLt (n : ℕ) (t : NafLookupTable8 T) : Prop :=
  ∀ k < 64, PointRepr.LimbsLt n t[k]!

end Curve25519Dalek.window
