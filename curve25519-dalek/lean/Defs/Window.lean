/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.CurveModels
public section

/-! # The lookup tables of `window.rs` (audited)

A table is an array of Niels points (`LookupTable T = Array T 8`, `LookupTableRadix32/64/128/256
T = Array T 16/32/64/128`, `NafLookupTable5 T = Array T 8`, `NafLookupTable8 T = Array T 64`),
generic in the entry type `T`. The entry types are the four Niels structures of `Defs.CurveModels`
(`ProjectiveNielsPoint`, `AffineNielsPoint`, in all four configurations); the class
`PointRepr` collects their `OnCurve`, `toPoint` and `LimbsLt`, so that each table predicate is
stated once: `….LimbsLt n t` says that every limb of every entry is `< 2^n`.

The basepoint tables of `edwards.rs` are in `Defs.Edwards`, the precomputations of
`scalar_mul` in `Defs.ScalarMul`. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

/-- A dalek point structure usable as a table entry: its curve predicate, the point it
represents and its limb bounds (the definitions of `Defs.CurveModels`, as instance fields). -/
class PointRepr (T : Type) where
  /-- The entry represents a point (`OnCurve` of its structure). -/
  OnCurve : T → Prop
  /-- The point represented (`toPoint` of its structure). -/
  toPoint : T → curve25519.edwards.Point
  /-- Every limb is `< 2^n` (`LimbsLt` of its structure). -/
  LimbsLt : ℕ → T → Prop

/-! ### The entry types -/

namespace backend.serial.curve_models

noncomputable instance ProjectiveNielsPoint.«x86_64-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«x86_64-tables» where
  OnCurve := ProjectiveNielsPoint.«x86_64-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«x86_64-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«x86_64-tables».LimbsLt

noncomputable instance ProjectiveNielsPoint.«i686-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«i686-tables» where
  OnCurve := ProjectiveNielsPoint.«i686-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«i686-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«i686-tables».LimbsLt

noncomputable instance ProjectiveNielsPoint.«x86_64-no-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«x86_64-no-tables» where
  OnCurve := ProjectiveNielsPoint.«x86_64-no-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«x86_64-no-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«x86_64-no-tables».LimbsLt

noncomputable instance ProjectiveNielsPoint.«i686-no-tables».instPointRepr :
    PointRepr ProjectiveNielsPoint.«i686-no-tables» where
  OnCurve := ProjectiveNielsPoint.«i686-no-tables».OnCurve
  toPoint := ProjectiveNielsPoint.«i686-no-tables».toPoint
  LimbsLt := ProjectiveNielsPoint.«i686-no-tables».LimbsLt

noncomputable instance AffineNielsPoint.«x86_64-tables».instPointRepr :
    PointRepr AffineNielsPoint.«x86_64-tables» where
  OnCurve := AffineNielsPoint.«x86_64-tables».OnCurve
  toPoint := AffineNielsPoint.«x86_64-tables».toPoint
  LimbsLt := AffineNielsPoint.«x86_64-tables».LimbsLt

noncomputable instance AffineNielsPoint.«i686-tables».instPointRepr :
    PointRepr AffineNielsPoint.«i686-tables» where
  OnCurve := AffineNielsPoint.«i686-tables».OnCurve
  toPoint := AffineNielsPoint.«i686-tables».toPoint
  LimbsLt := AffineNielsPoint.«i686-tables».LimbsLt

noncomputable instance AffineNielsPoint.«x86_64-no-tables».instPointRepr :
    PointRepr AffineNielsPoint.«x86_64-no-tables» where
  OnCurve := AffineNielsPoint.«x86_64-no-tables».OnCurve
  toPoint := AffineNielsPoint.«x86_64-no-tables».toPoint
  LimbsLt := AffineNielsPoint.«x86_64-no-tables».LimbsLt

noncomputable instance AffineNielsPoint.«i686-no-tables».instPointRepr :
    PointRepr AffineNielsPoint.«i686-no-tables» where
  OnCurve := AffineNielsPoint.«i686-no-tables».OnCurve
  toPoint := AffineNielsPoint.«i686-no-tables».toPoint
  LimbsLt := AffineNielsPoint.«i686-no-tables».LimbsLt

end backend.serial.curve_models

/-! ### The tables -/

namespace window

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

end window

end Curve25519Dalek
