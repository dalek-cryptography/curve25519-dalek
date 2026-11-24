module
public import ForHumans.Specs.Curves
public import Curve25519Dalek.Types
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public section

/-! # The lookup tables of `window.rs` (audited)

A table is an array of Niels points (`LookupTable T = Array T 8`, `LookupTableRadix32/64/128/256
T = Array T 16/32/64/128`, `NafLookupTable5 T = Array T 8`, `NafLookupTable8 T = Array T 64`),
generic in the entry type `T`. The entry types are the four Niels structures of
`ForHumans.Specs.Representation.CurveModels` and `Proofs.Representation.CurveModels`
(`ProjectiveNielsPoint`, `AffineNielsPoint`, in all four configurations); the class
`PointRepr` collects their `OnCurve`, `toPoint` and `LimbsLt`, so that each table predicate is
stated once: `….LimbsLt n t` says that every limb of every entry is `< 2^n`.

The basepoint tables of `edwards.rs` are in `ForHumans.Specs.Representation.Edwards`, the
precomputations of `scalar_mul` in `ForHumans.Specs.Representation.ScalarMul`. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

/-- A dalek point structure usable as a table entry: its curve predicate, the point it represents
and its limb bounds (the definitions of `ForHumans.Specs.Representation.CurveModels` and
`Proofs.Representation.CurveModels`, as instance fields). -/
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
