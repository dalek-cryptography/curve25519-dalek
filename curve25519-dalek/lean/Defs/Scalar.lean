/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
module
public import Curve25519Dalek.Types
public import Defs.Array
public section

/-! # The value of a `Scalar` (audited) -/

open Aeneas.Std

namespace Curve25519Dalek

/-- The natural number encoded little-endian by the 32 bytes of a `Scalar` (not necessarily
reduced modulo `L`). -/
def scalar.Scalar.asNat (self : scalar.Scalar) : ℕ :=
  self.bytes.asNat 8

/-- The natural number encoded by a `HalfWidthScalar` (a `Scalar` meant to be below `2^128`). -/
def scalar.HalfWidthScalar.asNat (self : scalar.HalfWidthScalar) : ℕ :=
  scalar.Scalar.asNat self

theorem scalar.Scalar.asNat_def (self : scalar.Scalar) : self.asNat = self.bytes.asNat 8 := by
  unfold scalar.Scalar.asNat
  rfl

theorem scalar.HalfWidthScalar.asNat_def (self : scalar.HalfWidthScalar) :
    self.asNat = scalar.Scalar.asNat self := by
  unfold scalar.HalfWidthScalar.asNat
  rfl

/-- Needed for `a[i]!` on arrays of scalars; the default (the zero scalar) is never observed for
in-range indices. -/
instance instInhabitedScalar : Inhabited scalar.Scalar := ⟨⟨Array.repeat 32#usize 0#u8⟩⟩

end Curve25519Dalek
