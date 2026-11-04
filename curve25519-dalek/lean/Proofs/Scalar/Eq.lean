/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
import Proofs.Scalar.CtEq
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar

@[step]
theorem eq_spec (self other : Scalar) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self = other) ⦄ := by
  unfold eq
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨b, hb⟩
  subst hb
  by_cases h : self = other
  · simp [h, hc1 h]
  · simp [h, hc0 h]

end Curve25519Dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar
