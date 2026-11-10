/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.SquareLimbs
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51
@[step]
theorem square_spec (self : FieldElement51) (hself : self.LimbsLt 54) :
    square self ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ 2 % p ∧ r.LimbsLt 52 ⦄ := by
  unfold square
  step*
end Curve25519Dalek.backend.serial.u64.field.FieldElement51
