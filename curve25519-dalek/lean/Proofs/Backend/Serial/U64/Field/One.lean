/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.FromLimbs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51
@[step]
theorem ONE_spec :
    ONE ⦃ (r : FieldElement51) =>
      r.asNat = 1 ∧ r.LimbsLt 51 ⦄ := by
  unfold ONE
  simp only [field.FieldElement51.asNat_def, Array.asNat_def]
  step*
  subst_vars
  decide
end Curve25519Dalek.backend.serial.u64.field.FieldElement51
