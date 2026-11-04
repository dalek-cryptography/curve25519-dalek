/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.FromLimbs
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51
@[step]
theorem MINUS_ONE_spec :
    MINUS_ONE ⦃ (r : FieldElement51) =>
      r.asNat + 1 = p ∧ r.LimbsLt 51 ⦄ := by
  unfold MINUS_ONE
  simp only [field.FieldElement51.asNat_def, Array.asNat_def]
  step*
  subst_vars
  refine ⟨?_, by decide⟩
  apply Nat.add_right_cancel (m := 19)
  rw [p_add_nineteen]
  decide
end Curve25519Dalek.backend.serial.u64.field.FieldElement51
