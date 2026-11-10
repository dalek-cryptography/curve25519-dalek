/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Helpers.FieldElement2625
import Proofs.Backend.Serial.U32.Field.FromLimbs
public section

/-!
# Spec theorem for `MINUS_ONE`

`MINUS_ONE` returns a `Result FieldElement2625` that is the field element `-1` represented using
ten limbs in the alternating `2^26/2^25` radix.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 296:4-299:7
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem MINUS_ONE_spec :
    MINUS_ONE ⦃ (r : FieldElement2625) =>
      r.asNat + 1 = p ∧ r.LimbsLt 26 ⦄ := by
  unfold MINUS_ONE
  simp only [asNat_def, Array.asNat2625_expand]
  step*
  subst_vars
  refine ⟨?_, by decide⟩
  apply Nat.add_right_cancel (m := 19)
  rw [p_add_nineteen]
  decide

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
