/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field
theorem SIXTEEN_P_spec :
    FieldElement51.asNat SIXTEEN_P = 16 * p ∧
      (∀ i : ℕ, i < 5 → 2 ^ 55 ≤ SIXTEEN_P[i]!.val + 304) ∧
        FieldElement51.LimbsLt 55 SIXTEEN_P := by
  unfold SIXTEEN_P
  simp only [field.FieldElement51.asNat_def, Array.asNat_def]
  refine ⟨?_, by decide⟩
  apply Nat.add_right_cancel (m := 16 * 19)
  rw [← Nat.mul_add, p_add_nineteen]
  decide
end Curve25519Dalek.backend.serial.u64.field
