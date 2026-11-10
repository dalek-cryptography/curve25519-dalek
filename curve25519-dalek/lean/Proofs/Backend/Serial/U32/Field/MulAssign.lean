/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Helpers.FieldElement2625
import Proofs.Backend.Serial.U32.Field.Mul
public section

/-!
# Spec theorem for `mul_assign`

`mul_assign self rhs` overwrites `self` with `&self * rhs`; in the extracted code it simply calls
`<&FieldElement2625 as Mul<&FieldElement2625>>::mul` and returns its result, so it inherits the
specification of `mul`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 118:4-121:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
namespace CoreOpsArithMulAssignSharedBFieldElement2625

@[step]
theorem mul_assign_spec (self rhs : FieldElement2625)
    (hself : ∀ i : ℕ, i < 10 → self[i]!.val < 3 * 2 ^ 26)
    (hrhs : ∀ i : ℕ, i < 10 → rhs[i]!.val < 3 * 2 ^ 26) :
    mul_assign self rhs ⦃ (r : FieldElement2625) =>
      r.asNat % p = self.asNat * rhs.asNat % p ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step*

end CoreOpsArithMulAssignSharedBFieldElement2625
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
