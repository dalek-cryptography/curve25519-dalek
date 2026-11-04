/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Helpers.FieldElement2625
import Proofs.Backend.Serial.U32.Field.AddAssign
public section

/-!
# Spec theorem for `add`

`&self + &rhs` copies `self` and adds `rhs` to the copy with `+=`, i.e. it adds the ten `u32` limbs
pairwise without carrying or reduction. If every limb sum fits in a `u32`, no addition overflows
and the represented value of the result is the exact sum of those of the operands.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 79:4-83:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP

namespace Curve25519Dalek.SharedAFieldElement2625
namespace Insts.CoreOpsArithAddSharedBFieldElement2625FieldElement2625

open backend.serial.u32.field

@[step]
theorem add_spec (self rhs : FieldElement2625)
    (hself : self.LimbsLt 31) (hrhs : rhs.LimbsLt 31) :
    add self rhs ⦃ (r : FieldElement2625) =>
      (∀ i : ℕ, i < 10 → r[i]!.val = self[i]!.val + rhs[i]!.val) ∧
        r.asNat = self.asNat + rhs.asNat ⦄ := by
  unfold add
  step*

end Insts.CoreOpsArithAddSharedBFieldElement2625FieldElement2625
end Curve25519Dalek.SharedAFieldElement2625
