/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Helpers.FieldElement2625
import Proofs.Backend.Serial.U32.Field.SubAssign
public section

/-!
# Spec theorem for `sub`

`sub self rhs` copies `self` and subtracts `rhs` from it in place; in the extracted code it
simply calls `<FieldElement2625 as SubAssign<&FieldElement2625>>::sub_assign`, so it inherits the
specification of `sub_assign`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 110:4-114:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.SharedAFieldElement2625.Insts
namespace CoreOpsArithSubSharedBFieldElement2625FieldElement2625

@[step]
theorem sub_spec (self rhs : FieldElement2625)
    (hself : self.LimbsLt 28) (hrhs : rhs.LimbsLt 28) :
    sub self rhs ⦃ (r : FieldElement2625) =>
      (r.asNat + rhs.asNat) % p = self.asNat % p ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

end CoreOpsArithSubSharedBFieldElement2625FieldElement2625
end Curve25519Dalek.SharedAFieldElement2625.Insts
