/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.Sub
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreOpsArithSubAssignSharedAFieldElement51
@[step]
theorem sub_assign_spec (self rhs : FieldElement51)
    (hself : self.LimbsLt 54) (hrhs : rhs.LimbsLt 54) :
    sub_assign self rhs ⦃ (r : FieldElement51) =>
      (r.asNat + rhs.asNat) % p = self.asNat % p ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step*
end CoreOpsArithSubAssignSharedAFieldElement51
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
