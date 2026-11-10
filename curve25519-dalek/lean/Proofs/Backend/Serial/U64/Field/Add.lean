/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.AddAssign
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithAddSharedAFieldElement51FieldElement51
@[step]
theorem add_spec (self rhs : FieldElement51)
    (hself : self.LimbsLt 54) (hrhs : rhs.LimbsLt 54) :
    add self rhs ⦃ (r : FieldElement51) =>
      ∀ i : ℕ, i < 5 → r[i]!.val = self[i]!.val + rhs[i]!.val ⦄ := by
  unfold add
  step*
end Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51
