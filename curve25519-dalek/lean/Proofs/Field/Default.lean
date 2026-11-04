/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
public import Defs.Scalar52
public import Defs.Scalar
import Proofs.Helpers.Montgomery
import Proofs.Backend.Serial.U64.Field.Zero
import Proofs.Backend.Serial.U32.Field.Zero
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault

@[step]
theorem default_spec :
    default ⦃ (r : FieldElement51) =>
      r.asNat = 0 ∧ r.LimbsLt 51 ⦄ := by
  unfold default
  step*

end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts.CoreDefaultDefault

@[step]
theorem default_spec :
    default ⦃ (r : FieldElement2625) =>
      r.asNat = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step*

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts.CoreDefaultDefault
