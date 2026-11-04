/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Helpers.FieldElement2625
import Proofs.Backend.Serial.U32.Field.Negate
public section

/-!
# Spec theorem for `neg`

`neg self` copies `self` and negates it in place; in the extracted code it simply calls
`FieldElement2625::negate`, so it inherits the specification of `negate`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 232:4-236:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.SharedAFieldElement2625.Insts.CoreOpsArithNegFieldElement2625

-- Note: as for negate_spec, a looser bound (self[i] < 8 * 2^26, roughly) would also hold.
@[step]
theorem neg_spec (self : FieldElement2625) (hself : self.LimbsLt 28) :
    neg self ⦃ (r : FieldElement2625) =>
      (r.asNat + self.asNat) % p = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold neg
  step*

end Curve25519Dalek.SharedAFieldElement2625.Insts.CoreOpsArithNegFieldElement2625
