/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Helpers.FieldElement2625
public section

/-!
# Spec theorem for `clone`

`FieldElement2625` derives `Clone` (and `Copy`), so `clone` returns a bitwise copy of the ten
`u32` limbs. In the extracted model the field element is a value, so `clone self` is `ok self`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 53:15-53:20
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625
namespace Insts.CoreCloneClone

@[step]
theorem clone_spec (self : FieldElement2625) :
    clone self ⦃ (result : FieldElement2625) =>
      result = self ⦄ := by
  simp [clone]

end Insts.CoreCloneClone
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
