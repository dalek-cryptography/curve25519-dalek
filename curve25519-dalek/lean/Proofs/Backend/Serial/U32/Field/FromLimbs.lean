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
# Spec theorem for `from_limbs`

`from_limbs` converts an `Array Std.U32 10#usize` into a `Result Array Std.U32 10#usize` simply by
applying the `ok` constructor to the input array. It is essentially just a type conversion.

Source: "curve25519-dalek/src/backend/serial/u32/field.rs", lines 287:4-289:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem from_limbs_spec (limbs : Array U32 10#usize) :
    from_limbs limbs ⦃ (r : FieldElement2625) =>
      r = limbs ⦄ := by
  unfold from_limbs
  step*

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
