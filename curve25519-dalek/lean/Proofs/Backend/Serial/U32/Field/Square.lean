/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Helpers.FieldElement2625
import Proofs.Backend.Serial.U32.Field.SquareInner
import Proofs.Backend.Serial.U32.Field.Reduce
public section

/-!
# Spec theorem for `square`

`square self` computes `self ^ 2` as a `FieldElement2625`. It first runs the squaring kernel
`square_inner`, which returns ten unreduced `u64` coefficients congruent to `self ^ 2` modulo `p`,
and then `reduce` carries these coefficients back into the alternating `2^26/2^25` radix.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 595:4-597:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625


@[step]
theorem square_spec (self : FieldElement2625) (hself : self.LimbsLt 27) :
    square self ⦃ (r : FieldElement2625) =>
      r.asNat % p = self.asNat ^ 2 % p ∧ r.LimbsLt 26 ⦄ := by
  unfold square
  step with square_inner_spec as ⟨a, h_mod, h_bound⟩
  step with reduce_spec as ⟨r, h_res_mod, h_res, _⟩
  exact ⟨h_res_mod.trans h_mod, h_res⟩

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
