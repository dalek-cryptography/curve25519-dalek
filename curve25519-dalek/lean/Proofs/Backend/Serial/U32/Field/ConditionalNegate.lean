/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Subtle
import Proofs.Backend.Serial.U32.Field.ConditionalAssign
import Proofs.Backend.Serial.U32.Field.Neg
public import Curve25519.Basic
public section

/-! # `ConditionallyNegatable::conditional_negate` on field elements -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `conditional_negate` on field elements: `x` if `c = 0`, `-x` if `c = 1`; limbs `< 2^28` in,
`< 2^26` out when negated. -/
@[step]
theorem conditional_negate_spec (x : FieldElement2625) (c : subtle.Choice)
    (hc : c.IsValid) (hx : x.LimbsLt 28) :
    subtle.ConditionallyNegatable.Blanket.conditional_negate
      backend.serial.u32.field.FieldElement2625.Insts.SubtleConditionallySelectable
      SharedAFieldElement2625.Insts.CoreOpsArithNegFieldElement2625 x c ⦃ (r : FieldElement2625) =>
      (c = 0#u8 → r = x) ∧
      (c = 1#u8 → (r.asNat + x.asNat) % p = 0 ∧ r.LimbsLt 26) ⦄ := by
  unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
  step as ⟨n, hn, hnb⟩
  step as ⟨r, hr0, hr1⟩
  exact ⟨hr0, fun hc => by rw [hr1 hc]; exact ⟨hn, hnb⟩⟩

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
