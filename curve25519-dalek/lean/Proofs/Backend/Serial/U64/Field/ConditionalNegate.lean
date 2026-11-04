/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
public import Subtle
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U64.Field.Neg
public import Curve25519.Basic
public section

/-! # `ConditionallyNegatable::conditional_negate` on field elements -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `conditional_negate` on field elements: `x` if `c = 0`, `-x` if `c = 1`; limbs `< 2^54` in,
`< 2^52` out when negated. -/
@[step]
theorem conditional_negate_spec (x : FieldElement51) (c : subtle.Choice)
    (hc : c.IsValid) (hx : x.LimbsLt 54) :
    subtle.ConditionallyNegatable.Blanket.conditional_negate
      backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
      Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51 x c ⦃ (r : FieldElement51) =>
      (c = 0#u8 → r = x) ∧
      (c = 1#u8 → (r.asNat + x.asNat) % p = 0 ∧ r.LimbsLt 52) ⦄ := by
  unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
  step as ⟨n, hn, hnb⟩
  step as ⟨r, hr0, hr1⟩
  exact ⟨hr0, fun hc => by rw [hr1 hc]; exact ⟨hn, hnb⟩⟩

end Curve25519Dalek.backend.serial.u64.field.FieldElement51
