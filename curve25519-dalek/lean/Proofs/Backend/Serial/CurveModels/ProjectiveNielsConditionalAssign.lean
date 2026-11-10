/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Subtle.Contract
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U32.Field.ConditionalAssign
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.curve_models

namespace ProjectiveNielsPoint.«x86_64-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_assign` for `ProjectiveNielsPoint`:
`self` if `choice = 0`, `other` if `choice = 1`. -/
@[step]
theorem conditional_assign_spec (self other : ProjectiveNielsPoint.«x86_64-tables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ := by
  unfold conditional_assign
  step*
  constructor <;> intro hc <;> simp [*]

end ProjectiveNielsPoint.«x86_64-tables».Insts.SubtleConditionallySelectable

namespace ProjectiveNielsPoint.«i686-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_assign` for `ProjectiveNielsPoint`:
`self` if `choice = 0`, `other` if `choice = 1`. -/
@[step]
theorem conditional_assign_spec (self other : ProjectiveNielsPoint.«i686-tables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : ProjectiveNielsPoint.«i686-tables») =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ := by
  unfold conditional_assign
  step*
  constructor <;> intro hc <;> simp [*]

end ProjectiveNielsPoint.«i686-tables».Insts.SubtleConditionallySelectable

namespace ProjectiveNielsPoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_assign` for `ProjectiveNielsPoint`:
`self` if `choice = 0`, `other` if `choice = 1`. -/
@[step]
theorem conditional_assign_spec (self other : ProjectiveNielsPoint.«x86_64-no-tables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ := by
  unfold conditional_assign
  step*
  constructor <;> intro hc <;> simp [*]

end ProjectiveNielsPoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

namespace ProjectiveNielsPoint.«i686-no-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_assign` for `ProjectiveNielsPoint`:
`self` if `choice = 0`, `other` if `choice = 1`. -/
@[step]
theorem conditional_assign_spec (self other : ProjectiveNielsPoint.«i686-no-tables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : ProjectiveNielsPoint.«i686-no-tables») =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ := by
  unfold conditional_assign
  step*
  constructor <;> intro hc <;> simp [*]

end ProjectiveNielsPoint.«i686-no-tables».Insts.SubtleConditionallySelectable

end Curve25519Dalek.backend.serial.curve_models
