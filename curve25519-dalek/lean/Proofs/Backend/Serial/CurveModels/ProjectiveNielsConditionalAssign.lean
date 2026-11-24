module
public import Curve25519Dalek.Funs
public import Proofs.External.Subtle.Contract
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U32.Field.ConditionalAssign
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.curve_models

namespace ProjectiveNielsPoint.«64bit-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_assign` for `ProjectiveNielsPoint`:
`self` if `choice = 0`, `other` if `choice = 1`. -/
@[step]
theorem conditional_assign_spec (self other : ProjectiveNielsPoint.«64bit-tables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ := by
  unfold conditional_assign
  step*
  constructor <;> intro hc <;> simp [*]

end ProjectiveNielsPoint.«64bit-tables».Insts.SubtleConditionallySelectable

namespace ProjectiveNielsPoint.«32bit-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_assign` for `ProjectiveNielsPoint`:
`self` if `choice = 0`, `other` if `choice = 1`. -/
@[step]
theorem conditional_assign_spec (self other : ProjectiveNielsPoint.«32bit-tables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ := by
  unfold conditional_assign
  step*
  constructor <;> intro hc <;> simp [*]

end ProjectiveNielsPoint.«32bit-tables».Insts.SubtleConditionallySelectable

namespace ProjectiveNielsPoint.«64bit-notables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_assign` for `ProjectiveNielsPoint`:
`self` if `choice = 0`, `other` if `choice = 1`. -/
@[step]
theorem conditional_assign_spec (self other : ProjectiveNielsPoint.«64bit-notables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ := by
  unfold conditional_assign
  step*
  constructor <;> intro hc <;> simp [*]

end ProjectiveNielsPoint.«64bit-notables».Insts.SubtleConditionallySelectable

namespace ProjectiveNielsPoint.«32bit-notables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_assign` for `ProjectiveNielsPoint`:
`self` if `choice = 0`, `other` if `choice = 1`. -/
@[step]
theorem conditional_assign_spec (self other : ProjectiveNielsPoint.«32bit-notables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ := by
  unfold conditional_assign
  step*
  constructor <;> intro hc <;> simp [*]

end ProjectiveNielsPoint.«32bit-notables».Insts.SubtleConditionallySelectable

end Curve25519Dalek.backend.serial.curve_models
