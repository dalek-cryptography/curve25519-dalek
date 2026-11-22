/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.External.Subtle.Contract
import Proofs.Backend.Serial.U64.Field.ConditionalSelect
import Proofs.Backend.Serial.U32.Field.ConditionalSelect
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.curve_models

namespace AffineNielsPoint.«64bit-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `AffineNielsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : AffineNielsPoint.«64bit-tables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : AffineNielsPoint.«64bit-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor <;> intro hc <;> simp [*]

end AffineNielsPoint.«64bit-tables».Insts.SubtleConditionallySelectable

namespace AffineNielsPoint.«32bit-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `AffineNielsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : AffineNielsPoint.«32bit-tables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : AffineNielsPoint.«32bit-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor <;> intro hc <;> simp [*]

end AffineNielsPoint.«32bit-tables».Insts.SubtleConditionallySelectable

namespace AffineNielsPoint.«64bit-notables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `AffineNielsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : AffineNielsPoint.«64bit-notables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : AffineNielsPoint.«64bit-notables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor <;> intro hc <;> simp [*]

end AffineNielsPoint.«64bit-notables».Insts.SubtleConditionallySelectable

namespace AffineNielsPoint.«32bit-notables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `AffineNielsPoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : AffineNielsPoint.«32bit-notables»)
    (choice : subtle.Choice) (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : AffineNielsPoint.«32bit-notables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor <;> intro hc <;> simp [*]

end AffineNielsPoint.«32bit-notables».Insts.SubtleConditionallySelectable

end Curve25519Dalek.backend.serial.curve_models
