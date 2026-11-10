/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Subtle.Contract
import Proofs.Backend.Serial.U64.Field.ConditionalSelect
import Proofs.Backend.Serial.U32.Field.ConditionalSelect
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.affine

namespace AffinePoint.«x86_64-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `AffinePoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : AffinePoint.«x86_64-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : AffinePoint.«x86_64-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor <;> intro hc <;> simp [*]

end AffinePoint.«x86_64-tables».Insts.SubtleConditionallySelectable

namespace AffinePoint.«i686-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `AffinePoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : AffinePoint.«i686-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : AffinePoint.«i686-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor <;> intro hc <;> simp [*]

end AffinePoint.«i686-tables».Insts.SubtleConditionallySelectable

namespace AffinePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `AffinePoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : AffinePoint.«x86_64-no-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : AffinePoint.«x86_64-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor <;> intro hc <;> simp [*]

end AffinePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

namespace AffinePoint.«i686-no-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable::conditional_select` for `AffinePoint`:
`a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : AffinePoint.«i686-no-tables») (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : AffinePoint.«i686-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor <;> intro hc <;> simp [*]

end AffinePoint.«i686-no-tables».Insts.SubtleConditionallySelectable

end Curve25519Dalek.edwards.affine
