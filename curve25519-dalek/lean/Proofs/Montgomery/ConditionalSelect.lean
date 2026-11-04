/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Montgomery
public import Subtle.Contract
public section

/-! # `ConditionallySelectable for MontgomeryPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for MontgomeryPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : MontgomeryPoint) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : MontgomeryPoint) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step with Array.Insts.SubtleConditionallySelectable.conditional_select_spec
    U8.Insts.SubtleConditionallySelectable a b choice hchoice
    (fun x y => U8.Insts.SubtleConditionallySelectable.conditional_assign_spec x y choice hchoice)
    as ⟨r, h0, h1⟩
  exact ⟨h0, h1⟩

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable
