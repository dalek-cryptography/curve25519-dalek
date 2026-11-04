/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
import Proofs.Helpers.Array
public import Curve25519.Basic
public import Defs.FieldElement51
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable
@[step]
theorem conditional_assign_spec (self other : FieldElement51) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_assign self other choice ⦃ (r : FieldElement51) =>
      (choice = 0#u8 → r = self) ∧ (choice = 1#u8 → r = other) ⦄ := by
  unfold conditional_assign
  step*
  constructor
  · intro hc
    simp [*, Array.set_getElem_five]
  · intro hc
    simp [*, Array.set_getElem_five]
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
