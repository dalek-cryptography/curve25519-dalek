/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Basic
public import Defs.FieldElement51
public import Subtle
import Mathlib.Tactic.ReduceModChar
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

/-- A five-element array rebuilt from its own elements is the array itself. -/
private theorem Aeneas.Std.Array.make_getElem_five {α : Type} (a : Array α 5#usize)
    (h : [a.val[0], a.val[1], a.val[2], a.val[3], a.val[4]].length = (5#usize).val) :
    Array.make 5#usize [a.val[0], a.val[1], a.val[2], a.val[3], a.val[4]] h = a := by
  ext : 1
  rw [Array.make_val]
  apply List.ext_getElem (by simp)
  grind

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable
@[step]
theorem conditional_select_spec (a b : FieldElement51) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : FieldElement51) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor
  · intro hc
    simp [*, Array.make_getElem_five]
  · intro hc
    simp [*, Array.make_getElem_five]
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
