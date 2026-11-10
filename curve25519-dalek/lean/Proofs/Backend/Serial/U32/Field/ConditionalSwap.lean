/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Helpers.FieldElement2625
import Proofs.Helpers.Array
public import Subtle
public import Zeroize
public section

/-!
# Spec theorem for `conditional_swap`

`conditional_swap a b choice` swaps two `FieldElement2625`s in place, limb by limb, with the
constant-time `u32::conditional_swap`. For a valid choice (`0` or `1`) the pair is swapped for `1`
and left unchanged for `0`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 272:4-283:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
namespace SubtleConditionallySelectable

@[step]
theorem conditional_swap_spec (a b : FieldElement2625) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_swap a b choice ⦃ (a' : FieldElement2625) (b' : FieldElement2625) =>
      (choice = 0#u8 → a' = a ∧ b' = b) ∧ (choice = 1#u8 → a' = b ∧ b' = a) ⦄ := by
  unfold conditional_swap
  step*
  constructor
  · intro hc
    simp [*, Array.set_getElem_ten]
  · intro hc
    simp [*, Array.set_getElem_ten]

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts.SubtleConditionallySelectable
