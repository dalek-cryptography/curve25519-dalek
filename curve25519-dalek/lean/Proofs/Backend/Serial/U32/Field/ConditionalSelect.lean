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
# Spec theorem for `conditional_select`

`conditional_select a b choice` builds a new `FieldElement2625` limb by limb, selecting each limb
with the constant-time `u32::conditional_select`. For a valid choice (`0` or `1`) the result is `a`
for `0` and `b` for `1`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 240:4-257:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
namespace SubtleConditionallySelectable

@[step]
theorem conditional_select_spec (a b : FieldElement2625) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : FieldElement2625) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step*
  constructor
  · intro hc
    simp [*, Array.make_getElem_ten]
  · intro hc
    simp [*, Array.make_getElem_ten]

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts.SubtleConditionallySelectable
