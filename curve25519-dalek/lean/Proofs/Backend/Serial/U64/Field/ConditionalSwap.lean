module
public import Curve25519Dalek.Funs
import Proofs.Helpers.Array
public import Proofs.Curve25519.Basic
public import Proofs.Representation.FieldElement51
public import Proofs.External.Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable
@[step]
theorem conditional_swap_spec (a b : FieldElement51) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_swap a b choice ⦃ (a' : FieldElement51) (b' : FieldElement51) =>
      (choice = 0#u8 → a' = a ∧ b' = b) ∧ (choice = 1#u8 → a' = b ∧ b' = a) ⦄ := by
  unfold conditional_swap
  step*
  constructor
  · intro hc
    simp [*, Array.set_getElem_five]
  · intro hc
    simp [*, Array.set_getElem_five]
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
