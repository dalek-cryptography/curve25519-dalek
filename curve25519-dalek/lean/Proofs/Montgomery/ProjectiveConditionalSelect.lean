/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Montgomery
public import Subtle.Contract
import Subtle.Lemmas
import Proofs.Backend.Serial.U64.Field.ConditionalSelect
import Proofs.Backend.Serial.U32.Field.ConditionalSelect
public section

/-! # `ConditionallySelectable for ProjectivePoint` (Montgomery) -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek

namespace montgomery.ProjectivePoint.«x86_64-tables».Insts.SubtleConditionallySelectable

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ConditionallySelectable for ProjectivePoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : montgomery.ProjectivePoint.«x86_64-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : montgomery.ProjectivePoint.«x86_64-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step as ⟨U, hU0, hU1⟩
  step as ⟨W, hW0, hW1⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hU0 h, hW0 h]
  · rw [hU1 h, hW1 h]


/-- `conditional_swap` (the trait's default, through `conditional_select`): `(b, a)` if
`choice = 1`, `(a, b)` if `choice = 0`. -/
@[step]
theorem conditional_swap_spec (a b : montgomery.ProjectivePoint.«x86_64-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    subtle.ConditionallySelectable.conditional_swap.default
      montgomery.ProjectivePoint.«x86_64-tables».Insts.SubtleConditionallySelectable a b choice
      ⦃ (r : montgomery.ProjectivePoint.«x86_64-tables» ×
          montgomery.ProjectivePoint.«x86_64-tables») =>
        (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄ :=
  subtle.ConditionallySelectable.conditional_swap.default_spec
    montgomery.ProjectivePoint.«x86_64-tables».Insts.SubtleConditionallySelectable a b choice fun x
        y =>
      subtle.ConditionallySelectable.conditional_assign.default_spec
        montgomery.ProjectivePoint.«x86_64-tables».Insts.SubtleConditionallySelectable x y choice
        (conditional_select_spec x y choice hchoice)

end montgomery.ProjectivePoint.«x86_64-tables».Insts.SubtleConditionallySelectable

namespace montgomery.ProjectivePoint.«i686-tables».Insts.SubtleConditionallySelectable

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ConditionallySelectable for ProjectivePoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : montgomery.ProjectivePoint.«i686-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : montgomery.ProjectivePoint.«i686-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step as ⟨U, hU0, hU1⟩
  step as ⟨W, hW0, hW1⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hU0 h, hW0 h]
  · rw [hU1 h, hW1 h]


/-- `conditional_swap` (the trait's default, through `conditional_select`): `(b, a)` if
`choice = 1`, `(a, b)` if `choice = 0`. -/
@[step]
theorem conditional_swap_spec (a b : montgomery.ProjectivePoint.«i686-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    subtle.ConditionallySelectable.conditional_swap.default
      montgomery.ProjectivePoint.«i686-tables».Insts.SubtleConditionallySelectable a b choice
      ⦃ (r : montgomery.ProjectivePoint.«i686-tables» ×
          montgomery.ProjectivePoint.«i686-tables») =>
        (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄ :=
  subtle.ConditionallySelectable.conditional_swap.default_spec
    montgomery.ProjectivePoint.«i686-tables».Insts.SubtleConditionallySelectable a b choice fun x
        y =>
      subtle.ConditionallySelectable.conditional_assign.default_spec
        montgomery.ProjectivePoint.«i686-tables».Insts.SubtleConditionallySelectable x y choice
        (conditional_select_spec x y choice hchoice)

end montgomery.ProjectivePoint.«i686-tables».Insts.SubtleConditionallySelectable

namespace montgomery.ProjectivePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ConditionallySelectable for ProjectivePoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : montgomery.ProjectivePoint.«x86_64-no-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : montgomery.ProjectivePoint.«x86_64-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step as ⟨U, hU0, hU1⟩
  step as ⟨W, hW0, hW1⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hU0 h, hW0 h]
  · rw [hU1 h, hW1 h]


/-- `conditional_swap` (the trait's default, through `conditional_select`): `(b, a)` if
`choice = 1`, `(a, b)` if `choice = 0`. -/
@[step]
theorem conditional_swap_spec (a b : montgomery.ProjectivePoint.«x86_64-no-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    subtle.ConditionallySelectable.conditional_swap.default
      montgomery.ProjectivePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable a b choice
      ⦃ (r : montgomery.ProjectivePoint.«x86_64-no-tables» ×
          montgomery.ProjectivePoint.«x86_64-no-tables») =>
        (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄ :=
  subtle.ConditionallySelectable.conditional_swap.default_spec
    montgomery.ProjectivePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable a b choice fun
        x y =>
      subtle.ConditionallySelectable.conditional_assign.default_spec
        montgomery.ProjectivePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable x y choice
        (conditional_select_spec x y choice hchoice)

end montgomery.ProjectivePoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

namespace montgomery.ProjectivePoint.«i686-no-tables».Insts.SubtleConditionallySelectable

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ConditionallySelectable for ProjectivePoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : montgomery.ProjectivePoint.«i686-no-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : montgomery.ProjectivePoint.«i686-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step as ⟨U, hU0, hU1⟩
  step as ⟨W, hW0, hW1⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hU0 h, hW0 h]
  · rw [hU1 h, hW1 h]


/-- `conditional_swap` (the trait's default, through `conditional_select`): `(b, a)` if
`choice = 1`, `(a, b)` if `choice = 0`. -/
@[step]
theorem conditional_swap_spec (a b : montgomery.ProjectivePoint.«i686-no-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    subtle.ConditionallySelectable.conditional_swap.default
      montgomery.ProjectivePoint.«i686-no-tables».Insts.SubtleConditionallySelectable a b choice
      ⦃ (r : montgomery.ProjectivePoint.«i686-no-tables» ×
          montgomery.ProjectivePoint.«i686-no-tables») =>
        (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄ :=
  subtle.ConditionallySelectable.conditional_swap.default_spec
    montgomery.ProjectivePoint.«i686-no-tables».Insts.SubtleConditionallySelectable a b choice fun
        x y =>
      subtle.ConditionallySelectable.conditional_assign.default_spec
        montgomery.ProjectivePoint.«i686-no-tables».Insts.SubtleConditionallySelectable x y choice
        (conditional_select_spec x y choice hchoice)

end montgomery.ProjectivePoint.«i686-no-tables».Insts.SubtleConditionallySelectable

end Curve25519Dalek
