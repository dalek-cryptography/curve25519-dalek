/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
public import Subtle
import Proofs.Helpers.Array
import Proofs.Helpers.StepSpecs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar.Insts.SubtleConditionallySelectable

/-- Byte arrays with the same entries are equal. -/
private theorem bytes_ext {x y : Array U8 32#usize} (h : ∀ i : ℕ, i < 32 →
  x[i]! = y[i]!) : x = y := by
  refine Aeneas.Std.Array.ext _ _ (List.ext_getElem (by simp) fun i h1 h2 => ?_)
  have hi : i < 32 := by simpa using h1
  have := h i hi
  rwa [Array.getElem!_Nat_eq, Array.getElem!_Nat_eq, getElem!_pos x.val i h1,
    getElem!_pos y.val i h2] at this

open scoped Helpers.IndexStep Helpers.UpdateStep in
/-- The loop selects the bytes one by one. -/
@[local step]
private theorem conditional_select_loop_spec (a b : Scalar) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select_loop { start := 0#usize, «end» := 32#usize } a b choice
      (Array.repeat 32#usize 0#u8) ⦃ (r : Array U8 32#usize) =>
      ∀ i : ℕ, i < 32 → (choice = 0#u8 → r[i]! = a.bytes[i]!) ∧
        (choice = 1#u8 → r[i]! = b.bytes[i]!) ⦄ := by
  unfold conditional_select_loop
  apply loop.spec_decr_nat (measure := fun (iter, _) => 32 - iter.start.val)
    (inv := fun (iter, r) => iter.end = 32#usize ∧ iter.start.val ≤ 32 ∧
      ∀ i < iter.start.val,
        (choice = 0#u8 → r[i]! = a.bytes[i]!) ∧ (choice = 1#u8 → r[i]! = b.bytes[i]!))
  · rintro ⟨iter, r⟩ ⟨hend, hstart, hsel⟩
    unfold conditional_select_loop.body
    by_cases hlt : iter.start.val < 32
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      step as ⟨z, hz0, hz1⟩
      step as ⟨r1, hr1, hr1'⟩
      refine ⟨by agrind, by agrind, fun j hj => ?_, by agrind⟩
      by_cases hjs : j = iter.start.val
      · subst hjs
        rw [hr1]
        exact ⟨fun h => by rw [hz0 h, hx], fun h => by rw [hz1 h, hy]⟩
      · rw [hr1' j hjs]
        exact hsel j (by scalar_tac)
    · step*
  · simp

@[step]
theorem conditional_select_spec (a b : Scalar) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : Scalar) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step as ⟨r, hr⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [bytes_ext fun i hi => (hr i hi).1 h]
  · rw [bytes_ext fun i hi => (hr i hi).2 h]

end Curve25519Dalek.scalar.Scalar.Insts.SubtleConditionallySelectable
