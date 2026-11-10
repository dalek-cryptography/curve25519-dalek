/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Basic
public import Defs.FieldElement51
import Proofs.Helpers.StepSpecs
import Subtle
import Proofs.Helpers.Array
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreOpsArithAddAssignSharedAFieldElement51

open scoped Helpers.IndexStep in
/-- The loop of `add_assign` adds the limbs one by one. -/
@[local step]
private theorem add_assign_loop_spec (self rhs : FieldElement51)
    (hself : self.LimbsLt 54) (hrhs : rhs.LimbsLt 54) :
    add_assign_loop { start := 0#usize, «end» := 5#usize } self rhs ⦃ (r : FieldElement51) =>
      ∀ i : ℕ, i < 5 → r[i]!.val = self[i]!.val + rhs[i]!.val ⦄ := by
  unfold add_assign_loop
  apply loop.spec_decr_nat (measure := fun (iter, _, _) => 5 - iter.start.val)
    (inv := fun (iter, a, b) => b = rhs ∧ iter.end = 5#usize ∧ iter.start.val ≤ 5 ∧
      (∀ i < iter.start.val, a[i]!.val = self[i]!.val + rhs[i]!.val) ∧
      ∀ i : ℕ, i < 5 → iter.start.val ≤ i → a[i]! = self[i]!)
  · rintro ⟨iter, a, b⟩ ⟨hb, hend, hstart, hlo, hhi⟩
    subst hb
    unfold add_assign_loop.body
    by_cases hlt : iter.start.val < 5
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step*
      subst_vars
      refine ⟨by agrind, by agrind, fun j hj => ?_, fun j hj hsj => ?_, by agrind⟩
      · by_cases hjs : iter.start.val = j
        · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨hjs, by scalar_tac⟩]
          agrind
        · rw [Array.getElem!_Nat_set_ne _ _ _ _ hjs]
          agrind
      · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac)]
        agrind
    · step*
  · simp

@[step]
theorem add_assign_spec (self rhs : FieldElement51)
    (hself : self.LimbsLt 54) (hrhs : rhs.LimbsLt 54) :
    add_assign self rhs ⦃ (r : FieldElement51) =>
      ∀ i : ℕ, i < 5 → r[i]!.val = self[i]!.val + rhs[i]!.val ⦄ := by
  unfold add_assign
  step*
end CoreOpsArithAddAssignSharedAFieldElement51
end Curve25519Dalek.backend.serial.u64.field.FieldElement51.Insts
