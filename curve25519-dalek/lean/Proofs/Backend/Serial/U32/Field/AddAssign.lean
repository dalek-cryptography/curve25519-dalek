/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
import Proofs.Helpers.FieldElement2625
public section

/-!
# Spec theorem for `add_assign`

`self += rhs` adds the ten `u32` limbs of `rhs` to those of `self`, limb by limb, in a `for` loop
over `0..10`, without any carrying or reduction. If every limb sum fits in a `u32`, no addition
overflows, every limb of the result is the exact sum of the corresponding limbs, and so the
represented value is the exact sum of the represented values.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 70:4-74:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625
namespace Insts.CoreOpsArithAddAssignSharedBFieldElement2625

namespace AddAssign

/-- Loop invariant of `add_assign`: the range ends at `10` and has not overshot it, every limb sum
of the original operands fits in a `u32`, the limbs before `iter.start` hold the limb sums and the
limbs from `iter.start` on still hold the original limbs of `initial`. -/
private def Invariant (initial rhs : FieldElement2625) (iter : core.ops.range.Range Usize)
    (self : FieldElement2625) : Prop :=
  iter.end = 10#usize ∧
  iter.start.val ≤ 10 ∧
  (∀ i : ℕ, i < 10 → initial[i]!.val + rhs[i]!.val ≤ U32.max) ∧
  (∀ i < iter.start.val, self[i]!.val = initial[i]!.val + rhs[i]!.val) ∧
  (∀ i : ℕ, i < 10 → iter.start.val ≤ i → self[i]! = initial[i]!)

end AddAssign

@[step]
private theorem add_assign_loop.body_spec (iter : core.ops.range.Range Usize)
    (self rhs initial : FieldElement2625)
    (h_inv : AddAssign.Invariant initial rhs iter self) :
    add_assign_loop.body iter self rhs ⦃
      (result : ControlFlow (core.ops.range.Range Usize × FieldElement2625 × FieldElement2625)
        FieldElement2625) =>
      match result with
      | .done self' =>
        iter.start.val = 10 ∧ self' = self ∧ AddAssign.Invariant initial rhs iter self'
      | .cont (iter', self', rhs') =>
        rhs' = rhs ∧ AddAssign.Invariant initial rhs iter' self' ∧
        iter'.start.val = iter.start.val + 1 ⦄ := by
  obtain ⟨h_end, h_start, h_bound, h_done, h_rest⟩ := h_inv
  unfold add_assign_loop.body
  step as ⟨next, iter', h_next, h_end'⟩
  simp only [h_end, UScalar.ofNatCore_val_eq] at h_next
  by_cases hi : iter.start.val < 10
  · simp only [hi, ↓reduceIte] at h_next
    obtain ⟨h_next, h_advance⟩ := h_next
    simp only [h_next]
    step as ⟨r_i, h_r_i⟩
    step as ⟨s_i, h_s_i⟩
    have h_rest_i := h_rest _ hi le_rfl
    rw [Array.getElem_val_eq_getElem!] at h_r_i h_s_i
    step with U32.add_spec as ⟨sum, h_sum⟩
    step as ⟨self', h_self'⟩
    refine ⟨⟨h_end'.trans h_end, by omega, h_bound, ?_, ?_⟩, h_advance⟩
    · intro j hj
      rw [h_self']
      by_cases hj' : iter.start.val = j
      · subst hj'
        rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by scalar_tac⟩, h_sum, h_s_i, h_r_i,
          h_rest_i]
      · rw [Array.getElem!_Nat_set_ne _ _ _ _ hj']
        exact h_done j (by omega)
    · intro j hj hj'
      rw [h_self', Array.getElem!_Nat_set_ne _ _ _ _ (by omega)]
      exact h_rest j hj (by omega)
  · simp only [hi, ↓reduceIte] at h_next
    obtain ⟨h_next, -⟩ := h_next
    simp only [h_next, spec_ok]
    exact ⟨by omega, trivial, h_end, h_start, h_bound, h_done, h_rest⟩

@[step]
private theorem add_assign_loop_spec (iter : core.ops.range.Range Usize)
    (self rhs initial : FieldElement2625)
    (h_inv : AddAssign.Invariant initial rhs iter self) :
    add_assign_loop iter self rhs ⦃ (result : FieldElement2625) =>
      (∀ i : ℕ, i < 10 → result[i]!.val = initial[i]!.val + rhs[i]!.val) ∧
      result.asNat = initial.asNat + rhs.asNat ⦄ := by
  unfold add_assign_loop
  refine loop.spec_decr_nat
    (fun state : core.ops.range.Range Usize × FieldElement2625 × FieldElement2625 =>
      10 - state.1.start.val)
    (fun (iter', self', rhs') => rhs' = rhs ∧ AddAssign.Invariant initial rhs iter' self')
    _ _ _ ?_ ⟨rfl, h_inv⟩
  rintro ⟨iter', self', rhs'⟩ ⟨h_rhs, h_state⟩
  subst h_rhs
  apply spec_mono (add_assign_loop.body_spec iter' self' rhs' initial h_state)
  intro flow h_flow
  cases flow with
  | done result =>
    obtain ⟨h_done, -, -, -, -, h_sums, -⟩ := h_flow
    have h_limbs : ∀ i : ℕ, i < 10 → result[i]!.val = initial[i]!.val + rhs'[i]!.val :=
      fun i hi => h_sums i (by omega)
    refine ⟨h_limbs, ?_⟩
    simp only [asNat_def, Array.asNat2625_eq_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => by
      rw [h_limbs i (Finset.mem_range.mp hi), Nat.mul_add]
  | cont state =>
    obtain ⟨iter'', self'', rhs''⟩ := state
    obtain ⟨h_rhs', h_state', h_advance⟩ := h_flow
    have h_start := h_state.2.1
    have h_next_start := h_state'.2.1
    exact ⟨⟨h_rhs', h_state'⟩, by dsimp only; omega⟩

@[step]
theorem add_assign_spec (self rhs : FieldElement2625)
    (hself : self.LimbsLt 31) (hrhs : rhs.LimbsLt 31) :
    add_assign self rhs ⦃ (r : FieldElement2625) =>
      (∀ i : ℕ, i < 10 → r[i]!.val = self[i]!.val + rhs[i]!.val) ∧
        r.asNat = self.asNat + rhs.asNat ⦄ := by
  have h_sum : ∀ i : ℕ, i < 10 → self[i]!.val + rhs[i]!.val ≤ U32.max := fun i hi => by
    have := hself i hi; have := hrhs i hi; scalar_tac
  unfold add_assign
  apply add_assign_loop_spec _ _ _ self
  refine ⟨rfl, by simp, h_sum, fun i hi => ?_, fun _ _ _ => rfl⟩
  simp at hi

end Insts.CoreOpsArithAddAssignSharedBFieldElement2625
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
