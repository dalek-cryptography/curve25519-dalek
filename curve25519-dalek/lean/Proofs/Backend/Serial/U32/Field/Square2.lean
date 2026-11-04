/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Proofs.Helpers.FieldElement2625
public import Subtle
public import Zeroize
import Proofs.Backend.Serial.U32.Field.SquareInner
import Proofs.Backend.Serial.U32.Field.Reduce
public section

/-!
# Spec theorem for `square2`

`square2 self` computes `2 * self ^ 2` as a `FieldElement2625`. It runs the squaring kernel
`square_inner`, doubles each of the ten unreduced `u64` coefficients in place through a mutable
iterator (`for coeff in &mut coeffs { *coeff += *coeff; }`), and then `reduce`s the doubled
coefficients. In the extracted code the loop threads the `IterMut` together with a backward
function: every step composes a write of the doubled coefficient at the current index onto the
backward function, and when the iterator is exhausted the backward function is applied to it,
yielding an iterator whose slice holds all doubled coefficients.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 600:4-606:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP
namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Square2

/-- Loop invariant of `square2`, relative to the original coefficients `coeffs`: the iterator still
holds the original coefficients (`iter.slice.val = coeffs.val`, as the forward iterator is never
written to), its position `iter.i` is at most `10`, and on any length-`10` iterator `im` the
accumulated backward function `back` keeps the length `10`, sets every entry `j < iter.i` to
`2 * coeffs[j]` and leaves every other entry as in `im`. -/
private def Invariant (coeffs : Array U64 10#usize) (iter : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) : Prop :=
  iter.slice.val = coeffs.val ∧
  iter.i ≤ 10 ∧
  ∀ im : core.slice.iter.IterMut U64, im.slice.val.length = 10 →
    (back im).slice.val.length = 10 ∧
    ∀ j : ℕ, j < 10 → (back im).slice.val[j]!.val =
      if j < iter.i then 2 * coeffs[j]!.val else im.slice.val[j]!.val

end Square2


@[step]
private theorem square2_loop.body_spec (iter : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64)
    (coeffs : Array U64 10#usize)
    (h_coeffs : ∀ i : ℕ, i < 10 → coeffs[i]!.val < 2 ^ 63)
    (h_inv : Square2.Invariant coeffs iter back) :
    square2_loop.body iter back ⦃
      (result : ControlFlow (core.slice.iter.IterMut U64 ×
        (core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64))
        (core.slice.iter.IterMut U64)) =>
      match result with
      | .done r =>
        r.slice.val.length = 10 ∧
        ∀ i : ℕ, i < 10 → r.slice.val[i]!.val = 2 * coeffs[i]!.val
      | .cont (iter', back') =>
        Square2.Invariant coeffs iter' back' ∧ iter'.i = iter.i + 1 ⦄ := by
  obtain ⟨h_slice, h_le, h_back⟩ := h_inv
  have h_len : iter.slice.val.length = 10 := by
    rw [h_slice]; simp
  unfold square2_loop.body core.slice.iter.IteratorIterMut.next
  by_cases hi : iter.i < iter.slice.len
  · simp only [hi, ↓reduceDIte]
    have hi' : iter.i < iter.slice.val.length := by scalar_tac
    have hi10 : iter.i < 10 := by omega
    have h_x : (iter.slice[iter.i]'hi').val = coeffs[iter.i]!.val := by
      rw [Slice.Inhabited_getElem_eq_getElem! _ _ hi', Slice.getElem!_Nat_eq, h_slice,
        Array.getElem!_Nat_eq]
    have h_bound := h_coeffs iter.i hi10
    step as ⟨coeff1, h_coeff1⟩
    refine ⟨h_slice, show iter.i + 1 ≤ 10 by omega, ?_⟩
    intro im him
    have h_set_len : (im.slice.setAtNat iter.i coeff1).val.length = 10 := by
      simpa only [Slice.setAtNat_length] using him
    obtain ⟨h_len', h_entries⟩ :=
      h_back { slice := im.slice.setAtNat iter.i coeff1, i := im.i } h_set_len
    refine ⟨h_len', fun j hj => ?_⟩
    rw [h_entries j hj]
    by_cases hj1 : j < iter.i
    · simp only [hj1, ↓reduceIte, show j < iter.i + 1 by omega]
    · by_cases hj2 : j = iter.i
      · subst hj2
        simp only [hj1, ↓reduceIte, Nat.lt_add_one]
        rw [Slice.getElem!_Nat_setAtNat_eq _ _ _ (by rw [Slice.length, him]; exact hi10)]
        omega
      · simp only [hj1, ↓reduceIte, show ¬ j < iter.i + 1 by omega]
        rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm hj2)]
  · simp only [hi, ↓reduceDIte]
    step*


@[step]
private theorem square2_loop_spec (iter : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64)
    (coeffs : Array U64 10#usize)
    (h_coeffs : ∀ i : ℕ, i < 10 → coeffs[i]!.val < 2 ^ 63)
    (h_inv : Square2.Invariant coeffs iter back) :
    square2_loop iter back ⦃ (r : core.slice.iter.IterMut U64) =>
      r.slice.val.length = 10 ∧
      ∀ i : ℕ, i < 10 → r.slice.val[i]!.val = 2 * coeffs[i]!.val ⦄ := by
  unfold square2_loop
  refine loop.spec_decr_nat
    (fun state : core.slice.iter.IterMut U64 ×
      (core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) => 10 - state.1.i)
    (fun (iter, back) => Square2.Invariant coeffs iter back)
    _ _ _ ?_ h_inv
  rintro ⟨iter, back⟩ h_state
  apply spec_mono (square2_loop.body_spec iter back coeffs h_coeffs h_state)
  intro flow h_flow
  cases flow with
  | done r => exact h_flow
  | cont state =>
    rcases state with ⟨iter', back'⟩
    rcases h_flow with ⟨h_state', h_advance⟩
    have h_le := h_state'.2.1
    exact ⟨h_state', by dsimp only; omega⟩


@[step]
theorem square2_spec (self : FieldElement2625) (hself : self.LimbsLt 27) :
    square2 self ⦃ (r : FieldElement2625) =>
      r.asNat % p = 2 * self.asNat ^ 2 % p ∧ r.LimbsLt 26 ⦄ := by
  unfold square2
  step as ⟨coeffs, h_mod, h_bound⟩
  step as ⟨iter, into_iter_back, h_iter_slice, h_iter_i, h_into_back⟩
  have h_coeffs : ∀ i : ℕ, i < 10 → coeffs[i]!.val < 2 ^ 63 := fun i hi => by
    have := h_bound i hi
    omega
  have h_inv : Square2.Invariant coeffs iter (fun im => im) :=
    ⟨h_iter_slice, by omega, fun im him => ⟨him, fun j _ => by simp [h_iter_i]⟩⟩
  step with square2_loop_spec iter (fun im => im) coeffs h_coeffs h_inv as ⟨r, h_r_len, h_r⟩
  have h_doubled : ∀ i : ℕ, i < 10 → (into_iter_back r)[i]!.val = 2 * coeffs[i]!.val := by
    intro i hi
    rw [Array.getElem!_Nat_eq, h_into_back r h_r_len, h_r i hi]
  step with reduce_spec as ⟨result, h_res_mod, h_res, _⟩
  refine ⟨?_, h_res⟩
  have h_sum : (into_iter_back r).asNat2625 = 2 * coeffs.asNat2625 := by
    rw [Array.asNat2625_eq_sum, Array.asNat2625_eq_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h_doubled i (Finset.mem_range.mp hi)]
    ring
  rw [h_res_mod, h_sum, Nat.mul_mod, h_mod, ← Nat.mul_mod]


end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
