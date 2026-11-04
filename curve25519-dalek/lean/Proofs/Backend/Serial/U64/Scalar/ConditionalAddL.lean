/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
public import Curve25519.Basic
import Proofs.Backend.Serial.U64.Constants.L
import Proofs.Backend.Serial.U64.Scalar.Index
import Proofs.Backend.Serial.U64.Scalar.IndexMut
import Proofs.Helpers.AsNat
import Proofs.Helpers.Scalar52
public import Subtle
import Proofs.Helpers.StepSpecs
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Bitwise
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

open scoped Helpers.MaskStep

/-- One carry step: adding `s + c · l` and the incoming carry `cin` at position `P`. -/
private theorem carry_step {Sa Ss SL P cin s l c carry1 : ℕ} (hIH : Sa + P * cin = Ss + c * SL)
    (hc1 : carry1 = cin + s + c * l) :
    Sa + P * (carry1 % 2 ^ 52) + P * 2 ^ 52 * (carry1 / 2 ^ 52)
      = Ss + P * s + c * (SL + P * l) := by
  rw [mul_assoc, add_assoc, ← mul_add, Nat.mod_add_div, hc1]
  calc Sa + P * (cin + s + c * l) = (Sa + P * cin) + P * s + c * (P * l) := by ring
    _ = _ := by rw [hIH]; ring

/-- The loop of `conditional_add_l` adds `c · L` limb by limb, where `c = 1` if
`condition = 1` and `c = 0` otherwise. -/
@[local step]
private theorem conditional_add_l_loop_spec (self : Scalar52) (condition : subtle.Choice)
    (mask : U64)
    (hself : self.LimbsLt 52) (hcondition : condition.IsValid)
    (hmask : mask.val = 2 ^ 52 - 1) :
    conditional_add_l_loop { start := 0#usize, «end» := 5#usize } self condition 0#u64 mask
    ⦃ (c : U64) (r : Scalar52) =>
      r.asNat + montgomeryRadix * (c.val / 2 ^ 52) =
        self.asNat + (if condition = 1#u8 then 1 else 0) * Scalar52.asNat constants.L ∧
      r.LimbsLt 52 ⦄ := by
  unfold conditional_add_l_loop
  apply loop.spec_decr_nat (measure := fun (iter, _, _) => 5 - iter.start.val)
    (inv := fun (iter, a, carry) => iter.end = 5#usize ∧ iter.start.val ≤ 5 ∧
      carry.val < 2 ^ 53 ∧ a.LimbsLt 52 ∧
      (∀ i : ℕ, i < 5 → iter.start.val ≤ i → a[i]! = self[i]!) ∧
      ∑ j ∈ Finset.range iter.start.val, 2 ^ (52 * j) * a[j]!.val
        + 2 ^ (52 * iter.start.val) * (carry.val / 2 ^ 52) =
        ∑ j ∈ Finset.range iter.start.val, 2 ^ (52 * j) * self[j]!.val
        + (if condition = 1#u8 then 1 else 0) *
          ∑ j ∈ Finset.range iter.start.val, 2 ^ (52 * j) * constants.L[j]!.val)
  · rintro ⟨iter, a, carry⟩ ⟨hend, hstart, hcarry, ha, hrest, hsum⟩
    unfold conditional_add_l_loop.body
    by_cases hlt : iter.start.val < 5
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      have hak : a[iter.start.val]! = self[iter.start.val]! := hrest _ hlt le_rfl
      step as ⟨l, hl⟩
      step as ⟨addend, haddend0, haddend1⟩
      have hlk : l.val < 2 ^ 52 := hl ▸ constants.L_spec.2 _ hlt
      have haddend : addend.val = (if condition = 1#u8 then 1 else 0) * l.val := by
        rcases hcondition with h | h <;> simp [h, haddend0, haddend1]
      have haddend_lt : addend.val < 2 ^ 52 := by
        rcases hcondition with h | h
        · simp [haddend0 h]
        · rw [haddend1 h]
          exact hlk
      step as ⟨cin, hcin, _⟩
      have hcin' : cin.val = carry.val / 2 ^ 52 := by rw [hcin, Nat.shiftRight_eq_div_pow]
      have hcin_le : cin.val ≤ 1 := by rw [hcin']; scalar_tac
      step as ⟨s, hs⟩
      step as ⟨i4, hi4⟩
      step as ⟨carry1, hcarry1⟩
      step as ⟨_, back, _, hback⟩
      step as ⟨i5, hi5⟩
      have hsk : s.val < 2 ^ 52 := hs ▸ ha _ hlt
      refine ⟨by rw [hend1, hend], by scalar_tac, by scalar_tac, fun i hi => ?_, fun i hi hki => ?_,
        ?_, by scalar_tac⟩
      · rw [hback]
        by_cases hik : iter.start.val = i
        · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨hik, by scalar_tac⟩, hi5]
          exact Nat.mod_lt _ (by norm_num)
        · rw [Array.getElem!_Nat_set_ne _ _ _ _ hik]
          exact ha i hi
      · rw [hback, Array.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac)]
        exact hrest i hi (by scalar_tac)
      · rw [hback, hstart1, Array.sum_range_succ_set _ _ _ _ (by scalar_tac), Finset.sum_range_succ,
          Finset.sum_range_succ, Nat.mul_succ, pow_add, hi5, ← hl, ← hak, ← hs]
        exact carry_step hsum (by rw [hcarry1, hi4, hcin', haddend])
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 5 := by scalar_tac
      rw [hk, show 52 * 5 = 260 by rfl, ← montgomeryRadix_def] at hsum
      simp only [WP.spec_ok]
      refine ⟨?_, ha⟩
      simp only [Scalar52.asNat_def, Array.asNat_eq_sum]
      exact hsum
  · exact ⟨rfl, by simp, by simp, hself, fun _ _ _ => rfl, by simp⟩

/-- A number below `M` that differs from `x` by a multiple of `M` is `x % M`. -/
private theorem eq_mod_of_add_mul_eq {r q x M : ℕ} (hr : r < M) (h : r + M * q = x) :
    r = x % M := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

@[step]
theorem conditional_add_l_spec (self : Scalar52) (condition : subtle.Choice)
    (hself : self.LimbsLt 52) (hcondition : condition.IsValid) :
    conditional_add_l self condition ⦃ (_ : U64) (r : Scalar52) =>
      (condition = 0#u8 → r.asNat = self.asNat) ∧
      (condition = 1#u8 → r.asNat = (self.asNat + L) % montgomeryRadix) ∧
      r.LimbsLt 52 ⦄ := by
  unfold conditional_add_l
  step as ⟨two_pow_52, htwo_pow_52⟩
  step as ⟨mask, hmask⟩
  have hmask' : mask.val = 2 ^ 52 - 1 := by scalar_tac
  apply spec_mono (conditional_add_l_loop_spec self condition mask hself hcondition hmask')
  rintro ⟨c, r⟩ ⟨hsum, hr⟩
  have hr_lt := Scalar52.asNat_lt r hr
  have hself_lt := Scalar52.asNat_lt self hself
  rw [constants.L_spec.1] at hsum
  refine ⟨fun h => ?_, fun h => ?_, hr⟩
  · rw [eq_mod_of_add_mul_eq hr_lt hsum, h, ite_eq_right (by decide), zero_mul, add_zero,
      Nat.mod_eq_of_lt hself_lt]
  · rw [eq_mod_of_add_mul_eq hr_lt hsum, h, ite_eq_left rfl, one_mul]

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
