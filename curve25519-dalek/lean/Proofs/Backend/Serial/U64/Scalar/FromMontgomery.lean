/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Limbs
import Proofs.Backend.Serial.U64.Scalar.Index
import Proofs.Helpers.Scalar52
import Proofs.Backend.Serial.U64.Scalar.MontgomeryReduce
import Proofs.Helpers.AsNat
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- The loop of `from_montgomery` copies the five limbs of `self` into the low limbs. -/
@[local step]
private theorem from_montgomery_loop_spec (self : Scalar52) :
    from_montgomery_loop { start := 0#usize, «end» := 5#usize } self
      (Array.repeat 9#usize 0#u128) ⦃ (limbs : Array U128 9#usize) =>
      (∀ i : ℕ, i < 5 → limbs[i]!.val = self[i]!.val) ∧
        ∀ i : ℕ, i < 9 → 5 ≤ i → limbs[i]!.val = 0 ⦄ := by
  unfold from_montgomery_loop
  apply loop.spec_decr_nat (measure := fun (iter, _) => 5 - iter.start.val)
    (inv := fun (iter, limbs) => iter.end = 5#usize ∧ iter.start.val ≤ 5 ∧
      (∀ i < iter.start.val, limbs[i]!.val = self[i]!.val) ∧
      ∀ i : ℕ, i < 9 → iter.start.val ≤ i → limbs[i]!.val = 0)
  · rintro ⟨iter, limbs⟩ ⟨hend, hstart, hlow, hhigh⟩
    unfold from_montgomery_loop.body
    by_cases hlt : iter.start.val < 5
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as
        ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      step as ⟨limbs1, hlimbs1⟩
      have hy' : y.val = self[iter.start.val]!.val := by
        rw [hy, hx, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      refine ⟨by rw [hend1, hend], by scalar_tac, fun i hi => ?_, fun i hi hi' => ?_,
        by scalar_tac⟩
      · rw [hlimbs1]
        by_cases hik : iter.start.val = i
        · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨hik, by scalar_tac⟩, hy', hik]
        · rw [Array.getElem!_Nat_set_ne _ _ _ _ hik]
          exact hlow i (by scalar_tac)
      · rw [hlimbs1, Array.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac)]
        exact hhigh i hi (by scalar_tac)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 5 := by scalar_tac
      rw [hk] at hlow hhigh
      simp only [WP.spec_ok]
      exact ⟨hlow, hhigh⟩
  · refine ⟨rfl, by simp, fun i hi => by simp at hi, fun i hi _ => ?_⟩
    rw [Array.getElem!_Nat_eq, Array.repeat_val, List.getElem!_replicate _ (n := (9#usize).val) hi]
    rfl

@[step]
theorem from_montgomery_spec (self : Scalar52) (hself : self.LimbsLt 52) :
    from_montgomery self ⦃ (r : Scalar52) =>
      r.asNat * montgomeryRadix % L = self.asNat % L ∧ r.asNat < L ∧
      r.LimbsLt 52 ⦄ := by
  unfold from_montgomery
  step as ⟨limbs, hlow, hhigh⟩
  have hval : limbs.asNat 52 = self.asNat := by
    rw [Array.asNat_nine, Scalar52.asNat_eq, hlow 0 (by decide), hlow 1 (by decide),
      hlow 2 (by decide), hlow 3 (by decide), hlow 4 (by decide), hhigh 5 (by decide) (by decide),
      hhigh 6 (by decide) (by decide), hhigh 7 (by decide) (by decide),
      hhigh 8 (by decide) (by decide)]
    simp only [mul_zero, add_zero, Nat.reduceMul]
  have hbound : ∀ i : ℕ, i < 9 → limbs[i]!.val < 2 ^ 127 := by
    intro i hi
    by_cases h5 : i < 5
    · rw [hlow i h5]
      exact (hself i h5).trans (by decide)
    · rw [hhigh i hi (Nat.le_of_not_lt h5)]
      decide
  have hlt : limbs.asNat 52 < montgomeryRadix * L :=
    hval ▸ (Scalar52.asNat_lt self hself).trans_le (Nat.le_mul_of_pos_right _ L_pos)
  step with montgomery_reduce_spec limbs hbound hlt as ⟨r, hr, hrL, hr_lt⟩
  exact ⟨hval ▸ hr, hrL, hr_lt⟩

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
