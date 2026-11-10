/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.SquareLimbs
import Proofs.Helpers.Limbs
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- The loop doubles the elements of `iter` from position `iter.i` on and hands the updated
iterator to `back`. -/
private theorem square2_loop_spec (iter : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64)
    (hi : iter.i ≤ iter.slice.length)
    (hov : ∀ j < iter.slice.length, iter.i ≤ j → 2 * iter.slice.val[j]!.val ≤ U64.max) :
    square2_loop iter back ⦃ (r : core.slice.iter.IterMut U64) =>
      ∃ im, r = back im ∧ im.slice.length = iter.slice.length ∧
        ∀ j < iter.slice.length, im.slice.val[j]!.val =
          if iter.i ≤ j then 2 * iter.slice.val[j]!.val else iter.slice.val[j]!.val ⦄ := by
  unfold square2_loop
  apply loop.spec_decr_nat (measure := fun s => iter.slice.length - s.1.i)
    (inv := fun s => s.1.slice = iter.slice ∧ iter.i ≤ s.1.i ∧ s.1.i ≤ iter.slice.length ∧
      ∀ im : core.slice.iter.IterMut U64, im.slice.length = iter.slice.length →
        ∃ im', s.2 im = back im' ∧ im'.slice.length = iter.slice.length ∧
          ∀ j < iter.slice.length, im'.slice.val[j]!.val =
            if iter.i ≤ j ∧ j < s.1.i then 2 * iter.slice.val[j]!.val else im.slice.val[j]!.val)
  · rintro ⟨it, bk⟩ ⟨hs, hlo, hhi, hbk⟩
    simp only at hs hlo hhi hbk
    unfold square2_loop.body core.slice.iter.IteratorIterMut.next
    simp only [Slice.len_val]
    by_cases hlt : it.i < it.slice.length
    · have hx : (it.slice[it.i]).val * 2 ≤ U64.max := by
        have := hov it.i (by simpa [hs] using hlt) hlo
        rw [← hs, getElem!_pos it.slice.val it.i hlt] at this
        rw [Nat.mul_comm]
        exact this
      rw [dite_eq_left hlt]
      step as ⟨limb1, hlimb1⟩
      refine ⟨hs, by scalar_tac, by rw [← hs]; exact hlt, fun im him => ?_,
        by rw [← hs]; exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self _)⟩
      obtain ⟨im', hbk', hlen, hval⟩ :=
        hbk { slice := im.slice.setAtNat it.i limb1, i := im.i } (by simpa using him)
      refine ⟨im', hbk', hlen, fun j hj => ?_⟩
      rw [hval j hj]
      by_cases hji : j = it.i
      · subst hji
        rw [ite_eq_right (by simp), ite_eq_left ⟨hlo, Nat.lt_succ_self _⟩,
          Slice.getElem!_Nat_setAtNat_eq _ _ _ (by scalar_tac), hlimb1, ← hs,
          getElem!_pos it.slice.val it.i hlt, Nat.mul_comm]
        rfl
      · rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm hji)]
        split_ifs <;> scalar_tac
    · rw [dite_eq_right hlt]
      step*
      obtain ⟨im', hbk', hlen, hval⟩ := hbk it (by rw [hs])
      refine ⟨im', hbk', hlen, fun j hj => ?_⟩
      have hend : it.i = iter.slice.length := le_antisymm hhi (by rw [← hs]; exact not_lt.mp hlt)
      rw [hval j hj, hs, hend]
      simp [hj]
  · exact ⟨rfl, le_refl _, hi, fun im him => ⟨im, rfl, him, fun j hj => by simp⟩⟩

@[step]
theorem square2_spec (self : FieldElement51) (hself : self.LimbsLt 54) :
    square2 self ⦃ (r : FieldElement51) =>
      r.asNat % p = 2 * self.asNat ^ 2 % p ∧ r.LimbsLt 53 ⦄ := by
  unfold square2
  step as ⟨sq, hsq, hsq_lt⟩
  step as ⟨it, back, hit, hi0, hback⟩
  have hlen5 : it.slice.length = 5 := by simp [Slice.length, hit]
  have hsq' : ∀ j : ℕ, j < 5 → 2 * (it.slice.val[j]!).val < 2 ^ 53 := fun j hj => by
    have := hsq_lt j hj
    rw [Array.getElem!_Nat_eq, ← hit] at this
    scalar_tac
  apply spec_bind (square2_loop_spec it (fun im => im) (by scalar_tac)
    (fun j hj _ => (hsq' j (by scalar_tac)).le.trans (by scalar_tac)))
  rintro r ⟨im, hr, hlen, hval⟩
  have hdbl : ∀ i : ℕ, i < 5 → (back im)[i]!.val = 2 * sq[i]!.val := fun i hi => by
    rw [Array.getElem!_Nat_eq, hback im (by scalar_tac), hval i (by scalar_tac), hi0,
      ite_eq_left (Nat.zero_le _), hit, ← Array.getElem!_Nat_eq]
  simp only [WP.spec_ok, hr]
  refine ⟨?_, fun i hi => ?_⟩
  · have h2 : FieldElement51.asNat (back im) = 2 * FieldElement51.asNat sq := by
      rw [FieldElement51.asNat_eq, FieldElement51.asNat_eq, hdbl 0 (by simp), hdbl 1 (by simp),
        hdbl 2 (by simp), hdbl 3 (by simp), hdbl 4 (by simp)]
      ring
    rw [h2, Nat.mul_mod, hsq, ← Nat.mul_mod]
  · rw [hdbl i hi]
    have := hsq_lt i hi
    scalar_tac
end Curve25519Dalek.backend.serial.u64.field.FieldElement51
