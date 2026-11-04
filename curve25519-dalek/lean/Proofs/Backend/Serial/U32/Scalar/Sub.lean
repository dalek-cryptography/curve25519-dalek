/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
import Mathlib.Tactic.ReduceModChar
import Proofs.Backend.Serial.U32.Scalar.ConditionalAddL
import Proofs.Backend.Serial.U32.Scalar.Index
import Proofs.Backend.Serial.U32.Scalar.IndexMut
import Proofs.Helpers.Scalar29
import Proofs.Backend.Serial.U32.Scalar.Zero
import Proofs.Helpers.AsNat
import Proofs.Helpers.StepSpecs
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

open scoped Helpers.MaskStep

/-- One borrow step of the subtraction loop, on a limb `x` and subtrahend `y = b_k + borrow`. -/
private theorem borrow_step {x y w : ℕ} (hx : x < 2 ^ 29) (hy : y ≤ 2 ^ 29)
    (hw : w = (x + (2 ^ 32 - y)) % 2 ^ 32) :
    w % 2 ^ 29 + y = x + 2 ^ 29 * (w / 2 ^ 31) := by
  omega

/-- The partial sums after one more limb of the subtraction loop. -/
private theorem sub_sum_step {Sd Sb Sa P beta dk bk ak beta' : ℕ} (hIH : Sd + Sb = Sa + P * beta)
    (hk : dk + (bk + beta) = ak + 2 ^ 29 * beta') :
    Sd + P * dk + (Sb + P * bk) = Sa + P * ak + P * 2 ^ 29 * beta' := by
  have h := congrArg (P * ·) hk
  simp only [mul_add] at h
  nlinarith [hIH, h]

/-- The loop of `sub` subtracts limb by limb with a borrow; the last borrow's top bit tells
whether `a < b`. -/
@[local step]
private theorem sub_loop_spec (a b : Scalar29) (mask : U32) (ha : a.LimbsLt 29)
    (hb : b.LimbsLt 29) (hmask : mask.val = 2 ^ 29 - 1) :
    sub_loop { start := 0#usize, «end» := 9#usize } a b ZERO mask 0#u32
    ⦃ (d : Scalar29) (borrow : U32) =>
      d.asNat + b.asNat = a.asNat + montgomeryRadix * (borrow.val / 2 ^ 31) ∧
      d.LimbsLt 29 ⦄ := by
  unfold sub_loop
  apply loop.spec_decr_nat (measure := fun (iter, _, _) => 9 - iter.start.val)
    (inv := fun (iter, d, borrow) => iter.end = 9#usize ∧ iter.start.val ≤ 9 ∧
      d.LimbsLt 29 ∧
      ∑ j ∈ Finset.range iter.start.val, 2 ^ (29 * j) * d[j]!.val
        + ∑ j ∈ Finset.range iter.start.val, 2 ^ (29 * j) * b[j]!.val =
        ∑ j ∈ Finset.range iter.start.val, 2 ^ (29 * j) * a[j]!.val
        + 2 ^ (29 * iter.start.val) * (borrow.val / 2 ^ 31))
  · rintro ⟨iter, d, borrow⟩ ⟨hend, hstart, hd, hsum⟩
    unfold sub_loop.body
    by_cases hlt : iter.start.val < 9
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      step as ⟨beta, hbeta, _⟩
      have hbeta' : beta.val = borrow.val / 2 ^ 31 := by rw [hbeta, Nat.shiftRight_eq_div_pow]
      have hbeta_le : beta.val ≤ 1 := by rw [hbeta']; scalar_tac
      have hxk : x.val < 2 ^ 29 := hx ▸ ha _ hlt
      have hyk : y.val < 2 ^ 29 := hy ▸ hb _ hlt
      step as ⟨y', hy'⟩
      step as ⟨w, hw⟩
      step as ⟨_, back, _, hback⟩
      step as ⟨dk, hdk⟩
      refine ⟨by rw [hend1, hend], by scalar_tac, fun i hi => ?_, ?_, by scalar_tac⟩
      · rw [hback]
        by_cases hik : iter.start.val = i
        · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨hik, by scalar_tac⟩, hdk]
          exact Nat.mod_lt _ (by norm_num)
        · rw [Array.getElem!_Nat_set_ne _ _ _ _ hik]
          exact hd i hi
      · rw [hback, hstart1, Array.sum_range_succ_set _ _ _ _ (by scalar_tac), Finset.sum_range_succ,
          Finset.sum_range_succ, Nat.mul_succ, pow_add, hdk, ← hx, ← hy]
        refine sub_sum_step hsum ?_
        rw [← hbeta', ← hy']
        refine borrow_step hxk (by scalar_tac) ?_
        rw [hw, core.num.U32.wrapping_sub_val_eq]
        simp [U32.size, U32.numBits]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 9 := by scalar_tac
      rw [hk, show 29 * 9 = 261 by rfl, ← montgomeryRadix_def] at hsum
      simp only [WP.spec_ok]
      refine ⟨?_, hd⟩
      simp only [Scalar29.asNat_def, Array.asNat_eq_sum]
      exact hsum
  · refine ⟨rfl, by simp, fun i hi => ?_, by simp⟩
    exact ZERO_spec.2 i hi

/-- The arithmetic of `sub`: the loop result `d` with borrow bit `beta`, corrected by
`conditional_add_l`. -/
private theorem sub_result {a b d r M beta : ℕ} (hsum : d + b = a + M * beta)
    (hbeta : beta = 0 ∨ beta = 1) (hd : d < M) (hLM : L < M) (ha' : a < b + L) (hb' : b ≤ L)
    (hr0 : beta = 0 → r = d) (hr1 : beta = 1 → r = (d + L) % M) :
    (r + b) % L = a % L ∧ r < L := by
  rcases hbeta with h | h
  · rw [hr0 h]
    subst h
    exact ⟨by rw [hsum, Nat.mul_zero, Nat.add_zero], by omega⟩
  · subst h
    have hmod : (d + L) % M = d + L - M := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hr1 rfl, hmod]
    exact ⟨by rw [show d + L - M + b = a + L by omega, Nat.add_mod_right], by omega⟩

/-- The correction step of `sub`, as a proposition kept opaque to `scalar_tac`. -/
private def SubCorrection (a b d : Scalar29) (beta : ℕ) : Prop :=
  ∀ r : Scalar29, (beta = 0 → r.asNat = d.asNat) →
    (beta = 1 → r.asNat = (d.asNat + L) % montgomeryRadix) →
    (r.asNat + b.asNat) % L = a.asNat % L ∧ r.asNat < L

@[step]
theorem sub_spec (a b : Scalar29) (ha : a.LimbsLt 29)
    (hb : b.LimbsLt 29) (ha' : a.asNat < b.asNat + L) (hb' : b.asNat ≤ L) :
    sub a b ⦃ (r : Scalar29) =>
      (r.asNat + b.asNat) % L = a.asNat % L ∧ r.asNat < L ∧ r.LimbsLt 29 ⦄ := by
  unfold sub
  step as ⟨two_pow_29, htwo_pow_29⟩
  step as ⟨mask, hmask⟩
  have hmask' : mask.val = 2 ^ 29 - 1 := by scalar_tac
  apply spec_bind (sub_loop_spec a b mask ha hb hmask')
  rintro ⟨d, borrow⟩ ⟨hsum, hd⟩
  have key : SubCorrection a b d (borrow.val / 2 ^ 31) := by
    have hd_lt := Scalar29.asNat_lt d hd
    have hbeta : borrow.val / 2 ^ 31 = 0 ∨ borrow.val / 2 ^ 31 = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ
        (Nat.div_lt_of_lt_mul (borrow.hBounds.trans_eq (by simp [UScalarTy.numBits]))))
    exact fun r hr0 hr1 => sub_result hsum hbeta hd_lt L_lt_montgomeryRadix ha' hb' hr0 hr1
  clear hsum
  step as ⟨beta, hbeta, _⟩
  step as ⟨c8, hc8⟩
  have hbeta' : beta.val = borrow.val / 2 ^ 31 := by rw [hbeta, Nat.shiftRight_eq_div_pow]
  have hbeta_le : beta.val ≤ 1 := by rw [hbeta']; scalar_tac
  have hc8' : c8.val = beta.val := by scalar_tac
  have hvalid : c8 = 0#u8 ∨ c8 = 1#u8 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbeta_le with h | h
    · exact Or.inl (by scalar_tac)
    · exact Or.inr (by scalar_tac)
  have hc0 : borrow.val / 2 ^ 31 = 0 → c8 = 0#u8 := fun h => by scalar_tac
  have hc1 : borrow.val / 2 ^ 31 = 1 → c8 = 1#u8 := fun h => by scalar_tac
  step as ⟨c, _, hc⟩
  subst hc
  step with conditional_add_l_spec as ⟨carry, r, hr0, hr1, hr⟩
  obtain ⟨hmod, hlt⟩ := key r (fun h => hr0 (hc0 h)) (fun h => hr1 (hc1 h))
  exact ⟨hmod, hlt, hr⟩

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
