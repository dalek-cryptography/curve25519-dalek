/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
import Mathlib.Tactic.ReduceModChar
import Proofs.Backend.Serial.U64.Scalar.ConditionalAddL
import Proofs.Backend.Serial.U64.Scalar.Index
import Proofs.Backend.Serial.U64.Scalar.IndexMut
import Proofs.Helpers.Scalar52
import Proofs.Backend.Serial.U64.Scalar.Zero
import Proofs.Helpers.AsNat
import Proofs.Helpers.StepSpecs
public import Curve25519.Basic
import Proofs.Helpers.Montgomery
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

open scoped Helpers.MaskStep

/-- One borrow step of the subtraction loop, on a limb `x` and subtrahend `y = b_k + borrow`. -/
private theorem borrow_step {x y w : ℕ} (hx : x < 2 ^ 52) (hy : y ≤ 2 ^ 52)
    (hw : w = (x + (2 ^ 64 - y)) % 2 ^ 64) :
    w % 2 ^ 52 + y = x + 2 ^ 52 * (w / 2 ^ 63) := by
  omega

/-- The partial sums after one more limb of the subtraction loop. -/
private theorem sub_sum_step {Sd Sb Sa P beta dk bk ak beta' : ℕ} (hIH : Sd + Sb = Sa + P * beta)
    (hk : dk + (bk + beta) = ak + 2 ^ 52 * beta') :
    Sd + P * dk + (Sb + P * bk) = Sa + P * ak + P * 2 ^ 52 * beta' := by
  have h := congrArg (P * ·) hk
  simp only [mul_add] at h
  nlinarith [hIH, h]

/-- The loop of `sub` subtracts limb by limb with a borrow; the last borrow's top bit tells
whether `a < b`. -/
@[local step]
private theorem sub_loop_spec (a b : Scalar52) (mask : U64) (ha : a.LimbsLt 52)
    (hb : b.LimbsLt 52) (hmask : mask.val = 2 ^ 52 - 1) :
    sub_loop { start := 0#usize, «end» := 5#usize } a b ZERO mask 0#u64
    ⦃ (d : Scalar52) (borrow : U64) =>
      d.asNat + b.asNat = a.asNat + montgomeryRadix * (borrow.val / 2 ^ 63) ∧
      d.LimbsLt 52 ⦄ := by
  unfold sub_loop
  apply loop.spec_decr_nat (measure := fun (iter, _, _) => 5 - iter.start.val)
    (inv := fun (iter, d, borrow) => iter.end = 5#usize ∧ iter.start.val ≤ 5 ∧
      d.LimbsLt 52 ∧
      ∑ j ∈ Finset.range iter.start.val, 2 ^ (52 * j) * d[j]!.val
        + ∑ j ∈ Finset.range iter.start.val, 2 ^ (52 * j) * b[j]!.val =
        ∑ j ∈ Finset.range iter.start.val, 2 ^ (52 * j) * a[j]!.val
        + 2 ^ (52 * iter.start.val) * (borrow.val / 2 ^ 63))
  · rintro ⟨iter, d, borrow⟩ ⟨hend, hstart, hd, hsum⟩
    unfold sub_loop.body
    by_cases hlt : iter.start.val < 5
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      step as ⟨beta, hbeta, _⟩
      have hbeta' : beta.val = borrow.val / 2 ^ 63 := by rw [hbeta, Nat.shiftRight_eq_div_pow]
      have hbeta_le : beta.val ≤ 1 := by rw [hbeta']; scalar_tac
      have hxk : x.val < 2 ^ 52 := hx ▸ ha _ hlt
      have hyk : y.val < 2 ^ 52 := hy ▸ hb _ hlt
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
        rw [hw, core.num.U64.wrapping_sub_val_eq]
        simp [U64.size, U64.numBits]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 5 := by scalar_tac
      rw [hk, show 52 * 5 = 260 by rfl, ← montgomeryRadix_def] at hsum
      simp only [WP.spec_ok]
      refine ⟨?_, hd⟩
      simp only [Scalar52.asNat_def, Array.asNat_eq_sum]
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
private def SubCorrection (a b d : Scalar52) (beta : ℕ) : Prop :=
  ∀ r : Scalar52, (beta = 0 → r.asNat = d.asNat) →
    (beta = 1 → r.asNat = (d.asNat + L) % montgomeryRadix) →
    (r.asNat + b.asNat) % L = a.asNat % L ∧ r.asNat < L

@[step]
theorem sub_spec (a b : Scalar52) (ha : a.LimbsLt 52)
    (hb : b.LimbsLt 52) (ha' : a.asNat < b.asNat + L) (hb' : b.asNat ≤ L) :
    sub a b ⦃ (r : Scalar52) =>
      (r.asNat + b.asNat) % L = a.asNat % L ∧ r.asNat < L ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨two_pow_52, htwo_pow_52⟩
  step as ⟨mask, hmask⟩
  have hmask' : mask.val = 2 ^ 52 - 1 := by scalar_tac
  apply spec_bind (sub_loop_spec a b mask ha hb hmask')
  rintro ⟨d, borrow⟩ ⟨hsum, hd⟩
  have key : SubCorrection a b d (borrow.val / 2 ^ 63) := by
    have hd_lt := Scalar52.asNat_lt d hd
    have hbeta : borrow.val / 2 ^ 63 = 0 ∨ borrow.val / 2 ^ 63 = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ
        (Nat.div_lt_of_lt_mul (borrow.hBounds.trans_eq (by simp [UScalarTy.numBits]))))
    exact fun r hr0 hr1 => sub_result hsum hbeta hd_lt L_lt_montgomeryRadix ha' hb' hr0 hr1
  clear hsum
  step as ⟨beta, hbeta, _⟩
  step as ⟨c8, hc8⟩
  have hbeta' : beta.val = borrow.val / 2 ^ 63 := by rw [hbeta, Nat.shiftRight_eq_div_pow]
  have hbeta_le : beta.val ≤ 1 := by rw [hbeta']; scalar_tac
  have hc8' : c8.val = beta.val := by scalar_tac
  have hvalid : c8 = 0#u8 ∨ c8 = 1#u8 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbeta_le with h | h
    · exact Or.inl (by scalar_tac)
    · exact Or.inr (by scalar_tac)
  have hc0 : borrow.val / 2 ^ 63 = 0 → c8 = 0#u8 := fun h => by scalar_tac
  have hc1 : borrow.val / 2 ^ 63 = 1 → c8 = 1#u8 := fun h => by scalar_tac
  step as ⟨c, _, hc⟩
  subst hc
  step with conditional_add_l_spec as ⟨carry, r, hr0, hr1, hr⟩
  obtain ⟨hmod, hlt⟩ := key r (fun h => hr0 (hc0 h)) (fun h => hr1 (hc1 h))
  exact ⟨hmod, hlt, hr⟩

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
