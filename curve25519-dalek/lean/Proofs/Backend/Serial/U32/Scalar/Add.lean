/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang, Oliver Butterley, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
import Proofs.Backend.Serial.U32.Constants.L
import Proofs.Backend.Serial.U32.Scalar.Index
import Proofs.Backend.Serial.U32.Scalar.IndexMut
import Proofs.Backend.Serial.U32.Scalar.Sub
import Proofs.Backend.Serial.U32.Scalar.Zero
import Proofs.Helpers.AsNat
import Proofs.Helpers.Scalar29
import Subtle
import Proofs.Helpers.StepSpecs
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.Bitwise
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

open scoped Helpers.MaskStep

/-- One carry step of the addition loop at position `P`. -/
private theorem add_carry_step {Ss Sa Sb P cin x y carry1 : ℕ} (hIH : Ss + P * cin = Sa + Sb)
    (hc1 : carry1 = x + y + cin) :
    Ss + P * (carry1 % 2 ^ 29) + P * 2 ^ 29 * (carry1 / 2 ^ 29) = Sa + P * x + (Sb + P * y) := by
  rw [mul_assoc, add_assoc, ← mul_add, Nat.mod_add_div, hc1]
  calc Ss + P * (x + y + cin) = (Ss + P * cin) + P * x + P * y := by ring
    _ = _ := by rw [hIH]; ring

/-- The loop of `add` adds limb by limb with a carry; the last carry is dropped. -/
@[local step]
private theorem add_loop_spec (a b : Scalar29) (mask : U32) (ha : a.LimbsLt 29)
    (hb : b.LimbsLt 29) (hmask : mask.val = 2 ^ 29 - 1) :
    add_loop { start := 0#usize, «end» := 9#usize } a b ZERO mask 0#u32
    ⦃ (r : Scalar29) =>
      r.asNat = (a.asNat + b.asNat) % montgomeryRadix ∧ r.LimbsLt 29 ⦄ := by
  unfold add_loop
  apply loop.spec_decr_nat (measure := fun (iter, _, _) => 9 - iter.start.val)
    (inv := fun (iter, s, carry) => iter.end = 9#usize ∧ iter.start.val ≤ 9 ∧
      carry.val < 2 ^ 30 ∧ s.LimbsLt 29 ∧
      ∑ j ∈ Finset.range iter.start.val, 2 ^ (29 * j) * s[j]!.val
        + 2 ^ (29 * iter.start.val) * (carry.val / 2 ^ 29) =
        ∑ j ∈ Finset.range iter.start.val, 2 ^ (29 * j) * a[j]!.val
        + ∑ j ∈ Finset.range iter.start.val, 2 ^ (29 * j) * b[j]!.val)
  · rintro ⟨iter, s, carry⟩ ⟨hend, hstart, hcarry, hs, hsum⟩
    unfold add_loop.body
    by_cases hlt : iter.start.val < 9
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      have hxk : x.val < 2 ^ 29 := hx ▸ ha _ hlt
      have hyk : y.val < 2 ^ 29 := hy ▸ hb _ hlt
      step as ⟨xy, hxy⟩
      step as ⟨cin, hcin, _⟩
      have hcin' : cin.val = carry.val / 2 ^ 29 := by rw [hcin, Nat.shiftRight_eq_div_pow]
      have hcin_le : cin.val ≤ 1 := by rw [hcin']; scalar_tac
      step as ⟨carry1, hcarry1⟩
      step as ⟨_, back, _, hback⟩
      step as ⟨sk, hsk⟩
      refine ⟨by rw [hend1, hend], by scalar_tac, by scalar_tac, fun i hi => ?_, ?_, by scalar_tac⟩
      · rw [hback]
        by_cases hik : iter.start.val = i
        · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨hik, by scalar_tac⟩, hsk]
          exact Nat.mod_lt _ (by norm_num)
        · rw [Array.getElem!_Nat_set_ne _ _ _ _ hik]
          exact hs i hi
      · rw [hback, hstart1, Array.sum_range_succ_set _ _ _ _ (by scalar_tac), Finset.sum_range_succ,
          Finset.sum_range_succ, Nat.mul_succ, pow_add, hsk, ← hx, ← hy]
        exact add_carry_step hsum (by rw [hcarry1, hxy, hcin'])
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 9 := by scalar_tac
      rw [hk, show 29 * 9 = 261 from rfl, ← montgomeryRadix_def] at hsum
      simp only [WP.spec_ok]
      have hs_eq : s.asNat + montgomeryRadix * (carry.val / 2 ^ 29) = a.asNat + b.asNat := by
        simp only [Scalar29.asNat_def, Array.asNat_eq_sum]
        exact hsum
      refine ⟨?_, hs⟩
      rw [← hs_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Scalar29.asNat_lt s hs)]
  · refine ⟨rfl, by simp, by simp, fun i hi => ZERO_spec.2 i hi, by simp⟩

@[step]
theorem add_spec (a b : Scalar29) (ha : a.LimbsLt 29)
    (hb : b.LimbsLt 29) (ha' : a.asNat < L) (hb' : b.asNat < L) :
    add a b ⦃ (r : Scalar29) =>
      r.asNat = (a.asNat + b.asNat) % L ∧ r.LimbsLt 29 ⦄ := by
  unfold add
  step as ⟨two_pow_29, htwo_pow_29⟩
  step as ⟨mask, hmask⟩
  have hmask' : mask.val = 2 ^ 29 - 1 := by scalar_tac
  step as ⟨s, hs, hs_lt⟩
  obtain ⟨hLc, hLl⟩ := constants.L_spec
  have hab : a.asNat + b.asNat < montgomeryRadix :=
    (Nat.add_lt_add ha' hb').trans_eq (Nat.two_mul L).symm |>.trans two_mul_L_lt_montgomeryRadix
  have hs' : s.asNat = a.asNat + b.asNat := by rw [hs, Nat.mod_eq_of_lt hab]
  step as ⟨r, hr_mod, hr_lt, hr⟩
  refine ⟨?_, hr⟩
  rw [← hs', ← hr_mod, hLc, Nat.add_mod_right, Nat.mod_eq_of_lt hr_lt]

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
