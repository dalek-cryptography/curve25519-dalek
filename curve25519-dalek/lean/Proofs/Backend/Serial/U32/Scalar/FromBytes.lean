/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U32.Scalar.IndexMut
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
import Proofs.Helpers.Bytes
import Proofs.Helpers.Scalar29
public import Curve25519.Basic
import Subtle
import Proofs.Backend.Serial.U32.Scalar.Zero
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Array
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

open scoped Helpers.IndexStep Helpers.UpdateStep Helpers.MaskStep

/-- The inner loop of `from_bytes` packs the 8 bytes of word `i` little-endian. -/
@[local step]
private theorem from_bytes_loop0_loop0_spec (bytes : Array U8 32#usize) (words : Array U32 8#usize)
    (i : Usize) (hi : i.val < 8) (hw : words[i.val]!.val = 0) :
    from_bytes_loop0_loop0 { start := 0#usize, «end» := 4#usize } bytes words i
    ⦃ (r : Array U32 8#usize) =>
      r[i.val]!.val = ∑ j ∈ Finset.range 4, 2 ^ (8 * j) * bytes[4 * i.val + j]!.val ∧
      ∀ k ≠ i.val, r[k]! = words[k]! ⦄ := by
  unfold from_bytes_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 4 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 4#usize ∧ iter.start.val ≤ 4 ∧
      w[i.val]!.val = ∑ j ∈ Finset.range iter.start.val, 2 ^ (8 * j) * bytes[4 * i.val + j]!.val ∧
      ∀ k ≠ i.val, w[k]! = words[k]!)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hwi, hrest⟩
    unfold from_bytes_loop0_loop0.body
    by_cases hlt : iter.start.val < 4
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨b, hb⟩
      step as ⟨b64, hb64⟩
      step as ⟨sh, hsh⟩
      step as ⟨shifted, hshifted, _⟩
      step as ⟨acc, hacc⟩
      step as ⟨acc', hacc', _⟩
      step as ⟨w', hw'i, hw'rest⟩
      have hbyte : b64.val = bytes[4 * i.val + iter.start.val]!.val := by
        rw [hb64, UScalar.cast_val_eq, hb, hi2, hi1, Nat.mul_comm]
        exact Nat.mod_eq_of_lt ((UScalar.hBounds _).trans (by decide))
      have hb_lt : b64.val < 2 ^ 8 := hbyte ▸ UScalar.hBounds _
      have hshift : shifted.val = b64.val <<< (8 * iter.start.val) := by
        rw [hshifted, hsh, Nat.mul_comm, Nat.mod_eq_of_lt]
        rw [Nat.shiftLeft_eq, show U32.size = 2 ^ 32 by simp [U32.size, U32.numBits]]
        calc b64.val * 2 ^ (8 * iter.start.val) < 2 ^ 8 * 2 ^ (8 * iter.start.val) :=
            Nat.mul_lt_mul_of_pos_right hb_lt (by positivity)
          _ = 2 ^ (8 * (iter.start.val + 1)) := by ring
          _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hacc_lt : acc.val < 2 ^ (8 * iter.start.val) := by
        rw [hacc, hwi]
        exact Nat.sum_pow_mul_lt 8 _ _ fun j _ => UScalar.hBounds _
      refine ⟨by rw [hend1, hend], hstart1 ▸ hlt, ?_, fun k hk => (hw'rest k hk).trans (hrest k hk),
        hstart1 ▸ Nat.sub_succ_lt_self _ _ hlt⟩
      rw [hw'i, hacc', UScalar.val_or, hshift, Nat.or_shiftLeft_eq_add_pow_mul _ hacc_lt, hacc, hwi,
        hstart1, Finset.sum_range_succ, hbyte]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 4 := Nat.le_antisymm hstart (Nat.not_lt.mp hlt)
      rw [hk] at hwi
      simp only [WP.spec_ok]
      exact ⟨hwi, hrest⟩
  · exact ⟨rfl, by simp, by simpa using hw, fun _ _ => rfl⟩

/-- The outer loop of `from_bytes` packs the 32 bytes into eight little-endian words. -/
@[local step]
private theorem from_bytes_loop0_spec (bytes : Array U8 32#usize) :
    from_bytes_loop0 { start := 0#usize, «end» := 8#usize } bytes (Array.repeat 8#usize 0#u32)
    ⦃ (w : Array U32 8#usize) =>
      ∀ k : ℕ, k < 8 → w[k]!.val = ∑ j ∈ Finset.range 4, 2 ^ (8 * j) * bytes[4 * k + j]!.val ⦄ := by
  unfold from_bytes_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 8 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 8#usize ∧ iter.start.val ≤ 8 ∧
      (∀ k < iter.start.val,
        w[k]!.val = ∑ j ∈ Finset.range 4, 2 ^ (8 * j) * bytes[4 * k + j]!.val) ∧
      ∀ k : ℕ, k < 8 → iter.start.val ≤ k → w[k]!.val = 0)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hdone, hzero⟩
    unfold from_bytes_loop0.body
    by_cases hlt : iter.start.val < 8
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step with from_bytes_loop0_loop0_spec as ⟨w', hw'i, hw'rest⟩
      refine ⟨by rw [hend1, hend], hstart1 ▸ hlt, fun k hk => ?_, fun k hk hsk => ?_,
        hstart1 ▸ Nat.sub_succ_lt_self _ _ hlt⟩
      · by_cases hki : k = iter.start.val
        · rw [hki, hw'i]
        · rw [hw'rest k hki]
          rw [hstart1] at hk
          exact hdone k (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hki)
      · rw [hstart1] at hsk
        have hsk' : iter.start.val < k := hsk
        rw [hw'rest k (Nat.ne_of_gt hsk')]
        exact hzero k hk (Nat.le_of_lt hsk')
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 8 := Nat.le_antisymm hstart (Nat.not_lt.mp hlt)
      rw [hk] at hdone
      simp only [WP.spec_ok]
      exact hdone
  · refine ⟨rfl, by simp, fun _ hk => absurd hk (by simp), fun k hk _ => ?_⟩
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- Limb 8: word 7 without its low 8 bits. -/
private theorem from_bytes.limb_8 (w7 : U32) : w7.val >>> 8 % 2 ^ 24 = w7.val / 2 ^ 8 :=
  Nat.shiftRight_mod_eq_of_lt (UScalar.hBounds _)

/-- The nine limbs cut from eight words represent the same number. -/
private theorem from_bytes.limbs_eq (w0 w1 w2 w3 w4 w5 w6 w7 : U32) :
    w0.val % 2 ^ 29 + 2 ^ 29 * ((w0.val >>> 29 ||| w1.val <<< 3 % U32.size) % 2 ^ 29)
      + 2 ^ 58 * ((w1.val >>> 26 ||| w2.val <<< 6 % U32.size) % 2 ^ 29)
      + 2 ^ 87 * ((w2.val >>> 23 ||| w3.val <<< 9 % U32.size) % 2 ^ 29)
      + 2 ^ 116 * ((w3.val >>> 20 ||| w4.val <<< 12 % U32.size) % 2 ^ 29)
      + 2 ^ 145 * ((w4.val >>> 17 ||| w5.val <<< 15 % U32.size) % 2 ^ 29)
      + 2 ^ 174 * ((w5.val >>> 14 ||| w6.val <<< 18 % U32.size) % 2 ^ 29)
      + 2 ^ 203 * ((w6.val >>> 11 ||| w7.val <<< 21 % U32.size) % 2 ^ 29)
      + 2 ^ 232 * (w7.val >>> 8 % 2 ^ 24)
      = w0.val + 2 ^ 32 * w1.val + 2 ^ 64 * w2.val + 2 ^ 96 * w3.val + 2 ^ 128 * w4.val
        + 2 ^ 160 * w5.val + 2 ^ 192 * w6.val + 2 ^ 224 * w7.val := by
  have g1 := limb_of_words w0 w1 (r := 29) (s := 3) (m := 26) rfl rfl
  have g2 := limb_of_words w1 w2 (r := 26) (s := 6) (m := 23) rfl rfl
  have g3 := limb_of_words w2 w3 (r := 23) (s := 9) (m := 20) rfl rfl
  have g4 := limb_of_words w3 w4 (r := 20) (s := 12) (m := 17) rfl rfl
  have g5 := limb_of_words w4 w5 (r := 17) (s := 15) (m := 14) rfl rfl
  have g6 := limb_of_words w5 w6 (r := 14) (s := 18) (m := 11) rfl rfl
  have g7 := limb_of_words w6 w7 (r := 11) (s := 21) (m := 8) rfl rfl
  have g8 := from_bytes.limb_8 w7
  have d0 := Nat.div_add_mod w0.val (2 ^ 29)
  have d1 := Nat.div_add_mod w1.val (2 ^ 26)
  have d2 := Nat.div_add_mod w2.val (2 ^ 23)
  have d3 := Nat.div_add_mod w3.val (2 ^ 20)
  have d4 := Nat.div_add_mod w4.val (2 ^ 17)
  have d5 := Nat.div_add_mod w5.val (2 ^ 14)
  have d6 := Nat.div_add_mod w6.val (2 ^ 11)
  have d7 := Nat.div_add_mod w7.val (2 ^ 8)
  zify at g1 g2 g3 g4 g5 g6 g7 g8 d0 d1 d2 d3 d4 d5 d6 d7 ⊢
  linear_combination 2 ^ 29 * g1 + 2 ^ 58 * g2 + 2 ^ 87 * g3 + 2 ^ 116 * g4 + 2 ^ 145 * g5
    + 2 ^ 174 * g6 + 2 ^ 203 * g7 + 2 ^ 232 * g8 + d0 + 2 ^ 32 * d1 + 2 ^ 64 * d2 + 2 ^ 96 * d3
    + 2 ^ 128 * d4 + 2 ^ 160 * d5 + 2 ^ 192 * d6 + 2 ^ 224 * d7

@[step]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (r : Scalar29) =>
      r.asNat = bytes.asNat 8 ∧ r.LimbsLt 29 ⦄ := by
  unfold from_bytes
  step with from_bytes_loop0_spec as ⟨w, hw⟩
  have hbytes : bytes.asNat 8
      = w[0]!.val + 2 ^ 32 * w[1]!.val + 2 ^ 64 * w[2]!.val + 2 ^ 96 * w[3]!.val
        + 2 ^ 128 * w[4]!.val + 2 ^ 160 * w[5]!.val + 2 ^ 192 * w[6]!.val
        + 2 ^ 224 * w[7]!.val := by
    rw [Array.asNat_eq_sum_blocks 8 4 8 bytes rfl, Finset.sum_range_succ (n := 7),
      Finset.sum_range_succ (n := 6), Finset.sum_range_succ (n := 5),
      Finset.sum_range_succ (n := 4), Finset.sum_range_succ (n := 3),
      Finset.sum_range_succ (n := 2), Finset.sum_range_succ (n := 1), Finset.sum_range_one,
      ← hw 0 (by norm_num), ← hw 1 (by norm_num), ← hw 2 (by norm_num), ← hw 3 (by norm_num),
      ← hw 4 (by norm_num), ← hw 5 (by norm_num), ← hw 6 (by norm_num), ← hw 7 (by norm_num)]
    simp only [Nat.reduceMul, pow_zero, Nat.one_mul]
  clear hw
  generalize hw0 : w[0]! = w0 at hbytes
  generalize hw1 : w[1]! = w1 at hbytes
  generalize hw2 : w[2]! = w2 at hbytes
  generalize hw3 : w[3]! = w3 at hbytes
  generalize hw4 : w[4]! = w4 at hbytes
  generalize hw5 : w[5]! = w5 at hbytes
  generalize hw6 : w[6]! = w6 at hbytes
  generalize hw7 : w[7]! = w7 at hbytes
  step as ⟨two_pow_29, htwo_pow_29⟩
  step as ⟨mask, hmask⟩
  have hmask' : mask.val = 2 ^ 29 - 1 := by scalar_tac
  step as ⟨two_pow_24, htwo_pow_24⟩
  step as ⟨top_mask, htop_mask⟩
  have htop_mask' : top_mask.val = 2 ^ 24 - 1 := by scalar_tac
  step*
  refine ⟨?_, Scalar29.getElem!_set_nine_lt _ _ _ _ _ _ _ _ _ _ (by simp only [*]; rfl)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rw [Scalar29.asNat_set_nine _ _ _ _ _ _ _ _ _ _ (by simp only [*]; rfl), hbytes]
    simp only [*, UScalar.val_or]
    exact from_bytes.limbs_eq w0 w1 w2 w3 w4 w5 w6 w7
  all_goals simp only [*]
  iterate 8 exact Nat.mod_lt _ (by norm_num)
  exact (Nat.mod_lt _ (by norm_num)).trans (by norm_num)

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
