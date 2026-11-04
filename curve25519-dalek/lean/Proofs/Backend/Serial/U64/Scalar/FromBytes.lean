/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
public import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U64.Scalar.IndexMut
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
import Proofs.Helpers.Bytes
import Proofs.Helpers.Scalar52
public import Curve25519.Basic
import Subtle
import Proofs.Backend.Serial.U64.Scalar.Zero
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Array
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

open scoped Helpers.IndexStep Helpers.UpdateStep Helpers.MaskStep

/-- The inner loop of `from_bytes` packs the 8 bytes of word `i` little-endian. -/
@[local step]
private theorem from_bytes_loop0_loop0_spec (bytes : Array U8 32#usize) (words : Array U64 4#usize)
    (i : Usize) (hi : i.val < 4) (hw : words[i.val]!.val = 0) :
    from_bytes_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words i
    ⦃ (r : Array U64 4#usize) =>
      r[i.val]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * i.val + j]!.val ∧
      ∀ k ≠ i.val, r[k]! = words[k]! ⦄ := by
  unfold from_bytes_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 8 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 8#usize ∧ iter.start.val ≤ 8 ∧
      w[i.val]!.val = ∑ j ∈ Finset.range iter.start.val, 2 ^ (8 * j) * bytes[8 * i.val + j]!.val ∧
      ∀ k ≠ i.val, w[k]! = words[k]!)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hwi, hrest⟩
    unfold from_bytes_loop0_loop0.body
    by_cases hlt : iter.start.val < 8
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
      have hbyte : b64.val = bytes[8 * i.val + iter.start.val]!.val := by
        rw [hb64, UScalar.cast_val_eq, hb, hi2, hi1, Nat.mul_comm]
        exact Nat.mod_eq_of_lt ((UScalar.hBounds _).trans (by decide))
      have hb_lt : b64.val < 2 ^ 8 := hbyte ▸ UScalar.hBounds _
      have hshift : shifted.val = b64.val <<< (8 * iter.start.val) := by
        rw [hshifted, hsh, Nat.mul_comm, Nat.mod_eq_of_lt]
        rw [Nat.shiftLeft_eq, show U64.size = 2 ^ 64 by simp [U64.size, U64.numBits]]
        exact Nat.byte_mul_two_pow_lt hb_lt hlt
      have hacc_lt : acc.val < 2 ^ (8 * iter.start.val) := by
        rw [hacc, hwi]
        exact Nat.sum_pow_mul_lt 8 _ _ fun j _ => UScalar.hBounds _
      refine ⟨by rw [hend1, hend], hstart1 ▸ hlt, ?_, fun k hk => (hw'rest k hk).trans (hrest k hk),
        hstart1 ▸ Nat.sub_succ_lt_self _ _ hlt⟩
      rw [hw'i, hacc', UScalar.val_or, hshift, Nat.or_shiftLeft_eq_add_pow_mul _ hacc_lt, hacc, hwi,
        hstart1, Finset.sum_range_succ, hbyte]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 8 := Nat.le_antisymm hstart (Nat.not_lt.mp hlt)
      rw [hk] at hwi
      simp only [WP.spec_ok]
      exact ⟨hwi, hrest⟩
  · exact ⟨rfl, by simp, by simpa using hw, fun _ _ => rfl⟩

/-- The outer loop of `from_bytes` packs the 32 bytes into four little-endian words. -/
@[local step]
private theorem from_bytes_loop0_spec (bytes : Array U8 32#usize) :
    from_bytes_loop0 { start := 0#usize, «end» := 4#usize } bytes (Array.repeat 4#usize 0#u64)
    ⦃ (w : Array U64 4#usize) =>
      ∀ k : ℕ, k < 4 → w[k]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * k + j]!.val ⦄ := by
  unfold from_bytes_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 4 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 4#usize ∧ iter.start.val ≤ 4 ∧
      (∀ k < iter.start.val,
        w[k]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * k + j]!.val) ∧
      ∀ k : ℕ, k < 4 → iter.start.val ≤ k → w[k]!.val = 0)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hdone, hzero⟩
    unfold from_bytes_loop0.body
    by_cases hlt : iter.start.val < 4
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
      have hk : iter.start.val = 4 := Nat.le_antisymm hstart (Nat.not_lt.mp hlt)
      rw [hk] at hdone
      simp only [WP.spec_ok]
      exact hdone
  · refine ⟨rfl, by simp, fun _ hk => absurd hk (by simp), fun k hk _ => ?_⟩
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl

/-- Limb 4: word 3 without its low 16 bits. -/
private theorem from_bytes.limb_4 (w3 : U64) : w3.val >>> 16 % 2 ^ 48 = w3.val / 2 ^ 16 :=
  Nat.shiftRight_mod_eq_of_lt (UScalar.hBounds _)

/-- The five limbs cut from four words represent the same number. -/
private theorem from_bytes.limbs_eq (w0 w1 w2 w3 : U64) :
    w0.val % 2 ^ 52 + 2 ^ 52 * ((w0.val >>> 52 ||| w1.val <<< 12 % U64.size) % 2 ^ 52)
      + 2 ^ 104 * ((w1.val >>> 40 ||| w2.val <<< 24 % U64.size) % 2 ^ 52)
      + 2 ^ 156 * ((w2.val >>> 28 ||| w3.val <<< 36 % U64.size) % 2 ^ 52)
      + 2 ^ 208 * (w3.val >>> 16 % 2 ^ 48)
      = w0.val + 2 ^ 64 * w1.val + 2 ^ 128 * w2.val + 2 ^ 192 * w3.val := by
  have g1 := limb1_of_words w0 w1
  have g2 := limb2_of_words w1 w2
  have g3 := limb3_of_words w2 w3
  have g4 := from_bytes.limb_4 w3
  have d0 := Nat.div_add_mod w0.val (2 ^ 52)
  have d1 := Nat.div_add_mod w1.val (2 ^ 40)
  have d2 := Nat.div_add_mod w2.val (2 ^ 28)
  have d3 := Nat.div_add_mod w3.val (2 ^ 16)
  zify at g1 g2 g3 g4 d0 d1 d2 d3 ⊢
  linear_combination 2 ^ 52 * g1 + 2 ^ 104 * g2 + 2 ^ 156 * g3 + 2 ^ 208 * g4 + d0
    + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3

@[step]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (r : Scalar52) =>
      r.asNat = bytes.asNat 8 ∧ r.LimbsLt 52 ⦄ := by
  unfold from_bytes
  step with from_bytes_loop0_spec as ⟨w, hw⟩
  have hbytes : bytes.asNat 8
      = w[0]!.val + 2 ^ 64 * w[1]!.val + 2 ^ 128 * w[2]!.val + 2 ^ 192 * w[3]!.val := by
    rw [Array.asNat_eq_sum_blocks 8 8 4 bytes rfl, Finset.sum_range_succ (n := 3),
      Finset.sum_range_succ (n := 2), Finset.sum_range_succ (n := 1), Finset.sum_range_one,
      ← hw 0 (by norm_num), ← hw 1 (by norm_num), ← hw 2 (by norm_num), ← hw 3 (by norm_num)]
    simp only [Nat.reduceMul, pow_zero, Nat.one_mul]
  clear hw
  generalize hw0 : w[0]! = w0 at hbytes
  generalize hw1 : w[1]! = w1 at hbytes
  generalize hw2 : w[2]! = w2 at hbytes
  generalize hw3 : w[3]! = w3 at hbytes
  step as ⟨two_pow_52, htwo_pow_52⟩
  step as ⟨mask, hmask⟩
  have hmask' : mask.val = 2 ^ 52 - 1 := by scalar_tac
  step as ⟨two_pow_48, htwo_pow_48⟩
  step as ⟨top_mask, htop_mask⟩
  have htop_mask' : top_mask.val = 2 ^ 48 - 1 := by scalar_tac
  step*
  refine ⟨?_, Scalar52.getElem!_set_five_lt _ _ _ _ _ _ (by simp only [*]; rfl) ?_ ?_ ?_ ?_ ?_⟩
  · rw [Scalar52.asNat_set_five _ _ _ _ _ _ (by simp only [*]; rfl), hbytes]
    simp only [*, UScalar.val_or]
    exact from_bytes.limbs_eq w0 w1 w2 w3
  all_goals simp only [*]
  iterate 4 exact Nat.mod_lt _ (by norm_num)
  exact (Nat.mod_lt _ (by norm_num)).trans (by norm_num)

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
