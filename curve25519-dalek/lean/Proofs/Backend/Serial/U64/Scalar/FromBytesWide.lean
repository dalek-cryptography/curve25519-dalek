/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U64.Constants.R
import Proofs.Backend.Serial.U64.Constants.RR
import Proofs.Backend.Serial.U64.Scalar.Add
import Proofs.Backend.Serial.U64.Scalar.IndexMut
import Proofs.Helpers.Scalar52
import Proofs.Backend.Serial.U64.Scalar.MontgomeryMul
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bytes
import Proofs.Helpers.StepSpecs
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

open scoped Helpers.IndexStep Helpers.UpdateStep Helpers.MaskStep

/-- The inner loop of `from_bytes_wide` packs the 8 bytes of word `i` little-endian. -/
@[local step]
private theorem from_bytes_wide_loop0_loop0_spec (bytes : Array U8 64#usize)
    (words : Array U64 8#usize)
    (i : Usize) (hi : i.val < 8) (hw : words[i.val]!.val = 0) :
    from_bytes_wide_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words i
    ⦃ (r : Array U64 8#usize) =>
      r[i.val]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * i.val + j]!.val ∧
      ∀ k ≠ i.val, r[k]! = words[k]! ⦄ := by
  unfold from_bytes_wide_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 8 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 8#usize ∧ iter.start.val ≤ 8 ∧
      w[i.val]!.val = ∑ j ∈ Finset.range iter.start.val, 2 ^ (8 * j) * bytes[8 * i.val + j]!.val ∧
      ∀ k ≠ i.val, w[k]! = words[k]!)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hwi, hrest⟩
    unfold from_bytes_wide_loop0_loop0.body
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

/-- The outer loop of `from_bytes_wide` packs the 64 bytes into eight little-endian words. -/
@[local step]
private theorem from_bytes_wide_loop0_spec (bytes : Array U8 64#usize) :
    from_bytes_wide_loop0 { start := 0#usize, «end» := 8#usize } bytes (Array.repeat 8#usize 0#u64)
    ⦃ (w : Array U64 8#usize) =>
      ∀ k : ℕ, k < 8 → w[k]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * k + j]!.val ⦄ := by
  unfold from_bytes_wide_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 8 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 8#usize ∧ iter.start.val ≤ 8 ∧
      (∀ k < iter.start.val,
        w[k]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * k + j]!.val) ∧
      ∀ k : ℕ, k < 8 → iter.start.val ≤ k → w[k]!.val = 0)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hdone, hzero⟩
    unfold from_bytes_wide_loop0.body
    by_cases hlt : iter.start.val < 8
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step with from_bytes_wide_loop0_loop0_spec as ⟨w', hw'i, hw'rest⟩
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

/-- Limb 4: word 3 without its low 16 bits, and the low 4 bits of word 4. -/
private theorem from_bytes_wide.limb_4 (w3 w4 : U64) :
    (w3.val >>> 16 ||| w4.val <<< 48 % U64.size) % 2 ^ 52
      = w3.val / 2 ^ 16 + 2 ^ 48 * (w4.val % 2 ^ 4) :=
  Nat.shiftRight_or_shiftLeft_mod _ (UScalar.hBounds _) (U64.two_pow_dvd_size (by norm_num))

/-- Limb 5: bits 4 to 55 of word 4. -/
private theorem from_bytes_wide.limb_5 (w4 : U64) :
    w4.val >>> 4 % 2 ^ 52 + 2 ^ 52 * (w4.val / 2 ^ 56) = w4.val / 2 ^ 4 :=
  Nat.shiftRight_mod_add_mul_div _ 4 52

/-- Limb 6: word 4 without its low 56 bits, and the low 44 bits of word 5. -/
private theorem from_bytes_wide.limb_6 (w4 w5 : U64) :
    (w4.val >>> 56 ||| w5.val <<< 8 % U64.size) % 2 ^ 52
      = w4.val / 2 ^ 56 + 2 ^ 8 * (w5.val % 2 ^ 44) :=
  Nat.shiftRight_or_shiftLeft_mod _ (UScalar.hBounds _) (U64.two_pow_dvd_size (by norm_num))

/-- Limb 7: word 5 without its low 44 bits, and the low 32 bits of word 6. -/
private theorem from_bytes_wide.limb_7 (w5 w6 : U64) :
    (w5.val >>> 44 ||| w6.val <<< 20 % U64.size) % 2 ^ 52
      = w5.val / 2 ^ 44 + 2 ^ 20 * (w6.val % 2 ^ 32) :=
  Nat.shiftRight_or_shiftLeft_mod _ (UScalar.hBounds _) (U64.two_pow_dvd_size (by norm_num))

/-- Limb 8: word 6 without its low 32 bits, and the low 20 bits of word 7. -/
private theorem from_bytes_wide.limb_8 (w6 w7 : U64) :
    (w6.val >>> 32 ||| w7.val <<< 32 % U64.size) % 2 ^ 52
      = w6.val / 2 ^ 32 + 2 ^ 32 * (w7.val % 2 ^ 20) :=
  Nat.shiftRight_or_shiftLeft_mod _ (UScalar.hBounds _) (U64.two_pow_dvd_size (by norm_num))

/-- The low five limbs represent the low 260 bits of the eight words. -/
private theorem from_bytes_wide.lo_eq (w0 w1 w2 w3 w4 : U64) :
    w0.val % 2 ^ 52 + 2 ^ 52 * ((w0.val >>> 52 ||| w1.val <<< 12 % U64.size) % 2 ^ 52)
      + 2 ^ 104 * ((w1.val >>> 40 ||| w2.val <<< 24 % U64.size) % 2 ^ 52)
      + 2 ^ 156 * ((w2.val >>> 28 ||| w3.val <<< 36 % U64.size) % 2 ^ 52)
      + 2 ^ 208 * ((w3.val >>> 16 ||| w4.val <<< 48 % U64.size) % 2 ^ 52)
      = w0.val + 2 ^ 64 * (w1.val + 2 ^ 64 * (w2.val + 2 ^ 64 * (w3.val
        + 2 ^ 64 * (w4.val % 2 ^ 4)))) := by
  have g1 := limb1_of_words w0 w1
  have g2 := limb2_of_words w1 w2
  have g3 := limb3_of_words w2 w3
  have g4 := from_bytes_wide.limb_4 w3 w4
  have d0 := Nat.div_add_mod w0.val (2 ^ 52)
  have d1 := Nat.div_add_mod w1.val (2 ^ 40)
  have d2 := Nat.div_add_mod w2.val (2 ^ 28)
  have d3 := Nat.div_add_mod w3.val (2 ^ 16)
  zify at g1 g2 g3 g4 d0 d1 d2 d3 ⊢
  linear_combination 2 ^ 52 * g1 + 2 ^ 104 * g2 + 2 ^ 156 * g3 + 2 ^ 208 * g4 + d0
    + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3

/-- The high five limbs represent the eight words shifted right by 260 bits (times `2 ^ 4`, to
stay in powers of `2 ^ 64`). -/
private theorem from_bytes_wide.hi_eq (w4 w5 w6 w7 : U64) :
    2 ^ 4 * (w4.val >>> 4 % 2 ^ 52
      + 2 ^ 52 * ((w4.val >>> 56 ||| w5.val <<< 8 % U64.size) % 2 ^ 52)
      + 2 ^ 104 * ((w5.val >>> 44 ||| w6.val <<< 20 % U64.size) % 2 ^ 52)
      + 2 ^ 156 * ((w6.val >>> 32 ||| w7.val <<< 32 % U64.size) % 2 ^ 52)
      + 2 ^ 208 * (w7.val >>> 20))
      = 2 ^ 4 * (w4.val / 2 ^ 4) + 2 ^ 64 * (w5.val + 2 ^ 64 * (w6.val + 2 ^ 64 * w7.val)) := by
  have g5 := from_bytes_wide.limb_5 w4
  have g6 := from_bytes_wide.limb_6 w4 w5
  have g7 := from_bytes_wide.limb_7 w5 w6
  have g8 := from_bytes_wide.limb_8 w6 w7
  have g9 : w7.val >>> 20 = w7.val / 2 ^ 20 := Nat.shiftRight_eq_div_pow _ _
  have d5 := Nat.div_add_mod w5.val (2 ^ 44)
  have d6 := Nat.div_add_mod w6.val (2 ^ 32)
  have d7 := Nat.div_add_mod w7.val (2 ^ 20)
  zify at g5 g6 g7 g8 g9 d5 d6 d7 ⊢
  linear_combination 2 ^ 4 * (g5 + 2 ^ 52 * g6 + 2 ^ 104 * g7 + 2 ^ 156 * g8 + 2 ^ 208 * g9
    + 2 ^ 60 * d5 + 2 ^ 124 * d6 + 2 ^ 188 * d7)

/-- The ten limbs cut from eight words: the low five plus `montgomeryRadix` times the high five. -/
private theorem from_bytes_wide.limbs_eq (w0 w1 w2 w3 w4 w5 w6 w7 : U64) :
    (w4.val >>> 4 % 2 ^ 52 + 2 ^ 52 * ((w4.val >>> 56 ||| w5.val <<< 8 % U64.size) % 2 ^ 52)
      + 2 ^ 104 * ((w5.val >>> 44 ||| w6.val <<< 20 % U64.size) % 2 ^ 52)
      + 2 ^ 156 * ((w6.val >>> 32 ||| w7.val <<< 32 % U64.size) % 2 ^ 52)
      + 2 ^ 208 * (w7.val >>> 20)) * montgomeryRadix
    + (w0.val % 2 ^ 52 + 2 ^ 52 * ((w0.val >>> 52 ||| w1.val <<< 12 % U64.size) % 2 ^ 52)
      + 2 ^ 104 * ((w1.val >>> 40 ||| w2.val <<< 24 % U64.size) % 2 ^ 52)
      + 2 ^ 156 * ((w2.val >>> 28 ||| w3.val <<< 36 % U64.size) % 2 ^ 52)
      + 2 ^ 208 * ((w3.val >>> 16 ||| w4.val <<< 48 % U64.size) % 2 ^ 52))
      = w0.val + 2 ^ 64 * (w1.val + 2 ^ 64 * (w2.val + 2 ^ 64 * (w3.val + 2 ^ 64 * (w4.val
        + 2 ^ 64 * (w5.val + 2 ^ 64 * (w6.val + 2 ^ 64 * w7.val)))))) := by
  have hhi := from_bytes_wide.hi_eq w4 w5 w6 w7
  have d4 := Nat.div_add_mod w4.val (2 ^ 4)
  have hR : montgomeryRadix = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 4))) :=
    montgomeryRadix_def.trans (by rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add])
  rw [from_bytes_wide.lo_eq, hR]
  generalize (2 : ℕ) ^ 64 = B at hhi ⊢
  generalize (2 : ℕ) ^ 4 = C at hhi d4 ⊢
  zify at hhi d4 ⊢
  linear_combination B ^ 4 * hhi + B ^ 4 * d4

/-- `montgomery_mul` by `R = montgomeryRadix mod L` reduces modulo `L`. -/
@[local step]
private theorem montgomery_mul_R_spec (a : Scalar52) (ha : a.LimbsLt 52) :
    montgomery_mul a constants.R ⦃ (r : Scalar52) =>
      r.asNat % L = a.asNat % L ∧ r.asNat < L ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hR, hR_limbs⟩ := constants.R_spec
  have hR_lt : constants.R.asNat < L := hR ▸ Nat.mod_lt _ L_pos
  apply spec_mono (montgomery_mul_spec a _ ha hR_limbs
    (Nat.mul_lt_mul'' (Scalar52.asNat_lt a ha) hR_lt))
  rintro r ⟨hr, hr_lt, hr_limbs⟩
  refine ⟨mod_L_of_mul_montgomeryRadix ?_, hr_lt, hr_limbs⟩
  rw [hr, hR, Nat.mul_mod_mod]

/-- `montgomery_mul` by `RR = montgomeryRadix ^ 2 mod L` multiplies by `R = montgomeryRadix mod L`
modulo `L`. -/
@[local step]
private theorem montgomery_mul_RR_spec (a : Scalar52) (ha : a.LimbsLt 52) :
    montgomery_mul a constants.RR ⦃ (r : Scalar52) =>
      r.asNat % L = a.asNat * constants.R.asNat % L ∧ r.asNat < L ∧
      r.LimbsLt 52 ⦄ := by
  obtain ⟨hRR, hRR_limbs⟩ := constants.RR_spec
  have hRR_lt : constants.RR.asNat < L := hRR ▸ Nat.mod_lt _ L_pos
  apply spec_mono (montgomery_mul_spec a _ ha hRR_limbs
    (Nat.mul_lt_mul'' (Scalar52.asNat_lt a ha) hRR_lt))
  rintro r ⟨hr, hr_lt, hr_limbs⟩
  refine ⟨?_, hr_lt, hr_limbs⟩
  rw [hRR] at hr
  rw [mod_L_of_mul_montgomeryRadix_eq_mul_RR hr, constants.R_spec.1, Nat.mul_mod_mod]

/-- The result of `from_bytes_wide` modulo `L`: `hi · R + lo`, with the Montgomery factors of
the two products cancelled. -/
private theorem from_bytes_wide.mod_L_eq {r hi lo H Lo x : ℕ} (hr : r = (hi + lo) % L)
    (hhi : hi % L = H * constants.R.asNat % L) (hlo : lo % L = Lo % L)
    (hx : H * montgomeryRadix + Lo = x) : r = x % L := by
  rw [hr, Nat.add_mod, hhi, hlo, constants.R_spec.1, Nat.mul_mod_mod, ← Nat.add_mod, hx]

/-- The 64 bytes as eight little-endian words, in Horner form. -/
private theorem from_bytes_wide.bytes_eq (bytes : Array U8 64#usize) (w : Array U64 8#usize)
    (hw : ∀ k : ℕ, k < 8 → w[k]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * k + j]!.val) :
    bytes.asNat 8 = w[0]!.val + 2 ^ 64 * (w[1]!.val + 2 ^ 64 * (w[2]!.val + 2 ^ 64 * (w[3]!.val
      + 2 ^ 64 * (w[4]!.val + 2 ^ 64 * (w[5]!.val + 2 ^ 64 * (w[6]!.val
      + 2 ^ 64 * w[7]!.val)))))) := by
  rw [Array.asNat_eq_sum_blocks 8 8 8 bytes rfl]
  simp only [show ∀ k : ℕ, (2 : ℕ) ^ (64 * k) = (2 ^ 64) ^ k from fun k => pow_mul 2 64 k]
  rw [Finset.sum_range_succ (n := 7), Finset.sum_range_succ (n := 6),
    Finset.sum_range_succ (n := 5), Finset.sum_range_succ (n := 4),
    Finset.sum_range_succ (n := 3), Finset.sum_range_succ (n := 2),
    Finset.sum_range_succ (n := 1), Finset.sum_range_one,
    ← hw 0 (by norm_num), ← hw 1 (by norm_num), ← hw 2 (by norm_num), ← hw 3 (by norm_num),
    ← hw 4 (by norm_num), ← hw 5 (by norm_num), ← hw 6 (by norm_num), ← hw 7 (by norm_num)]
  generalize (2 : ℕ) ^ 64 = B
  ring

@[step]
theorem from_bytes_wide_spec (bytes : Array U8 64#usize) :
    from_bytes_wide bytes ⦃ (r : Scalar52) =>
      r.asNat = bytes.asNat 8 % L ∧ r.LimbsLt 52 ⦄ := by
  unfold from_bytes_wide
  step with from_bytes_wide_loop0_spec as ⟨w, hw⟩
  have hbytes := from_bytes_wide.bytes_eq bytes w hw
  clear hw
  generalize hw0 : w[0]! = w0 at hbytes
  generalize hw1 : w[1]! = w1 at hbytes
  generalize hw2 : w[2]! = w2 at hbytes
  generalize hw3 : w[3]! = w3 at hbytes
  generalize hw4 : w[4]! = w4 at hbytes
  generalize hw5 : w[5]! = w5 at hbytes
  generalize hw6 : w[6]! = w6 at hbytes
  generalize hw7 : w[7]! = w7 at hbytes
  have hw7_lt : w7.val < 2 ^ 64 := w7.hBounds
  step as ⟨two_pow_52, htwo_pow_52⟩
  step as ⟨mask, hmask⟩
  have hmask' : mask.val = 2 ^ 52 - 1 := by scalar_tac
  step*
  · refine Scalar52.getElem!_set_five_lt _ _ _ _ _ _ (by simp only [*]; rfl) ?_ ?_ ?_ ?_ ?_ <;>
      simp only [*] <;> exact Nat.mod_lt _ (by norm_num)
  · refine Scalar52.getElem!_set_five_lt _ _ _ _ _ _ (by simp only [*]; rfl) ?_ ?_ ?_ ?_ ?_ <;>
      simp only [*]
    iterate 4 exact Nat.mod_lt _ (by norm_num)
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (hw7_lt.trans (by norm_num))
  refine ⟨from_bytes_wide.mod_L_eq (by assumption) (by assumption) (by assumption) ?_,
    by assumption⟩
  rw [hbytes, Scalar52.asNat_set_five _ _ _ _ _ _ (by simp only [*]; rfl),
    Scalar52.asNat_set_five _ _ _ _ _ _ (by simp only [*]; rfl)]
  simp only [*, UScalar.val_or]
  exact from_bytes_wide.limbs_eq w0 w1 w2 w3 w4 w5 w6 w7

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
