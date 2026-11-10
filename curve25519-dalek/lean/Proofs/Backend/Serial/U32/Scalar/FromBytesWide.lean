/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U32.Constants.R
import Proofs.Backend.Serial.U32.Constants.RR
import Proofs.Backend.Serial.U32.Scalar.Add
import Proofs.Backend.Serial.U32.Scalar.IndexMut
import Proofs.Helpers.Scalar29
import Proofs.Backend.Serial.U32.Scalar.MontgomeryMul
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bytes
import Proofs.Helpers.StepSpecs
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

open scoped Helpers.IndexStep Helpers.UpdateStep Helpers.MaskStep

/-- The inner loop of `from_bytes_wide` packs the 4 bytes of word `i` little-endian. -/
@[local step]
private theorem from_bytes_wide_loop0_loop0_spec (bytes : Array U8 64#usize)
    (words : Array U32 16#usize) (i : Usize) (hi : i.val < 16) (hw : words[i.val]!.val = 0) :
    from_bytes_wide_loop0_loop0 { start := 0#usize, «end» := 4#usize } bytes words i
    ⦃ (r : Array U32 16#usize) =>
      r[i.val]!.val = ∑ j ∈ Finset.range 4, 2 ^ (8 * j) * bytes[4 * i.val + j]!.val ∧
      ∀ k ≠ i.val, r[k]! = words[k]! ⦄ := by
  unfold from_bytes_wide_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 4 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 4#usize ∧ iter.start.val ≤ 4 ∧
      w[i.val]!.val = ∑ j ∈ Finset.range iter.start.val, 2 ^ (8 * j) * bytes[4 * i.val + j]!.val ∧
      ∀ k ≠ i.val, w[k]! = words[k]!)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hwi, hrest⟩
    unfold from_bytes_wide_loop0_loop0.body
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

/-- The outer loop of `from_bytes_wide` packs the 64 bytes into sixteen little-endian words. -/
@[local step]
private theorem from_bytes_wide_loop0_spec (bytes : Array U8 64#usize) :
    from_bytes_wide_loop0 { start := 0#usize, «end» := 16#usize } bytes
      (Array.repeat 16#usize 0#u32)
    ⦃ (w : Array U32 16#usize) =>
      ∀ k : ℕ, k < 16 → w[k]!.val = ∑ j ∈ Finset.range 4, 2 ^ (8 * j) * bytes[4 * k + j]!.val ⦄ :=
        by
  unfold from_bytes_wide_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 16 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 16#usize ∧ iter.start.val ≤ 16 ∧
      (∀ k < iter.start.val,
        w[k]!.val = ∑ j ∈ Finset.range 4, 2 ^ (8 * j) * bytes[4 * k + j]!.val) ∧
      ∀ k : ℕ, k < 16 → iter.start.val ≤ k → w[k]!.val = 0)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hdone, hzero⟩
    unfold from_bytes_wide_loop0.body
    by_cases hlt : iter.start.val < 16
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
      have hk : iter.start.val = 16 := Nat.le_antisymm hstart (Nat.not_lt.mp hlt)
      rw [hk] at hdone
      simp only [WP.spec_ok]
      exact hdone
  · refine ⟨rfl, by simp, fun _ hk => absurd hk (by simp), fun k hk _ => ?_⟩
    interval_cases k <;> rfl


/-- The low nine limbs represent the low 261 bits of the sixteen words. -/
private theorem from_bytes_wide.lo_eq (w0 w1 w2 w3 w4 w5 w6 w7 w8 : U32) :
    w0.val % 2 ^ 29 + 2 ^ 29 * ((w0.val >>> 29 ||| w1.val <<< 3 % U32.size) % 2 ^ 29)
      + 2 ^ 58 * ((w1.val >>> 26 ||| w2.val <<< 6 % U32.size) % 2 ^ 29)
      + 2 ^ 87 * ((w2.val >>> 23 ||| w3.val <<< 9 % U32.size) % 2 ^ 29)
      + 2 ^ 116 * ((w3.val >>> 20 ||| w4.val <<< 12 % U32.size) % 2 ^ 29)
      + 2 ^ 145 * ((w4.val >>> 17 ||| w5.val <<< 15 % U32.size) % 2 ^ 29)
      + 2 ^ 174 * ((w5.val >>> 14 ||| w6.val <<< 18 % U32.size) % 2 ^ 29)
      + 2 ^ 203 * ((w6.val >>> 11 ||| w7.val <<< 21 % U32.size) % 2 ^ 29)
      + 2 ^ 232 * ((w7.val >>> 8 ||| w8.val <<< 24 % U32.size) % 2 ^ 29)
      = w0.val + 2 ^ 32 * (w1.val + 2 ^ 32 * (w2.val + 2 ^ 32 * (w3.val + 2 ^ 32 * (w4.val
        + 2 ^ 32 * (w5.val + 2 ^ 32 * (w6.val + 2 ^ 32 * (w7.val
        + 2 ^ 32 * (w8.val % 2 ^ 5)))))))) := by
  have g1 := limb_of_words w0 w1 (r := 29) (s := 3) (m := 26) rfl rfl
  have g2 := limb_of_words w1 w2 (r := 26) (s := 6) (m := 23) rfl rfl
  have g3 := limb_of_words w2 w3 (r := 23) (s := 9) (m := 20) rfl rfl
  have g4 := limb_of_words w3 w4 (r := 20) (s := 12) (m := 17) rfl rfl
  have g5 := limb_of_words w4 w5 (r := 17) (s := 15) (m := 14) rfl rfl
  have g6 := limb_of_words w5 w6 (r := 14) (s := 18) (m := 11) rfl rfl
  have g7 := limb_of_words w6 w7 (r := 11) (s := 21) (m := 8) rfl rfl
  have g8 := limb_of_words w7 w8 (r := 8) (s := 24) (m := 5) rfl rfl
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

/-- The high nine limbs represent the sixteen words shifted right by 261 bits (times `2 ^ 5`, to
stay in powers of `2 ^ 32`). -/
private theorem from_bytes_wide.hi_eq (w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    2 ^ 5 * ((w8.val >>> 5 ||| w9.val <<< 27 % U32.size) % 2 ^ 29 + 2 ^ 29 * (w9.val >>> 2 % 2 ^ 29)
      + 2 ^ 58 * ((w9.val >>> 31 ||| w10.val <<< 1 % U32.size) % 2 ^ 29)
      + 2 ^ 87 * ((w10.val >>> 28 ||| w11.val <<< 4 % U32.size) % 2 ^ 29)
      + 2 ^ 116 * ((w11.val >>> 25 ||| w12.val <<< 7 % U32.size) % 2 ^ 29)
      + 2 ^ 145 * ((w12.val >>> 22 ||| w13.val <<< 10 % U32.size) % 2 ^ 29)
      + 2 ^ 174 * ((w13.val >>> 19 ||| w14.val <<< 13 % U32.size) % 2 ^ 29)
      + 2 ^ 203 * ((w14.val >>> 16 ||| w15.val <<< 16 % U32.size) % 2 ^ 29)
      + 2 ^ 232 * (w15.val >>> 13))
      = 2 ^ 5 * (w8.val / 2 ^ 5) + 2 ^ 32 * (w9.val + 2 ^ 32 * (w10.val + 2 ^ 32 * (w11.val
        + 2 ^ 32 * (w12.val + 2 ^ 32 * (w13.val + 2 ^ 32 * (w14.val + 2 ^ 32 * (w15.val))))))) := by
  have g9 := limb_of_words w8 w9 (r := 5) (s := 27) (m := 2) rfl rfl
  have g10 : w9.val >>> 2 % 2 ^ 29 = w9.val / 2 ^ 2 % 2 ^ 29 := by
    rw [Nat.shiftRight_eq_div_pow]
  have g11 := limb_of_words w9 w10 (r := 31) (s := 1) (m := 28) rfl rfl
  have g12 := limb_of_words w10 w11 (r := 28) (s := 4) (m := 25) rfl rfl
  have g13 := limb_of_words w11 w12 (r := 25) (s := 7) (m := 22) rfl rfl
  have g14 := limb_of_words w12 w13 (r := 22) (s := 10) (m := 19) rfl rfl
  have g15 := limb_of_words w13 w14 (r := 19) (s := 13) (m := 16) rfl rfl
  have g16 := limb_of_words w14 w15 (r := 16) (s := 16) (m := 13) rfl rfl
  have g17 : w15.val >>> 13 = w15.val / 2 ^ 13 := Nat.shiftRight_eq_div_pow _ _
  have d9 := Nat.div_add_mod w9.val (2 ^ 2)
  have e9 := Nat.div_add_mod (w9.val / 2 ^ 2) (2 ^ 29)
  rw [Nat.div_div_eq_div_mul, ← pow_add] at e9
  have d10 := Nat.div_add_mod w10.val (2 ^ 28)
  have d11 := Nat.div_add_mod w11.val (2 ^ 25)
  have d12 := Nat.div_add_mod w12.val (2 ^ 22)
  have d13 := Nat.div_add_mod w13.val (2 ^ 19)
  have d14 := Nat.div_add_mod w14.val (2 ^ 16)
  have d15 := Nat.div_add_mod w15.val (2 ^ 13)
  zify at g9 g10 g11 g12 g13 g14 g15 g16 g17 d9 e9 d10 d11 d12 d13 d14 d15 ⊢
  linear_combination 2 ^ 5 * g9 + 2 ^ 34 * g10 + 2 ^ 63 * g11 + 2 ^ 92 * g12 + 2 ^ 121 * g13
    + 2 ^ 150 * g14 + 2 ^ 179 * g15 + 2 ^ 208 * g16 + 2 ^ 237 * g17 + 2 ^ 32 * d9 + 2 ^ 34 * e9
    + 2 ^ 64 * d10 + 2 ^ 96 * d11 + 2 ^ 128 * d12 + 2 ^ 160 * d13 + 2 ^ 192 * d14 + 2 ^ 224 * d15

/-- The eighteen limbs cut from sixteen words: the low nine plus `montgomeryRadix` times the high
nine. -/
private theorem from_bytes_wide.limbs_eq (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 :
    U32) :
    ((w8.val >>> 5 ||| w9.val <<< 27 % U32.size) % 2 ^ 29 + 2 ^ 29 * (w9.val >>> 2 % 2 ^ 29)
      + 2 ^ 58 * ((w9.val >>> 31 ||| w10.val <<< 1 % U32.size) % 2 ^ 29)
      + 2 ^ 87 * ((w10.val >>> 28 ||| w11.val <<< 4 % U32.size) % 2 ^ 29)
      + 2 ^ 116 * ((w11.val >>> 25 ||| w12.val <<< 7 % U32.size) % 2 ^ 29)
      + 2 ^ 145 * ((w12.val >>> 22 ||| w13.val <<< 10 % U32.size) % 2 ^ 29)
      + 2 ^ 174 * ((w13.val >>> 19 ||| w14.val <<< 13 % U32.size) % 2 ^ 29)
      + 2 ^ 203 * ((w14.val >>> 16 ||| w15.val <<< 16 % U32.size) % 2 ^ 29)
      + 2 ^ 232 * (w15.val >>> 13)) * montgomeryRadix
    + (w0.val % 2 ^ 29 + 2 ^ 29 * ((w0.val >>> 29 ||| w1.val <<< 3 % U32.size) % 2 ^ 29)
      + 2 ^ 58 * ((w1.val >>> 26 ||| w2.val <<< 6 % U32.size) % 2 ^ 29)
      + 2 ^ 87 * ((w2.val >>> 23 ||| w3.val <<< 9 % U32.size) % 2 ^ 29)
      + 2 ^ 116 * ((w3.val >>> 20 ||| w4.val <<< 12 % U32.size) % 2 ^ 29)
      + 2 ^ 145 * ((w4.val >>> 17 ||| w5.val <<< 15 % U32.size) % 2 ^ 29)
      + 2 ^ 174 * ((w5.val >>> 14 ||| w6.val <<< 18 % U32.size) % 2 ^ 29)
      + 2 ^ 203 * ((w6.val >>> 11 ||| w7.val <<< 21 % U32.size) % 2 ^ 29)
      + 2 ^ 232 * ((w7.val >>> 8 ||| w8.val <<< 24 % U32.size) % 2 ^ 29))
      = w0.val + 2 ^ 32 * (w1.val + 2 ^ 32 * (w2.val + 2 ^ 32 * (w3.val + 2 ^ 32 * (w4.val
        + 2 ^ 32 * (w5.val + 2 ^ 32 * (w6.val + 2 ^ 32 * (w7.val + 2 ^ 32 * (w8.val
        + 2 ^ 32 * (w9.val + 2 ^ 32 * (w10.val + 2 ^ 32 * (w11.val + 2 ^ 32 * (w12.val
        + 2 ^ 32 * (w13.val + 2 ^ 32 * (w14.val + 2 ^ 32 * (w15.val))))))))))))))) := by
  have hhi := from_bytes_wide.hi_eq w8 w9 w10 w11 w12 w13 w14 w15
  have d8 := Nat.div_add_mod w8.val (2 ^ 5)
  have hR : montgomeryRadix = 2 ^ 32 * (2 ^ 32 * (2 ^ 32 * (2 ^ 32 * (2 ^ 32 * (2 ^ 32 *
      (2 ^ 32 * (2 ^ 32 * 2 ^ 5))))))) := by
    rw [montgomeryRadix_def]
    simp only [← Nat.pow_add]
  rw [from_bytes_wide.lo_eq, hR]
  generalize (2 : ℕ) ^ 32 = B at hhi ⊢
  generalize (2 : ℕ) ^ 5 = C at hhi d8 ⊢
  zify at hhi d8 ⊢
  linear_combination B ^ 8 * hhi + B ^ 8 * d8

/-- `montgomery_mul` by `R = montgomeryRadix mod L` reduces modulo `L`. -/
@[local step]
private theorem montgomery_mul_R_spec (a : Scalar29) (ha : a.LimbsLt 29) :
    montgomery_mul a constants.R ⦃ (r : Scalar29) =>
      r.asNat % L = a.asNat % L ∧ r.asNat < L ∧ r.LimbsLt 29 ⦄ := by
  obtain ⟨hR, hR_limbs⟩ := constants.R_spec
  have hR_lt : constants.R.asNat < L := hR ▸ Nat.mod_lt _ L_pos
  apply spec_mono (montgomery_mul_spec a _ ha hR_limbs
    (Nat.mul_lt_mul'' (Scalar29.asNat_lt a ha) hR_lt))
  rintro r ⟨hr, hr_lt, hr_limbs⟩
  refine ⟨mod_L_of_mul_montgomeryRadix ?_, hr_lt, hr_limbs⟩
  rw [hr, hR, Nat.mul_mod_mod]

/-- `montgomery_mul` by `RR = montgomeryRadix ^ 2 mod L` multiplies by `R = montgomeryRadix mod L`
modulo `L`. -/
@[local step]
private theorem montgomery_mul_RR_spec (a : Scalar29) (ha : a.LimbsLt 29) :
    montgomery_mul a constants.RR ⦃ (r : Scalar29) =>
      r.asNat % L = a.asNat * constants.R.asNat % L ∧ r.asNat < L ∧
      r.LimbsLt 29 ⦄ := by
  obtain ⟨hRR, hRR_limbs⟩ := constants.RR_spec
  have hRR_lt : constants.RR.asNat < L := hRR ▸ Nat.mod_lt _ L_pos
  apply spec_mono (montgomery_mul_spec a _ ha hRR_limbs
    (Nat.mul_lt_mul'' (Scalar29.asNat_lt a ha) hRR_lt))
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

/-- The 64 bytes as sixteen little-endian words, in Horner form. -/
private theorem from_bytes_wide.bytes_eq (bytes : Array U8 64#usize) (w : Array U32 16#usize)
    (hw : ∀ k : ℕ, k < 16 → w[k]!.val = ∑ j ∈ Finset.range 4, 2 ^ (8 * j) * bytes[4 * k + j]!.val) :
    bytes.asNat 8 = w[0]!.val + 2 ^ 32 * (w[1]!.val + 2 ^ 32 * (w[2]!.val + 2 ^ 32 * (w[3]!.val
      + 2 ^ 32 * (w[4]!.val + 2 ^ 32 * (w[5]!.val + 2 ^ 32 * (w[6]!.val + 2 ^ 32 * (w[7]!.val
      + 2 ^ 32 * (w[8]!.val + 2 ^ 32 * (w[9]!.val + 2 ^ 32 * (w[10]!.val + 2 ^ 32 * (w[11]!.val
      + 2 ^ 32 * (w[12]!.val + 2 ^ 32 * (w[13]!.val + 2 ^ 32 * (w[14]!.val
      + 2 ^ 32 * (w[15]!.val))))))))))))))) := by
  rw [Array.asNat_eq_sum_blocks 8 4 16 bytes rfl]
  simp only [show ∀ k : ℕ, (2 : ℕ) ^ (32 * k) = (2 ^ 32) ^ k from fun k => pow_mul 2 32 k]
  rw [Finset.sum_range_succ (n := 15), Finset.sum_range_succ (n := 14),
    Finset.sum_range_succ (n := 13), Finset.sum_range_succ (n := 12),
    Finset.sum_range_succ (n := 11), Finset.sum_range_succ (n := 10),
    Finset.sum_range_succ (n := 9), Finset.sum_range_succ (n := 8),
    Finset.sum_range_succ (n := 7), Finset.sum_range_succ (n := 6),
    Finset.sum_range_succ (n := 5), Finset.sum_range_succ (n := 4),
    Finset.sum_range_succ (n := 3), Finset.sum_range_succ (n := 2),
    Finset.sum_range_succ (n := 1), Finset.sum_range_one, ← hw 0 (by norm_num),
    ← hw 1 (by norm_num), ← hw 2 (by norm_num), ← hw 3 (by norm_num), ← hw 4 (by norm_num),
    ← hw 5 (by norm_num), ← hw 6 (by norm_num), ← hw 7 (by norm_num), ← hw 8 (by norm_num),
    ← hw 9 (by norm_num), ← hw 10 (by norm_num), ← hw 11 (by norm_num), ← hw 12 (by norm_num),
    ← hw 13 (by norm_num), ← hw 14 (by norm_num), ← hw 15 (by norm_num)]
  generalize (2 : ℕ) ^ 32 = B
  ring

set_option linter.hashCommand false in
#decompose from_bytes_wide from_bytes_wide_eq
  letRange 4 59 => from_bytes_wide.low
  letRange 5 52 => from_bytes_wide.high

attribute [nolint docBlame defsWithUnderscore] from_bytes_wide.low from_bytes_wide.high

/-- The low limbs: limbs 0 to 7 through the write-back function `back8`, and limb 8. -/
private theorem from_bytes_wide.low_spec (words : Array U32 16#usize) (mask : U32)
    (hmask : mask.val = 2 ^ 29 - 1) :
    from_bytes_wide.low words mask ⦃ (back : U32 → Scalar29) (w8 : U32)
        (back8 : U32 → Scalar29) (l8 : U32) =>
      (∀ x, back x = ZERO.set 0#usize x) ∧ w8 = words[8]! ∧
      l8.val = (words[7]!.val >>> 8 ||| words[8]!.val <<< 24 % U32.size) % 2 ^ 29 ∧
      ∀ x,
        (back8 x)[0]!.val = words[0]!.val % 2 ^ 29 ∧
        (back8 x)[1]!.val = (words[0]!.val >>> 29 ||| words[1]!.val <<< 3 % U32.size) % 2 ^ 29 ∧
        (back8 x)[2]!.val = (words[1]!.val >>> 26 ||| words[2]!.val <<< 6 % U32.size) % 2 ^ 29 ∧
        (back8 x)[3]!.val = (words[2]!.val >>> 23 ||| words[3]!.val <<< 9 % U32.size) % 2 ^ 29 ∧
        (back8 x)[4]!.val = (words[3]!.val >>> 20 ||| words[4]!.val <<< 12 % U32.size) % 2 ^ 29 ∧
        (back8 x)[5]!.val = (words[4]!.val >>> 17 ||| words[5]!.val <<< 15 % U32.size) % 2 ^ 29 ∧
        (back8 x)[6]!.val = (words[5]!.val >>> 14 ||| words[6]!.val <<< 18 % U32.size) % 2 ^ 29 ∧
        (back8 x)[7]!.val = (words[6]!.val >>> 11 ||| words[7]!.val <<< 21 % U32.size) % 2 ^ 29 ∧
        (back8 x)[8]! = x ⦄ := by
  unfold from_bytes_wide.low
  step*
  refine ⟨by assumption, by assumption, by simp only [*, UScalar.val_or], fun x => ?_⟩
  simp (disch := simp) only [*, UScalar.val_or, Array.getElem!_Nat_set_ne,
    Array.getElem!_Nat_set_eq]
  simp only [and_self]

/-- The high limbs: limbs 0 to 6 through the write-back function `back15`, and limbs 7 and 8. -/
private theorem from_bytes_wide.high_spec (words : Array U32 16#usize) (mask : U32)
    (hmask : mask.val = 2 ^ 29 - 1) (back : U32 → Scalar29)
    (hback : ∀ x, back x = ZERO.set 0#usize x) (w8 : U32) (hw8 : w8 = words[8]!) :
    from_bytes_wide.high words mask back w8 ⦃ (back15 : U32 → Scalar29) (l16 l17 : U32) =>
      l16.val = (words[14]!.val >>> 16 ||| words[15]!.val <<< 16 % U32.size) % 2 ^ 29 ∧
      l17.val = words[15]!.val >>> 13 ∧
      ∀ x,
        (back15 x)[0]!.val = (words[8]!.val >>> 5 ||| words[9]!.val <<< 27 % U32.size) % 2 ^ 29 ∧
        (back15 x)[1]!.val = words[9]!.val >>> 2 % 2 ^ 29 ∧
        (back15 x)[2]!.val = (words[9]!.val >>> 31 ||| words[10]!.val <<< 1 % U32.size) % 2 ^ 29 ∧
        (back15 x)[3]!.val = (words[10]!.val >>> 28 ||| words[11]!.val <<< 4 % U32.size) % 2 ^ 29 ∧
        (back15 x)[4]!.val = (words[11]!.val >>> 25 ||| words[12]!.val <<< 7 % U32.size) % 2 ^ 29 ∧
        (back15 x)[5]!.val = (words[12]!.val >>> 22 ||| words[13]!.val <<< 10 % U32.size) % 2 ^ 29 ∧
        (back15 x)[6]!.val = (words[13]!.val >>> 19 ||| words[14]!.val <<< 13 % U32.size) % 2 ^ 29 ∧
        (back15 x)[7]! = x ⦄ := by
  unfold from_bytes_wide.high
  step*
  refine ⟨by simp only [*, UScalar.val_or], by simp only [*], fun x => ?_⟩
  simp (disch := simp) only [*, UScalar.val_or, Array.getElem!_Nat_set_ne,
    Array.getElem!_Nat_set_eq]
  simp only [and_self]

@[step]
theorem from_bytes_wide_spec (bytes : Array U8 64#usize) :
    from_bytes_wide bytes ⦃ (r : Scalar29) =>
      r.asNat = bytes.asNat 8 % L ∧ r.LimbsLt 29 ⦄ := by
  rw [from_bytes_wide_eq]
  step with from_bytes_wide_loop0_spec as ⟨w, hw⟩
  have hbytes := from_bytes_wide.bytes_eq bytes w hw
  clear hw
  have hw15 : w[15]!.val < 2 ^ 32 := w[15]!.hBounds
  step as ⟨two_pow_29, htwo_pow_29⟩
  step as ⟨mask, hmask⟩
  have hmask' : mask.val = 2 ^ 29 - 1 := by scalar_tac
  step with from_bytes_wide.low_spec w mask hmask' as ⟨back, w8, back8, l8, hback, hw8, hl8, hlo⟩
  step with from_bytes_wide.high_spec w mask hmask' back hback w8 hw8 as
    ⟨back15, l16, l17, hl16, hl17, hhi⟩
  step as ⟨r, back16, _, hback16⟩
  obtain ⟨hlo0, hlo1, hlo2, hlo3, hlo4, hlo5, hlo6, hlo7, hlo8⟩ := hlo l8
  obtain ⟨hhi0, hhi1, hhi2, hhi3, hhi4, hhi5, hhi6, hhi7⟩ := hhi l16
  have hlo_lt : (back8 l8).LimbsLt 29 := by
    intro i hi
    interval_cases i <;> simp only [hlo0, hlo1, hlo2, hlo3, hlo4, hlo5, hlo6, hlo7, hlo8,
      hl8] <;> exact Nat.mod_lt _ (by norm_num)
  have hhi_lt : (back16 l17).LimbsLt 29 := by
    intro i hi
    rw [hback16]
    interval_cases i <;>
      simp (disch := simp) only [Array.getElem!_Nat_set_ne, Array.getElem!_Nat_set_eq, hhi0, hhi1,
        hhi2, hhi3, hhi4, hhi5, hhi6, hhi7,
        hl16, hl17]
    iterate 8 exact Nat.mod_lt _ (by norm_num)
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (hw15.trans (by norm_num))
  step with montgomery_mul_R_spec (back8 l8) hlo_lt as ⟨lo9, hlo9, hlo9L, hlo9_lt⟩
  step with montgomery_mul_RR_spec (back16 l17) hhi_lt as ⟨hi9, hhi9, hhi9L, hhi9_lt⟩
  step with add_spec hi9 lo9 hhi9_lt hlo9_lt hhi9L hlo9L as ⟨res, hres, hres_lt⟩
  refine ⟨from_bytes_wide.mod_L_eq hres hhi9 hlo9 ?_, hres_lt⟩
  rw [hbytes, Scalar29.asNat_eq, Scalar29.asNat_eq, hback16]
  simp (disch := simp) only [Array.getElem!_Nat_set_ne, Array.getElem!_Nat_set_eq, hlo0, hlo1,
    hlo2, hlo3, hlo4, hlo5, hlo6, hlo7, hlo8, hl8,
    hhi0, hhi1, hhi2, hhi3, hhi4, hhi5, hhi6, hhi7, hl16, hl17]
  exact from_bytes_wide.limbs_eq w[0]! w[1]! w[2]! w[3]! w[4]! w[5]! w[6]! w[7]! w[8]! w[9]! w[10]!
    w[11]! w[12]! w[13]! w[14]! w[15]!

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
