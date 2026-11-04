/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Aeneas.Tactic.Solver.ScalarTac.Init
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import Proofs.Backend.Serial.U64.Field.Reduce
import Proofs.Helpers.Limbs
import Proofs.Helpers.StepSpecs
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

/-- Bit `k` of a number below `2 ^ k` is clear. -/
private theorem Nat.and_two_pow_eq_zero_of_lt {x k : ℕ} (hx : x < 2 ^ k) : x &&& 2 ^ k = 0 := by
  rw [Nat.and_two_pow, Nat.testBit_lt_two_pow hx, Bool.toNat_false, Nat.zero_mul]

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

set_option linter.hashCommand false in
#decompose to_bytes to_bytes_eq
  letRange 2 14 => to_bytes.quotient
  letRange 3 40 => to_bytes.carry
  letRange 4 109 => to_bytes.pack

attribute [nolint docBlame defsWithUnderscore] to_bytes.quotient to_bytes.carry to_bytes.pack

/-! ## Byte packing -/

/-- Bytes 0–6: limb 0 and the low 5 bits of limb 1. -/
private theorem to_bytes.bytes_0_6 (l0 l1 : U64) (h0 : l0.val < 2 ^ 51) :
    l0.val % 2 ^ 8 + 2 ^ 8 * (l0.val >>> 8 % 2 ^ 8) + 2 ^ 16 * (l0.val >>> 16 % 2 ^ 8)
      + 2 ^ 24 * (l0.val >>> 24 % 2 ^ 8) + 2 ^ 32 * (l0.val >>> 32 % 2 ^ 8)
      + 2 ^ 40 * (l0.val >>> 40 % 2 ^ 8)
      + 2 ^ 48 * ((l0.val >>> 48 ||| l1.val <<< 3 % U64.size) % 2 ^ 8)
      = l0.val + 2 ^ 51 * (l1.val % 2 ^ 5) := by
  have hs := Nat.sum_shiftRight_mod l0.val 0 8 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.pow_zero,
    Nat.one_mul, Nat.zero_add, Nat.shiftRight_zero] at hs
  rw [hs, Nat.shiftRight_or_shiftLeft_mod _ ?_ (U64.two_pow_dvd_size ?_), Nat.mul_add,
    ← Nat.add_assoc, Nat.mod_add_div]
  · ring
  · exact h0
  · norm_num

/-- Bytes 7–12: limb 1 without its low 5 bits, and the low 2 bits of limb 2. -/
private theorem to_bytes.bytes_7_12 (l1 l2 : U64) (h1 : l1.val < 2 ^ 51) :
    l1.val >>> 5 % 2 ^ 8 + 2 ^ 8 * (l1.val >>> 13 % 2 ^ 8) + 2 ^ 16 * (l1.val >>> 21 % 2 ^ 8)
      + 2 ^ 24 * (l1.val >>> 29 % 2 ^ 8) + 2 ^ 32 * (l1.val >>> 37 % 2 ^ 8)
      + 2 ^ 40 * ((l1.val >>> 45 ||| l2.val <<< 6 % U64.size) % 2 ^ 8)
      = l1.val / 2 ^ 5 + 2 ^ 46 * (l2.val % 2 ^ 2) := by
  have hs := Nat.sum_shiftRight_mod l1.val 5 8 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd,
    Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hs
  rw [hs, Nat.shiftRight_or_shiftLeft_mod _ ?_ (U64.two_pow_dvd_size ?_), Nat.mul_add,
    ← Nat.add_assoc, Nat.shiftRight_mod_add_mul_div]
  · ring
  · exact h1
  · norm_num

/-- Bytes 13–19: limb 2 without its low 2 bits, and the low 7 bits of limb 3. -/
private theorem to_bytes.bytes_13_19 (l2 l3 : U64) (h2 : l2.val < 2 ^ 51) :
    l2.val >>> 2 % 2 ^ 8 + 2 ^ 8 * (l2.val >>> 10 % 2 ^ 8) + 2 ^ 16 * (l2.val >>> 18 % 2 ^ 8)
      + 2 ^ 24 * (l2.val >>> 26 % 2 ^ 8) + 2 ^ 32 * (l2.val >>> 34 % 2 ^ 8)
      + 2 ^ 40 * (l2.val >>> 42 % 2 ^ 8)
      + 2 ^ 48 * ((l2.val >>> 50 ||| l3.val <<< 1 % U64.size) % 2 ^ 8)
      = l2.val / 2 ^ 2 + 2 ^ 49 * (l3.val % 2 ^ 7) := by
  have hs := Nat.sum_shiftRight_mod l2.val 2 8 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd,
    Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hs
  rw [hs, Nat.shiftRight_or_shiftLeft_mod _ ?_ (U64.two_pow_dvd_size ?_), Nat.mul_add,
    ← Nat.add_assoc, Nat.shiftRight_mod_add_mul_div]
  · ring
  · exact h2
  · norm_num

/-- Bytes 20–25: limb 3 without its low 7 bits, and the low 4 bits of limb 4. -/
private theorem to_bytes.bytes_20_25 (l3 l4 : U64) (h3 : l3.val < 2 ^ 51) :
    l3.val >>> 7 % 2 ^ 8 + 2 ^ 8 * (l3.val >>> 15 % 2 ^ 8) + 2 ^ 16 * (l3.val >>> 23 % 2 ^ 8)
      + 2 ^ 24 * (l3.val >>> 31 % 2 ^ 8) + 2 ^ 32 * (l3.val >>> 39 % 2 ^ 8)
      + 2 ^ 40 * ((l3.val >>> 47 ||| l4.val <<< 4 % U64.size) % 2 ^ 8)
      = l3.val / 2 ^ 7 + 2 ^ 44 * (l4.val % 2 ^ 4) := by
  have hs := Nat.sum_shiftRight_mod l3.val 7 8 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd,
    Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hs
  rw [hs, Nat.shiftRight_or_shiftLeft_mod _ ?_ (U64.two_pow_dvd_size ?_), Nat.mul_add,
    ← Nat.add_assoc, Nat.shiftRight_mod_add_mul_div]
  · ring
  · exact h3
  · norm_num

/-- Bytes 26–31: limb 4 without its low 4 bits. -/
private theorem to_bytes.bytes_26_31 (l4 : U64) (h4 : l4.val < 2 ^ 51) :
    l4.val >>> 4 % 2 ^ 8 + 2 ^ 8 * (l4.val >>> 12 % 2 ^ 8) + 2 ^ 16 * (l4.val >>> 20 % 2 ^ 8)
      + 2 ^ 24 * (l4.val >>> 28 % 2 ^ 8) + 2 ^ 32 * (l4.val >>> 36 % 2 ^ 8)
      + 2 ^ 40 * (l4.val >>> 44 % 2 ^ 8)
      = l4.val / 2 ^ 4 := by
  have hs := Nat.sum_shiftRight_mod l4.val 4 8 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd,
    Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hs
  rw [hs]
  exact Nat.shiftRight_mod_eq_of_lt (h4.trans (by norm_num))

/-- The 32 bytes written by `to_bytes` spell out the five 51-bit limbs. -/
private theorem to_bytes.bytes_eq (l0 l1 l2 l3 l4 : U64) (h0 : l0.val < 2 ^ 51)
    (h1 : l1.val < 2 ^ 51) (h2 : l2.val < 2 ^ 51) (h3 : l3.val < 2 ^ 51) (h4 : l4.val < 2 ^ 51) :
    l0.val % 2 ^ 8 + 2 ^ 8 * (l0.val >>> 8 % 2 ^ 8 + 2 ^ 8 * (l0.val >>> 16 % 2 ^ 8 + 2 ^ 8 *
      (l0.val >>> 24 % 2 ^ 8 + 2 ^ 8 * (l0.val >>> 32 % 2 ^ 8 + 2 ^ 8 * (l0.val >>> 40 % 2 ^ 8 +
      2 ^ 8 * ((l0.val >>> 48 ||| l1.val <<< 3 % U64.size) % 2 ^ 8 + 2 ^ 8 * (l1.val >>> 5 % 2 ^
      8 + 2 ^ 8 * (l1.val >>> 13 % 2 ^ 8 + 2 ^ 8 * (l1.val >>> 21 % 2 ^ 8 + 2 ^ 8 * (l1.val >>>
      29 % 2 ^ 8 + 2 ^ 8 * (l1.val >>> 37 % 2 ^ 8 + 2 ^ 8 * ((l1.val >>> 45 ||| l2.val <<< 6 %
      U64.size) % 2 ^ 8 + 2 ^ 8 * (l2.val >>> 2 % 2 ^ 8 + 2 ^ 8 * (l2.val >>> 10 % 2 ^ 8 + 2 ^ 8
      * (l2.val >>> 18 % 2 ^ 8 + 2 ^ 8 * (l2.val >>> 26 % 2 ^ 8 + 2 ^ 8 * (l2.val >>> 34 % 2 ^ 8
      + 2 ^ 8 * (l2.val >>> 42 % 2 ^ 8 + 2 ^ 8 * ((l2.val >>> 50 ||| l3.val <<< 1 % U64.size) %
      2 ^ 8 + 2 ^ 8 * (l3.val >>> 7 % 2 ^ 8 + 2 ^ 8 * (l3.val >>> 15 % 2 ^ 8 + 2 ^ 8 * (l3.val
      >>> 23 % 2 ^ 8 + 2 ^ 8 * (l3.val >>> 31 % 2 ^ 8 + 2 ^ 8 * (l3.val >>> 39 % 2 ^ 8 + 2 ^ 8 *
      ((l3.val >>> 47 ||| l4.val <<< 4 % U64.size) % 2 ^ 8 + 2 ^ 8 * (l4.val >>> 4 % 2 ^ 8 + 2 ^
      8 * (l4.val >>> 12 % 2 ^ 8 + 2 ^ 8 * (l4.val >>> 20 % 2 ^ 8 + 2 ^ 8 * (l4.val >>> 28 % 2 ^
      8 + 2 ^ 8 * (l4.val >>> 36 % 2 ^ 8 + 2 ^ 8 * (l4.val >>> 44 % 2 ^
      8)))))))))))))))))))))))))))))))
      = l0.val + 2 ^ 51 * l1.val + 2 ^ 102 * l2.val + 2 ^ 153 * l3.val + 2 ^ 204 * l4.val := by
  have g0 := to_bytes.bytes_0_6 l0 l1 h0
  have g1 := to_bytes.bytes_7_12 l1 l2 h1
  have g2 := to_bytes.bytes_13_19 l2 l3 h2
  have g3 := to_bytes.bytes_20_25 l3 l4 h3
  have g4 := to_bytes.bytes_26_31 l4 h4
  have d1 := Nat.div_add_mod l1.val (2 ^ 5)
  have d2 := Nat.div_add_mod l2.val (2 ^ 2)
  have d3 := Nat.div_add_mod l3.val (2 ^ 7)
  have d4 := Nat.div_add_mod l4.val (2 ^ 4)
  zify at g0 g1 g2 g3 g4 d1 d2 d3 d4 ⊢
  linear_combination g0 + 2 ^ 56 * g1 + 2 ^ 104 * g2 + 2 ^ 160 * g3 + 2 ^ 208 * g4
    + 2 ^ 51 * d1 + 2 ^ 102 * d2 + 2 ^ 153 * d3 + 2 ^ 204 * d4

/-- The byte-packing phase of `to_bytes`: canonical limbs are written out as 32 bytes. -/
@[local step]
private theorem to_bytes.pack_spec (limbs : Array U64 5#usize)
    (hlimbs : FieldElement51.LimbsLt 51 limbs) :
    to_bytes.pack limbs ⦃ (s : Array U8 32#usize) =>
      s.asNat 8 = FieldElement51.asNat limbs ∧ s[31]!.val < 2 ^ 7 ⦄ := by
  unfold FieldElement51.LimbsLt at hlimbs
  rw [Nat.forall_lt_five] at hlimbs
  simp (disch := simp) only [Array.getElem!_Nat_eq, getElem!_pos] at hlimbs
  obtain ⟨h0, h1, h2, h3, h4⟩ := hlimbs
  unfold to_bytes.pack
  step*
  subst_vars
  refine ⟨?_, ?_⟩
  · rw [FieldElement51.asNat_eq]
    simp (disch := simp) only [Array.getElem!_Nat_eq, getElem!_pos]
    simp only [Array.asNat_def, Array.set_val_eq, Array.repeat_val, UScalar.ofNatCore_val_eq,
      List.replicate_succ, List.replicate_zero, List.set_cons_zero, List.set_cons_succ,
      List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil]
    simp only [*, UScalar.cast_val_eq, UScalar.val_or, UScalarTy.U8_numBits_eq]
    exact to_bytes.bytes_eq _ _ _ _ _ h0 h1 h2 h3 h4
  · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨by simp, by simp⟩]
    simp only [*, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, Nat.shiftRight_eq_div_pow]
    exact (Nat.mod_le _ _).trans_lt (Nat.div_lt_of_lt_mul (h4.trans_eq (by norm_num)))

/-! ## Quotient and carry phases -/

attribute [local scalar_tac_simps] Nat.shiftRight_eq_div_pow

/-- The quotient phase of `to_bytes`: `q = ⌊(fe + 19) / 2^255⌋`. -/
@[local step]
private theorem to_bytes.quotient_spec (fe : FieldElement51) (i : U64) (hi : i.val = fe[0]!.val)
    (hfe : fe.LimbsLt 52) :
    to_bytes.quotient fe i ⦃ (q : U64) => q.val = (fe.asNat + 19) / 2 ^ 255 ⦄ := by
  unfold FieldElement51.LimbsLt at hfe
  rw [Nat.forall_lt_five] at hfe
  rw [FieldElement51.asNat_eq]
  simp (disch := simp) only [Array.getElem!_Nat_eq, getElem!_pos] at hi hfe ⊢
  obtain ⟨h0, h1, h2, h3, h4⟩ := hfe
  unfold to_bytes.quotient
  step*

/-- Propagating the carries of `f + t` through five 51-bit limbs and dropping the last carry
computes `(f + t) % 2^255`. -/
private theorem carry_chain_mod (f₀ f₁ f₂ f₃ f₄ t : ℕ) :
    (f₀ + t) % 2 ^ 51 + 2 ^ 51 * ((f₁ + (f₀ + t) / 2 ^ 51) % 2 ^ 51)
      + 2 ^ 102 * ((f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
      + 2 ^ 153 * ((f₃ + (f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
      + 2 ^ 204
        * ((f₄ + (f₃ + (f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
      = (f₀ + 2 ^ 51 * f₁ + 2 ^ 102 * f₂ + 2 ^ 153 * f₃ + 2 ^ 204 * f₄ + t) % 2 ^ 255 := by
  have e₀ := Nat.div_add_mod (f₀ + t) (2 ^ 51)
  have e₁ := Nat.div_add_mod (f₁ + (f₀ + t) / 2 ^ 51) (2 ^ 51)
  have e₂ := Nat.div_add_mod (f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) (2 ^ 51)
  have e₃ := Nat.div_add_mod (f₃ + (f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) (2 ^ 51)
  have e₄ := Nat.div_add_mod
    (f₄ + (f₃ + (f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) (2 ^ 51)
  set S := (f₀ + t) % 2 ^ 51 + 2 ^ 51 * ((f₁ + (f₀ + t) / 2 ^ 51) % 2 ^ 51)
      + 2 ^ 102 * ((f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
      + 2 ^ 153 * ((f₃ + (f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
      + 2 ^ 204
        * ((f₄ + (f₃ + (f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
    with hS
  have hlt : S < 2 ^ 255 := by scalar_tac
  have h : S + 2 ^ 255
      * ((f₄ + (f₃ + (f₂ + (f₁ + (f₀ + t) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51)
      = f₀ + 2 ^ 51 * f₁ + 2 ^ 102 * f₂ + 2 ^ 153 * f₃ + 2 ^ 204 * f₄ + t := by
    rw [hS]
    zify at e₀ e₁ e₂ e₃ e₄ ⊢
    linear_combination e₀ + 2 ^ 51 * e₁ + 2 ^ 102 * e₂ + 2 ^ 153 * e₃ + 2 ^ 204 * e₄
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The last two carries of the carry phase stay within `U64`. -/
private theorem carry_le_max {f₀ f₁ f₂ f₃ f₄ q : ℕ} (h₀ : f₀ < 2 ^ 52) (h₁ : f₁ < 2 ^ 52)
    (h₂ : f₂ < 2 ^ 52) (h₃ : f₃ < 2 ^ 52) (h₄ : f₄ < 2 ^ 52) (hq : q ≤ 1) :
    f₃ + (f₂ + (f₁ + (f₀ + 19 * q) >>> 51) >>> 51) >>> 51 ≤ U64.max ∧
      f₄ + (f₃ + (f₂ + (f₁ + (f₀ + 19 * q) >>> 51) >>> 51) >>> 51) >>> 51 ≤ U64.max := by
  simp only [Nat.shiftRight_eq_div_pow, U64.max_eq]
  omega

open scoped Helpers.IndexStep Helpers.UpdateStep Helpers.MaskStep in
/-- The carry phase of `to_bytes`: `fe + 19 q` reduced modulo `2^255`, in canonical limbs. -/
@[local step]
private theorem to_bytes.carry_spec (fe : FieldElement51) (i q : U64) (hi : i.val = fe[0]!.val)
    (hfe : fe.LimbsLt 52) (hq : q.val ≤ 1) :
    to_bytes.carry fe i q ⦃ (r : Array U64 5#usize) =>
      FieldElement51.asNat r = (fe.asNat + 19 * q.val) % 2 ^ 255 ∧
      FieldElement51.LimbsLt 51 r ⦄ := by
  unfold FieldElement51.LimbsLt at hfe ⊢
  rw [Nat.forall_lt_five] at hfe
  obtain ⟨h0, h1, h2, h3, h4⟩ := hfe
  simp only [Nat.forall_lt_five, FieldElement51.asNat_eq]
  unfold to_bytes.carry
  step; step; step; step as ⟨two_pow_51, h_two_pow_51⟩; step as ⟨mask, h_mask⟩
  have h_mask' : mask.val = 2 ^ 51 - 1 := by scalar_tac
  step*
  · simp (disch := simp) only [*]
    exact (carry_le_max h0 h1 h2 h3 h4 hq).1
  · simp (disch := simp) only [*]
    exact (carry_le_max h0 h1 h2 h3 h4 hq).2
  · simp (disch := simp) only [*, Nat.shiftRight_eq_div_pow]
    exact ⟨carry_chain_mod _ _ _ _ _ _, Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity),
      Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity)⟩

/-- Adding `19 q` with `q = ⌊(x + 19) / 2^255⌋` and reducing modulo `2^255` reduces `x < 2 p`
modulo `p`. -/
private theorem canonical_mod (x : ℕ) (hx : x < 2 * p) :
    (x + 19 * ((x + 19) / 2 ^ 255)) % 2 ^ 255 = x % p := by
  have hp := p_add_nineteen
  by_cases h : x + 19 < 2 ^ 255
  · have hxp : x < p := by scalar_tac
    rw [Nat.div_eq_of_lt h, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt (by scalar_tac),
      Nat.mod_eq_of_lt hxp]
  · obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le (show p ≤ x by scalar_tac)
    have hy : y < p := by scalar_tac
    rw [Nat.div_eq_of_lt_le (k := 1) (by scalar_tac) (by scalar_tac), Nat.mul_one,
      show p + y + 19 = y + 2 ^ 255 by scalar_tac, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by scalar_tac),
      Nat.add_mod_left, Nat.mod_eq_of_lt hy]

/-- The final check of `to_bytes`: the top bit of the last byte is clear. -/
private theorem and_128_eq_zero {x y : U8} (hy : y.val = (x &&& 128#u8).val)
    (hx : x.val < 2 ^ 7) : y = 0#u8 := by
  apply UScalar.eq_of_val_eq
  rw [hy, UScalar.val_and]
  exact Nat.and_two_pow_eq_zero_of_lt hx

open scoped Helpers.IndexStep Helpers.UpdateStep in
@[step]
theorem to_bytes_spec (self : FieldElement51) :
    to_bytes self ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 = self.asNat % p ⦄ := by
  rw [to_bytes_eq]
  step as ⟨fe, hfe_mod, hfe, hfe_lt⟩
  step as ⟨i, hi⟩
  step as ⟨q, hq⟩
  have hq1 : q.val ≤ 1 := by
    have hp := p_add_nineteen
    rw [hq, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by positivity)]
    scalar_tac
  step*
  · apply and_128_eq_zero (by assumption)
    simp only [*]
  · simp only [*, canonical_mod _ hfe_lt]
end Curve25519Dalek.backend.serial.u64.field.FieldElement51
