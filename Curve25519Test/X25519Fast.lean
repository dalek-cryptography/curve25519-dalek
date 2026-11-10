/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Fast.X25519
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
public section

/-! # The fast X25519 is `x25519Nat` (not audited)

`curve25519.Fast.x25519 = curve25519.x25519Nat`, so that RFC 7748's iterated test can be run on
the fast version (`Curve25519Test.X25519Iterated`). A field element `a : Fe` stands for
`a.toZ = (a.val : ZMod p)`; `a.Bnd B` bounds its limbs. The carry steps keep the value modulo `p`
and move the bounds (`carry_spec`: limbs below `2^63` become limbs below `2^26`); the uncarried
product of limbs below `2^27` has limbs below `2^63` and the product value (`mulRaw_spec`); the
ladder step is RFC 7748's `xDBL` and `xADD` (`step_spec`), the inversion is `z ^ (p - 2)`
(`invert_spec`), and the loop is `XZ.ladderLoop` (`loop_spec`). -/

namespace curve25519.Fast

open MontgomeryModel

/-- Limb `i`. -/
def Fe.limb (a : Fe) : Fin 10 → UInt64
  | 0 => a.f0
  | 1 => a.f1
  | 2 => a.f2
  | 3 => a.f3
  | 4 => a.f4
  | 5 => a.f5
  | 6 => a.f6
  | 7 => a.f7
  | 8 => a.f8
  | 9 => a.f9

/-- The limbs are below the bounds `B`. -/
def Fe.Bnd (a : Fe) (B : Fin 10 → ℕ) : Prop :=
  ∀ i, (a.limb i).toNat < B i

/-- The field element of the limbs. -/
def Fe.toZ (a : Fe) : ZMod p :=
  (a.val : ZMod p)

theorem Fe.Bnd.mono {a : Fe} {B C : Fin 10 → ℕ} (h : a.Bnd B) (hBC : ∀ i, B i ≤ C i) :
    a.Bnd C :=
  fun i => lt_of_lt_of_le (h i) (hBC i)

theorem Fe.bnd_iff (a : Fe) (B : Fin 10 → ℕ) :
    a.Bnd B ↔
      a.f0.toNat < B 0 ∧ a.f1.toNat < B 1 ∧ a.f2.toNat < B 2 ∧ a.f3.toNat < B 3 ∧
      a.f4.toNat < B 4 ∧ a.f5.toNat < B 5 ∧ a.f6.toNat < B 6 ∧ a.f7.toNat < B 7 ∧
      a.f8.toNat < B 8 ∧ a.f9.toNat < B 9 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ i
    fin_cases i <;> assumption

theorem p_eq_sub : p = 2 ^ 255 - 19 := by
  rw [p_eq_numeral]
  norm_num

theorem natCast_two_pow_255 : ((2 : ℕ) ^ 255 : ZMod p) = 19 := by
  have h : ((2 ^ 255 - 19 + 19 : ℕ) : ZMod p) = 19 := by
    rw [Nat.cast_add, ← p_eq_sub, ZMod.natCast_self, zero_add]
    norm_num
  rwa [show 2 ^ 255 - 19 + 19 = 2 ^ 255 by norm_num, Nat.cast_pow, Nat.cast_ofNat] at h

/-! ### Carries -/

/-- Carrying limb `9` into limb `0` keeps the value modulo `p`, as `2^255 = 19`. -/
theorem natCast_carry9 (n : ℕ) :
    ((n % 2 ^ 25 * 2 ^ 230 + 19 * (n / 2 ^ 25) : ℕ) : ZMod p) = ((n * 2 ^ 230 : ℕ) : ZMod p) := by
  have h : n % 2 ^ 25 * 2 ^ 230 + 19 * (n / 2 ^ 25) + n / 2 ^ 25 * p = n * 2 ^ 230 := by
    rw [p_eq_numeral]
    omega
  rw [← h, Nat.cast_add _ (_ * p), Nat.cast_mul _ p, ZMod.natCast_self, mul_zero, add_zero]

theorem carry0_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 1 + B 0 / 2 ^ 26 < 2 ^ 64) :
    (carry0 a).Bnd (Function.update (Function.update B 0 (2 ^ 26)) 1
      (B 1 + B 0 / 2 ^ 26)) ∧ (carry0 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f0.toNat / 2 ^ 26 ≤ B 0 / 2 ^ 26 := Nat.div_le_div_right (by omega)
  have ei : (carry0 a).f0.toNat = a.f0.toNat % 2 ^ 26 := by
    simp only [carry0, UInt64.toNat_mod]
    rfl
  have ej : (carry0 a).f1.toNat = a.f1.toNat + a.f0.toNat / 2 ^ 26 := by
    simp only [carry0, UInt64.toNat_add, UInt64.toNat_div]
    norm_num
    omega
  have o2 : (carry0 a).f2 = a.f2 := rfl
  have o3 : (carry0 a).f3 = a.f3 := rfl
  have o4 : (carry0 a).f4 = a.f4 := rfl
  have o5 : (carry0 a).f5 = a.f5 := rfl
  have o6 : (carry0 a).f6 = a.f6 := rfl
  have o7 : (carry0 a).f7 = a.f7 := rfl
  have o8 : (carry0 a).f8 = a.f8 := rfl
  have o9 : (carry0 a).f9 = a.f9 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o2, o3, o4, o5, o6, o7, o8, o9]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o2, o3, o4, o5, o6, o7, o8, o9]
    have := Nat.div_add_mod a.f0.toNat (2 ^ 26)
    exact congrArg Nat.cast (by omega)

theorem carry1_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 2 + B 1 / 2 ^ 25 < 2 ^ 64) :
    (carry1 a).Bnd (Function.update (Function.update B 1 (2 ^ 25)) 2
      (B 2 + B 1 / 2 ^ 25)) ∧ (carry1 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f1.toNat / 2 ^ 25 ≤ B 1 / 2 ^ 25 := Nat.div_le_div_right (by omega)
  have ei : (carry1 a).f1.toNat = a.f1.toNat % 2 ^ 25 := by
    simp only [carry1, UInt64.toNat_mod]
    rfl
  have ej : (carry1 a).f2.toNat = a.f2.toNat + a.f1.toNat / 2 ^ 25 := by
    simp only [carry1, UInt64.toNat_add, UInt64.toNat_div]
    norm_num
    omega
  have o0 : (carry1 a).f0 = a.f0 := rfl
  have o3 : (carry1 a).f3 = a.f3 := rfl
  have o4 : (carry1 a).f4 = a.f4 := rfl
  have o5 : (carry1 a).f5 = a.f5 := rfl
  have o6 : (carry1 a).f6 = a.f6 := rfl
  have o7 : (carry1 a).f7 = a.f7 := rfl
  have o8 : (carry1 a).f8 = a.f8 := rfl
  have o9 : (carry1 a).f9 = a.f9 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o0, o3, o4, o5, o6, o7, o8, o9]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o0, o3, o4, o5, o6, o7, o8, o9]
    have := Nat.div_add_mod a.f1.toNat (2 ^ 25)
    exact congrArg Nat.cast (by omega)

theorem carry2_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 3 + B 2 / 2 ^ 26 < 2 ^ 64) :
    (carry2 a).Bnd (Function.update (Function.update B 2 (2 ^ 26)) 3
      (B 3 + B 2 / 2 ^ 26)) ∧ (carry2 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f2.toNat / 2 ^ 26 ≤ B 2 / 2 ^ 26 := Nat.div_le_div_right (by omega)
  have ei : (carry2 a).f2.toNat = a.f2.toNat % 2 ^ 26 := by
    simp only [carry2, UInt64.toNat_mod]
    rfl
  have ej : (carry2 a).f3.toNat = a.f3.toNat + a.f2.toNat / 2 ^ 26 := by
    simp only [carry2, UInt64.toNat_add, UInt64.toNat_div]
    norm_num
    omega
  have o0 : (carry2 a).f0 = a.f0 := rfl
  have o1 : (carry2 a).f1 = a.f1 := rfl
  have o4 : (carry2 a).f4 = a.f4 := rfl
  have o5 : (carry2 a).f5 = a.f5 := rfl
  have o6 : (carry2 a).f6 = a.f6 := rfl
  have o7 : (carry2 a).f7 = a.f7 := rfl
  have o8 : (carry2 a).f8 = a.f8 := rfl
  have o9 : (carry2 a).f9 = a.f9 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o0, o1, o4, o5, o6, o7, o8, o9]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o0, o1, o4, o5, o6, o7, o8, o9]
    have := Nat.div_add_mod a.f2.toNat (2 ^ 26)
    exact congrArg Nat.cast (by omega)

theorem carry3_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 4 + B 3 / 2 ^ 25 < 2 ^ 64) :
    (carry3 a).Bnd (Function.update (Function.update B 3 (2 ^ 25)) 4
      (B 4 + B 3 / 2 ^ 25)) ∧ (carry3 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f3.toNat / 2 ^ 25 ≤ B 3 / 2 ^ 25 := Nat.div_le_div_right (by omega)
  have ei : (carry3 a).f3.toNat = a.f3.toNat % 2 ^ 25 := by
    simp only [carry3, UInt64.toNat_mod]
    rfl
  have ej : (carry3 a).f4.toNat = a.f4.toNat + a.f3.toNat / 2 ^ 25 := by
    simp only [carry3, UInt64.toNat_add, UInt64.toNat_div]
    norm_num
    omega
  have o0 : (carry3 a).f0 = a.f0 := rfl
  have o1 : (carry3 a).f1 = a.f1 := rfl
  have o2 : (carry3 a).f2 = a.f2 := rfl
  have o5 : (carry3 a).f5 = a.f5 := rfl
  have o6 : (carry3 a).f6 = a.f6 := rfl
  have o7 : (carry3 a).f7 = a.f7 := rfl
  have o8 : (carry3 a).f8 = a.f8 := rfl
  have o9 : (carry3 a).f9 = a.f9 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o0, o1, o2, o5, o6, o7, o8, o9]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o0, o1, o2, o5, o6, o7, o8, o9]
    have := Nat.div_add_mod a.f3.toNat (2 ^ 25)
    exact congrArg Nat.cast (by omega)

theorem carry4_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 5 + B 4 / 2 ^ 26 < 2 ^ 64) :
    (carry4 a).Bnd (Function.update (Function.update B 4 (2 ^ 26)) 5
      (B 5 + B 4 / 2 ^ 26)) ∧ (carry4 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f4.toNat / 2 ^ 26 ≤ B 4 / 2 ^ 26 := Nat.div_le_div_right (by omega)
  have ei : (carry4 a).f4.toNat = a.f4.toNat % 2 ^ 26 := by
    simp only [carry4, UInt64.toNat_mod]
    rfl
  have ej : (carry4 a).f5.toNat = a.f5.toNat + a.f4.toNat / 2 ^ 26 := by
    simp only [carry4, UInt64.toNat_add, UInt64.toNat_div]
    norm_num
    omega
  have o0 : (carry4 a).f0 = a.f0 := rfl
  have o1 : (carry4 a).f1 = a.f1 := rfl
  have o2 : (carry4 a).f2 = a.f2 := rfl
  have o3 : (carry4 a).f3 = a.f3 := rfl
  have o6 : (carry4 a).f6 = a.f6 := rfl
  have o7 : (carry4 a).f7 = a.f7 := rfl
  have o8 : (carry4 a).f8 = a.f8 := rfl
  have o9 : (carry4 a).f9 = a.f9 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o0, o1, o2, o3, o6, o7, o8, o9]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o0, o1, o2, o3, o6, o7, o8, o9]
    have := Nat.div_add_mod a.f4.toNat (2 ^ 26)
    exact congrArg Nat.cast (by omega)

theorem carry5_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 6 + B 5 / 2 ^ 25 < 2 ^ 64) :
    (carry5 a).Bnd (Function.update (Function.update B 5 (2 ^ 25)) 6
      (B 6 + B 5 / 2 ^ 25)) ∧ (carry5 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f5.toNat / 2 ^ 25 ≤ B 5 / 2 ^ 25 := Nat.div_le_div_right (by omega)
  have ei : (carry5 a).f5.toNat = a.f5.toNat % 2 ^ 25 := by
    simp only [carry5, UInt64.toNat_mod]
    rfl
  have ej : (carry5 a).f6.toNat = a.f6.toNat + a.f5.toNat / 2 ^ 25 := by
    simp only [carry5, UInt64.toNat_add, UInt64.toNat_div]
    norm_num
    omega
  have o0 : (carry5 a).f0 = a.f0 := rfl
  have o1 : (carry5 a).f1 = a.f1 := rfl
  have o2 : (carry5 a).f2 = a.f2 := rfl
  have o3 : (carry5 a).f3 = a.f3 := rfl
  have o4 : (carry5 a).f4 = a.f4 := rfl
  have o7 : (carry5 a).f7 = a.f7 := rfl
  have o8 : (carry5 a).f8 = a.f8 := rfl
  have o9 : (carry5 a).f9 = a.f9 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o0, o1, o2, o3, o4, o7, o8, o9]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o0, o1, o2, o3, o4, o7, o8, o9]
    have := Nat.div_add_mod a.f5.toNat (2 ^ 25)
    exact congrArg Nat.cast (by omega)

theorem carry6_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 7 + B 6 / 2 ^ 26 < 2 ^ 64) :
    (carry6 a).Bnd (Function.update (Function.update B 6 (2 ^ 26)) 7
      (B 7 + B 6 / 2 ^ 26)) ∧ (carry6 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f6.toNat / 2 ^ 26 ≤ B 6 / 2 ^ 26 := Nat.div_le_div_right (by omega)
  have ei : (carry6 a).f6.toNat = a.f6.toNat % 2 ^ 26 := by
    simp only [carry6, UInt64.toNat_mod]
    rfl
  have ej : (carry6 a).f7.toNat = a.f7.toNat + a.f6.toNat / 2 ^ 26 := by
    simp only [carry6, UInt64.toNat_add, UInt64.toNat_div]
    norm_num
    omega
  have o0 : (carry6 a).f0 = a.f0 := rfl
  have o1 : (carry6 a).f1 = a.f1 := rfl
  have o2 : (carry6 a).f2 = a.f2 := rfl
  have o3 : (carry6 a).f3 = a.f3 := rfl
  have o4 : (carry6 a).f4 = a.f4 := rfl
  have o5 : (carry6 a).f5 = a.f5 := rfl
  have o8 : (carry6 a).f8 = a.f8 := rfl
  have o9 : (carry6 a).f9 = a.f9 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o0, o1, o2, o3, o4, o5, o8, o9]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o0, o1, o2, o3, o4, o5, o8, o9]
    have := Nat.div_add_mod a.f6.toNat (2 ^ 26)
    exact congrArg Nat.cast (by omega)

theorem carry7_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 8 + B 7 / 2 ^ 25 < 2 ^ 64) :
    (carry7 a).Bnd (Function.update (Function.update B 7 (2 ^ 25)) 8
      (B 8 + B 7 / 2 ^ 25)) ∧ (carry7 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f7.toNat / 2 ^ 25 ≤ B 7 / 2 ^ 25 := Nat.div_le_div_right (by omega)
  have ei : (carry7 a).f7.toNat = a.f7.toNat % 2 ^ 25 := by
    simp only [carry7, UInt64.toNat_mod]
    rfl
  have ej : (carry7 a).f8.toNat = a.f8.toNat + a.f7.toNat / 2 ^ 25 := by
    simp only [carry7, UInt64.toNat_add, UInt64.toNat_div]
    norm_num
    omega
  have o0 : (carry7 a).f0 = a.f0 := rfl
  have o1 : (carry7 a).f1 = a.f1 := rfl
  have o2 : (carry7 a).f2 = a.f2 := rfl
  have o3 : (carry7 a).f3 = a.f3 := rfl
  have o4 : (carry7 a).f4 = a.f4 := rfl
  have o5 : (carry7 a).f5 = a.f5 := rfl
  have o6 : (carry7 a).f6 = a.f6 := rfl
  have o9 : (carry7 a).f9 = a.f9 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o0, o1, o2, o3, o4, o5, o6, o9]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o0, o1, o2, o3, o4, o5, o6, o9]
    have := Nat.div_add_mod a.f7.toNat (2 ^ 25)
    exact congrArg Nat.cast (by omega)

theorem carry8_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 9 + B 8 / 2 ^ 26 < 2 ^ 64) :
    (carry8 a).Bnd (Function.update (Function.update B 8 (2 ^ 26)) 9
      (B 9 + B 8 / 2 ^ 26)) ∧ (carry8 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f8.toNat / 2 ^ 26 ≤ B 8 / 2 ^ 26 := Nat.div_le_div_right (by omega)
  have ei : (carry8 a).f8.toNat = a.f8.toNat % 2 ^ 26 := by
    simp only [carry8, UInt64.toNat_mod]
    rfl
  have ej : (carry8 a).f9.toNat = a.f9.toNat + a.f8.toNat / 2 ^ 26 := by
    simp only [carry8, UInt64.toNat_add, UInt64.toNat_div]
    norm_num
    omega
  have o0 : (carry8 a).f0 = a.f0 := rfl
  have o1 : (carry8 a).f1 = a.f1 := rfl
  have o2 : (carry8 a).f2 = a.f2 := rfl
  have o3 : (carry8 a).f3 = a.f3 := rfl
  have o4 : (carry8 a).f4 = a.f4 := rfl
  have o5 : (carry8 a).f5 = a.f5 := rfl
  have o6 : (carry8 a).f6 = a.f6 := rfl
  have o7 : (carry8 a).f7 = a.f7 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o0, o1, o2, o3, o4, o5, o6, o7]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o0, o1, o2, o3, o4, o5, o6, o7]
    have := Nat.div_add_mod a.f8.toNat (2 ^ 26)
    exact congrArg Nat.cast (by omega)

theorem carry9_spec (a : Fe) (B : Fin 10 → ℕ) (ha : a.Bnd B)
    (hB : B 0 + 19 * (B 9 / 2 ^ 25) < 2 ^ 64) :
    (carry9 a).Bnd (Function.update (Function.update B 9 (2 ^ 25)) 0
      (B 0 + 19 * (B 9 / 2 ^ 25))) ∧ (carry9 a).toZ = a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ha
  have hdiv : a.f9.toNat / 2 ^ 25 ≤ B 9 / 2 ^ 25 := Nat.div_le_div_right (by omega)
  have ei : (carry9 a).f9.toNat = a.f9.toNat % 2 ^ 25 := by
    simp only [carry9, UInt64.toNat_mod]
    rfl
  have ej : (carry9 a).f0.toNat = a.f0.toNat + 19 * (a.f9.toNat / 2 ^ 25) := by
    simp only [carry9, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div]
    norm_num
    omega
  have o1 : (carry9 a).f1 = a.f1 := rfl
  have o2 : (carry9 a).f2 = a.f2 := rfl
  have o3 : (carry9 a).f3 = a.f3 := rfl
  have o4 : (carry9 a).f4 = a.f4 := rfl
  have o5 : (carry9 a).f5 = a.f5 := rfl
  have o6 : (carry9 a).f6 = a.f6 := rfl
  have o7 : (carry9 a).f7 = a.f7 := rfl
  have o8 : (carry9 a).f8 = a.f8 := rfl
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, ei, ej, o1, o2, o3, o4, o5, o6, o7, o8]
    simp only [Function.update]
    norm_num
    omega
  · simp only [Fe.toZ, Fe.val]
    rw [ei, ej, o1, o2, o3, o4, o5, o6, o7, o8]
    have := Nat.div_add_mod a.f9.toNat (2 ^ 25)
    have h := natCast_carry9 a.f9.toNat
    push_cast at h ⊢
    linear_combination h

/-- The carry chain: limbs below `2^63` become limbs below `2^26`, and the value is kept modulo
`p`. -/
theorem carry_spec (a : Fe) (ha : a.Bnd fun _ => 2 ^ 63) :
    (carry a).Bnd (fun _ => 2 ^ 26) ∧ (carry a).toZ = a.toZ := by
  obtain ⟨b1, e1⟩ := carry0_spec _ _ ha (by decide +kernel)
  obtain ⟨b2, e2⟩ := carry4_spec _ _ b1 (by decide +kernel)
  obtain ⟨b3, e3⟩ := carry1_spec _ _ b2 (by decide +kernel)
  obtain ⟨b4, e4⟩ := carry5_spec _ _ b3 (by decide +kernel)
  obtain ⟨b5, e5⟩ := carry2_spec _ _ b4 (by decide +kernel)
  obtain ⟨b6, e6⟩ := carry6_spec _ _ b5 (by decide +kernel)
  obtain ⟨b7, e7⟩ := carry3_spec _ _ b6 (by decide +kernel)
  obtain ⟨b8, e8⟩ := carry7_spec _ _ b7 (by decide +kernel)
  obtain ⟨b9, e9⟩ := carry4_spec _ _ b8 (by decide +kernel)
  obtain ⟨b10, e10⟩ := carry8_spec _ _ b9 (by decide +kernel)
  obtain ⟨b11, e11⟩ := carry9_spec _ _ b10 (by decide +kernel)
  obtain ⟨b12, e12⟩ := carry0_spec _ _ b11 (by decide +kernel)
  refine ⟨b12.mono (by decide +kernel), ?_⟩
  simp only [carry]
  rw [e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]

theorem mulRaw_spec (a b : Fe) (ha : a.Bnd fun _ => 2 ^ 27) (hb : b.Bnd fun _ => 2 ^ 27) :
    (mulRaw a b).Bnd (fun _ => 2 ^ 63) ∧ (mulRaw a b).toZ = a.toZ * b.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha
  rw [Fe.bnd_iff] at hb
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hb
  have hb0 : a.f0.toNat * b.f0.toNat + 19 * (a.f2.toNat * b.f8.toNat) +
      19 * (a.f4.toNat * b.f6.toNat) + 19 * (a.f6.toNat * b.f4.toNat) +
      19 * (a.f8.toNat * b.f2.toNat) + 38 * (a.f1.toNat * b.f9.toNat) +
      38 * (a.f3.toNat * b.f7.toNat) + 38 * (a.f5.toNat * b.f5.toNat) +
      38 * (a.f7.toNat * b.f3.toNat) + 38 * (a.f9.toNat * b.f1.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb1 : a.f0.toNat * b.f1.toNat + a.f1.toNat * b.f0.toNat + 19 * (a.f2.toNat * b.f9.toNat) +
      19 * (a.f3.toNat * b.f8.toNat) + 19 * (a.f4.toNat * b.f7.toNat) +
      19 * (a.f5.toNat * b.f6.toNat) + 19 * (a.f6.toNat * b.f5.toNat) +
      19 * (a.f7.toNat * b.f4.toNat) + 19 * (a.f8.toNat * b.f3.toNat) +
      19 * (a.f9.toNat * b.f2.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb2 : a.f0.toNat * b.f2.toNat + a.f2.toNat * b.f0.toNat + 2 * (a.f1.toNat * b.f1.toNat) +
      19 * (a.f4.toNat * b.f8.toNat) + 19 * (a.f6.toNat * b.f6.toNat) +
      19 * (a.f8.toNat * b.f4.toNat) + 38 * (a.f3.toNat * b.f9.toNat) +
      38 * (a.f5.toNat * b.f7.toNat) + 38 * (a.f7.toNat * b.f5.toNat) +
      38 * (a.f9.toNat * b.f3.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb3 : a.f0.toNat * b.f3.toNat + a.f1.toNat * b.f2.toNat + a.f2.toNat * b.f1.toNat +
      a.f3.toNat * b.f0.toNat + 19 * (a.f4.toNat * b.f9.toNat) + 19 * (a.f5.toNat * b.f8.toNat) +
      19 * (a.f6.toNat * b.f7.toNat) + 19 * (a.f7.toNat * b.f6.toNat) +
      19 * (a.f8.toNat * b.f5.toNat) + 19 * (a.f9.toNat * b.f4.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb4 : a.f0.toNat * b.f4.toNat + a.f2.toNat * b.f2.toNat + a.f4.toNat * b.f0.toNat +
      2 * (a.f1.toNat * b.f3.toNat) + 2 * (a.f3.toNat * b.f1.toNat) +
      19 * (a.f6.toNat * b.f8.toNat) + 19 * (a.f8.toNat * b.f6.toNat) +
      38 * (a.f5.toNat * b.f9.toNat) + 38 * (a.f7.toNat * b.f7.toNat) +
      38 * (a.f9.toNat * b.f5.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb5 : a.f0.toNat * b.f5.toNat + a.f1.toNat * b.f4.toNat + a.f2.toNat * b.f3.toNat +
      a.f3.toNat * b.f2.toNat + a.f4.toNat * b.f1.toNat + a.f5.toNat * b.f0.toNat +
      19 * (a.f6.toNat * b.f9.toNat) + 19 * (a.f7.toNat * b.f8.toNat) +
      19 * (a.f8.toNat * b.f7.toNat) + 19 * (a.f9.toNat * b.f6.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb6 : a.f0.toNat * b.f6.toNat + a.f2.toNat * b.f4.toNat + a.f4.toNat * b.f2.toNat +
      a.f6.toNat * b.f0.toNat + 2 * (a.f1.toNat * b.f5.toNat) + 2 * (a.f3.toNat * b.f3.toNat) +
      2 * (a.f5.toNat * b.f1.toNat) + 19 * (a.f8.toNat * b.f8.toNat) +
      38 * (a.f7.toNat * b.f9.toNat) + 38 * (a.f9.toNat * b.f7.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb7 : a.f0.toNat * b.f7.toNat + a.f1.toNat * b.f6.toNat + a.f2.toNat * b.f5.toNat +
      a.f3.toNat * b.f4.toNat + a.f4.toNat * b.f3.toNat + a.f5.toNat * b.f2.toNat +
      a.f6.toNat * b.f1.toNat + a.f7.toNat * b.f0.toNat + 19 * (a.f8.toNat * b.f9.toNat) +
      19 * (a.f9.toNat * b.f8.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb8 : a.f0.toNat * b.f8.toNat + a.f2.toNat * b.f6.toNat + a.f4.toNat * b.f4.toNat +
      a.f6.toNat * b.f2.toNat + a.f8.toNat * b.f0.toNat + 2 * (a.f1.toNat * b.f7.toNat) +
      2 * (a.f3.toNat * b.f5.toNat) + 2 * (a.f5.toNat * b.f3.toNat) +
      2 * (a.f7.toNat * b.f1.toNat) + 38 * (a.f9.toNat * b.f9.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb9 : a.f0.toNat * b.f9.toNat + a.f1.toNat * b.f8.toNat + a.f2.toNat * b.f7.toNat +
      a.f3.toNat * b.f6.toNat + a.f4.toNat * b.f5.toNat + a.f5.toNat * b.f4.toNat +
      a.f6.toNat * b.f3.toNat + a.f7.toNat * b.f2.toNat + a.f8.toNat * b.f1.toNat +
      a.f9.toNat * b.f0.toNat ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) + (2 ^ 27 - 1) * (2 ^ 27 - 1) +
      (2 ^ 27 - 1) * (2 ^ 27 - 1) := by
    gcongr <;> omega
  have e0 : (mulRaw a b).f0.toNat = a.f0.toNat * b.f0.toNat + 19 * (a.f2.toNat * b.f8.toNat) +
      19 * (a.f4.toNat * b.f6.toNat) + 19 * (a.f6.toNat * b.f4.toNat) +
      19 * (a.f8.toNat * b.f2.toNat) + 38 * (a.f1.toNat * b.f9.toNat) +
      38 * (a.f3.toNat * b.f7.toNat) + 38 * (a.f5.toNat * b.f5.toNat) +
      38 * (a.f7.toNat * b.f3.toNat) + 38 * (a.f9.toNat * b.f1.toNat) := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb0 (by norm_num)
  have e1 : (mulRaw a b).f1.toNat = a.f0.toNat * b.f1.toNat + a.f1.toNat * b.f0.toNat +
      19 * (a.f2.toNat * b.f9.toNat) + 19 * (a.f3.toNat * b.f8.toNat) +
      19 * (a.f4.toNat * b.f7.toNat) + 19 * (a.f5.toNat * b.f6.toNat) +
      19 * (a.f6.toNat * b.f5.toNat) + 19 * (a.f7.toNat * b.f4.toNat) +
      19 * (a.f8.toNat * b.f3.toNat) + 19 * (a.f9.toNat * b.f2.toNat) := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb1 (by norm_num)
  have e2 : (mulRaw a b).f2.toNat = a.f0.toNat * b.f2.toNat + a.f2.toNat * b.f0.toNat +
      2 * (a.f1.toNat * b.f1.toNat) + 19 * (a.f4.toNat * b.f8.toNat) +
      19 * (a.f6.toNat * b.f6.toNat) + 19 * (a.f8.toNat * b.f4.toNat) +
      38 * (a.f3.toNat * b.f9.toNat) + 38 * (a.f5.toNat * b.f7.toNat) +
      38 * (a.f7.toNat * b.f5.toNat) + 38 * (a.f9.toNat * b.f3.toNat) := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb2 (by norm_num)
  have e3 : (mulRaw a b).f3.toNat = a.f0.toNat * b.f3.toNat + a.f1.toNat * b.f2.toNat +
      a.f2.toNat * b.f1.toNat + a.f3.toNat * b.f0.toNat + 19 * (a.f4.toNat * b.f9.toNat) +
      19 * (a.f5.toNat * b.f8.toNat) + 19 * (a.f6.toNat * b.f7.toNat) +
      19 * (a.f7.toNat * b.f6.toNat) + 19 * (a.f8.toNat * b.f5.toNat) +
      19 * (a.f9.toNat * b.f4.toNat) := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb3 (by norm_num)
  have e4 : (mulRaw a b).f4.toNat = a.f0.toNat * b.f4.toNat + a.f2.toNat * b.f2.toNat +
      a.f4.toNat * b.f0.toNat + 2 * (a.f1.toNat * b.f3.toNat) + 2 * (a.f3.toNat * b.f1.toNat) +
      19 * (a.f6.toNat * b.f8.toNat) + 19 * (a.f8.toNat * b.f6.toNat) +
      38 * (a.f5.toNat * b.f9.toNat) + 38 * (a.f7.toNat * b.f7.toNat) +
      38 * (a.f9.toNat * b.f5.toNat) := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb4 (by norm_num)
  have e5 : (mulRaw a b).f5.toNat = a.f0.toNat * b.f5.toNat + a.f1.toNat * b.f4.toNat +
      a.f2.toNat * b.f3.toNat + a.f3.toNat * b.f2.toNat + a.f4.toNat * b.f1.toNat +
      a.f5.toNat * b.f0.toNat + 19 * (a.f6.toNat * b.f9.toNat) + 19 * (a.f7.toNat * b.f8.toNat) +
      19 * (a.f8.toNat * b.f7.toNat) + 19 * (a.f9.toNat * b.f6.toNat) := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb5 (by norm_num)
  have e6 : (mulRaw a b).f6.toNat = a.f0.toNat * b.f6.toNat + a.f2.toNat * b.f4.toNat +
      a.f4.toNat * b.f2.toNat + a.f6.toNat * b.f0.toNat + 2 * (a.f1.toNat * b.f5.toNat) +
      2 * (a.f3.toNat * b.f3.toNat) + 2 * (a.f5.toNat * b.f1.toNat) +
      19 * (a.f8.toNat * b.f8.toNat) + 38 * (a.f7.toNat * b.f9.toNat) +
      38 * (a.f9.toNat * b.f7.toNat) := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb6 (by norm_num)
  have e7 : (mulRaw a b).f7.toNat = a.f0.toNat * b.f7.toNat + a.f1.toNat * b.f6.toNat +
      a.f2.toNat * b.f5.toNat + a.f3.toNat * b.f4.toNat + a.f4.toNat * b.f3.toNat +
      a.f5.toNat * b.f2.toNat + a.f6.toNat * b.f1.toNat + a.f7.toNat * b.f0.toNat +
      19 * (a.f8.toNat * b.f9.toNat) + 19 * (a.f9.toNat * b.f8.toNat) := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb7 (by norm_num)
  have e8 : (mulRaw a b).f8.toNat = a.f0.toNat * b.f8.toNat + a.f2.toNat * b.f6.toNat +
      a.f4.toNat * b.f4.toNat + a.f6.toNat * b.f2.toNat + a.f8.toNat * b.f0.toNat +
      2 * (a.f1.toNat * b.f7.toNat) + 2 * (a.f3.toNat * b.f5.toNat) +
      2 * (a.f5.toNat * b.f3.toNat) + 2 * (a.f7.toNat * b.f1.toNat) +
      38 * (a.f9.toNat * b.f9.toNat) := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb8 (by norm_num)
  have e9 : (mulRaw a b).f9.toNat = a.f0.toNat * b.f9.toNat + a.f1.toNat * b.f8.toNat +
      a.f2.toNat * b.f7.toNat + a.f3.toNat * b.f6.toNat + a.f4.toNat * b.f5.toNat +
      a.f5.toNat * b.f4.toNat + a.f6.toNat * b.f3.toNat + a.f7.toNat * b.f2.toNat +
      a.f8.toNat * b.f1.toNat + a.f9.toNat * b.f0.toNat := by
    simp only [mulRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod]
    norm_num
    exact lt_of_le_of_lt hb9 (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
    exact ⟨lt_of_le_of_lt hb0 (by norm_num), lt_of_le_of_lt hb1 (by norm_num),
      lt_of_le_of_lt hb2 (by norm_num), lt_of_le_of_lt hb3 (by norm_num),
      lt_of_le_of_lt hb4 (by norm_num), lt_of_le_of_lt hb5 (by norm_num),
      lt_of_le_of_lt hb6 (by norm_num), lt_of_le_of_lt hb7 (by norm_num),
      lt_of_le_of_lt hb8 (by norm_num), lt_of_le_of_lt hb9 (by norm_num)⟩
  · have h := natCast_two_pow_255
    simp only [Fe.toZ, Fe.val]
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
    push_cast at h ⊢
    linear_combination -(2 ^ 1 * ((a.f1.toNat : ZMod p) * b.f9.toNat) +
      (a.f2.toNat : ZMod p) * b.f8.toNat + 2 ^ 26 * ((a.f2.toNat : ZMod p) * b.f9.toNat) +
      2 ^ 1 * ((a.f3.toNat : ZMod p) * b.f7.toNat) + 2 ^ 26 * ((a.f3.toNat : ZMod p) * b.f8.toNat) +
      2 ^ 52 * ((a.f3.toNat : ZMod p) * b.f9.toNat) + (a.f4.toNat : ZMod p) * b.f6.toNat +
      2 ^ 26 * ((a.f4.toNat : ZMod p) * b.f7.toNat) +
      2 ^ 51 * ((a.f4.toNat : ZMod p) * b.f8.toNat) +
      2 ^ 77 * ((a.f4.toNat : ZMod p) * b.f9.toNat) + 2 ^ 1 * ((a.f5.toNat : ZMod p) * b.f5.toNat) +
      2 ^ 26 * ((a.f5.toNat : ZMod p) * b.f6.toNat) +
      2 ^ 52 * ((a.f5.toNat : ZMod p) * b.f7.toNat) +
      2 ^ 77 * ((a.f5.toNat : ZMod p) * b.f8.toNat) +
      2 ^ 103 * ((a.f5.toNat : ZMod p) * b.f9.toNat) + (a.f6.toNat : ZMod p) * b.f4.toNat +
      2 ^ 26 * ((a.f6.toNat : ZMod p) * b.f5.toNat) +
      2 ^ 51 * ((a.f6.toNat : ZMod p) * b.f6.toNat) +
      2 ^ 77 * ((a.f6.toNat : ZMod p) * b.f7.toNat) +
      2 ^ 102 * ((a.f6.toNat : ZMod p) * b.f8.toNat) +
      2 ^ 128 * ((a.f6.toNat : ZMod p) * b.f9.toNat) +
      2 ^ 1 * ((a.f7.toNat : ZMod p) * b.f3.toNat) + 2 ^ 26 * ((a.f7.toNat : ZMod p) * b.f4.toNat) +
      2 ^ 52 * ((a.f7.toNat : ZMod p) * b.f5.toNat) +
      2 ^ 77 * ((a.f7.toNat : ZMod p) * b.f6.toNat) +
      2 ^ 103 * ((a.f7.toNat : ZMod p) * b.f7.toNat) +
      2 ^ 128 * ((a.f7.toNat : ZMod p) * b.f8.toNat) +
      2 ^ 154 * ((a.f7.toNat : ZMod p) * b.f9.toNat) + (a.f8.toNat : ZMod p) * b.f2.toNat +
      2 ^ 26 * ((a.f8.toNat : ZMod p) * b.f3.toNat) +
      2 ^ 51 * ((a.f8.toNat : ZMod p) * b.f4.toNat) +
      2 ^ 77 * ((a.f8.toNat : ZMod p) * b.f5.toNat) +
      2 ^ 102 * ((a.f8.toNat : ZMod p) * b.f6.toNat) +
      2 ^ 128 * ((a.f8.toNat : ZMod p) * b.f7.toNat) +
      2 ^ 153 * ((a.f8.toNat : ZMod p) * b.f8.toNat) +
      2 ^ 179 * ((a.f8.toNat : ZMod p) * b.f9.toNat) +
      2 ^ 1 * ((a.f9.toNat : ZMod p) * b.f1.toNat) + 2 ^ 26 * ((a.f9.toNat : ZMod p) * b.f2.toNat) +
      2 ^ 52 * ((a.f9.toNat : ZMod p) * b.f3.toNat) +
      2 ^ 77 * ((a.f9.toNat : ZMod p) * b.f4.toNat) +
      2 ^ 103 * ((a.f9.toNat : ZMod p) * b.f5.toNat) +
      2 ^ 128 * ((a.f9.toNat : ZMod p) * b.f6.toNat) +
      2 ^ 154 * ((a.f9.toNat : ZMod p) * b.f7.toNat) +
      2 ^ 179 * ((a.f9.toNat : ZMod p) * b.f8.toNat) +
      2 ^ 205 * ((a.f9.toNat : ZMod p) * b.f9.toNat)) * h

theorem sqRaw_spec (a : Fe) (ha : a.Bnd fun _ => 2 ^ 27) :
    (sqRaw a).Bnd (fun _ => 2 ^ 63) ∧ (sqRaw a).toZ = a.toZ * a.toZ := by
  rw [Fe.bnd_iff] at ha
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha
  have hb0 : a.f0.toNat * a.f0.toNat + 38 * (a.f2.toNat * a.f8.toNat) +
      38 * (a.f4.toNat * a.f6.toNat) + 38 * (a.f5.toNat * a.f5.toNat) +
      76 * (a.f1.toNat * a.f9.toNat) + 76 * (a.f3.toNat * a.f7.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      76 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 76 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb1 : 2 * (a.f0.toNat * a.f1.toNat) + 38 * (a.f2.toNat * a.f9.toNat) +
      38 * (a.f3.toNat * a.f8.toNat) + 38 * (a.f4.toNat * a.f7.toNat) +
      38 * (a.f5.toNat * a.f6.toNat) ≤
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb2 : 2 * (a.f0.toNat * a.f2.toNat) + 2 * (a.f1.toNat * a.f1.toNat) +
      19 * (a.f6.toNat * a.f6.toNat) + 38 * (a.f4.toNat * a.f8.toNat) +
      76 * (a.f3.toNat * a.f9.toNat) + 76 * (a.f5.toNat * a.f7.toNat) ≤
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      76 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 76 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb3 : 2 * (a.f0.toNat * a.f3.toNat) + 2 * (a.f1.toNat * a.f2.toNat) +
      38 * (a.f4.toNat * a.f9.toNat) + 38 * (a.f5.toNat * a.f8.toNat) +
      38 * (a.f6.toNat * a.f7.toNat) ≤
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb4 : a.f2.toNat * a.f2.toNat + 2 * (a.f0.toNat * a.f4.toNat) +
      4 * (a.f1.toNat * a.f3.toNat) + 38 * (a.f6.toNat * a.f8.toNat) +
      38 * (a.f7.toNat * a.f7.toNat) + 76 * (a.f5.toNat * a.f9.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      4 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 76 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb5 : 2 * (a.f0.toNat * a.f5.toNat) + 2 * (a.f1.toNat * a.f4.toNat) +
      2 * (a.f2.toNat * a.f3.toNat) + 38 * (a.f6.toNat * a.f9.toNat) +
      38 * (a.f7.toNat * a.f8.toNat) ≤
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb6 : 2 * (a.f0.toNat * a.f6.toNat) + 2 * (a.f2.toNat * a.f4.toNat) +
      2 * (a.f3.toNat * a.f3.toNat) + 4 * (a.f1.toNat * a.f5.toNat) +
      19 * (a.f8.toNat * a.f8.toNat) + 76 * (a.f7.toNat * a.f9.toNat) ≤
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 4 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      19 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 76 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb7 : 2 * (a.f0.toNat * a.f7.toNat) + 2 * (a.f1.toNat * a.f6.toNat) +
      2 * (a.f2.toNat * a.f5.toNat) + 2 * (a.f3.toNat * a.f4.toNat) +
      38 * (a.f8.toNat * a.f9.toNat) ≤
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb8 : a.f4.toNat * a.f4.toNat + 2 * (a.f0.toNat * a.f8.toNat) +
      2 * (a.f2.toNat * a.f6.toNat) + 4 * (a.f1.toNat * a.f7.toNat) +
      4 * (a.f3.toNat * a.f5.toNat) + 38 * (a.f9.toNat * a.f9.toNat) ≤
      (2 ^ 27 - 1) * (2 ^ 27 - 1) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 4 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      4 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 38 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have hb9 : 2 * (a.f0.toNat * a.f9.toNat) + 2 * (a.f1.toNat * a.f8.toNat) +
      2 * (a.f2.toNat * a.f7.toNat) + 2 * (a.f3.toNat * a.f6.toNat) +
      2 * (a.f4.toNat * a.f5.toNat) ≤
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) + 2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) +
      2 * ((2 ^ 27 - 1) * (2 ^ 27 - 1)) := by
    gcongr <;> omega
  have e0 : (sqRaw a).f0.toNat = a.f0.toNat * a.f0.toNat + 38 * (a.f2.toNat * a.f8.toNat) +
      38 * (a.f4.toNat * a.f6.toNat) + 38 * (a.f5.toNat * a.f5.toNat) +
      76 * (a.f1.toNat * a.f9.toNat) + 76 * (a.f3.toNat * a.f7.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb0 (by norm_num)
  have e1 : (sqRaw a).f1.toNat = 2 * (a.f0.toNat * a.f1.toNat) + 38 * (a.f2.toNat * a.f9.toNat) +
      38 * (a.f3.toNat * a.f8.toNat) + 38 * (a.f4.toNat * a.f7.toNat) +
      38 * (a.f5.toNat * a.f6.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb1 (by norm_num)
  have e2 : (sqRaw a).f2.toNat = 2 * (a.f0.toNat * a.f2.toNat) + 2 * (a.f1.toNat * a.f1.toNat) +
      19 * (a.f6.toNat * a.f6.toNat) + 38 * (a.f4.toNat * a.f8.toNat) +
      76 * (a.f3.toNat * a.f9.toNat) + 76 * (a.f5.toNat * a.f7.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb2 (by norm_num)
  have e3 : (sqRaw a).f3.toNat = 2 * (a.f0.toNat * a.f3.toNat) + 2 * (a.f1.toNat * a.f2.toNat) +
      38 * (a.f4.toNat * a.f9.toNat) + 38 * (a.f5.toNat * a.f8.toNat) +
      38 * (a.f6.toNat * a.f7.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb3 (by norm_num)
  have e4 : (sqRaw a).f4.toNat = a.f2.toNat * a.f2.toNat + 2 * (a.f0.toNat * a.f4.toNat) +
      4 * (a.f1.toNat * a.f3.toNat) + 38 * (a.f6.toNat * a.f8.toNat) +
      38 * (a.f7.toNat * a.f7.toNat) + 76 * (a.f5.toNat * a.f9.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb4 (by norm_num)
  have e5 : (sqRaw a).f5.toNat = 2 * (a.f0.toNat * a.f5.toNat) + 2 * (a.f1.toNat * a.f4.toNat) +
      2 * (a.f2.toNat * a.f3.toNat) + 38 * (a.f6.toNat * a.f9.toNat) +
      38 * (a.f7.toNat * a.f8.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb5 (by norm_num)
  have e6 : (sqRaw a).f6.toNat = 2 * (a.f0.toNat * a.f6.toNat) + 2 * (a.f2.toNat * a.f4.toNat) +
      2 * (a.f3.toNat * a.f3.toNat) + 4 * (a.f1.toNat * a.f5.toNat) +
      19 * (a.f8.toNat * a.f8.toNat) + 76 * (a.f7.toNat * a.f9.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb6 (by norm_num)
  have e7 : (sqRaw a).f7.toNat = 2 * (a.f0.toNat * a.f7.toNat) + 2 * (a.f1.toNat * a.f6.toNat) +
      2 * (a.f2.toNat * a.f5.toNat) + 2 * (a.f3.toNat * a.f4.toNat) +
      38 * (a.f8.toNat * a.f9.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb7 (by norm_num)
  have e8 : (sqRaw a).f8.toNat = a.f4.toNat * a.f4.toNat + 2 * (a.f0.toNat * a.f8.toNat) +
      2 * (a.f2.toNat * a.f6.toNat) + 4 * (a.f1.toNat * a.f7.toNat) +
      4 * (a.f3.toNat * a.f5.toNat) + 38 * (a.f9.toNat * a.f9.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb8 (by norm_num)
  have e9 : (sqRaw a).f9.toNat = 2 * (a.f0.toNat * a.f9.toNat) + 2 * (a.f1.toNat * a.f8.toNat) +
      2 * (a.f2.toNat * a.f7.toNat) + 2 * (a.f3.toNat * a.f6.toNat) +
      2 * (a.f4.toNat * a.f5.toNat) := by
    simp only [sqRaw, UInt64.toNat_add, UInt64.toNat_mul, Nat.add_mod_mod,
      Nat.mod_add_mod, Nat.mul_mod_mod]
    norm_num
    exact lt_of_le_of_lt hb9 (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [Fe.bnd_iff, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
    exact ⟨lt_of_le_of_lt hb0 (by norm_num), lt_of_le_of_lt hb1 (by norm_num),
      lt_of_le_of_lt hb2 (by norm_num), lt_of_le_of_lt hb3 (by norm_num),
      lt_of_le_of_lt hb4 (by norm_num), lt_of_le_of_lt hb5 (by norm_num),
      lt_of_le_of_lt hb6 (by norm_num), lt_of_le_of_lt hb7 (by norm_num),
      lt_of_le_of_lt hb8 (by norm_num), lt_of_le_of_lt hb9 (by norm_num)⟩
  · have h := natCast_two_pow_255
    simp only [Fe.toZ, Fe.val]
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
    push_cast at h ⊢
    linear_combination -(2 ^ 1 * ((a.f1.toNat : ZMod p) * a.f9.toNat) +
      (a.f2.toNat : ZMod p) * a.f8.toNat + 2 ^ 26 * ((a.f2.toNat : ZMod p) * a.f9.toNat) +
      2 ^ 1 * ((a.f3.toNat : ZMod p) * a.f7.toNat) + 2 ^ 26 * ((a.f3.toNat : ZMod p) * a.f8.toNat) +
      2 ^ 52 * ((a.f3.toNat : ZMod p) * a.f9.toNat) + (a.f4.toNat : ZMod p) * a.f6.toNat +
      2 ^ 26 * ((a.f4.toNat : ZMod p) * a.f7.toNat) +
      2 ^ 51 * ((a.f4.toNat : ZMod p) * a.f8.toNat) +
      2 ^ 77 * ((a.f4.toNat : ZMod p) * a.f9.toNat) + 2 ^ 1 * ((a.f5.toNat : ZMod p) * a.f5.toNat) +
      2 ^ 26 * ((a.f5.toNat : ZMod p) * a.f6.toNat) +
      2 ^ 52 * ((a.f5.toNat : ZMod p) * a.f7.toNat) +
      2 ^ 77 * ((a.f5.toNat : ZMod p) * a.f8.toNat) +
      2 ^ 103 * ((a.f5.toNat : ZMod p) * a.f9.toNat) + (a.f6.toNat : ZMod p) * a.f4.toNat +
      2 ^ 26 * ((a.f6.toNat : ZMod p) * a.f5.toNat) +
      2 ^ 51 * ((a.f6.toNat : ZMod p) * a.f6.toNat) +
      2 ^ 77 * ((a.f6.toNat : ZMod p) * a.f7.toNat) +
      2 ^ 102 * ((a.f6.toNat : ZMod p) * a.f8.toNat) +
      2 ^ 128 * ((a.f6.toNat : ZMod p) * a.f9.toNat) +
      2 ^ 1 * ((a.f7.toNat : ZMod p) * a.f3.toNat) + 2 ^ 26 * ((a.f7.toNat : ZMod p) * a.f4.toNat) +
      2 ^ 52 * ((a.f7.toNat : ZMod p) * a.f5.toNat) +
      2 ^ 77 * ((a.f7.toNat : ZMod p) * a.f6.toNat) +
      2 ^ 103 * ((a.f7.toNat : ZMod p) * a.f7.toNat) +
      2 ^ 128 * ((a.f7.toNat : ZMod p) * a.f8.toNat) +
      2 ^ 154 * ((a.f7.toNat : ZMod p) * a.f9.toNat) + (a.f8.toNat : ZMod p) * a.f2.toNat +
      2 ^ 26 * ((a.f8.toNat : ZMod p) * a.f3.toNat) +
      2 ^ 51 * ((a.f8.toNat : ZMod p) * a.f4.toNat) +
      2 ^ 77 * ((a.f8.toNat : ZMod p) * a.f5.toNat) +
      2 ^ 102 * ((a.f8.toNat : ZMod p) * a.f6.toNat) +
      2 ^ 128 * ((a.f8.toNat : ZMod p) * a.f7.toNat) +
      2 ^ 153 * ((a.f8.toNat : ZMod p) * a.f8.toNat) +
      2 ^ 179 * ((a.f8.toNat : ZMod p) * a.f9.toNat) +
      2 ^ 1 * ((a.f9.toNat : ZMod p) * a.f1.toNat) + 2 ^ 26 * ((a.f9.toNat : ZMod p) * a.f2.toNat) +
      2 ^ 52 * ((a.f9.toNat : ZMod p) * a.f3.toNat) +
      2 ^ 77 * ((a.f9.toNat : ZMod p) * a.f4.toNat) +
      2 ^ 103 * ((a.f9.toNat : ZMod p) * a.f5.toNat) +
      2 ^ 128 * ((a.f9.toNat : ZMod p) * a.f6.toNat) +
      2 ^ 154 * ((a.f9.toNat : ZMod p) * a.f7.toNat) +
      2 ^ 179 * ((a.f9.toNat : ZMod p) * a.f8.toNat) +
      2 ^ 205 * ((a.f9.toNat : ZMod p) * a.f9.toNat)) * h

/-! ### Operations on represented field elements -/

/-- `a` has limbs below `2 ^ n` and stands for `x`. -/
def Fe.R (n : ℕ) (a : Fe) (x : ZMod p) : Prop :=
  a.Bnd (fun _ => 2 ^ n) ∧ a.toZ = x

theorem Fe.R.le {a : Fe} {x : ZMod p} (h : a.R 26 x) : a.R 27 x :=
  ⟨h.1.mono fun _ => by norm_num, h.2⟩

theorem Fe.R.of_eq {a : Fe} {n : ℕ} {x y : ZMod p} (h : a.R n x) (hxy : x = y) : a.R n y :=
  ⟨h.1, h.2.trans hxy⟩

theorem Fe.R.carry {a : Fe} {x : ZMod p} (ha : a.Bnd fun _ => 2 ^ 63) (hx : a.toZ = x) :
    (carry a).R 26 x :=
  ⟨(carry_spec a ha).1, (carry_spec a ha).2.trans hx⟩

theorem Fe.R.mul {a b : Fe} {x y : ZMod p} (ha : a.R 27 x) (hb : b.R 27 y) :
    (mul a b).R 26 (x * y) := by
  obtain ⟨h1, h2⟩ := mulRaw_spec a b ha.1 hb.1
  exact Fe.R.carry h1 (by rw [h2, ha.2, hb.2])

theorem Fe.R.sq {a : Fe} {x : ZMod p} (ha : a.R 27 x) : (sq a).R 26 (x ^ 2) := by
  obtain ⟨h1, h2⟩ := sqRaw_spec a ha.1
  exact Fe.R.carry h1 (by rw [h2, ha.2, pow_two])

theorem Fe.R.add {a b : Fe} {x y : ZMod p} (ha : a.R 26 x) (hb : b.R 26 y) :
    (add a b).R 27 (x + y) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  rw [Fe.bnd_iff] at ha1 hb1
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha1
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hb1
  simp only [Fe.R, Fe.bnd_iff, ← ha2, ← hb2, Fe.toZ, Fe.val, Fast.add, UInt64.toNat_add]
  refine ⟨by omega, ?_⟩
  rw [← Nat.cast_add]
  exact congrArg Nat.cast (by omega)

theorem Fe.R.sub {a b : Fe} {x y : ZMod p} (ha : a.R 27 x) (hb : b.R 26 y) :
    (sub a b).R 26 (x - y) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  rw [Fe.bnd_iff] at ha1 hb1
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha1
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hb1
  refine Fe.R.carry ?_ ?_
  · simp only [Fe.bnd_iff, Fast.subRaw, UInt64.toNat_sub, UInt64.toNat_add]
    norm_num
    omega
  · have h : (subRaw a b).val + b.val = a.val + 4 * p := by
      simp only [Fe.val, Fast.subRaw, UInt64.toNat_sub, UInt64.toNat_add]
      rw [p_eq_numeral]
      norm_num
      omega
    have h' := congrArg (Nat.cast : ℕ → ZMod p) h
    push_cast [ZMod.natCast_self] at h'
    simp only [Fe.toZ, ← ha2, ← hb2]
    linear_combination h'

theorem Fe.R.mul121665 {a : Fe} {x : ZMod p} (ha : a.R 26 x) :
    (mul121665 a).R 26 (121665 * x) := by
  obtain ⟨ha1, ha2⟩ := ha
  rw [Fe.bnd_iff] at ha1
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha1
  have e : ∀ c : UInt64, c.toNat < 2 ^ 26 → (c * 121665).toNat = c.toNat * 121665 := by
    intro c hc
    simp only [UInt64.toNat_mul, UInt64.reduceToNat]
    omega
  refine Fe.R.carry ?_ ?_
  · simp only [Fe.bnd_iff, e _ a0, e _ a1, e _ a2, e _ a3, e _ a4, e _ a5,
      e _ a6, e _ a7, e _ a8, e _ a9]
    omega
  · simp only [Fe.toZ, Fe.val, ← ha2, e _ a0, e _ a1, e _ a2, e _ a3, e _ a4,
      e _ a5, e _ a6, e _ a7, e _ a8, e _ a9]
    push_cast
    ring

theorem Fe.R.sqn {a : Fe} {x : ZMod p} (ha : a.R 26 x) (n : ℕ) :
    (sqn a n).R 26 (x ^ 2 ^ n) := by
  induction n generalizing a x with
  | zero => simpa [Fast.sqn] using ha
  | succ n ih =>
    rw [Fast.sqn]
    exact (ih ha.le.sq).of_eq (by ring)

theorem invert_spec {z : Fe} {x : ZMod p} (hz : z.R 26 x) :
    (invert z).R 26 (x ^ (p - 2)) := by
  have g2 := hz.le.sq
  have g9 := (g2.sqn 2).le.mul hz.le
  have g11 := g9.le.mul g2.le
  have g5 := g11.le.sq.le.mul g9.le
  have g10 := (g5.sqn 5).le.mul g5.le
  have g20 := (g10.sqn 10).le.mul g10.le
  have g40 := (g20.sqn 20).le.mul g20.le
  have g50 := (g40.sqn 10).le.mul g10.le
  have g100 := (g50.sqn 50).le.mul g50.le
  have g200 := (g100.sqn 100).le.mul g100.le
  have g250 := (g200.sqn 50).le.mul g50.le
  have g := (g250.sqn 5).le.mul g11.le
  rw [show p - 2 = 2 ^ 255 - 21 by rw [p_eq_numeral]; norm_num]
  exact g.of_eq (by ring)

theorem ofNat_spec (x : ℕ) : (ofNat x).R 26 (x % 2 ^ 255 : ℕ) := by
  refine ⟨?_, ?_⟩
  · simp only [Fe.bnd_iff, ofNat, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  · simp only [Fe.toZ, Fe.val, ofNat, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact congrArg Nat.cast (by omega)

/-! ### The ladder -/

/-- The ladder state `s` stands for `(R₀, R₁)`, with limbs below `2^26`. -/
def St.R (s : St) (R₀ R₁ : XZ (ZMod p)) : Prop :=
  s.x2.R 26 R₀.U ∧ s.z2.R 26 R₀.W ∧ s.x3.R 26 R₁.U ∧ s.z3.R 26 R₁.W

/-- The ladder step is RFC 7748's `xDBL` and `xADD` (`XZ.dbl`, `XZ.add`). -/
theorem step_spec {x1 x2 z2 x3 z3 : Fe} {u : ZMod p} {P Q : XZ (ZMod p)} (h1 : x1.R 26 u)
    (h2 : x2.R 26 P.U) (h3 : z2.R 26 P.W) (h4 : x3.R 26 Q.U) (h5 : z3.R 26 Q.W) :
    (step x1 x2 z2 x3 z3).R (XZ.dbl 121665 P) (XZ.add P Q u) := by
  have hA := h2.add h3
  have hB := h2.le.sub h3
  have hAA := hA.sq
  have hBB := hB.le.sq
  have hE := hAA.le.sub hBB
  have hC := h4.add h5
  have hD := h4.le.sub h5
  have hDA := hD.le.mul hA
  have hCB := hC.mul hB.le
  simp only [St.R, step, XZ.dbl, XZ.add]
  exact ⟨hAA.le.mul hBB.le, hE.le.mul (hAA.add hE.mul121665), (hDA.add hCB).sq,
    h1.le.mul (hDA.le.sub hCB).le.sq.le⟩

/-- Bit `j < 64` of a word. -/
theorem testBit_word (n j : ℕ) (hj : j < 64) :
    (((n % 2 ^ 64).toUInt64 >>> j.toUInt64) % 2 == 1) = n.testBit j := by
  have h : (((n % 2 ^ 64).toUInt64 >>> j.toUInt64) % 2).toNat = n / 2 ^ j % 2 := by
    simp only [UInt64.toNat_mod, UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, UInt64.reduceToNat]
    rw [show j % 2 ^ 64 % 64 = j by omega, Nat.mod_mod,
      show (2 : ℕ) ^ 64 = 2 ^ j * 2 ^ (64 - j) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]
  rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, h,
    decide_eq_true_iff, UInt64.toNat_one]

theorem bit_eq (k t : ℕ) (ht : t < 256) :
    bit (k % 2 ^ 64).toUInt64 (k / 2 ^ 64 % 2 ^ 64).toUInt64 (k / 2 ^ 128 % 2 ^ 64).toUInt64
      (k / 2 ^ 192 % 2 ^ 64).toUInt64 t = k.testBit t := by
  unfold bit
  split_ifs with h0 h1 h2
  · rw [testBit_word _ _ (by omega), Nat.mod_eq_of_lt (a := t) (by omega)]
  all_goals
    rw [testBit_word _ _ (by omega), Nat.testBit_div_two_pow]
    congr 1
    omega

/-- The loop is `XZ.ladderLoop`. -/
theorem loop_spec {x1 : Fe} {u : ZMod p} (h1 : x1.R 26 u) (k : ℕ) (w0 w1 w2 w3 : UInt64)
    (hbit : ∀ t < 255, bit w0 w1 w2 w3 t = k.testBit t) (t : ℕ) (ht : t ≤ 255) (s : St)
    (sw : Bool) (R₀ R₁ : XZ (ZMod p)) (hs : s.R R₀ R₁) :
    (loop x1 w0 w1 w2 w3 t s sw).1.R (XZ.ladderLoop 121665 u k t ⟨R₀, R₁, sw⟩).R₀
      (XZ.ladderLoop 121665 u k t ⟨R₀, R₁, sw⟩).R₁ ∧
    (loop x1 w0 w1 w2 w3 t s sw).2 = (XZ.ladderLoop 121665 u k t ⟨R₀, R₁, sw⟩).swap := by
  induction t generalizing s sw R₀ R₁ with
  | zero => exact ⟨hs, rfl⟩
  | succ t ih =>
    obtain ⟨hx2, hz2, hx3, hz3⟩ := hs
    rw [loop, XZ.ladderLoop, XZ.ladderStep, hbit t (by omega)]
    cases hsw : sw ^^ k.testBit t
    · simp only [XZ.cswap, Bool.false_eq_true, ↓reduceIte]
      exact ih (by omega) _ _ _ _ (step_spec h1 hx2 hz2 hx3 hz3)
    · simp only [XZ.cswap, ↓reduceIte]
      exact ih (by omega) _ _ _ _ (step_spec h1 hx3 hz3 hx2 hz2)

/-- **The fast X25519 is `x25519Nat`.** -/
theorem x25519_eq (k u : ℕ) : x25519 k u = x25519Nat k u := by
  have hu : (ofNat u).R 26 (decodeU u) := ofNat_spec u
  have h1 : (ofNat 1).R 26 1 := (ofNat_spec 1).of_eq (by norm_num)
  have h0 : (ofNat 0).R 26 0 := (ofNat_spec 0).of_eq (by norm_num)
  have hbit := fun t (ht : t < 255) => bit_eq (clamp k) t (by omega)
  obtain ⟨hR, hsw⟩ := loop_spec hu (clamp k) _ _ _ _ hbit 255 le_rfl
    ⟨ofNat 1, ofNat 0, ofNat u, ofNat 1⟩ false ⟨1, 0⟩
    ⟨decodeU u, 1⟩ ⟨h1, h0, hu, h1⟩
  simp only [x25519, x25519Nat, MontgomeryModel.ladder, montgomery_a24_eq, XZ.ladder,
    XZ.ladderXZ, toU_eq_mul_pow_sub_two, encodeU]
  generalize loop _ _ _ _ _ _ _ _ = r at hR hsw ⊢
  rw [show Fast.clamp k = curve25519.clamp k from rfl] at hR hsw
  generalize XZ.ladderLoop (121665 : ZMod p) (decodeU u) (curve25519.clamp k) 255 _ = S
    at hR hsw ⊢
  obtain ⟨hx2, hz2, hx3, hz3⟩ := hR
  have key : ∀ {X Z : Fe} {V : XZ (ZMod p)}, X.R 26 V.U → Z.R 26 V.W →
      (mul X (invert Z)).val % (2 ^ 255 - 19) = (V.U * V.W ^ (p - 2)).val := by
    intro X Z V hX hZ
    have h := (hX.le.mul (invert_spec hZ).le).2
    rw [← h, Fe.toZ, ZMod.val_natCast, p_eq_sub]
  cases hs : S.swap <;> simp only [hs, XZ.cswap] at hsw ⊢ <;> simp only [hsw] <;>
    first | exact key hx2 hz2 | exact key hx3 hz3

end curve25519.Fast
