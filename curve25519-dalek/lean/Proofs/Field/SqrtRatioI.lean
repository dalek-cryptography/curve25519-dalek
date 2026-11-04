/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Alessandro D'Angelo
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
public import Proofs.Field.PowP58
import Curve25519.Prime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ReduceModChar
import Proofs.Helpers.ZMod
public import Curve25519.Ristretto.Encoding.Defs
public import Curve25519.Basic
import Proofs.Helpers.Backend.U32.Bytes
import Proofs.Helpers.Backend.U64.Bytes
public section

/-! # `FieldElement::sqrt_ratio_i`

RFC 9496's `SQRT_RATIO_M1`, proved once over a `Backend` in `ZMod p`
(`Backend.sqrtRatioIBody_spec`); the specs of both backends, stated on `asNat` modulo `p`, follow
through `Backend.sqrtRatioI_asNat`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `FieldElement::sqrt_ratio_i` over a backend. -/
@[expose] def sqrtRatioIBody (u v : B.F) : Result (subtle.Choice × B.F) := do
  let fe ← B.square v
  let v3 ← B.mul fe v
  let fe1 ← B.square v3
  let v7 ← B.mul fe1 v
  let fe2 ← B.mul u v3
  let fe3 ← B.mul u v7
  let fe4 ← B.powP58 fe3
  let r ← B.mul fe2 fe4
  let fe5 ← B.square r
  let check ← B.mul v fe5
  let fe6 ← B.constSqrtM1
  let correct_sign_sqrt ← B.ctEq check u
  let fe7 ← B.neg u
  let flipped_sign_sqrt ← B.ctEq check fe7
  let fe8 ← B.mul fe7 fe6
  let flipped_sign_sqrt_i ← B.ctEq check fe8
  let r_prime ← B.mul fe6 r
  let c ←
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor flipped_sign_sqrt flipped_sign_sqrt_i
  let r1 ← B.condAssign r r_prime c
  let r_is_negative ← B.isNegative r1
  let r2 ← B.condNeg r1 r_is_negative
  let was_nonzero_square ←
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor correct_sign_sqrt flipped_sign_sqrt
  ok (was_nonzero_square, r2)

/-- The exponent `(p - 5) / 8` of `pow_p58`, kept irreducible. -/
private def e58 : ℕ := 2 ^ 252 - 3

private theorem e58_def : 2 ^ 252 - 3 = e58 := rfl

private theorem e58_eq : 8 * e58 + 5 = p := by
  unfold e58
  have := p_add_nineteen
  omega

attribute [irreducible] e58

/-! ## Arithmetic in `ZMod p` -/

/-- In a field containing a square root `i` of `-1`, the fourth roots of unity are `±1`, `±i`. -/
private theorem eq_one_or_neg_one_or_of_pow_four_eq_one {K : Type*} [Field K] {t i : K}
    (hi : i ^ 2 = -1) (ht : t ^ 4 = 1) : t = 1 ∨ t = -1 ∨ t = i ∨ t = -i := by
  have h : (t - 1) * (t + 1) * ((t - i) * (t + i)) = 0 := by
    linear_combination ht - (t ^ 2 - 1) * hi
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at h
  tauto

private theorem two_ne_zero_p : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) h'
  have := p_add_nineteen
  omega

private theorem sqrtM1_sq : (curve25519.sqrtM1 : ZMod p) ^ 2 = -1 := by
  have h := ZMod.natCast_eq_zero_iff_mod.mpr sqrtM1_sq_add_one_mod_p
  push_cast at h
  linear_combination h

private theorem one_ne_neg_one_p : (1 : ZMod p) ≠ -1 := by
  intro h
  exact two_ne_zero_p (by linear_combination h)

private theorem sqrtM1_ne_one : (curve25519.sqrtM1 : ZMod p) ≠ 1 := by
  intro h
  have := sqrtM1_sq
  rw [h] at this
  exact one_ne_neg_one_p (by simpa using this)

private theorem sqrtM1_ne_neg_one : (curve25519.sqrtM1 : ZMod p) ≠ -1 := by
  intro h
  have := sqrtM1_sq
  rw [h] at this
  exact one_ne_neg_one_p (by simpa using this)

private theorem sqrtM1_ne_neg_self : (curve25519.sqrtM1 : ZMod p) ≠ -curve25519.sqrtM1 := by
  intro h
  have h0 : (curve25519.sqrtM1 : ZMod p) = 0 := by
    have : 2 * (curve25519.sqrtM1 : ZMod p) = 0 := by linear_combination h
    simpa [two_ne_zero_p] using this
  have := sqrtM1_sq
  rw [h0] at this
  exact one_ne_neg_one_p (by simpa using this.symm)

/-- `v r² = u w^((p-1)/4)` for `r = u v³ w^((p-5)/8)`, `w = u v⁷`. -/
private theorem check_eq (U V : ZMod p) (n : ℕ) :
    V * (U * V ^ 3 * (U * V ^ 7) ^ n) ^ 2 = U * (U * V ^ 7) ^ (2 * n + 1) := by
  ring

/-- `w^((p-1)/4)` is a fourth root of unity. -/
private theorem pow_cases (W : ZMod p) (hW : W ≠ 0) :
    W ^ (2 * e58 + 1) = 1 ∨ W ^ (2 * e58 + 1) = -1 ∨ W ^ (2 * e58 + 1) = curve25519.sqrtM1 ∨
      W ^ (2 * e58 + 1) = -curve25519.sqrtM1 := by
  refine eq_one_or_neg_one_or_of_pow_four_eq_one sqrtM1_sq ?_
  rw [← pow_mul, show (2 * e58 + 1) * 4 = p - 1 by have := e58_eq; omega]
  exact ZMod.pow_card_sub_one_eq_one hW

/-- If `u / v` is a nonzero square, `w^((p-1)/4) = ±1`. -/
private theorem pow_cases_of_sq (X V : ZMod p) (hX : X ≠ 0) (hV : V ≠ 0) :
    (X ^ 2 * V * V ^ 7) ^ (2 * e58 + 1) = 1 ∨ (X ^ 2 * V * V ^ 7) ^ (2 * e58 + 1) = -1 := by
  rw [← mul_self_eq_one_iff, ← pow_add, show X ^ 2 * V * V ^ 7 = (X * V ^ 4) ^ 2 by ring,
    ← pow_mul, show 2 * (2 * e58 + 1 + (2 * e58 + 1)) = p - 1 by have := e58_eq; omega]
  exact ZMod.pow_card_sub_one_eq_one (mul_ne_zero hX (pow_ne_zero _ hV))

/-- Negating an odd canonical value gives an even one (`p` is odd). -/
private theorem neg_val_mod_two {X : ZMod p} (h : X.val % 2 = 1) : (-X).val % 2 = 0 := by
  have hX : X ≠ 0 := by
    rintro rfl
    simp at h
  rw [ZMod.neg_val]
  simp only [hX, ↓reduceIte]
  have hp2 : p % 2 = 1 := by
    have := p_add_nineteen
    omega
  have := ZMod.val_lt X
  omega

/-! ## The `Choice` logic -/

private theorem choice_or {a b : subtle.Choice} {P Q : Prop} (ha1 : P → a = 1#u8)
    (ha0 : ¬P → a = 0#u8) (hb1 : Q → b = 1#u8) (hb0 : ¬Q → b = 0#u8) :
    (P ∨ Q → (a ||| b) = 1#u8) ∧ (¬(P ∨ Q) → (a ||| b) = 0#u8) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp_all [show (1#u8 ||| 1#u8) = 1#u8 by decide]

/-- `sqrtRatioIBody` computes RFC 9496's `SQRT_RATIO_M1`. -/
theorem sqrtRatioIBody_spec (hsq : B.SquareSpec) (hmul : B.MulSpec) (hneg : B.NegSpec)
    (hp58 : B.PowP58Spec) (hm1 : B.SqrtM1Spec) (hct : B.CtEqSpec) (hca : B.CondAssignSpec)
    (hcn : B.CondNegSpec) (hisn : B.IsNegativeSpec) (u v : B.F) (hu : B.SqIn u)
    (hv : B.SqIn v) :
    B.sqrtRatioIBody u v ⦃ (c : subtle.Choice) (r : B.F) =>
      c.IsValid ∧ (B.toField u = 0 → c = 1#u8 ∧ B.toField r = 0) ∧
      (B.toField u ≠ 0 → B.toField v = 0 → c = 0#u8 ∧ B.toField r = 0) ∧
      (B.toField v ≠ 0 → (∃ x : ZMod p, x ^ 2 * B.toField v = B.toField u) →
        c = 1#u8 ∧ B.toField r ^ 2 * B.toField v = B.toField u) ∧
      (B.toField v ≠ 0 → (¬∃ x : ZMod p, x ^ 2 * B.toField v = B.toField u) →
        c = 0#u8 ∧ B.toField r ^ 2 * B.toField v = curve25519.sqrtM1 * B.toField u) ∧
      (B.toField r).val % 2 = 0 ∧ B.Red r ⦄ := by
  unfold sqrtRatioIBody
  step with hsq v hv as ⟨fe, hfe, hfeb⟩
  step with hmul fe v (B.red_mulIn hfeb) (B.sqIn_mulIn hv) as ⟨v3, hv3, hv3b⟩
  step with hsq v3 (B.red_sqIn hv3b) as ⟨fe1, hfe1, hfe1b⟩
  step with hmul fe1 v (B.red_mulIn hfe1b) (B.sqIn_mulIn hv) as ⟨v7, hv7, hv7b⟩
  step with hmul u v3 (B.sqIn_mulIn hu) (B.red_mulIn hv3b) as ⟨fe2, hfe2, hfe2b⟩
  step with hmul u v7 (B.sqIn_mulIn hu) (B.red_mulIn hv7b) as ⟨fe3, hfe3, hfe3b⟩
  step with hp58 fe3 (B.red_sqIn hfe3b) as ⟨fe4, hfe4, hfe4b⟩
  rw [e58_def] at hfe4
  step with hmul fe2 fe4 (B.red_mulIn hfe2b) (B.red_mulIn hfe4b) as ⟨r, hr, hrb⟩
  step with hsq r (B.red_sqIn hrb) as ⟨fe5, hfe5, hfe5b⟩
  step with hmul v fe5 (B.sqIn_mulIn hv) (B.red_mulIn hfe5b) as ⟨check, hcheck, hcheckb⟩
  apply spec_bind hm1
  rintro fe6 ⟨hfe6, hfe6b⟩
  step with hct check u as ⟨cs, hcsv, hcs1, hcs0⟩
  step with hneg u (B.sqIn_mulIn hu) as ⟨fe7, hfe7, hfe7b⟩
  step with hct check fe7 as ⟨fs, hfsv, hfs1, hfs0⟩
  step with hmul fe7 fe6 (B.red_mulIn hfe7b) (B.red_mulIn hfe6b) as ⟨fe8, hfe8, hfe8b⟩
  step with hct check fe8 as ⟨fsi, hfsiv, hfsi1, hfsi0⟩
  step with hmul fe6 r (B.red_mulIn hfe6b) (B.red_mulIn hrb) as ⟨r', hr', hr'b⟩
  step as ⟨c, hcv, hc⟩
  step with hca r r' c hcv as ⟨r1, hr10, hr11⟩
  have hr1b : B.Red r1 := by
    rcases hcv with h | h
    · rw [hr10 h]
      exact hrb
    · rw [hr11 h]
      exact hr'b
  step with hisn r1 as ⟨rn, hrnv, hrn⟩
  step with hcn r1 rn hrnv (B.red_mulIn hr1b) as ⟨r2, hr20, hr21⟩
  step as ⟨out, houtv, hout⟩
  -- the value of `r2`
  have hsq : B.toField r2 ^ 2 = B.toField r1 ^ 2 := by
    rcases hrnv with h | h
    · rw [hr20 h]
    · rw [(hr21 h).1, neg_sq]
  have hpar : (B.toField r2).val % 2 = 0 := by
    rcases hrnv with h | h
    · rw [hr20 h, ← hrn, h]
      rfl
    · rw [(hr21 h).1]
      refine neg_val_mod_two ?_
      rw [← hrn, h]
      rfl
  have hr2b : B.Red r2 := by
    rcases hrnv with h | h
    · rw [hr20 h]
      exact hr1b
    · exact (hr21 h).2
  -- name the values in `ZMod p`
  set U : ZMod p := B.toField u with hU
  set V : ZMod p := B.toField v with hV
  have eR : B.toField r = U * V ^ 3 * (U * V ^ 7) ^ e58 := by
    rw [hr, hfe2, hfe4, hfe3, hv7, hfe1, hv3, hfe]
    ring
  have eF8 : B.toField fe8 = -U * curve25519.sqrtM1 := by rw [hfe8, hfe7, hfe6]
  have eR' : B.toField r' = curve25519.sqrtM1 * B.toField r := by rw [hr', hfe6]
  have eC0 : B.toField check = V * B.toField r ^ 2 := by rw [hcheck, hfe5]
  rw [hfe7] at hfs1 hfs0
  rw [eF8] at hfsi1 hfsi0
  set R : ZMod p := B.toField r with hR
  set T : ZMod p := (U * V ^ 7) ^ (2 * e58 + 1) with hT
  clear_value U V R T
  have eVR : V * R ^ 2 = U * T := by
    rw [eR, hT]
    exact check_eq U V e58
  rw [eC0, eVR] at hcs1 hfs1 hfsi1 hcs0 hfs0 hfsi0
  obtain ⟨hc1, hc0⟩ := choice_or hfs1 hfs0 hfsi1 hfsi0
  rw [← hc] at hc1 hc0
  obtain ⟨ho1, ho0⟩ := choice_or hcs1 hcs0 hfs1 hfs0
  rw [← hout] at ho1 ho0
  have hR1 : U * T = -U ∨ U * T = -U * curve25519.sqrtM1 → V * B.toField r1 ^ 2 = -(U * T) := by
    intro h
    rw [hr11 (hc1 h), eR', mul_pow, sqrtM1_sq, ← eVR]
    ring
  have hR1' : ¬(U * T = -U ∨ U * T = -U * curve25519.sqrtM1) → V * B.toField r1 ^ 2 = U * T := by
    intro h
    rw [hr10 (hc0 h), ← hR, eVR]
  have hr2V : V * B.toField r2 ^ 2 = V * B.toField r1 ^ 2 := by rw [hsq]
  have hzero : R = 0 → B.toField r2 = 0 := by
    intro h0
    rw [← pow_eq_zero_iff two_ne_zero, hsq]
    rcases hcv with h | h
    · rw [hr10 h, ← hR, h0]
      ring
    · rw [hr11 h, eR', h0]
      ring
  have hcase1 : U = 0 → out = 1#u8 ∧ B.toField r2 = 0 := fun hU0 =>
    ⟨ho1 (Or.inl (by rw [hU0, zero_mul])), hzero (by rw [eR, hU0]; ring)⟩
  refine ⟨houtv, hcase1, fun hU0 hV0 => ?_, fun hV0 x hx => ?_, fun hV0 hns => ?_, hpar, hr2b⟩
  · -- `u ≠ 0`, `v = 0`
    have hT0 : T = 0 := by
      rw [hT, hV0]
      simp
    refine ⟨ho0 ?_, hzero (by rw [eR, hV0]; ring)⟩
    rw [hT0, mul_zero]
    rintro (h | h)
    · exact hU0 h.symm
    · exact hU0 (neg_eq_zero.mp h.symm)
  · -- `u / v` is a square
    by_cases hU0 : U = 0
    · obtain ⟨h1, h2⟩ := hcase1 hU0
      refine ⟨h1, ?_⟩
      rw [h2, hU0]
      ring
    have hX0 : x ≠ 0 := by
      intro h
      apply hU0
      rw [← hx, h]
      ring
    have hT' : T = 1 ∨ T = -1 := by
      rw [hT, ← hx]
      exact pow_cases_of_sq _ _ hX0 hV0
    rw [mul_comm, hr2V]
    rcases hT' with h | h
    · refine ⟨ho1 (Or.inl (by rw [h, mul_one])), ?_⟩
      rw [hR1' ?_, h, mul_one]
      rw [h]
      rintro (h' | h')
      · exact one_ne_neg_one_p (mul_left_cancel₀ hU0 (by linear_combination h'))
      · exact sqrtM1_ne_neg_one (mul_left_cancel₀ hU0 (by linear_combination h'))
    · refine ⟨ho1 (Or.inr (by rw [h, mul_neg_one])), ?_⟩
      rw [hR1 (Or.inl (by rw [h, mul_neg_one])), h]
      ring
  · -- `u / v` is not a square
    have hU0 : U ≠ 0 := by
      intro h
      exact hns ⟨0, by rw [h]; ring⟩
    have hW : U * V ^ 7 ≠ 0 := mul_ne_zero hU0 (pow_ne_zero _ hV0)
    rw [mul_comm _ U, mul_comm, hr2V]
    rcases pow_cases _ hW with h | h | h | h <;> rw [← hT] at h
    · exact absurd ⟨R, by rw [mul_comm, eVR, h, mul_one]⟩ hns
    · refine absurd ⟨B.toField r', ?_⟩ hns
      rw [eR']
      linear_combination (R ^ 2 * V) * sqrtM1_sq - eVR - U * h
    · have hn : ¬(U * T = -U ∨ U * T = -U * curve25519.sqrtM1) := by
        rw [h]
        rintro (h' | h')
        · exact sqrtM1_ne_neg_one (mul_left_cancel₀ hU0 (by linear_combination h'))
        · exact sqrtM1_ne_neg_self (mul_left_cancel₀ hU0 (by linear_combination h'))
      refine ⟨ho0 ?_, by rw [hR1' hn, h]⟩
      rw [h]
      rintro (h' | h')
      · exact sqrtM1_ne_one (mul_left_cancel₀ hU0 (by linear_combination h'))
      · exact sqrtM1_ne_neg_one (mul_left_cancel₀ hU0 (by linear_combination h'))
    · have hy : U * T = -U * curve25519.sqrtM1 := by
        rw [h]
        ring
      refine ⟨ho0 ?_, by rw [hR1 (Or.inr hy), h]; ring⟩
      rw [h]
      rintro (h' | h')
      · exact sqrtM1_ne_neg_one (mul_left_cancel₀ hU0 (by linear_combination -h'))
      · exact sqrtM1_ne_one (mul_left_cancel₀ hU0 (by linear_combination -h'))

/-! ## Back to the specs' form on `asNat` -/

variable {B}

private theorem sq_mul_iff (r v : B.F) (n : ℕ) (w : ZMod p) (hw : w = n) :
    B.toField r ^ 2 * B.toField v = w ↔ B.asNat r ^ 2 * B.asNat v % p = n % p := by
  rw [B.toField_eq, B.toField_eq, hw, ← ZMod.natCast_eq_natCast_iff']
  push_cast
  rfl

private theorem exists_sq_iff (u v : B.F) :
    (∃ x : ℕ, x ^ 2 * B.asNat v % p = B.asNat u % p) ↔
      ∃ x : ZMod p, x ^ 2 * B.toField v = B.toField u := by
  rw [B.toField_eq, B.toField_eq]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff'] at hx
    push_cast at hx
    exact hx
  · rintro ⟨X, hX⟩
    refine ⟨X.val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    simpa using hX

/-- The `ZMod p` form of `sqrtRatioIBody_spec` gives the `asNat` form of the backends' specs. -/
theorem sqrtRatioI_asNat {u v r : B.F} {c : subtle.Choice}
    (h : c.IsValid ∧ (B.toField u = 0 → c = 1#u8 ∧ B.toField r = 0) ∧
      (B.toField u ≠ 0 → B.toField v = 0 → c = 0#u8 ∧ B.toField r = 0) ∧
      (B.toField v ≠ 0 → (∃ x : ZMod p, x ^ 2 * B.toField v = B.toField u) →
        c = 1#u8 ∧ B.toField r ^ 2 * B.toField v = B.toField u) ∧
      (B.toField v ≠ 0 → (¬∃ x : ZMod p, x ^ 2 * B.toField v = B.toField u) →
        c = 0#u8 ∧ B.toField r ^ 2 * B.toField v = curve25519.sqrtM1 * B.toField u) ∧
      (B.toField r).val % 2 = 0 ∧ B.Red r) :
    c.IsValid ∧ (B.asNat u % p = 0 → c = 1#u8 ∧ B.asNat r % p = 0) ∧
      (B.asNat u % p ≠ 0 → B.asNat v % p = 0 → c = 0#u8 ∧ B.asNat r % p = 0) ∧
      (B.asNat v % p ≠ 0 → (∃ x : ℕ, x ^ 2 * B.asNat v % p = B.asNat u % p) →
        c = 1#u8 ∧ B.asNat r ^ 2 * B.asNat v % p = B.asNat u % p) ∧
      (B.asNat v % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * B.asNat v % p = B.asNat u % p) →
        c = 0#u8 ∧ B.asNat r ^ 2 * B.asNat v % p = curve25519.sqrtM1 * B.asNat u % p) ∧
      B.asNat r % p % 2 = 0 ∧ B.Red r := by
  obtain ⟨hv, h1, h2, h3, h4, h5, h6⟩ := h
  simp only [ne_eq, ← toField_eq_zero_iff, exists_sq_iff]
  refine ⟨hv, h1, h2, fun hv0 hx => ?_, fun hv0 hx => ?_, by rw [← toField_val]; exact h5, h6⟩
  · obtain ⟨hc, hr⟩ := h3 hv0 hx
    exact ⟨hc, (sq_mul_iff r v _ _ (B.toField_eq u)).mp hr⟩
  · obtain ⟨hc, hr⟩ := h4 hv0 hx
    exact ⟨hc, (sq_mul_iff r v _ _ (by rw [B.toField_eq]; push_cast; rfl)).mp hr⟩


/-! ## Helpers for the callers of `sqrt_ratio_i` -/

/-- **`sqrtRatioI` computes `sqrtRatioM1`**: from the conjuncts of `SqrtRatioISpec`. -/
theorem sqrtRatioM1_eq {U V R : ZMod p} {c : subtle.Choice}
    (h0 : U = 0 → c = 1#u8 ∧ R = 0) (h1 : U ≠ 0 → V = 0 → c = 0#u8 ∧ R = 0)
    (h2 : V ≠ 0 → (∃ x : ZMod p, x ^ 2 * V = U) → c = 1#u8 ∧ R ^ 2 * V = U)
    (h3 : V ≠ 0 → (¬∃ x : ZMod p, x ^ 2 * V = U) →
      c = 0#u8 ∧ R ^ 2 * V = curve25519.sqrtM1 * U)
    (hpar : R.val % 2 = 0) :
    sqrtRatioM1 U V = (decide (c = 1#u8), R) := by
  have hneg : ¬ R.IsNeg := ZMod.not_isNeg_iff.mpr hpar
  by_cases hu : U = 0
  · obtain ⟨rfl, hr⟩ := h0 hu
    rw [hu, hr, sqrtRatioM1_zero_left, decide_eq_true rfl]
  by_cases hv : V = 0
  · obtain ⟨rfl, hr⟩ := h1 hu hv
    rw [hv, hr, sqrtRatioM1_zero_right hu, decide_eq_false (by decide)]
  by_cases hsq : ∃ x : ZMod p, x ^ 2 * V = U
  · obtain ⟨rfl, hr⟩ := h2 hv hsq
    rw [sqrtRatioM1_eq_of_mul_sq_eq hv (by rw [mul_comm]; exact hr) hneg, decide_eq_true rfl]
  · obtain ⟨rfl, hr⟩ := h3 hv hsq
    rw [sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul hu hv (by rw [mul_comm]; exact hr) hneg,
      decide_eq_false (by decide)]

/-- The shape of `IsNegativeSpec`. -/
theorem eq_one_iff_isNeg {c : subtle.Choice} {X : ZMod p} (h : c.val = X.val % 2) :
    c = 1#u8 ↔ X.IsNeg := by
  rw [ZMod.isNeg_iff, ← h]
  constructor
  · rintro rfl
    rfl
  · intro h1
    exact UScalar.eq_of_val_eq h1

/-- A choice that is `1` exactly when `P` holds selects between two values (the shape of
`CondAssignSpec`/`CondNegSpec` results). -/
theorem eq_ite_of_choice {c : subtle.Choice} {P : Prop} [Decidable P] {α : Type} {r a b : α}
    (hc : c.IsValid) (hP : c = 1#u8 ↔ P) (h0 : c = 0#u8 → r = a) (h1 : c = 1#u8 → r = b) :
    r = if P then b else a := by
  rcases hc with rfl | rfl
  · rw [ite_eq_right (fun h => absurd (hP.mpr h) (by decide)), h0 rfl]
  · rw [ite_eq_left (hP.mp rfl), h1 rfl]

end Curve25519Dalek.Backend

namespace Curve25519Dalek.field.FieldElement51

theorem sqrt_ratio_i_eq : sqrt_ratio_i = Backend.sqrtRatioIBody Backend.U64 := rfl

@[step]
theorem sqrt_ratio_i_spec (u v : FieldElement51) (hu : u.LimbsLt 54)
    (hv : v.LimbsLt 54) :
    sqrt_ratio_i u v ⦃ (c : subtle.Choice) (r : FieldElement51) =>
      c.IsValid ∧ (u.asNat % p = 0 → c = 1#u8 ∧ r.asNat % p = 0) ∧
      (u.asNat % p ≠ 0 → v.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0) ∧
      (v.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
        c = 1#u8 ∧ r.asNat ^ 2 * v.asNat % p = u.asNat % p) ∧
      (v.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
        c = 0#u8 ∧ r.asNat ^ 2 * v.asNat % p = sqrtM1 * u.asNat % p) ∧
      r.asNat % p % 2 = 0 ∧ r.LimbsLt 52 ⦄ := by
  rw [sqrt_ratio_i_eq]
  apply spec_mono (Backend.sqrtRatioIBody_spec Backend.U64 Backend.U64.square_spec
    Backend.U64.mul_spec Backend.U64.neg_spec Backend.U64.powP58_spec Backend.U64.sqrtM1_spec
    Backend.U64.ct_eq_spec Backend.U64.conditional_assign_spec
    Backend.U64.conditional_negate_spec Backend.U64.is_negative_spec u v hu hv)
  rintro ⟨c, r⟩ h
  exact Backend.sqrtRatioI_asNat h

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

theorem sqrt_ratio_i_eq : sqrt_ratio_i = Backend.sqrtRatioIBody Backend.U32 := rfl

@[step]
theorem sqrt_ratio_i_spec (u v : FieldElement2625) (hu : u.LimbsLt 27)
    (hv : v.LimbsLt 27) :
    sqrt_ratio_i u v ⦃ (c : subtle.Choice) (r : FieldElement2625) =>
      c.IsValid ∧ (u.asNat % p = 0 → c = 1#u8 ∧ r.asNat % p = 0) ∧
      (u.asNat % p ≠ 0 → v.asNat % p = 0 → c = 0#u8 ∧ r.asNat % p = 0) ∧
      (v.asNat % p ≠ 0 → (∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
        c = 1#u8 ∧ r.asNat ^ 2 * v.asNat % p = u.asNat % p) ∧
      (v.asNat % p ≠ 0 → (¬∃ x : ℕ, x ^ 2 * v.asNat % p = u.asNat % p) →
        c = 0#u8 ∧ r.asNat ^ 2 * v.asNat % p = sqrtM1 * u.asNat % p) ∧
      r.asNat % p % 2 = 0 ∧ r.LimbsLt 26 ⦄ := by
  rw [sqrt_ratio_i_eq]
  apply spec_mono (Backend.sqrtRatioIBody_spec Backend.U32 Backend.U32.square_spec
    Backend.U32.mul_spec Backend.U32.neg_spec Backend.U32.powP58_spec Backend.U32.sqrtM1_spec
    Backend.U32.ct_eq_spec Backend.U32.conditional_assign_spec
    Backend.U32.conditional_negate_spec Backend.U32.is_negative_spec u v hu hv)
  rintro ⟨c, r⟩ h
  exact Backend.sqrtRatioI_asNat h

end Curve25519Dalek.field.FieldElement2625

namespace Curve25519Dalek.Backend

theorem U64.sqrtRatioI_spec : U64.SqrtRatioISpec :=
  sqrtRatioIBody_spec U64 U64.square_spec U64.mul_spec U64.neg_spec U64.powP58_spec
    U64.sqrtM1_spec U64.ct_eq_spec U64.conditional_assign_spec U64.conditional_negate_spec
    U64.is_negative_spec

theorem U32.sqrtRatioI_spec : U32.SqrtRatioISpec :=
  sqrtRatioIBody_spec U32 U32.square_spec U32.mul_spec U32.neg_spec U32.powP58_spec
    U32.sqrtM1_spec U32.ct_eq_spec U32.conditional_assign_spec U32.conditional_negate_spec
    U32.is_negative_spec

end Curve25519Dalek.Backend
