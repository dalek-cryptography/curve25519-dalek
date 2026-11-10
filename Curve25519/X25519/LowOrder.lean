/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519.ToEllipticCurve.Montgomery.XOnly
import Curve25519.Proofs.X25519.LowOrderCerts
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.LinearCombination
public section

/-! # The coordinates sent to `0` by X25519

`x25519Nat k u = 0` for every scalar `k` exactly when `decodeU u` is one of the five field elements
`0`, `1`, `-1`, `u₈` and `u₈⁻¹` (`x25519Nat_eq_zero_iff`), where `u₈` is the `u`-coordinate of a
point of order `8` of `montgomery` (`u8`).

The proof is x-only. On `u`-coordinates, doubling is `dblU u = (u² - 1)² / (4 u (u² + A u + 1))`
(`MontgomeryModel.xMul_two`), so multiplication by `2 ^ n` is the `n`-th iterate of `dblU`
(`MontgomeryModel.xMul_two_pow`). The set `S` of the five coordinates is closed under preimages
by `dblU` (`isLowOrderU_of_isLowOrderU_dblU`): `dblU w = 0` only for `w = 0, ±1`,
`dblU w = 1` only for `w = u₈, u₈⁻¹`, and `dblU w = c` has no solution `w` when
`c² + A c + 1` is not a square, which is the case for `c = -1, u₈, u₈⁻¹`
(`Curve25519.Proofs.X25519.LowOrderCerts`). The scalar `0` clamps to `2 ^ 254`, so
`x25519Nat 0 u = 0` already puts `decodeU u` in `S`; conversely `dblU` sends `S` to `0` in three
steps, and every clamped scalar is a multiple of `8`. -/

namespace curve25519

open MontgomeryModel Proofs

/-- The `u`-coordinate `u₈` of a point of order `8` of `montgomery` (`dblU u₈ = 1`, the
`u`-coordinate of its points of order `4`); the other points of order `8` have `u = u₈⁻¹`. -/
@[expose] def u8 : ZMod p :=
  325606250916557431795983626356110631294008115727848805560023387167927233504

/-- The five coordinates sent to `0` by `x25519Nat` (`x25519Nat_eq_zero_iff`). -/
@[expose] def IsLowOrderU (v : ZMod p) : Prop :=
  v = 0 ∨ v = 1 ∨ v = -1 ∨ v = u8 ∨ v = u8⁻¹

/-- `u₈⁻¹` as a numeral. -/
theorem u8_inv :
    u8⁻¹ = 39382357235489614581723060781553021112529911719440698176882885853963445705823 :=
  (eq_inv_of_mul_eq_one_right (u8_mul_u8' _ _ rfl rfl)).symm

private theorem u8_ne_zero : u8 ≠ 0 :=
  left_ne_zero_of_mul_eq_one (u8_mul_u8' _ _ rfl u8_inv)

private theorem not_isSquare_of_pow {x : ZMod p} (h : x ^ (p / 2) = -1) : ¬ IsSquare x := by
  intro hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by rw [p_eq_numeral]; decide)] at h
    exact neg_ne_zero.mpr one_ne_zero h.symm
  have h1 := (ZMod.euler_criterion p hx0).mp hx
  rw [h] at h1
  exact ZMod.neg_one_ne_one h1

private theorem dblU_def (w : ZMod p) :
    montgomery.dblU w = (w ^ 2 - 1) ^ 2 / (4 * w * (w ^ 2 + 486662 * w + 1)) := by
  rw [dblU, montgomery_A_eq]

/-- `w² + A w + 1 ≠ 0`: `A² - 4` is not a square (no point of order `2` besides `(0, 0)`). -/
private theorem quad_ne_zero (w : ZMod p) : w ^ 2 + 486662 * w + 1 ≠ 0 := by
  intro h
  exact not_isSquare_of_pow a_sq_sub_four_pow ⟨2 * w + 486662, by linear_combination (-4) * h⟩

private theorem natCast_ne_zero {n : ℕ} (h0 : 0 < n) (hn : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt h0 hn

private theorem four_ne_zero' : (4 : ZMod p) ≠ 0 := by
  exact_mod_cast natCast_ne_zero (n := 4) (by norm_num) (by rw [p_eq_numeral]; norm_num)

private theorem den_eq_zero_iff (w : ZMod p) : 4 * w * (w ^ 2 + 486662 * w + 1) = 0 ↔ w = 0 := by
  simp only [mul_eq_zero, four_ne_zero', quad_ne_zero, false_or, or_false]

/-- `dblU w = c` has no solution when `c ≠ 0` and `c² + A c + 1` is not a square. -/
private theorem dblU_ne {c : ZMod p} (hc0 : c ≠ 0) (hc : ¬ IsSquare (c ^ 2 + 486662 * c + 1))
    (w : ZMod p) : montgomery.dblU w ≠ c := by
  intro h
  rw [dblU_def] at h
  have hw : w ≠ 0 := by
    rintro rfl
    rw [(den_eq_zero_iff 0).mpr rfl, div_zero] at h
    exact hc0 h.symm
  have hden : 4 * w * (w ^ 2 + 486662 * w + 1) ≠ 0 := fun h0 => hw ((den_eq_zero_iff w).mp h0)
  rw [div_eq_iff hden] at h
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast natCast_ne_zero (n := 2) (by norm_num) (by rw [p_eq_numeral]; norm_num)
  refine hc ⟨(w ^ 2 - 2 * c * w + 1) / (2 * w), ?_⟩
  rw [← sq, div_pow, eq_div_iff (pow_ne_zero 2 (mul_ne_zero h2 hw))]
  linear_combination (-1) * h

private theorem dblU_eq_zero {w : ZMod p} (h : montgomery.dblU w = 0) :
    w = 0 ∨ w = 1 ∨ w = -1 := by
  rw [dblU_def, div_eq_zero_iff, den_eq_zero_iff] at h
  rcases h with h | h
  · have h' : (w - 1) * (w + 1) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      linear_combination this
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact Or.inr (Or.inl (sub_eq_zero.mp h1))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h1))
  · exact Or.inl h

private theorem dblU_eq_one {w : ZMod p} (h : montgomery.dblU w = 1) : w = u8 ∨ w = u8⁻¹ := by
  rw [dblU_def] at h
  have hden : 4 * w * (w ^ 2 + 486662 * w + 1) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    exact zero_ne_one h
  rw [div_eq_one_iff_eq hden] at h
  obtain ⟨r, hr⟩ : ∃ r : ZMod p,
      r = 48802004052532134862652268456126542835229456083994414501085850622543968879637 :=
    ⟨_, rfl⟩
  have hfac : (w ^ 2 - (2 + 2 * r) * w + 1) * (w ^ 2 - (2 - 2 * r) * w + 1) = 0 := by
    linear_combination h - 4 * w ^ 2 * r_sq r hr
  rcases mul_eq_zero.mp hfac with h1 | h1
  · have h2 : (w - u8) * (w - u8⁻¹) = 0 := by
      linear_combination h1 - w * u8_add_u8' u8 u8⁻¹ r rfl u8_inv hr + u8_mul_u8' u8 u8⁻¹ rfl u8_inv
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl (sub_eq_zero.mp h3)
    · exact Or.inr (sub_eq_zero.mp h3)
  · exact absurd ⟨2 * w - (2 - 2 * r), by linear_combination (-4) * h1⟩
      (not_isSquare_of_pow (two_sub_two_r_sq_sub_four_pow r hr))

/-- The five coordinates are closed under preimages by `dblU`. -/
theorem isLowOrderU_of_isLowOrderU_dblU {w : ZMod p} (h : IsLowOrderU (montgomery.dblU w)) :
    IsLowOrderU w := by
  rcases h with h | h | h | h | h
  · rcases dblU_eq_zero h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases dblU_eq_one h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · refine absurd h (dblU_ne (neg_ne_zero.mpr one_ne_zero) ?_ w)
    rw [show (-1 : ZMod p) ^ 2 + 486662 * -1 + 1 = 2 - 486662 by ring]
    exact not_isSquare_of_pow two_sub_a_pow
  · exact absurd h (dblU_ne u8_ne_zero (not_isSquare_of_pow (u8_sq_add_pow _ rfl)) w)
  · exact absurd h (dblU_ne (inv_ne_zero u8_ne_zero)
      (not_isSquare_of_pow (u8'_sq_add_pow _ u8_inv)) w)

theorem isLowOrderU_of_iterate {n : ℕ} {v : ZMod p} (h : IsLowOrderU (montgomery.dblU^[n] v)) :
    IsLowOrderU v := by
  induction n generalizing v with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact isLowOrderU_of_isLowOrderU_dblU (ih h)

private theorem dblU_zero : montgomery.dblU 0 = 0 := by
  rw [dblU_def, (den_eq_zero_iff 0).mpr rfl, div_zero]

private theorem dblU_of_sq_eq_one {w : ZMod p} (hw : w ^ 2 = 1) : montgomery.dblU w = 0 := by
  rw [dblU_def, hw, sub_self, zero_pow two_ne_zero, zero_div]

private theorem dblU_u8_of {w : ZMod p} (hw0 : w ≠ 0)
    (h : (w ^ 2 - 1) ^ 2 = 4 * w * (w ^ 2 + 486662 * w + 1)) : montgomery.dblU w = 1 := by
  rw [dblU_def, h, div_self fun h0 => hw0 ((den_eq_zero_iff w).mp h0)]

/-- Every one of the five coordinates is sent to `0` by `dblU` in three steps. -/
theorem dblU_iterate_three_of_isLowOrderU {v : ZMod p} (h : IsLowOrderU v) :
    montgomery.dblU^[3] v = 0 := by
  have h1 : montgomery.dblU 1 = 0 := dblU_of_sq_eq_one (one_pow 2)
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rcases h with rfl | rfl | rfl | rfl | rfl
  · rw [dblU_zero, dblU_zero, dblU_zero]
  · rw [h1, dblU_zero, dblU_zero]
  · rw [dblU_of_sq_eq_one (w := -1) (by ring), dblU_zero, dblU_zero]
  · rw [dblU_u8_of u8_ne_zero (u8_dbl u8 rfl), h1, dblU_zero]
  · rw [dblU_u8_of (inv_ne_zero u8_ne_zero) (u8'_dbl _ u8_inv), h1,
      dblU_zero]

/-- **The coordinates sent to `0` by X25519**: `x25519Nat k u = 0` for every scalar `k` iff
`decodeU u` is `0`, `1`, `-1`, `u₈` or `u₈⁻¹`. The scalar `k = 0` already decides it. -/
theorem x25519Nat_eq_zero_iff (u : ℕ) : (∀ k, x25519Nat k u = 0) ↔ IsLowOrderU (decodeU u) := by
  constructor
  · intro h
    have h0 := h 0
    rw [x25519Nat_eq_xMul, show clamp 0 = 2 ^ 254 by rfl, xMul_two_pow not_isSquare_two, encodeU,
      ZMod.val_eq_zero] at h0
    exact isLowOrderU_of_iterate (n := 254) (h0 ▸ Or.inl rfl)
  · intro h k
    refine x25519Nat_eq_zero_of_xMul_eight ?_ k
    rw [show (8 : ℕ) = 2 ^ 3 by rfl, xMul_two_pow not_isSquare_two]
    exact dblU_iterate_three_of_isLowOrderU h

end curve25519
