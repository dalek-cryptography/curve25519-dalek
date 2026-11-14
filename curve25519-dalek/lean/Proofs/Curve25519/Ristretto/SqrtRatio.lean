/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Field
import all ForHumans.Specs.Field
public import Proofs.Curve25519.Edwards.Basic
import Proofs.Curve25519.Ristretto.Algebra
import Mathlib.Tactic.LinearCombination
public section

/-! # `SQRT_RATIO_M1` and the decoded point

The facts about `sqrtRatioM1` (RFC 9496 §4.2, defined in `ForHumans/Specs/Field.lean`):
`sqrtRatioM1_spec` states its four cases in one theorem, and the uniqueness lemmas
`sqrtRatioM1_eq_of_mul_sq_eq`, `sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul`, `sqrtRatioM1_zero_left`,
`sqrtRatioM1_zero_right` connect it to dalek's `sqrt_ratio_i`. Also `decodeRepNat_equation`: the
point that RFC 9496 §4.3.1 decodes is on the curve (used by `Ristretto.decodeRepNat`). -/

namespace curve25519

open TwistedEdwardsModel

/-! ### `SQRT_RATIO_M1` -/

theorem sqrtRatioM1_of_v_eq_zero {u v : ZMod p} (hv : v = 0) :
    sqrtRatioM1 u v = (decide (u = 0), 0) := by
  unfold sqrtRatioM1
  rw [ite_eq_left hv]

theorem sqrtRatioM1_zero_zero : sqrtRatioM1 (0 : ZMod p) 0 = (true, 0) := by
  rw [sqrtRatioM1_of_v_eq_zero rfl, decide_eq_true rfl]

/-- `v = 0`, `u ≠ 0`: `(false, 0)`. -/
theorem sqrtRatioM1_zero_right {u : ZMod p} (hu : u ≠ 0) : sqrtRatioM1 u 0 = (false, 0) := by
  rw [sqrtRatioM1_of_v_eq_zero rfl, decide_eq_false hu]

/-- `u = 0`: `(true, 0)`. -/
theorem sqrtRatioM1_zero_left (v : ZMod p) : sqrtRatioM1 0 v = (true, 0) := by
  by_cases hv : v = 0
  · rw [hv, sqrtRatioM1_zero_zero]
  · have h : IsSquare ((0 : ZMod p) / v) := ⟨0, by rw [zero_div, mul_zero]⟩
    unfold sqrtRatioM1
    rw [ite_eq_right hv, dite_eq_left h]
    have h0 : Classical.choose h = 0 :=
      mul_self_eq_zero.mp (by rw [← Classical.choose_spec h, zero_div])
    rw [h0, ZMod.abs_zero]

/-- `v ≠ 0`, `u / v` a square: `(true, r)` with `v r² = u`. -/
theorem sqrtRatioM1_of_isSquare {u v : ZMod p} (hv : v ≠ 0) (h : IsSquare (u / v)) :
    (sqrtRatioM1 u v).1 = true ∧ v * (sqrtRatioM1 u v).2 ^ 2 = u := by
  unfold sqrtRatioM1
  rw [ite_eq_right hv, dite_eq_left h]
  refine ⟨rfl, ?_⟩
  have hc := Classical.choose_spec h
  change v * (Classical.choose h).abs ^ 2 = u
  rw [ZMod.abs_sq, sq, ← hc, mul_div_cancel₀ u hv]

/-- `v ≠ 0`, `u / v` not a square: `(false, r)` with `v r² = √-1 · u`. -/
theorem sqrtRatioM1_of_not_isSquare {u v : ZMod p} (hv : v ≠ 0) (h : ¬ IsSquare (u / v)) :
    (sqrtRatioM1 u v).1 = false ∧ v * (sqrtRatioM1 u v).2 ^ 2 = sqrtM1 * u := by
  unfold sqrtRatioM1
  rw [ite_eq_right hv, dite_eq_right h]
  refine ⟨rfl, ?_⟩
  have hc := Classical.choose_spec (isSquare_sqrtM1_mul_of_not_isSquare h)
  change v * (Classical.choose (isSquare_sqrtM1_mul_of_not_isSquare h)).abs ^ 2 = sqrtM1 * u
  rw [ZMod.abs_sq, sq, ← hc, mul_left_comm, mul_div_cancel₀ u hv]

/-- The root returned by `sqrtRatioM1` is never negative. -/
theorem not_isNeg_sqrtRatioM1_snd (u v : ZMod p) : ¬ (sqrtRatioM1 u v).2.IsNeg := by
  by_cases hv : v = 0
  · rw [sqrtRatioM1_of_v_eq_zero hv]
    exact ZMod.not_isNeg_zero
  · unfold sqrtRatioM1
    rw [ite_eq_right hv]
    by_cases h : IsSquare (u / v)
    · rw [dite_eq_left h]
      exact ZMod.not_isNeg_abs _
    · rw [dite_eq_right h]
      exact ZMod.not_isNeg_abs _

/-- **The specification of `SQRT_RATIO_M1`** (the shape of the dalek `sqrt_ratio_i_spec`): the
four cases `u = 0`, `v = 0`, `u / v` a square, `u / v` not a square, and the sign of the root. -/
theorem sqrtRatioM1_spec (u v : ZMod p) :
    (u = 0 → sqrtRatioM1 u v = (true, 0)) ∧
    (u ≠ 0 → v = 0 → sqrtRatioM1 u v = (false, 0)) ∧
    (v ≠ 0 → IsSquare (u / v) →
      (sqrtRatioM1 u v).1 = true ∧ v * (sqrtRatioM1 u v).2 ^ 2 = u) ∧
    (v ≠ 0 → ¬ IsSquare (u / v) →
      (sqrtRatioM1 u v).1 = false ∧ v * (sqrtRatioM1 u v).2 ^ 2 = sqrtM1 * u) ∧
    ¬ (sqrtRatioM1 u v).2.IsNeg :=
  ⟨fun hu => hu ▸ sqrtRatioM1_zero_left v, fun hu hv => hv ▸ sqrtRatioM1_zero_right hu,
    sqrtRatioM1_of_isSquare, sqrtRatioM1_of_not_isSquare, not_isNeg_sqrtRatioM1_snd u v⟩

/-- `was_square` is `true` iff `u = 0`, or `v ≠ 0` and `u / v` is a square. -/
theorem sqrtRatioM1_fst_iff (u v : ZMod p) :
    (sqrtRatioM1 u v).1 = true ↔ u = 0 ∨ (v ≠ 0 ∧ IsSquare (u / v)) := by
  constructor
  · intro h
    by_cases hv : v = 0
    · rw [sqrtRatioM1_of_v_eq_zero hv] at h
      exact Or.inl (of_decide_eq_true h)
    · by_cases hsq : IsSquare (u / v)
      · exact Or.inr ⟨hv, hsq⟩
      · rw [(sqrtRatioM1_of_not_isSquare hv hsq).1] at h
        exact absurd h Bool.false_ne_true
  · rintro (rfl | ⟨hv, hsq⟩)
    · rw [sqrtRatioM1_zero_left]
    · exact (sqrtRatioM1_of_isSquare hv hsq).1

/-- **Uniqueness, square case**: `sqrtRatioM1 u v = (true, r)` for the non-negative root `r` of
`u / v`. -/
theorem sqrtRatioM1_eq_of_mul_sq_eq {u v r : ZMod p} (hv : v ≠ 0) (hr : v * r ^ 2 = u)
    (hneg : ¬ r.IsNeg) : sqrtRatioM1 u v = (true, r) := by
  have h : IsSquare (u / v) := ⟨r, by rw [← hr, mul_div_cancel_left₀ _ hv, sq]⟩
  obtain ⟨h1, h2⟩ := sqrtRatioM1_of_isSquare hv h
  refine Prod.ext h1 ?_
  exact ZMod.eq_of_sq_eq_of_isNeg_iff (mul_left_cancel₀ hv (h2.trans hr.symm))
    (iff_of_false (not_isNeg_sqrtRatioM1_snd u v) hneg)

/-- **Uniqueness, non-square case**: `sqrtRatioM1 u v = (false, r)` for the non-negative root `r`
of `√-1 · u / v`, when `u ≠ 0`. -/
theorem sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul {u v r : ZMod p} (hu : u ≠ 0) (hv : v ≠ 0)
    (hr : v * r ^ 2 = sqrtM1 * u) (hneg : ¬ r.IsNeg) : sqrtRatioM1 u v = (false, r) := by
  have h : ¬ IsSquare (u / v) := by
    rintro ⟨t, ht⟩
    have h1 : sqrtM1 * (u / v) = r ^ 2 := by
      rw [← mul_div_assoc, ← hr, mul_div_cancel_left₀ _ hv]
    rw [ht] at h1
    by_cases ht0 : t = 0
    · rw [ht0, mul_zero, mul_zero] at h1
      rw [← h1, mul_zero] at hr
      exact hu ((mul_eq_zero.mp hr.symm).resolve_left sqrtM1_ne_zero)
    · apply not_isSquare_sqrtM1
      refine ⟨r / t, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero ht0 ht0)]
      linear_combination h1
  obtain ⟨h1, h2⟩ := sqrtRatioM1_of_not_isSquare hv h
  refine Prod.ext h1 ?_
  exact ZMod.eq_of_sq_eq_of_isNeg_iff (mul_left_cancel₀ hv (h2.trans hr.symm))
    (iff_of_false (not_isNeg_sqrtRatioM1_snd u v) hneg)

/-! The inverse square root `sqrtRatioM1 1 v` (dalek's `invsqrt`). -/

theorem sqrtRatioM1_one_zero : sqrtRatioM1 (1 : ZMod p) 0 = (false, 0) :=
  sqrtRatioM1_zero_right one_ne_zero

/-- `sqrtRatioM1 1 v` succeeds iff `v` is a nonzero square. -/
theorem sqrtRatioM1_one_fst_iff (v : ZMod p) :
    (sqrtRatioM1 1 v).1 = true ↔ v ≠ 0 ∧ IsSquare v := by
  rw [sqrtRatioM1_fst_iff, one_div, isSquare_inv]
  exact or_iff_right one_ne_zero

/-- `sqrtRatioM1 1 v` returns `r` with `v r² = 1` for a nonzero square `v`. -/
theorem sqrtRatioM1_one_of_isSquare {v : ZMod p} (hv : v ≠ 0) (h : IsSquare v) :
    v * (sqrtRatioM1 1 v).2 ^ 2 = 1 :=
  (sqrtRatioM1_of_isSquare hv (by rw [one_div, isSquare_inv]; exact h)).2

/-- When `sqrtRatioM1 1 v` succeeds, its root `r` has `v r² = 1`. -/
theorem sqrtRatioM1_one_of_fst {v : ZMod p} (h : (sqrtRatioM1 1 v).1 = true) :
    v * (sqrtRatioM1 1 v).2 ^ 2 = 1 := by
  obtain ⟨hv, hsq⟩ := (sqrtRatioM1_one_fst_iff v).mp h
  exact sqrtRatioM1_one_of_isSquare hv hsq

/-- `sqrtRatioM1 1 v = (true, r)` for the non-negative `r` with `v r² = 1`. -/
theorem sqrtRatioM1_one_eq_of_mul_sq_eq {v r : ZMod p} (hr : v * r ^ 2 = 1) (hneg : ¬ r.IsNeg) :
    sqrtRatioM1 1 v = (true, r) :=
  sqrtRatioM1_eq_of_mul_sq_eq (fun hv => one_ne_zero (by rw [← hr, hv, zero_mul])) hr hneg

/-! ### The representative-level codec -/

namespace Ristretto

/-- The decoded point is on the model: for `s` and the root `r` with `v u2² r² = 1`
(`u1 = 1 - s²`, `u2 = 1 + s²`, `v = -(d u1²) - u2²`), the point `(|2 s (r u2)|, u1 (r (r u2) v))`
satisfies the equation of `edwards`. -/
theorem decodeRepNat_equation (s r : ZMod p)
    (hr : (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2) * (1 + s ^ 2) ^ 2 * r ^ 2 = 1) :
    edwards.Equation (2 * s * (r * (1 + s ^ 2))).abs
      ((1 - s ^ 2) * (r * (r * (1 + s ^ 2)) * (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2))) :=
  Proofs.decodeNat_equation s r hr

end Ristretto

end curve25519
