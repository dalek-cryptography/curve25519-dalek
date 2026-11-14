/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.ToEllipticCurve.TwistedEdwards.Defs
public import EllipticCurve.TwistedEdwards.Lemmas
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # Twisted Edwards models: points with a given `y` (staged for `EllipticCurve`)

On a complete twisted Edwards model `E`:

* the equation solved for `x²`: `d y² - a ≠ 0` (`d_mul_sq_sub_a_ne_zero`), so `(x, y)` is on the
  model iff `x ^ 2 = E.xSq y` (`equation_iff_sq_eq_xSq`), `xSq y` is a square iff some point
  has this `y` (`isSquare_xSq_iff`), and `xSq y = 0` iff `y² = 1` (`xSq_eq_zero_iff`);
* the points with a given `y` are `(±x, y)` (`sq_x_eq_sq_x_of_y_eq`, `x_eq_or_eq_neg_of_y_eq`),
  so over a finite field there are at most `2 |F|` points (`natCard_point_le`);
* `(x, y) ↦ (-x, -y)` preserves the equation (`equation_neg_neg`), and is the translation by the
  point `(0, -1)` of order `2` (`add_x_of_x_eq_zero_of_y_eq_neg_one`,
  `add_y_of_x_eq_zero_of_y_eq_neg_one`).

Staged here for upstreaming to the `EllipticCurve` library: these depend only on the model. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

/-- `(x, y) ↦ (-x, -y)` preserves the equation. -/
theorem equation_neg_neg {x y : F} (h : E.Equation x y) : E.Equation (-x) (-y) := by
  unfold Equation at h ⊢
  linear_combination h

/-! ### The equation solved for `x²` -/

section IsComplete

variable [E.IsComplete]

/-- `d y² - a ≠ 0` for every `y` on a complete model (`a` is a nonzero square, `d` is not). -/
theorem d_mul_sq_sub_a_ne_zero (y : F) : E.d * y ^ 2 - E.a ≠ 0 := by
  intro h
  have ha : E.a = E.d * y ^ 2 := (sub_eq_zero.mp h).symm
  by_cases hy : y = 0
  · rw [hy] at ha
    exact IsComplete.a_ne_zero (E := E) (by rw [ha]; ring)
  · obtain ⟨s, hs⟩ := IsComplete.isSquare_a (E := E)
    apply IsComplete.not_isSquare_d (E := E)
    refine ⟨s / y, ?_⟩
    rw [div_mul_div_comm, ← hs, ha, eq_div_iff (mul_ne_zero hy hy)]
    ring

/-- On a complete model, `(x, y)` is on the model iff `x² = (y² - 1) / (d y² - a)`. -/
theorem equation_iff_sq_eq_xSq {x y : F} : E.Equation x y ↔ x ^ 2 = E.xSq y := by
  unfold Equation xSq
  rw [eq_div_iff (d_mul_sq_sub_a_ne_zero y)]
  constructor <;> intro h <;> linear_combination -h

/-- `xSq y = 0` iff `y² = 1`: the points with `x = 0` are `(0, ±1)`. -/
theorem xSq_eq_zero_iff {y : F} : E.xSq y = 0 ↔ y ^ 2 = 1 := by
  unfold xSq
  rw [div_eq_zero_iff, sub_eq_zero, or_iff_left (d_mul_sq_sub_a_ne_zero y)]

/-- `y` is the `y`-coordinate of a point iff `xSq y` is a square. -/
theorem isSquare_xSq_iff {y : F} : IsSquare (E.xSq y) ↔ ∃ x, E.Equation x y := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, equation_iff_sq_eq_xSq.mpr (by rw [hr, sq])⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← sq, equation_iff_sq_eq_xSq.mp hx]⟩

theorem Point.sq_x_eq_xSq (P : E.Point) : P.x ^ 2 = E.xSq P.y :=
  equation_iff_sq_eq_xSq.mp P.equation

/-! ### The points with a given `y` -/

/-- Two points with the same `y` have the same `x²`. -/
theorem sq_x_eq_sq_x_of_y_eq {P Q : E.Point} (h : P.y = Q.y) : P.x ^ 2 = Q.x ^ 2 := by
  rw [P.sq_x_eq_xSq, Q.sq_x_eq_xSq, h]

/-- Two points with the same `y` have `x = x'` or `x = -x'`. -/
theorem x_eq_or_eq_neg_of_y_eq {P Q : E.Point} (h : P.y = Q.y) : P.x = Q.x ∨ P.x = -Q.x :=
  sq_eq_sq_iff_eq_or_eq_neg.mp (sq_x_eq_sq_x_of_y_eq h)

/-- **At most two points for each `y`**: a complete model over a finite field has at most
`2 |F|` points. -/
theorem natCard_point_le [Finite F] : Nat.card E.Point ≤ 2 * Nat.card F := by
  classical
  -- an `x`-coordinate for each `y` that occurs; every point is `(±r y, y)`
  let r : F → F := fun y => if h : ∃ P : E.Point, P.y = y then (Classical.choose h).x else 0
  have hr (P : E.Point) : P.x = r P.y ∨ P.x = -r P.y := by
    have h : ∃ Q : E.Point, Q.y = P.y := ⟨P, rfl⟩
    simp only [r, dite_eq_left h]
    exact x_eq_or_eq_neg_of_y_eq (Classical.choose_spec h).symm
  have hinj : Function.Injective fun P : E.Point => (P.y, decide (P.x = r P.y)) := by
    intro P Q h
    simp only [Prod.mk.injEq, decide_eq_decide] at h
    obtain ⟨hy, hb⟩ := h
    refine Point.ext ?_ hy
    by_cases hP : P.x = r P.y
    · rw [hP, hb.mp hP, hy]
    · rw [(hr P).resolve_left hP, (hr Q).resolve_left (mt hb.mpr hP), hy]
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm] at h

end IsComplete

/-! ### Translation by the point `(0, -1)` -/

section Translation

variable [E.IsComplete] [NeZero (6 : F)]

/-- Adding the point `P = (0, -1)` negates `x` (the group form of
`addX_of_x_eq_zero_of_y_eq_neg_one`). -/
theorem add_x_of_x_eq_zero_of_y_eq_neg_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = -1) : (P + Q).x = -Q.x := by
  rw [add_x, addX_of_x_eq_zero_of_y_eq_neg_one Q hx hy]

/-- Adding the point `P = (0, -1)` negates `y` (the group form of
`addY_of_x_eq_zero_of_y_eq_neg_one`). -/
theorem add_y_of_x_eq_zero_of_y_eq_neg_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = -1) : (P + Q).y = -Q.y := by
  rw [add_y, addY_of_x_eq_zero_of_y_eq_neg_one Q hx hy]

end Translation

end TwistedEdwardsModel
