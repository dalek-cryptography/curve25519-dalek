/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Prime
public import Mathlib.Algebra.Field.ZMod
import EllipticCurve.Mathlib.Algebra.Group.Even
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
public section

/-! # Squares modulo `p`

Which constants of curve25519 are squares in `ZMod p`: `a = -1` and `a - d` are
(`isSquare_a`, `a_sub_d_eq_sq`); `d`, `-d`, `sqrtM1 = √-1` and `2` are not (`not_isSquare_d`,
`not_isSquare_neg_d`, `not_isSquare_sqrtM1`, `not_isSquare_two`), by Euler's criterion
(`d_pow_p_div_two`, `sqrtM1_pow_p_div_two`) and `p ≡ 5 (mod 8)`; and `√-1 · x` is a square when
`x` is not (`isSquare_sqrtM1_mul_of_not_isSquare`). These make the Edwards model complete, the
twist of the Montgomery model a non-square twist, and `SQRT_RATIO_M1` total. -/

namespace curve25519

/-- `a = -1` is a square: `a = sqrtM1²`. -/
theorem isSquare_a : IsSquare a :=
  ⟨(sqrtM1 : ZMod p), by rw [a_def, ← sqrtM1_sq, sq]⟩

/-- `a - d = (2 / sqrtNegAAddTwo)²` is a square. -/
theorem a_sub_d_eq_sq : a - d = (2 / sqrtNegAAddTwo) ^ 2 := by
  rw [div_pow, eq_div_iff (pow_ne_zero 2 sqrtNegAAddTwo_ne_zero), mul_comm,
    ← four_eq_sqrtNegAAddTwo_sq_mul]
  norm_num

/-- `d` is not a square (Euler's criterion, `d_pow_p_div_two`). -/
theorem not_isSquare_d : ¬ IsSquare d := by
  intro h
  have hd := (ZMod.euler_criterion p d_ne_zero).mp h
  rw [d_pow_p_div_two] at hd
  exact ZMod.neg_one_ne_one hd

/-- `sqrtM1 = √-1` is not a square modulo `p` (Euler's criterion, `sqrtM1_pow_p_div_two`:
`p ≡ 5 (mod 8)`). -/
theorem not_isSquare_sqrtM1 : ¬ IsSquare (sqrtM1 : ZMod p) := by
  intro h
  have hpow := (ZMod.euler_criterion p sqrtM1_ne_zero).mp h
  rw [sqrtM1_pow_p_div_two] at hpow
  exact ZMod.neg_one_ne_one hpow

/-- `-d` is not a square: `-1` is one and `d` is not. -/
theorem not_isSquare_neg_d : ¬ IsSquare (-d) := by
  rintro ⟨r, hr⟩
  apply not_isSquare_d
  refine ⟨sqrtM1 * r, ?_⟩
  linear_combination -hr - r ^ 2 * sqrtM1_sq

/-- `sqrtM1 · x` is a square when `x` is not (the product of two non-squares). -/
theorem isSquare_sqrtM1_mul_of_not_isSquare {x : ZMod p} (hx : ¬ IsSquare x) :
    IsSquare (sqrtM1 * x) := by
  have hx0 : x ≠ 0 := ne_zero_of_not_isSquare hx
  have hpow : x ^ (p / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one p hx0).resolve_left
      fun h => hx ((ZMod.euler_criterion p hx0).mpr h)
  rw [ZMod.euler_criterion p (mul_ne_zero sqrtM1_ne_zero hx0), mul_pow, sqrtM1_pow_p_div_two,
    hpow]
  ring

/-- `2` is not a square modulo `p`, since `p ≡ 5 (mod 8)`. -/
theorem not_isSquare_two : ¬ IsSquare (2 : ZMod p) := by
  have h2 := two_lt_p
  rw [ZMod.exists_sq_eq_two_iff (by omega), p_mod_eight]
  decide

end curve25519
