/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519.Edwards.Torsion
import Curve25519.Edwards.Order
import Curve25519.Proofs.Ristretto.DescentCert
import Curve25519.ToEllipticCurve.TwistedEdwards.Even
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section

/-! # ristretto255: even points and the 4-torsion

ristretto255 (RFC 9496) represents its elements by **even** Edwards points (`Even P`, i.e.
`P = Q + Q`), two representatives standing for the same element when they differ by 4-torsion
(`edwards.Rel`, from `Curve25519.Models.TwistedEdwards.Decaf.Defs`). No quotient type is
defined: the specifications speak about representatives, and these are the facts they need.

* The even points are the points killed by `4 L` (`even_iff_four_mul_L_nsmul`), a subgroup of
  order `4 L` (`card_even`, index `2`) containing the 4-torsion (`torsionBy_four_le_even`) and
  the basepoint (`even_basepoint`); a point related to an even point is even (`even_of_rel`).
* Two representatives are related iff `x₁ y₂ = y₁ x₂` or `x₁ x₂ = y₁ y₂` (`rel_iff_formula`,
  RFC 9496's equality, what `RistrettoPoint::ct_eq` computes); the class of `(x, y)` is
  `{(x, y), (-x, -y), (y √-1, x √-1), (-(y √-1), -(x √-1))}` (`rel_iff_coords`).
* A point is even iff `1 - y²` is a square (`even_iff_isSquare`, the 2-descent criterion of
  Decaf: the validity test of the encoding); in particular a point with
  `y = (1 - s²) / (1 + s²)` is even (`even_of_y_eq_div`), as decoding and `MAP` produce.

The 2-descent: the generic subgroup `edwards.descent = {P | IsSquare ((a - d)(1 - y²))}` of
`EllipticCurve.TwistedEdwards.Even` contains the even points, `a - d` is a square, and
`torsion8 ∉ descent` by Euler's criterion (`one_sub_torsion8_y_sq_pow_p_div_two` in
`Curve25519.Proofs.Ristretto.DescentCert`); as the even points have index `2`, `descent` is the
even subgroup (`descent_eq_even`, from the generic
`TwistedEdwardsModel.descent_eq_even_of_index_eq_two`). -/

namespace curve25519

open TwistedEdwardsModel

/-! ### The even points -/

/-- **The even points**: in the cyclic group of order `8 L`, the doubles are the points killed
by `4 L`. -/
theorem even_iff_four_mul_L_nsmul (P : edwards.Point) : Even P ↔ (4 * L) • P = 0 := by
  constructor
  · rintro ⟨Q, rfl⟩
    rw [← two_nsmul, smul_smul, show 4 * L * 2 = 8 * L by ring, eight_mul_L_nsmul]
  · intro h
    obtain ⟨⟨i, n⟩, hq, -⟩ := exists_unique_decomposition P
    dsimp only at hq
    have hL := L_mod_two
    rw [hq, smul_add, smul_smul, smul_smul,
      show 4 * L * (n : ℕ) = 4 * n * L by ring, mul_smul (4 * (n : ℕ)) L, L_nsmul_basepoint,
      smul_zero, add_zero, ← addOrderOf_dvd_iff_nsmul_eq_zero, addOrderOf_torsion8,
      mul_assoc] at h
    have h2 : 2 ∣ L * i := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) h
    have hi : 2 ∣ (i : ℕ) := by
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h2L | h2i
      · omega
      · exact h2i
    obtain ⟨j, hj⟩ := hi
    have h2L : 2 * ((L + 1) / 2) = L + 1 := by omega
    refine ⟨j • torsion8 + ((L + 1) / 2 * n) • basepoint, ?_⟩
    rw [hq, hj, ← two_nsmul, smul_add, smul_smul, smul_smul,
      show 2 * ((L + 1) / 2 * (n : ℕ)) = n + n * L by rw [← mul_assoc, h2L]; ring, add_smul,
      mul_smul (n : ℕ) L, L_nsmul_basepoint, smul_zero, add_zero]

/-- The 4-torsion consists of even points. -/
theorem torsionBy_four_le_even :
    AddSubgroup.torsionBy edwards.Point 4 ≤ AddSubgroup.even edwards.Point := by
  intro P hP
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, AddSubgroup.torsionBy.nsmul_iff] at hP
  rw [AddSubgroup.mem_even, even_iff_four_mul_L_nsmul, mul_comm, ← smul_smul, hP, smul_zero]

/-- `2 • (torsion8 + basepoint)` has order `4 L`. -/
theorem addOrderOf_two_nsmul_torsion8_add_basepoint :
    addOrderOf (2 • (torsion8 + basepoint)) = 4 * L := by
  rw [addOrderOf_nsmul' _ (by norm_num : (2 : ℕ) ≠ 0), addOrderOf_torsion8_add_basepoint,
    Nat.gcd_eq_right (Dvd.dvd.mul_right (by norm_num : 2 ∣ 8) L)]
  omega

/-- The even points are the multiples of `2 • (torsion8 + basepoint)`. -/
theorem even_eq_zmultiples :
    AddSubgroup.even edwards.Point = AddSubgroup.zmultiples (2 • (torsion8 + basepoint)) := by
  apply le_antisymm
  · intro P hP
    obtain ⟨Q, rfl⟩ := (AddSubgroup.mem_even.mp hP).exists_two_nsmul
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (zmultiples_torsion8_add_basepoint_eq_top ▸ AddSubgroup.mem_top Q)
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨k, ?_⟩
    rw [← hk, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, mul_comm]
  · rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.mem_even.mpr (Even.two_nsmul _)

/-- **The even points** form a subgroup of order `4 L` (index `2`). -/
theorem card_even : Nat.card (AddSubgroup.even edwards.Point) = 4 * L := by
  rw [even_eq_zmultiples, Nat.card_zmultiples, addOrderOf_two_nsmul_torsion8_add_basepoint]

/-- The even points have index `2`. -/
theorem index_even : (AddSubgroup.even edwards.Point).index = 2 := by
  have h := (AddSubgroup.even edwards.Point).index_mul_card
  rw [card_even, card_edwards] at h
  exact Nat.eq_of_mul_eq_mul_right (by have := L_pos; omega) (h.trans (by ring))

/-- The basepoint is even. -/
theorem even_basepoint : Even basepoint :=
  (even_iff_four_mul_L_nsmul _).mpr (by rw [mul_smul, L_nsmul_basepoint, smul_zero])

/-- A point related to an even point is even: the 4-torsion is even. -/
theorem even_of_rel {P Q : edwards.Point} (hP : Even P) (h : edwards.Rel P Q) : Even Q := by
  have hT := torsionBy_four_le_even ((rel_iff_sub_mem Q P).mp (rel_symm h))
  rw [show Q = P + (Q - P) by abel]
  exact AddSubgroup.mem_even.mp ((AddSubgroup.even _).add_mem (AddSubgroup.mem_even.mpr hP) hT)

/-! ### Equality of representatives -/

/-- **Equality of representatives**: `P` and `Q` represent the same element of ristretto255 iff
`x₁ y₂ = y₁ x₂` or `x₁ x₂ = y₁ y₂` (RFC 9496's equality, what `RistrettoPoint::ct_eq`
computes). -/
theorem rel_iff_formula (P Q : edwards.Point) :
    edwards.Rel P Q ↔ P.x * Q.y = P.y * Q.x ∨ P.x * Q.x = P.y * Q.y :=
  rel_iff_of_a_eq_neg_one edwards_a_eq_neg_one P Q

/-- **The class in coordinates**: `Q` is in the class of `P` iff `Q` is `(x, y)`, `(-x, -y)`
(`P + (0, -1)`), `(y √-1, x √-1)` (`P + (√-1, 0)`) or `(-(y √-1), -(x √-1))`
(`P + (-√-1, 0)`). -/
theorem rel_iff_coords (P Q : edwards.Point) :
    edwards.Rel P Q ↔
      (Q.x = P.x ∧ Q.y = P.y) ∨ (Q.x = -P.x ∧ Q.y = -P.y) ∨
        (Q.x = P.y * sqrtM1 ∧ Q.y = P.x * sqrtM1) ∨
        (Q.x = -(P.y * sqrtM1) ∧ Q.y = -(P.x * sqrtM1)) :=
  rel_iff_coords_of_a_eq_neg_one edwards_a_eq_neg_one sqrtM1_sq P Q

/-! ### The 2-descent -/

/-- Membership in the 2-descent subgroup of `edwards`: `1 - y²` is a square (the factor `a - d`
is a nonzero square). -/
theorem mem_descent_iff (P : edwards.Point) : P ∈ edwards.descent ↔ IsSquare (1 - P.y ^ 2) :=
  mem_descent_iff_of_sub_eq_sq (div_ne_zero two_ne_zero sqrtNegAAddTwo_ne_zero)
    (by rw [edwards_a, edwards_d]; exact a_sub_d_eq_sq) P

/-- The 2-descent certificate: `1 - y²` is not a square at the point of order `8`
(Euler's criterion, `Proofs.one_sub_torsion8_y_sq_pow_p_div_two`). -/
theorem not_isSquare_one_sub_torsion8_y_sq : ¬ IsSquare (1 - torsion8.y ^ 2) := by
  have hpow : (1 - torsion8.y ^ 2) ^ (p / 2) = -1 := by
    rw [torsion8_y_eq]
    exact_mod_cast Proofs.one_sub_torsion8_y_sq_pow_p_div_two
  have hne : 1 - torsion8.y ^ 2 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.div_pos two_lt_p.le two_pos).ne'] at hpow
    exact one_ne_zero (by linear_combination hpow)
  intro h
  have := (ZMod.euler_criterion p hne).mp h
  rw [hpow] at this
  exact ZMod.neg_one_ne_one this

/-- The point of order `8` is not in the 2-descent subgroup. -/
theorem torsion8_not_mem_descent : torsion8 ∉ edwards.descent := by
  rw [mem_descent_iff]
  exact not_isSquare_one_sub_torsion8_y_sq

/-- **The 2-descent**: the subgroup of points with `1 - y²` a square is exactly the subgroup of
even points (`even ≤ descent` generically, the even points have index `2`, and
`torsion8 ∉ descent` by the certificate). -/
theorem descent_eq_even : edwards.descent = AddSubgroup.even edwards.Point :=
  descent_eq_even_of_index_eq_two index_even torsion8_not_mem_descent

/-- **The 2-descent criterion** (Decaf/Ristretto): a point is even iff `1 - y²` is a square. -/
theorem even_iff_isSquare (P : edwards.Point) : Even P ↔ IsSquare (1 - P.y ^ 2) := by
  rw [← AddSubgroup.mem_even, ← descent_eq_even, mem_descent_iff]

/-- A point with `y = (1 - s²) / (1 + s²)` is even: `1 - y² = (2 s / (1 + s²))²`. This is the
`y`-coordinate that decoding and `MAP` produce. -/
theorem even_of_y_eq_div {P : edwards.Point} {s : ZMod p} (hs : 1 + s ^ 2 ≠ 0)
    (hy : P.y = (1 - s ^ 2) / (1 + s ^ 2)) : Even P := by
  rw [even_iff_isSquare, hy]
  refine ⟨2 * s / (1 + s ^ 2), ?_⟩
  field_simp
  ring

end curve25519
