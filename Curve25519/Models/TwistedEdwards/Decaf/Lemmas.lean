/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Models.TwistedEdwards.Decaf.Defs
public import Curve25519.Models.Field.Sign
public import Mathlib.LinearAlgebra.SModEq.Basic
import Curve25519.ToEllipticCurve.TwistedEdwards.Lemmas
import EllipticCurve.TwistedEdwards.Even
import EllipticCurve.TwistedEdwards.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # The Decaf/Ristretto relation on a complete twisted Edwards model: characterising lemmas

The audited statements about `Curve25519.Models.TwistedEdwards.Decaf.Defs`: `E.Rel` is
congruence modulo the 4-torsion (`rel_iff_smodEq`, Mathlib's `SModEq`), hence an equivalence
relation compatible with the group law (`rel_refl`, …, `rel_nsmul`), and in coordinates
(`rel_iff`, and `rel_iff_of_a_eq_neg_one` for `a = -1`), through the 4-torsion in coordinates
(`mem_torsionBy_four_iff` of `EllipticCurve.TwistedEdwards.Even`). For `a = -1` and a square root
`i` of `-1`, the class of `(x, y)` is `{(x, y), (-x, -y), (i y, i x), (-(i y), -(i x))}`
(`rel_iff_coords_of_a_eq_neg_one`; `(y i, x i)` is on the model by `equation_rot_of_a_eq_neg_one`),
and over `ZMod q` (`q` an odd prime) a class has at most one representative with `x` and `x y`
non-negative, `y ≠ 0` and `y ≠ -1` (`eq_of_rel_of_canonical_of_a_eq_neg_one`, the canonical
representative of Decaf/Ristretto encoding). -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F} [E.IsComplete]

/-! ### The relation -/

/-- `E.Rel P Q` unfolds to `P - Q ∈ E.Point[4]`. -/
theorem rel_iff_sub_mem (P Q : E.Point) :
    E.Rel P Q ↔ P - Q ∈ AddSubgroup.torsionBy E.Point 4 :=
  Iff.rfl

/-- `E.Rel` is congruence modulo the 4-torsion. -/
theorem rel_iff_smodEq (P Q : E.Point) :
    E.Rel P Q ↔ P ≡ Q [SMOD Submodule.torsionBy ℤ E.Point 4] :=
  SModEq.sub_mem.symm

theorem rel_refl (P : E.Point) : E.Rel P P :=
  (rel_iff_smodEq P P).mpr SModEq.rfl

theorem rel_symm {P Q : E.Point} (h : E.Rel P Q) : E.Rel Q P :=
  (rel_iff_smodEq Q P).mpr ((rel_iff_smodEq P Q).mp h).symm

theorem rel_trans {P Q R : E.Point} (hPQ : E.Rel P Q) (hQR : E.Rel Q R) : E.Rel P R :=
  (rel_iff_smodEq P R).mpr (((rel_iff_smodEq P Q).mp hPQ).trans ((rel_iff_smodEq Q R).mp hQR))

/-- `Rel` is compatible with addition. -/
theorem rel_add {P P' Q Q' : E.Point} (hP : E.Rel P P') (hQ : E.Rel Q Q') :
    E.Rel (P + Q) (P' + Q') :=
  (rel_iff_smodEq _ _).mpr (((rel_iff_smodEq P P').mp hP).add ((rel_iff_smodEq Q Q').mp hQ))

/-- `Rel` is compatible with negation. -/
theorem rel_neg {P Q : E.Point} (h : E.Rel P Q) : E.Rel (-P) (-Q) :=
  (rel_iff_smodEq _ _).mpr ((rel_iff_smodEq P Q).mp h).neg

/-- `Rel` is compatible with subtraction. -/
theorem rel_sub {P P' Q Q' : E.Point} (hP : E.Rel P P') (hQ : E.Rel Q Q') :
    E.Rel (P - Q) (P' - Q') :=
  (rel_iff_smodEq _ _).mpr (((rel_iff_smodEq P P').mp hP).sub ((rel_iff_smodEq Q Q').mp hQ))

/-- `Rel` is compatible with scalar multiplication. -/
theorem rel_nsmul (n : ℕ) {P Q : E.Point} (h : E.Rel P Q) : E.Rel (n • P) (n • Q) :=
  (rel_iff_smodEq _ _).mpr (((rel_iff_smodEq P Q).mp h).nsmul n)

/-! ### In coordinates -/

variable [NeZero (6 : F)]

/-- **`Rel` in coordinates**: `P - Q` is 4-torsion iff `x₁ y₂ = y₁ x₂` (then `P - Q ∈ {(0, ±1)}`)
or `y₁ y₂ + a x₁ x₂ = 0` (then `P - Q` has `y = 0`). -/
theorem rel_iff (P Q : E.Point) :
    E.Rel P Q ↔ P.x * Q.y = P.y * Q.x ∨ P.y * Q.y + E.a * P.x * Q.x = 0 := by
  rw [rel_iff_sub_mem, mem_torsionBy_four_iff, sub_x, sub_y]
  unfold addX addY
  rw [div_eq_zero_iff, div_eq_zero_iff, or_iff_left (addDen₁_ne_zero P (-Q)),
    or_iff_left (addDen₂_ne_zero P (-Q)), neg_x, neg_y]
  exact or_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
    ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

/-- `Rel` in coordinates for `a = -1` (Decaf/Ristretto, RFC 9496's equality): `x₁ y₂ = y₁ x₂`
or `x₁ x₂ = y₁ y₂`. -/
theorem rel_iff_of_a_eq_neg_one (ha : E.a = -1) (P Q : E.Point) :
    E.Rel P Q ↔ P.x * Q.y = P.y * Q.x ∨ P.x * Q.x = P.y * Q.y := by
  rw [rel_iff, ha]
  exact or_congr_right ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

/-- For `a = -1` and `i² = -1`, `(y i, x i)` is on the model with `(x, y)`. -/
theorem equation_rot_of_a_eq_neg_one {F : Type u} [Field F] {E : TwistedEdwardsModel F}
    (ha : E.a = -1) {i : F} (hi : i ^ 2 = -1) {x y : F} (h : E.Equation x y) :
    E.Equation (y * i) (x * i) := by
  unfold Equation at h ⊢
  rw [ha] at h ⊢
  rw [mul_pow, mul_pow, hi]
  linear_combination h

/-- **The class in coordinates** for `a = -1`, with `i² = -1`: `Q` is related to `P = (x, y)` iff
`Q` is `(x, y)`, `(-x, -y)` (`P + (0, -1)`), `(y i, x i)` (`P + (i, 0)`) or `(-(y i), -(x i))`
(`P + (-i, 0)`). -/
theorem rel_iff_coords_of_a_eq_neg_one (ha : E.a = -1) {i : F} (hi : i ^ 2 = -1)
    (P Q : E.Point) :
    E.Rel P Q ↔
      (Q.x = P.x ∧ Q.y = P.y) ∨ (Q.x = -P.x ∧ Q.y = -P.y) ∨
        (Q.x = P.y * i ∧ Q.y = P.x * i) ∨ (Q.x = -(P.y * i) ∧ Q.y = -(P.x * i)) := by
  constructor
  · intro h
    have hQ : Q = P + (Q - P) := by abel
    rcases (mem_torsionBy_four_iff (Q - P)).mp ((rel_iff_sub_mem Q P).mp (rel_symm h)) with
      hx | hy
    · rcases y_eq_one_or_eq_neg_one_of_x_eq_zero (Q - P).equation hx with hy | hy
      · have h0 : Q - P = 0 := Point.ext (by rw [hx, zero_x]) (by rw [hy, zero_y])
        rw [sub_eq_zero] at h0
        exact Or.inl ⟨by rw [h0], by rw [h0]⟩
      · rw [hQ, add_comm]
        exact Or.inr (Or.inl ⟨add_x_of_x_eq_zero_of_y_eq_neg_one P hx hy,
          add_y_of_x_eq_zero_of_y_eq_neg_one P hx hy⟩)
    · have hsq : (Q - P).x ^ 2 = i ^ 2 := by
        have e := (Q - P).equation
        unfold Equation at e
        rw [ha, hy] at e
        rw [hi]
        linear_combination -e
      have hx : (P + (Q - P)).x = (Q - P).x * P.y := by
        rw [add_x]
        unfold addX addDen₁
        rw [hy]
        ring
      have hy' : (P + (Q - P)).y = P.x * (Q - P).x := by
        rw [add_y]
        unfold addY addDen₂
        rw [hy, ha]
        ring
      rw [hQ, hx, hy']
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h <;> rw [h]
      · exact Or.inr (Or.inr (Or.inl ⟨mul_comm _ _, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by ring, by ring⟩))
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩) <;>
      rw [rel_iff_of_a_eq_neg_one ha, hx, hy]
    · exact Or.inl (by ring)
    · exact Or.inl (by ring)
    · exact Or.inr (by ring)
    · exact Or.inr (by ring)

/-! ### The canonical representative over `ZMod q` -/

section ZMod

variable {q : ℕ} [Fact q.Prime] [Fact (q % 2 = 1)] [NeZero (6 : ZMod q)]
  {E : TwistedEdwardsModel (ZMod q)} [E.IsComplete]

/-- **Uniqueness of the canonical representative** for `a = -1` (`i² = -1`): two related points
with `x` and `x y` non-negative, `y ≠ 0` and `y ≠ -1` are equal. -/
theorem eq_of_rel_of_canonical_of_a_eq_neg_one (ha : E.a = -1) {i : ZMod q} (hi : i ^ 2 = -1)
    {P Q : E.Point} (h : E.Rel P Q)
    (hPx : ¬ P.x.IsNeg) (hPxy : ¬ (P.x * P.y).IsNeg) (hPy : P.y ≠ 0) (hPy1 : P.y ≠ -1)
    (hQx : ¬ Q.x.IsNeg) (hQxy : ¬ (Q.x * Q.y).IsNeg) (hQy : Q.y ≠ 0) (hQy1 : Q.y ≠ -1) :
    P = Q := by
  rw [rel_iff_coords_of_a_eq_neg_one ha hi] at h
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | h
  · exact (Point.ext hx hy).symm
  · exfalso
    rw [hx] at hQx
    have hx0 : P.x = 0 := ZMod.eq_zero_of_not_isNeg_of_not_isNeg_neg hPx hQx
    have hy1 : P.y = 1 :=
      (y_eq_one_or_eq_neg_one_of_x_eq_zero P.equation hx0).resolve_right hPy1
    rw [hy, hy1] at hQy1
    exact hQy1 rfl
  · -- the two rotations: `x y` changes sign, and `y = 0` when `x = 0`
    exfalso
    have hrot : Q.x * Q.y = -(P.x * P.y) ∧ (P.x = 0 → Q.y = 0) := by
      rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] <;>
        exact ⟨by linear_combination (P.x * P.y) * hi, fun h0 => by rw [h0]; ring⟩
    rw [hrot.1] at hQxy
    have h0 : P.x * P.y = 0 := ZMod.eq_zero_of_not_isNeg_of_not_isNeg_neg hPxy hQxy
    exact hQy (hrot.2 ((mul_eq_zero.mp h0).resolve_right hPy))

end ZMod

end TwistedEdwardsModel
