/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Bytes
public import Curve25519.Edwards.Basepoint
public import Curve25519.Ristretto.Encoding.Defs
import all Curve25519.Ristretto.Encoding.Defs
import Curve25519.Proofs.Ristretto.Algebra
import Curve25519.Proofs.Ristretto.Certs
import Curve25519.Ristretto.Even
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # The ristretto255 encoding (RFC 9496 §4.3.1–4.3.2): properties

RFC 9496 on 32-byte strings (`Vector UInt8 32`) is `Ristretto.encodeRep` and `Ristretto.decodeRep`
(at the end), computed by the arithmetic cores `Ristretto.encodeRepNat` and `Ristretto.decodeRepNat`
of `Curve25519.Ristretto.Encoding.Defs` on the little-endian value of the bytes. The audited
statements here are about the cores. Both act on representatives: even Edwards points, two of them
standing for the same element of ristretto255 when they are related by `edwards.Rel`
(`Curve25519.Ristretto.Even`).

* Decoding: `decodeRepNat_eq_some_iff` (`decodeRepNat s = some P` iff `s < p` is non-negative, `P`
  has `y = (1 - s²) / (1 + s²)`, `x` and `x y` non-negative and `y ≠ 0`), `decodeRepNat_eq_none_iff`
  (the rejection reasons of RFC 9496 §4.3.1), `even_decodeRepNat`, `decodeRepNat_y`.
* Encoding: `encodeRepNat_lt`, `not_isNeg_encodeRepNat`, the round trips `encodeRepNat_decodeRepNat`
  and `decodeRepNat_encodeRepNat`, and **the encoding of ristretto255**: on even points, two
  representatives have the same encoding iff they are related (`encodeRepNat_eq_iff`; one direction
  is the invariance `encodeRepNat_rel`). The encoding of the basepoint is `encodeRepNat_basepoint`
  (RFC 9496 §A.1, a kernel certificate in `Curve25519.Proofs.Ristretto.Certs`).
* The uniqueness of the canonical representative of a class `eq_of_rel_of_canonical` (`x` and `x y`
  non-negative, `y ≠ 0`, `y ≠ -1`), the generic
  `TwistedEdwardsModel.eq_of_rel_of_canonical_of_a_eq_neg_one` at `edwards`.

The proof of the round trips goes through the canonical representative of a class: every class
contains one (`exists_canon`), and when `x y ≠ 0` it is the only representative with `x` and `x y`
non-negative (`eq_of_rel_of_canonical`); `encodeRepNat` of any representative is `|D (1 - y_C)|`
with `D² (1 - y_C²) = 1` for the canonical `(x_C, y_C)` (the `rotate`/sign machinery of §4.3.2), and
`decodeRepNat` returns the canonical representative. -/

namespace curve25519

open TwistedEdwardsModel

/-! ### The canonical representative -/

/-- **Uniqueness of the canonical representative**: two representatives of one class with `x`
and `x y` non-negative, `y ≠ 0` and `y ≠ -1` are equal. -/
theorem eq_of_rel_of_canonical {P Q : edwards.Point} (h : edwards.Rel P Q)
    (hPx : ¬ P.x.IsNeg) (hPxy : ¬ (P.x * P.y).IsNeg) (hPy : P.y ≠ 0) (hPy1 : P.y ≠ -1)
    (hQx : ¬ Q.x.IsNeg) (hQxy : ¬ (Q.x * Q.y).IsNeg) (hQy : Q.y ≠ 0) (hQy1 : Q.y ≠ -1) :
    P = Q :=
  eq_of_rel_of_canonical_of_a_eq_neg_one edwards_a_eq_neg_one sqrtM1_sq h hPx hPxy hPy hPy1 hQx
    hQxy hQy hQy1

namespace Ristretto

/-! ### Decoding -/

/-! The intermediate quantities of RFC 9496 §4.3.1, internal. -/

private noncomputable def decU1 (s : ℕ) : ZMod p := 1 - (s : ZMod p) ^ 2

private noncomputable def decU2 (s : ℕ) : ZMod p := 1 + (s : ZMod p) ^ 2

private noncomputable def decV (s : ℕ) : ZMod p := -(d * decU1 s ^ 2) - decU2 s ^ 2

private noncomputable def decW (s : ℕ) : ZMod p := decV s * decU2 s ^ 2

private noncomputable def decR (s : ℕ) : ZMod p := (sqrtRatioM1 1 (decW s)).2

private noncomputable def decX (s : ℕ) : ZMod p := (2 * (s : ZMod p) * (decR s * decU2 s)).abs

private noncomputable def decY (s : ℕ) : ZMod p := decU1 s * (decR s * (decR s * decU2 s) * decV s)

private theorem decodeRepNat_of_not {s : ℕ} (h : ¬ (s < p ∧ ¬ (s : ZMod p).IsNeg)) :
    decodeRepNat s = none := by
  unfold decodeRepNat
  rw [ite_eq_right h]

private theorem decodeRepNat_of_lt {s : ℕ} (h : s < p ∧ ¬ (s : ZMod p).IsNeg) :
    decodeRepNat s =
      if hc : (sqrtRatioM1 1 (decW s)).1 = true ∧ ¬ (decX s * decY s).IsNeg ∧ decY s ≠ 0 then
        some ⟨decX s, decY s, decodeRepNat_equation s (decR s) (sqrtRatioM1_one_of_fst hc.1)⟩
      else none := by
  unfold decodeRepNat
  rw [ite_eq_left h]
  rfl

/-- **The rejection reasons of decoding** (RFC 9496 §4.3.1): `decodeRepNat s = none` iff `s ≥ p`,
`s` is negative, `v u2²` has no inverse square root (`was_square = false`), the decoded `x y` is
negative, or the decoded `y` is `0`. -/
theorem decodeRepNat_eq_none_iff (s : ℕ) :
    decodeRepNat s = none ↔
      p ≤ s ∨ (s : ZMod p).IsNeg ∨
        let s' : ZMod p := s
        let u1 := 1 - s' ^ 2
        let u2 := 1 + s' ^ 2
        let v := -(d * u1 ^ 2) - u2 ^ 2
        let r := (sqrtRatioM1 1 (v * u2 ^ 2)).2
        let x := (2 * s' * (r * u2)).abs
        let y := u1 * (r * (r * u2) * v)
        (sqrtRatioM1 1 (v * u2 ^ 2)).1 = false ∨ (x * y).IsNeg ∨ y = 0 := by
  change decodeRepNat s = none ↔ p ≤ s ∨ (s : ZMod p).IsNeg ∨
    (sqrtRatioM1 1 (decW s)).1 = false ∨ (decX s * decY s).IsNeg ∨ decY s = 0
  by_cases h : s < p ∧ ¬ (s : ZMod p).IsNeg
  · rw [decodeRepNat_of_lt h]
    by_cases hc : (sqrtRatioM1 1 (decW s)).1 = true ∧ ¬ (decX s * decY s).IsNeg ∧ decY s ≠ 0
    · rw [dite_eq_left hc]
      refine iff_of_false (by simp) ?_
      rintro (h' | h' | h' | h' | h')
      · omega
      · exact h.2 h'
      · rw [hc.1] at h'
        exact absurd h' (by decide)
      · exact hc.2.1 h'
      · exact hc.2.2 h'
    · rw [dite_eq_right hc]
      refine iff_of_true rfl (Or.inr (Or.inr ?_))
      rw [not_and_or, not_and_or, not_not, not_not] at hc
      rcases hc with hc | hc | hc
      · exact Or.inl (Bool.eq_false_iff.mpr hc)
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
  · rw [decodeRepNat_of_not h]
    refine iff_of_true rfl ?_
    rw [not_and_or, not_not] at h
    rcases h with h | h
    · exact Or.inl (not_lt.mp h)
    · exact Or.inr (Or.inl h)

/-- **The meaning of decoding**: `decodeRepNat s = some P` iff `s < p` is non-negative and `P` is
the point with `y = (1 - s²) / (1 + s²)`, `x` and `x y` non-negative and `y ≠ 0`. -/
theorem decodeRepNat_eq_some_iff {s : ℕ} {P : edwards.Point} :
    decodeRepNat s = some P ↔
      s < p ∧ ¬ (s : ZMod p).IsNeg ∧
        P.y = (1 - (s : ZMod p) ^ 2) / (1 + (s : ZMod p) ^ 2) ∧
        ¬ P.x.IsNeg ∧ ¬ (P.x * P.y).IsNeg ∧ P.y ≠ 0 := by
  constructor
  · intro h
    by_cases hs : s < p ∧ ¬ (s : ZMod p).IsNeg
    · rw [decodeRepNat_of_lt hs] at h
      by_cases hc : (sqrtRatioM1 1 (decW s)).1 = true ∧ ¬ (decX s * decY s).IsNeg ∧ decY s ≠ 0
      · rw [dite_eq_left hc, Option.some.injEq] at h
        subst h
        refine ⟨hs.1, hs.2, ?_, ZMod.not_isNeg_abs _, hc.2.1, hc.2.2⟩
        exact Proofs.decodeNat_y_eq s (decR s) (sqrtRatioM1_one_of_fst hc.1)
      · rw [dite_eq_right hc] at h
        cases h
    · rw [decodeRepNat_of_not hs] at h
      cases h
  · rintro ⟨hs, hneg, hy, hx, hxy, hy0⟩
    have hu2 : decU2 s ≠ 0 := by
      intro h
      apply hy0
      rw [hy]
      change decU1 s / decU2 s = 0
      rw [h, div_zero]
    have hyu : P.y * (1 + (s : ZMod p) ^ 2) = 1 - (s : ZMod p) ^ 2 := (eq_div_iff hu2).mp hy
    have hv : decV s ≠ 0 := Proofs.decodeNat_v_ne_zero s
    have hxv := Proofs.x_sq_mul_v_eq (s : ZMod p) P.equation hyu
    have hW0 : decW s ≠ 0 := mul_ne_zero hv (pow_ne_zero 2 hu2)
    have hWsq : IsSquare (decW s) := by
      by_cases hx0 : P.x = 0
      · have hs0 : (s : ZMod p) = 0 := by
          rw [hx0] at hxv
          have h4 : (4 : ZMod p) * (s : ZMod p) ^ 2 = 0 := by linear_combination -hxv
          exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp h4).resolve_left four_ne_zero)
        refine ⟨sqrtAdMinusOne, ?_⟩
        unfold decW decV decU1 decU2
        rw [hs0]
        linear_combination -sqrtAdMinusOne_sq - d * a_def
      · refine ⟨2 * (s : ZMod p) * decU2 s / P.x, ?_⟩
        unfold decW decV decU1 decU2
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx0 hx0)]
        linear_combination (1 + (s : ZMod p) ^ 2) ^ 2 * hxv
    have hfst : (sqrtRatioM1 1 (decW s)).1 = true := (sqrtRatioM1_one_fst_iff _).mpr ⟨hW0, hWsq⟩
    have hr : decW s * decR s ^ 2 = 1 := sqrtRatioM1_one_of_fst hfst
    have hyd : decY s = P.y := (Proofs.decodeNat_y_eq s (decR s) hr).trans hy.symm
    have hxd : decX s = P.x := by
      refine ZMod.eq_of_sq_eq_of_isNeg_iff ?_
        (iff_of_false (ZMod.not_isNeg_abs _) hx)
      exact mul_right_cancel₀ hv ((Proofs.decodeNat_x_sq_mul_v s (decR s) hr).trans hxv.symm)
    rw [decodeRepNat_of_lt ⟨hs, hneg⟩,
      dite_eq_left ⟨hfst, by rw [hxd, hyd]; exact hxy, by rw [hyd]; exact hy0⟩]
    exact congrArg some (Point.ext hxd hyd)

/-- The decoded point has `y = (1 - s²) / (1 + s²)`. -/
theorem decodeRepNat_y {s : ℕ} {P : edwards.Point} (h : decodeRepNat s = some P) :
    P.y = (1 - (s : ZMod p) ^ 2) / (1 + (s : ZMod p) ^ 2) :=
  (decodeRepNat_eq_some_iff.mp h).2.2.1

theorem decodeRepNat_y_ne_zero {s : ℕ} {P : edwards.Point} (h : decodeRepNat s = some P) :
    P.y ≠ 0 :=
  (decodeRepNat_eq_some_iff.mp h).2.2.2.2.2

/-- `1 + s² ≠ 0` for a decoded `s`. -/
theorem one_add_sq_ne_zero_of_decodeRepNat {s : ℕ} {P : edwards.Point}
    (h : decodeRepNat s = some P) :
    1 + (s : ZMod p) ^ 2 ≠ 0 := by
  intro h0
  apply decodeRepNat_y_ne_zero h
  rw [decodeRepNat_y h, h0, div_zero]

/-- The decoded point has `y ≠ -1`: it is never `(0, -1)`. -/
theorem decodeRepNat_y_ne_neg_one {s : ℕ} {P : edwards.Point} (h : decodeRepNat s = some P) :
    P.y ≠ -1 := by
  intro h1
  have hu2 := one_add_sq_ne_zero_of_decodeRepNat h
  have hy := decodeRepNat_y h
  rw [h1, eq_div_iff hu2] at hy
  have h2 : (2 : ZMod p) = 0 := by linear_combination -hy
  exact two_ne_zero h2

/-- **The decoded point is even**: `1 - y² = (2 s / (1 + s²))²`. -/
theorem even_decodeRepNat {s : ℕ} {P : edwards.Point} (h : decodeRepNat s = some P) : Even P :=
  even_of_y_eq_div (one_add_sq_ne_zero_of_decodeRepNat h) (decodeRepNat_y h)

/-- `decodeRepNat 0 = some 0`: `0` decodes to the identity. -/
theorem decodeRepNat_zero : decodeRepNat 0 = some 0 := by
  rw [decodeRepNat_eq_some_iff, zero_x, zero_y, Nat.cast_zero]
  refine ⟨p_pos, ZMod.not_isNeg_zero, by norm_num, ZMod.not_isNeg_zero, ?_, one_ne_zero⟩
  rw [zero_mul]
  exact ZMod.not_isNeg_zero

/-! ### Encoding -/

/-! The intermediate quantities of RFC 9496 §4.3.2 after `z_inv = 1`, internal: the rotated
point `(xRot, yRot)` (`(y √-1, x √-1)` when `x y` is negative), its canonical `y`-coordinate
`yC` (negated when `xRot` is negative), and the denominator `denC`. -/

private noncomputable def encW (P : edwards.Point) : ZMod p :=
  (1 + P.y) * (1 - P.y) * (P.x * P.y) ^ 2

private noncomputable def encI (P : edwards.Point) : ZMod p := (sqrtRatioM1 1 (encW P)).2

private noncomputable def xRot (P : edwards.Point) : ZMod p :=
  if (P.x * P.y).IsNeg then P.y * sqrtM1 else P.x

private noncomputable def yRot (P : edwards.Point) : ZMod p :=
  if (P.x * P.y).IsNeg then P.x * sqrtM1 else P.y

private noncomputable def yC (P : edwards.Point) : ZMod p :=
  if (xRot P).IsNeg then -yRot P else yRot P

private noncomputable def denC (P : edwards.Point) : ZMod p :=
  if (P.x * P.y).IsNeg then encI P * ((1 + P.y) * (1 - P.y)) * invsqrtAMinusD
  else encI P * (P.x * P.y)

theorem encodeRepNat_lt (P : edwards.Point) : encodeRepNat P < p := by
  rw [encodeRepNat_eq]
  exact ZMod.val_lt _

/-- An encoding is a non-negative field element. -/
theorem not_isNeg_encodeRepNat (P : edwards.Point) : ¬ ((encodeRepNat P : ℕ) : ZMod p).IsNeg := by
  rw [encodeRepNat_eq]
  dsimp only
  rw [ZMod.natCast_zmod_val]
  exact ZMod.not_isNeg_abs _

/-- The 4-torsion (`x y = 0`) encodes to `0`. -/
theorem encodeRepNat_of_mul_eq_zero {P : edwards.Point} (h : P.x * P.y = 0) : encodeRepNat P
    = 0 := by
  rw [encodeRepNat_eq]
  dsimp only
  rw [h, show (1 + P.y) * (1 - P.y) * (0 : ZMod p) ^ 2 = 0 by ring, sqrtRatioM1_one_zero]
  simp [ZMod.not_isNeg_zero, ZMod.abs_zero]

theorem encodeRepNat_zero : encodeRepNat 0 = 0 :=
  encodeRepNat_of_mul_eq_zero (by rw [zero_x, zero_mul])

/-- `W I² = 1` for an even point with `x y ≠ 0`: `W = (1 + y)(1 - y)(x y)²` is a nonzero square. -/
private theorem encW_mul_sq_eq_one {P : edwards.Point} (hP : Even P) (hxy : P.x * P.y ≠ 0) :
    encW P * encI P ^ 2 = 1 := by
  have hx : P.x ≠ 0 := fun h => hxy (by rw [h, zero_mul])
  have hW0 : encW P ≠ 0 := by
    unfold encW
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero 2 hxy)
    · intro h
      exact y_ne_neg_one_of_x_ne_zero P.equation hx (by linear_combination h)
    · intro h
      exact y_ne_one_of_x_ne_zero P.equation hx (by linear_combination -h)
  obtain ⟨q, hq⟩ := (even_iff_isSquare P).mp hP
  exact sqrtRatioM1_one_of_isSquare hW0 (Proofs.enc_W_isSquare hq)

/-- `encodeRepNat` after `z_inv = 1`: `|denC (1 - yC)|`. -/
private theorem encodeRepNat_eq_of_mul_sq_eq_one {P : edwards.Point}
    (hW : encW P * encI P ^ 2 = 1) :
    encodeRepNat P = (denC P * (1 - yC P)).abs.val := by
  rw [encodeRepNat_eq]
  dsimp only
  have hz : (sqrtRatioM1 1 ((1 + P.y) * (1 - P.y) * (P.x * P.y) ^ 2)).2 * ((1 + P.y) * (1 - P.y)) *
      ((sqrtRatioM1 1 ((1 + P.y) * (1 - P.y) * (P.x * P.y) ^ 2)).2 * (P.x * P.y)) * (P.x * P.y) =
        1 :=
    Proofs.enc_zInv_eq_one P.x P.y _ hW
  rw [hz, mul_one, mul_one]
  rfl

/-- The squared canonical `y`: `-x²` after a rotation, `y²` otherwise. -/
private theorem yC_sq (P : edwards.Point) :
    yC P ^ 2 = if (P.x * P.y).IsNeg then -(P.x ^ 2) else P.y ^ 2 := by
  unfold yC yRot
  split_ifs
  · rw [neg_sq, mul_pow, sqrtM1_sq]; ring
  · exact neg_sq _
  · rw [mul_pow, sqrtM1_sq]; ring
  · rfl

/-- `denC² (1 - yC²) = 1`. -/
private theorem denC_sq {P : edwards.Point} (hW : encW P * encI P ^ 2 = 1) :
    denC P ^ 2 * (1 - yC P ^ 2) = 1 := by
  have hc : -P.x ^ 2 + P.y ^ 2 = 1 + d * P.x ^ 2 * P.y ^ 2 := by
    have h := P.equation
    unfold Equation at h
    rw [edwards_a_eq_neg_one, edwards_d] at h
    linear_combination h
  have hW' : (1 + P.y) * (1 - P.y) * (P.x * P.y) ^ 2 * encI P ^ 2 = 1 := hW
  rw [yC_sq]
  unfold denC
  split_ifs
  · have hK : (invsqrtAMinusD : ZMod p) ^ 2 * (-1 - d) = 1 := by
      rw [← a_def]
      exact invsqrtAMinusD_sq_mul
    have := Proofs.enc_den1_sq d sqrtM1 P.x P.y (encI P) invsqrtAMinusD sqrtM1_sq hc hW' hK
    rwa [mul_pow P.x, sqrtM1_sq, mul_neg, mul_one] at this
  · exact Proofs.enc_den2_sq P.x P.y (encI P) hW'

/-- `(y √-1, x √-1)` is on the model with `(x, y)`. -/
private theorem equation_rot {x y : ZMod p} (h : edwards.Equation x y) :
    edwards.Equation (y * sqrtM1) (x * sqrtM1) :=
  equation_rot_of_a_eq_neg_one edwards_a_eq_neg_one sqrtM1_sq h

/-- **The canonical representative**: the class of `P` contains the point `(|xRot|, yC)`. -/
private theorem exists_canon (P : edwards.Point) :
    ∃ C : edwards.Point, edwards.Rel P C ∧ C.x = (xRot P).abs ∧ C.y = yC P := by
  unfold yC xRot yRot
  by_cases hrot : (P.x * P.y).IsNeg
  · rw [ite_eq_left hrot, ite_eq_left hrot]
    by_cases hflip : (P.y * sqrtM1).IsNeg
    · refine ⟨⟨-(P.y * sqrtM1), -(P.x * sqrtM1), equation_neg_neg (equation_rot P.equation)⟩,
        ?_, ?_, ?_⟩
      · rw [rel_iff_coords]
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact (ZMod.abs_of_isNeg hflip).symm
      · exact (ite_eq_left hflip).symm
    · refine ⟨⟨P.y * sqrtM1, P.x * sqrtM1, equation_rot P.equation⟩, ?_, ?_, ?_⟩
      · rw [rel_iff_coords]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact (ZMod.abs_of_not_isNeg hflip).symm
      · exact (ite_eq_right hflip).symm
  · rw [ite_eq_right hrot, ite_eq_right hrot]
    by_cases hflip : P.x.IsNeg
    · refine ⟨⟨-P.x, -P.y, equation_neg_neg P.equation⟩, ?_, ?_, ?_⟩
      · rw [rel_iff_coords]
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact (ZMod.abs_of_isNeg hflip).symm
      · exact (ite_eq_left hflip).symm
    · refine ⟨P, rel_refl P, ?_, ?_⟩
      · exact (ZMod.abs_of_not_isNeg hflip).symm
      · exact (ite_eq_right hflip).symm

private theorem yC_ne_zero {P : edwards.Point} (hxy : P.x * P.y ≠ 0) : yC P ≠ 0 := by
  have hx : P.x ≠ 0 := fun h => hxy (by rw [h, zero_mul])
  have hy : P.y ≠ 0 := fun h => hxy (by rw [h, mul_zero])
  unfold yC yRot
  split_ifs
  · exact neg_ne_zero.mpr (mul_ne_zero hx sqrtM1_ne_zero)
  · exact neg_ne_zero.mpr hy
  · exact mul_ne_zero hx sqrtM1_ne_zero
  · exact hy

/-- The canonical representative has `x y` non-negative. -/
private theorem not_isNeg_abs_xRot_mul_yC (P : edwards.Point) :
    ¬ ((xRot P).abs * yC P).IsNeg := by
  have hprod : (xRot P).abs * yC P = xRot P * yRot P := by
    unfold yC
    split_ifs with h
    · rw [ZMod.abs_of_isNeg h]; ring
    · rw [ZMod.abs_of_not_isNeg h]
  rw [hprod]
  unfold xRot yRot
  split_ifs with h
  · rw [show P.y * sqrtM1 * (P.x * sqrtM1) = -(P.x * P.y) by
      linear_combination (P.x * P.y) * sqrtM1_sq]
    exact ZMod.not_isNeg_neg_of_isNeg h
  · exact h

/-- **Encoding then decoding**: `decodeRepNat (encodeRepNat P)` is the canonical representative of
the class of an even point `P`. -/
theorem decodeRepNat_encodeRepNat {P : edwards.Point} (hP : Even P) :
    ∃ Q : edwards.Point, decodeRepNat (encodeRepNat P) = some Q ∧ edwards.Rel P Q := by
  by_cases hxy : P.x * P.y = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [encodeRepNat_of_mul_eq_zero hxy, decodeRepNat_zero]
    · rw [rel_iff_sub_mem, sub_zero, TwistedEdwardsModel.mem_torsionBy_four_iff]
      exact mul_eq_zero.mp hxy
  · obtain ⟨C, hrel, hCx, hCy⟩ := exists_canon P
    have hW := encW_mul_sq_eq_one hP hxy
    have hD := denC_sq hW
    have hS := Proofs.mul_one_sub_sq_eq_div hD
    have hy1 : 1 + yC P ≠ 0 := by
      intro h
      have h' : yC P = -1 := by linear_combination h
      rw [h'] at hD
      exact one_ne_zero (by linear_combination -hD)
    refine ⟨C, ?_, hrel⟩
    rw [decodeRepNat_eq_some_iff, encodeRepNat_eq_of_mul_sq_eq_one hW, ZMod.natCast_zmod_val]
    refine ⟨ZMod.val_lt _, ZMod.not_isNeg_abs _, ?_, ?_, ?_, ?_⟩
    · rw [hCy, ZMod.abs_sq]
      exact (Proofs.div_eq_of_sq_eq_div hy1 hS).symm
    · rw [hCx]
      exact ZMod.not_isNeg_abs _
    · rw [hCx, hCy]
      exact not_isNeg_abs_xRot_mul_yC P
    · rw [hCy]
      exact yC_ne_zero hxy

/-- **Decoding then encoding**: a decoded point encodes to its encoding. -/
theorem encodeRepNat_decodeRepNat {s : ℕ} {P : edwards.Point} (h : decodeRepNat s = some P) :
    encodeRepNat P = s := by
  obtain ⟨hs, hneg, hy, hx, hxy, hy0⟩ := decodeRepNat_eq_some_iff.mp h
  have hu2 := one_add_sq_ne_zero_of_decodeRepNat h
  have hyu : P.y * (1 + (s : ZMod p) ^ 2) = 1 - (s : ZMod p) ^ 2 := (eq_div_iff hu2).mp hy
  by_cases hx0 : P.x = 0
  · have hy1 : P.y = 1 :=
      (y_eq_one_or_eq_neg_one_of_x_eq_zero P.equation hx0).resolve_right
        (decodeRepNat_y_ne_neg_one h)
    have hs0 : (s : ZMod p) = 0 := by
      rw [hy1, one_mul] at hyu
      have h2 : (2 : ZMod p) * (s : ZMod p) ^ 2 = 0 := by linear_combination hyu
      exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
    have hs' : s = 0 := by
      rw [← ZMod.val_cast_of_lt hs, hs0, ZMod.val_zero]
    rw [hs', encodeRepNat_of_mul_eq_zero (by rw [hx0, zero_mul])]
  · have hxy0 : P.x * P.y ≠ 0 := mul_ne_zero hx0 hy0
    have hW := encW_mul_sq_eq_one (even_decodeRepNat h) hxy0
    have hrot : xRot P = P.x := ite_eq_right hxy
    have hyC : yC P = P.y := by
      unfold yC
      rw [hrot, ite_eq_right hx]
      exact ite_eq_right hxy
    have hD := denC_sq hW
    rw [hyC] at hD
    have hS := Proofs.mul_one_sub_sq_eq_div hD
    have h1y : 1 + P.y ≠ 0 := fun h' =>
      y_ne_neg_one_of_x_ne_zero P.equation hx0 (by linear_combination h')
    have hs2 : (s : ZMod p) ^ 2 = (1 - P.y) / (1 + P.y) := by
      rw [eq_div_iff h1y]
      linear_combination hyu
    rw [encodeRepNat_eq_of_mul_sq_eq_one hW, hyC]
    have hSs : (denC P * (1 - P.y)).abs = (s : ZMod p) :=
      ZMod.eq_of_sq_eq_of_isNeg_iff (by rw [ZMod.abs_sq, hS, hs2])
        (iff_of_false (ZMod.not_isNeg_abs _) hneg)
    rw [hSs, ZMod.val_cast_of_lt hs]

/-- **Invariance on classes**: representatives of one class have the same encoding. -/
theorem encodeRepNat_rel {P Q : edwards.Point} (hP : Even P) (h : edwards.Rel P Q) :
    encodeRepNat P = encodeRepNat Q := by
  have hQ : Even Q := even_of_rel hP h
  obtain ⟨Q₁, h₁, r₁⟩ := decodeRepNat_encodeRepNat hP
  obtain ⟨Q₂, h₂, r₂⟩ := decodeRepNat_encodeRepNat hQ
  obtain ⟨-, -, -, hx₁, hxy₁, hy₁⟩ := decodeRepNat_eq_some_iff.mp h₁
  obtain ⟨-, -, -, hx₂, hxy₂, hy₂⟩ := decodeRepNat_eq_some_iff.mp h₂
  have hQ₁₂ : Q₁ = Q₂ :=
    eq_of_rel_of_canonical (rel_trans (rel_trans (rel_symm r₁) h) r₂) hx₁ hxy₁ hy₁
      (decodeRepNat_y_ne_neg_one h₁) hx₂ hxy₂ hy₂ (decodeRepNat_y_ne_neg_one h₂)
  rw [← encodeRepNat_decodeRepNat h₁, ← encodeRepNat_decodeRepNat h₂, hQ₁₂]

/-- **The encoding separates the classes**: two even points have the same encoding iff they are
in the same class. -/
theorem encodeRepNat_eq_iff {P Q : edwards.Point} (hP : Even P) (hQ : Even Q) :
    encodeRepNat P = encodeRepNat Q ↔ edwards.Rel P Q := by
  constructor
  · intro h
    obtain ⟨Q₁, h₁, r₁⟩ := decodeRepNat_encodeRepNat hP
    obtain ⟨Q₂, h₂, r₂⟩ := decodeRepNat_encodeRepNat hQ
    rw [h, h₂, Option.some.injEq] at h₁
    exact rel_trans r₁ (h₁ ▸ rel_symm r₂)
  · exact encodeRepNat_rel hP

/-! ### The basepoint -/

/-- **The encoding of the basepoint** (RFC 9496 §A.1, dalek's `RISTRETTO_BASEPOINT_COMPRESSED`):
the bytes `e2 f2 ae 0a 6a bc 4e 71 a8 84 a9 61 c5 00 51 5f 58 e3 0b 6a a5 82 dd 8d b6 a6 59 45
e0 8d 2d 76`, little-endian. -/
theorem encodeRepNat_basepoint : encodeRepNat curve25519.basepoint =
    53453403443306840533278073560698739391446669128918427283046925944918568268514 :=
  Proofs.encodeRepNat_of_basepoint_coords _ basepoint_x_eq basepoint_y_eq

/-! ### RFC 9496 on 32-byte strings -/

/-- RFC 9496 §4.3.2 `Encode` of a representative: the 32 little-endian bytes of
`encodeRepNat`. -/
@[expose] noncomputable def encodeRep (P : edwards.Point) : Vector UInt8 32 :=
  encodeLittleEndian 32 (encodeRepNat P)

/-- RFC 9496 §4.3.1 `Decode` of 32 bytes to a representative: `decodeRepNat` of their value. -/
@[expose] noncomputable def decodeRep (b : Vector UInt8 32) : Option edwards.Point :=
  decodeRepNat (decodeLittleEndian b)

theorem encodeRepNat_lt_two_pow_256 (P : edwards.Point) : encodeRepNat P < 256 ^ 32 :=
  (encodeRepNat_lt P).trans (p_lt_two_pow_255.trans (by norm_num))

/-- `b` is the encoding of `P` iff its value is `encodeRepNat P`. -/
theorem eq_encodeRep_iff (b : Vector UInt8 32) (P : edwards.Point) :
    b = encodeRep P ↔ decodeLittleEndian b = encodeRepNat P :=
  eq_encodeLittleEndian_iff b (encodeRepNat_lt_two_pow_256 P)

theorem decodeLittleEndian_encodeRep (P : edwards.Point) :
    decodeLittleEndian (encodeRep P) = encodeRepNat P := by
  rw [encodeRep, decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (encodeRepNat_lt_two_pow_256 P)]

end Ristretto

end curve25519
