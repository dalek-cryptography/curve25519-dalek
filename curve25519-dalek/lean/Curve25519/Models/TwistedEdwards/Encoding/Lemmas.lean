/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Models.TwistedEdwards.Encoding.Defs
public import Curve25519.ToEllipticCurve.TwistedEdwards.Lemmas
import all Curve25519.Models.TwistedEdwards.Encoding.Defs
import Mathlib.Tactic.Ring
public section

/-! # Point encoding of a twisted Edwards model over `ZMod p`: characterising lemmas

The audited statements about `TwistedEdwardsModel.encode` and `TwistedEdwardsModel.decode`
(RFC 8032 §5.1.2–5.1.3), for a complete model `E` over `ZMod p` and a width `bits` with
`p < 2 ^ bits`:

* the shape of an encoding: `encode_lt`, `encode_mod_two_pow` (the low `bits` bits are `y.val`),
  `encode_div_two_pow` (bit `bits` is the sign of `x`), `encode_injective`, `encode_zero`;
* the meaning of strict decoding: `decode_eq_some_iff` (`decode n = some P` iff `n` has at most
  `bits + 1` bits, its low `bits` bits are a canonical `y`, `P.y` is that `y`, and the sign of
  `P.x` is bit `bits`), `decode_eq_some_iff_encode_eq` (`decode n = some P ↔ encode P = n`),
  `decode_encode`, `encode_decode`, `decode_isSome_iff`, and `decode_eq_none_iff` (the
  rejection reasons: too many bits, `y ≥ p`, `xSq y` not a square, or `y² = 1` with the sign
  bit set, RFC 8032's "`x = 0` and `x_0 = 1`").

Also the uniqueness of a point given `y` and the sign of `x` (`eq_of_y_eq_of_isNeg_iff`, from
the solved equation `x ^ 2 = E.xSq y` of `Curve25519.ToEllipticCurve.TwistedEdwards.Lemmas`),
the heart of both `decode_eq_some_iff` and `encode_injective`. These lemmas are the whole
interface to the hidden `decode`. -/

namespace TwistedEdwardsModel

/-! ### Models over `ZMod p` -/

variable {p : ℕ} [Fact p.Prime] {E : TwistedEdwardsModel (ZMod p)} {bits : ℕ}

/-- `p` is odd for a complete model over `ZMod p` (`2 ≠ 0`). -/
theorem mod_two_eq_one_of_isComplete (E : TwistedEdwardsModel (ZMod p)) [E.IsComplete] :
    p % 2 = 1 :=
  ZMod.mod_two_eq_one_of_two_ne_zero (IsComplete.two_ne_zero (E := E))

/-- **Uniqueness**: a point of a complete model is determined by `y` and the sign of `x`. -/
theorem eq_of_y_eq_of_isNeg_iff [E.IsComplete] {P Q : E.Point} (hy : P.y = Q.y)
    (hs : P.x.IsNeg ↔ Q.x.IsNeg) : P = Q :=
  have : Fact (p % 2 = 1) := ⟨mod_two_eq_one_of_isComplete E⟩
  Point.ext (ZMod.eq_of_sq_eq_of_isNeg_iff (sq_x_eq_sq_x_of_y_eq hy) hs) hy

/-! ### The encoding -/

section encode

variable (E bits)

/-- The encoding of the zero `(0, 1)` is `1`. -/
theorem encode_zero [E.IsComplete] : encode E bits 0 = 1 := by
  unfold encode
  rw [zero_x, zero_y, ite_eq_right ZMod.not_isNeg_zero, mul_zero, add_zero, ZMod.val_one]

variable [hbits : Fact (p < 2 ^ bits)]

private theorem val_y_lt_two_pow (P : E.Point) : P.y.val < 2 ^ bits :=
  lt_of_lt_of_le (ZMod.val_lt _) hbits.out.le

/-- An encoding has at most `bits + 1` bits. -/
theorem encode_lt (P : E.Point) : encode E bits P < 2 ^ (bits + 1) := by
  unfold encode
  have := val_y_lt_two_pow E bits P
  rw [pow_succ]
  split_ifs <;> omega

/-- The low `bits` bits of an encoding are `y.val`. -/
theorem encode_mod_two_pow (P : E.Point) : encode E bits P % 2 ^ bits = P.y.val := by
  unfold encode
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val_y_lt_two_pow E bits P)]

/-- Bit `bits` of an encoding is the sign of `x`. -/
theorem encode_div_two_pow (P : E.Point) :
    encode E bits P / 2 ^ bits = if P.x.IsNeg then 1 else 0 := by
  unfold encode
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos bits),
    Nat.div_eq_of_lt (val_y_lt_two_pow E bits P), zero_add]

/-- **Injectivity**: distinct points have distinct encodings. -/
theorem encode_injective [E.IsComplete] : Function.Injective (encode E bits) := by
  intro P Q h
  have hy : P.y = Q.y := ZMod.val_injective p
    (by rw [← encode_mod_two_pow E bits P, ← encode_mod_two_pow E bits Q, h])
  have hs : (if P.x.IsNeg then 1 else 0) = if Q.x.IsNeg then 1 else 0 := by
    rw [← encode_div_two_pow E bits P, ← encode_div_two_pow E bits Q, h]
  refine eq_of_y_eq_of_isNeg_iff hy ?_
  by_cases hP : P.x.IsNeg <;> by_cases hQ : Q.x.IsNeg
  · exact iff_of_true hP hQ
  · rw [ite_eq_left hP, ite_eq_right hQ] at hs
    exact absurd hs one_ne_zero
  · rw [ite_eq_right hP, ite_eq_left hQ] at hs
    exact absurd hs zero_ne_one
  · exact iff_of_false hP hQ

end encode

/-! ### Strict decoding -/

section decode

variable (E bits) [E.IsComplete]

/-- **The meaning of strict decoding**: `decode n = some P` iff `n < 2 ^ (bits + 1)`, the low
`bits` bits of `n` are a canonical `y` (below `p`), `P.y` is that `y`, and the sign of `P.x` is
bit `bits` of `n`. -/
theorem decode_eq_some_iff {n : ℕ} {P : E.Point} :
    decode E bits n = some P ↔
      n < 2 ^ (bits + 1) ∧ n % 2 ^ bits < p ∧ P.y = ((n % 2 ^ bits : ℕ) : ZMod p) ∧
        (P.x.IsNeg ↔ n / 2 ^ bits = 1) := by
  unfold decode
  split_ifs with hn hx
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨hn.1, hn.2, rfl, (Classical.choose_spec hx).2⟩
    · rintro ⟨-, -, hy, hs⟩
      refine eq_of_y_eq_of_isNeg_iff hy.symm ?_
      rw [hs]
      exact (Classical.choose_spec hx).2
  · refine iff_of_false (by simp) ?_
    rintro ⟨-, -, hy, hs⟩
    exact hx ⟨P.x, hy ▸ P.equation, hs⟩
  · refine iff_of_false (by simp) ?_
    rintro ⟨h1, h2, -, -⟩
    exact hn ⟨h1, h2⟩

/-- **The rejection reasons**: strict decoding fails iff `n` has more than `bits + 1` bits, or
the low `bits` bits are not a canonical `y` (`y ≥ p`), or `xSq y` is not a square (no point has
this `y`), or `y² = 1` (the only point is `(0, y)`) while the sign bit is set. -/
theorem decode_eq_none_iff {n : ℕ} :
    decode E bits n = none ↔
      2 ^ (bits + 1) ≤ n ∨ p ≤ n % 2 ^ bits ∨
        ¬ IsSquare (E.xSq ((n % 2 ^ bits : ℕ) : ZMod p)) ∨
        (((n % 2 ^ bits : ℕ) : ZMod p) ^ 2 = 1 ∧ n / 2 ^ bits = 1) := by
  have : Fact (p % 2 = 1) := ⟨mod_two_eq_one_of_isComplete E⟩
  unfold decode
  split_ifs with hn hx
  · refine iff_of_false (by simp) ?_
    rintro (h | h | h | ⟨h1, h2⟩)
    · exact absurd hn.1 (not_lt.mpr h)
    · exact absurd hn.2 (not_lt.mpr h)
    · exact h (isSquare_xSq_iff.mpr ⟨_, (Classical.choose_spec hx).1⟩)
    · have hx0 := x_eq_zero_of_y_sq_eq_one (Classical.choose_spec hx).1 h1
      exact ZMod.not_isNeg_zero (hx0 ▸ (Classical.choose_spec hx).2.mpr h2)
  · refine iff_of_true rfl ?_
    by_cases hsq : IsSquare (E.xSq ((n % 2 ^ bits : ℕ) : ZMod p))
    · obtain ⟨x, hxE⟩ := isSquare_xSq_iff.mp hsq
      by_cases hy1 : ((n % 2 ^ bits : ℕ) : ZMod p) ^ 2 = 1
      · by_cases hs : n / 2 ^ bits = 1
        · exact Or.inr (Or.inr (Or.inr ⟨hy1, hs⟩))
        · exact absurd
            ⟨0, by unfold Equation; rw [hy1]; ring, iff_of_false ZMod.not_isNeg_zero hs⟩ hx
      · have hx0 : x ≠ 0 := fun h0 => hy1 (y_sq_eq_one_of_x_eq_zero hxE h0)
        exfalso
        apply hx
        by_cases hs : n / 2 ^ bits = 1
        · rcases ZMod.isNeg_or_isNeg_neg hx0 with h | h
          · exact ⟨x, hxE, iff_of_true h hs⟩
          · exact ⟨-x, equation_neg hxE, iff_of_true h hs⟩
        · by_cases h : x.IsNeg
          · exact ⟨-x, equation_neg hxE, iff_of_false (ZMod.not_isNeg_neg_of_isNeg h) hs⟩
          · exact ⟨x, hxE, iff_of_false h hs⟩
    · exact Or.inr (Or.inr (Or.inl hsq))
  · refine iff_of_true rfl ?_
    rw [not_and_or, not_lt, not_lt] at hn
    rcases hn with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

variable [Fact (p < 2 ^ bits)]

/-- **Strict decoding is the inverse of encoding**: `decode n = some P` iff `encode P = n`. -/
theorem decode_eq_some_iff_encode_eq {n : ℕ} {P : E.Point} :
    decode E bits n = some P ↔ encode E bits P = n := by
  rw [decode_eq_some_iff]
  constructor
  · rintro ⟨hn, hlt, hy, hs⟩
    have hval : P.y.val = n % 2 ^ bits := by rw [hy, ZMod.val_cast_of_lt hlt]
    have hdiv : (if P.x.IsNeg then 1 else 0) = n / 2 ^ bits := by
      have h2 : n / 2 ^ bits < 2 := Nat.div_lt_of_lt_mul (by rwa [pow_succ] at hn)
      split_ifs with h
      · exact (hs.mp h).symm
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp h2) with h0 | h1
        · exact h0.symm
        · exact absurd (hs.mpr h1) h
    unfold encode
    rw [hval, hdiv]
    exact Nat.mod_add_div n (2 ^ bits)
  · rintro rfl
    refine ⟨encode_lt E bits P, ?_, ?_, ?_⟩
    · rw [encode_mod_two_pow]
      exact ZMod.val_lt _
    · rw [encode_mod_two_pow, ZMod.natCast_zmod_val]
    · rw [encode_div_two_pow]
      split_ifs with h
      · exact iff_of_true h rfl
      · exact iff_of_false h (by decide)

/-- Decoding an encoding gives the point back. -/
theorem decode_encode (P : E.Point) : decode E bits (encode E bits P) = some P :=
  (decode_eq_some_iff_encode_eq E bits).mpr rfl

/-- Encoding a decoded point gives the input back: strict decoding accepts only canonical
encodings. -/
theorem encode_decode {n : ℕ} {P : E.Point} (h : decode E bits n = some P) :
    encode E bits P = n :=
  (decode_eq_some_iff_encode_eq E bits).mp h

/-- Strict decoding succeeds exactly on the encodings. -/
theorem decode_isSome_iff {n : ℕ} : (decode E bits n).isSome ↔ ∃ P, encode E bits P = n := by
  rw [Option.isSome_iff_exists]
  simp only [decode_eq_some_iff_encode_eq]

end decode

end TwistedEdwardsModel
