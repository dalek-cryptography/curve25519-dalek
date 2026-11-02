/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
import Curve25519.Proofs.Ristretto.Algebra
import Mathlib.Tactic.LinearCombination
public section

/-! # The ristretto255 encoding (RFC 9496 §4.2, §4.3.1, §4.3.2): definitions

The square-root helper `sqrtRatioM1 u v` (RFC 9496 §4.2 `SQRT_RATIO_M1`): `(true, √(u/v))` when
`v ≠ 0` and `u/v` is a square, `(true, 0)` when `u = v = 0`, `(false, 0)` when `u ≠ 0 = v`, and
`(false, √(√-1 · u/v))` otherwise, the root being non-negative
(`ZMod.IsNeg`); it is exposed, with its characterisation `sqrtRatioM1_spec` (all cases in one
statement, for reading) and the uniqueness lemmas `sqrtRatioM1_eq_of_mul_sq_eq`,
`sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul`, `sqrtRatioM1_zero_left`,
`sqrtRatioM1_zero_right` (through which the dalek field specification `sqrt_ratio_i_spec`
connects to it). Its non-square branch rests on
`sqrtM1` not being a square (`not_isSquare_sqrtM1`, `p ≡ 5 (mod 8)`).

The representative-level codec, hidden: `decodeRep s` (§4.3.1, the Edwards point encoded by the
canonical non-negative field element `s < p`, or `none`) and `encodeRep P` (§4.3.2 on the
extended representative `(x, y, 1, x y)` of a point, a natural number below `p`). Their
properties, in particular the round trips and the invariance of `encodeRep` on the classes of
`edwards.Rel`, are in `Curve25519.Ristretto.Encoding`. The field identities behind the on-curve
proof of `decodeRep` are in `Curve25519.Proofs.Ristretto.Algebra` (not audited). -/

namespace curve25519

open TwistedEdwardsModel

/-! ### `SQRT_RATIO_M1` -/

open scoped Classical in
/-- RFC 9496 §4.2 `SQRT_RATIO_M1(u, v)`: `(true, r)` with `v r² = u` when `u / v` is a square,
`(false, r)` with `v r² = √-1 · u` otherwise, `r` non-negative in both cases; `(u = 0, 0)` when
`v = 0`. Exposed; see `sqrtRatioM1_spec`. -/
@[expose] noncomputable def sqrtRatioM1 (u v : ZMod p) : Bool × ZMod p :=
  if v = 0 then (decide (u = 0), 0)
  else if h : IsSquare (u / v) then (true, (Classical.choose h).abs)
  else (false, (Classical.choose (isSquare_sqrtM1_mul_of_not_isSquare h)).abs)

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
theorem decodeRep_equation (s r : ZMod p)
    (hr : (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2) * (1 + s ^ 2) ^ 2 * r ^ 2 = 1) :
    edwards.Equation (2 * s * (r * (1 + s ^ 2))).abs
      ((1 - s ^ 2) * (r * (r * (1 + s ^ 2)) * (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2))) :=
  Proofs.decode_equation s r hr

/-- RFC 9496 §4.3.1, the decoding of a representative: `none` unless `s < p` and `s` is
non-negative; then with `u1 = 1 - s²`, `u2 = 1 + s²`, `v = -(d u1²) - u2²`,
`(wasSquare, r) = SQRT_RATIO_M1(1, v u2²)`, `x = |2 s r u2|`, `y = u1 r (r u2) v`: `none` if
`¬ wasSquare`, `x y` is negative or `y = 0`, else `some (x, y)`. Hidden; see
`decodeRep_eq_some_iff`, `decodeRep_eq_none_iff` in `Curve25519.Ristretto.Encoding`. -/
noncomputable def decodeRep (s : ℕ) : Option edwards.Point :=
  if s < p ∧ ¬ (s : ZMod p).IsNeg then
    let s' : ZMod p := s
    let u1 := 1 - s' ^ 2
    let u2 := 1 + s' ^ 2
    let v := -(d * u1 ^ 2) - u2 ^ 2
    let r := (sqrtRatioM1 1 (v * u2 ^ 2)).2
    let denX := r * u2
    let denY := r * denX * v
    let x := (2 * s' * denX).abs
    let y := u1 * denY
    if h : (sqrtRatioM1 1 (v * u2 ^ 2)).1 = true ∧ ¬ (x * y).IsNeg ∧ y ≠ 0 then
      some ⟨x, y, decodeRep_equation s' r (sqrtRatioM1_one_of_fst h.1)⟩
    else none
  else none

/-- RFC 9496 §4.3.2, the encoding of a representative, on the extended coordinates
`(x, y, 1, x y)` of the point: with `u1 = (1 + y)(1 - y)`, `u2 = x y`,
`(_, invsqrt) = SQRT_RATIO_M1(1, u1 u2²)`, `den1 = invsqrt u1`, `den2 = invsqrt u2`,
`zInv = den1 den2 t`, `rotate = IS_NEGATIVE(t zInv)`; `(x', y', denInv) = (y √-1, x √-1,
den1 · INVSQRT_A_MINUS_D)` if `rotate` else `(x, y, den2)`; `y'' = -y'` if `x' zInv` is negative
else `y'`; the result is `|denInv (1 - y'')|` as a natural number below `p`. Hidden; see
`encodeRep_eq`. -/
noncomputable def encodeRep (P : edwards.Point) : ℕ :=
  let x := P.x
  let y := P.y
  let t := x * y
  let u1 := (1 + y) * (1 - y)
  let u2 := x * y
  let invsqrt := (sqrtRatioM1 1 (u1 * u2 ^ 2)).2
  let den1 := invsqrt * u1
  let den2 := invsqrt * u2
  let zInv := den1 * den2 * t
  let ix := x * sqrtM1
  let iy := y * sqrtM1
  let enchanted := den1 * invsqrtAMinusD
  let rotate := (t * zInv).IsNeg
  let x' := if rotate then iy else x
  let y' := if rotate then ix else y
  let denInv := if rotate then enchanted else den2
  let y'' := if (x' * zInv).IsNeg then -y' else y'
  (denInv * (1 - y'')).abs.val

/-- `encodeRep P`, RFC 9496 §4.3.2 spelled out. -/
theorem encodeRep_eq (P : edwards.Point) : encodeRep P =
    let x := P.x
    let y := P.y
    let t := x * y
    let u1 := (1 + y) * (1 - y)
    let u2 := x * y
    let invsqrt := (sqrtRatioM1 1 (u1 * u2 ^ 2)).2
    let den1 := invsqrt * u1
    let den2 := invsqrt * u2
    let zInv := den1 * den2 * t
    let ix := x * sqrtM1
    let iy := y * sqrtM1
    let enchanted := den1 * invsqrtAMinusD
    let rotate := (t * zInv).IsNeg
    let x' := if rotate then iy else x
    let y' := if rotate then ix else y
    let denInv := if rotate then enchanted else den2
    let y'' := if (x' * zInv).IsNeg then -y' else y'
    (denInv * (1 - y'')).abs.val := by
  unfold encodeRep
  rfl

end Ristretto

end curve25519
