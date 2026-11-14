/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

/-! # The field identities behind the ristretto255 encoding (not audited)

The algebra of RFC 9496 §4.3.1 (decoding) and §4.3.2 (encoding), stated for field elements
with explicit hypotheses in place of the square roots: for decoding, `W r² = 1` where
`W = v u2²`, `u1 = 1 - s²`, `u2 = 1 + s²`, `v = -(d u1²) - u2²`; for encoding, `W I² = 1` where
`W = (1 + y)(1 - y)(x y)²`. The results are instantiated by `Curve25519.Ristretto.Encoding.Defs`
(the on-curve proof of `decodeRepNat`) and `Curve25519.Ristretto.Encoding` (the round trips). -/

namespace curve25519.Proofs

open TwistedEdwardsModel

/-- `1 + d ≠ 0`: `a - d ≠ 0` with `a = -1`. -/
theorem one_add_d_ne_zero : 1 + d ≠ 0 := fun h =>
  a_sub_d_ne_zero (by rw [a_def]; linear_combination -h)

/-- `d - 1 ≠ 0`: `1` is a square and `d` is not. -/
theorem d_sub_one_ne_zero : d - 1 ≠ 0 := by
  intro h
  apply not_isSquare_d
  exact ⟨1, by linear_combination h⟩

theorem one_sub_d_sq_ne_zero : 1 - d ^ 2 ≠ 0 := by
  intro h
  have h' : (1 + d) * (d - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h' with h' | h'
  · exact one_add_d_ne_zero h'
  · exact d_sub_one_ne_zero h'

/-! ### Decoding (RFC 9496 §4.3.1) -/

/-- `v = -(d u1²) - u2² ≠ 0`: a zero would make `-d` a square (or `2 = 0`). -/
theorem decodeNat_v_ne_zero (s : ZMod p) : -(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2 ≠ 0 := by
  intro h
  by_cases h1 : 1 - s ^ 2 = 0
  · have h2 : (1 + s ^ 2) ^ 2 = 0 := by rw [h1] at h; linear_combination -h
    have h2' : 1 + s ^ 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2
    have h3 : (2 : ZMod p) = 0 := by linear_combination h1 + h2'
    exact two_ne_zero h3
  · apply not_isSquare_neg_d
    refine ⟨(1 + s ^ 2) / (1 - s ^ 2), ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero h1 h1)]
    linear_combination h

/-- `u2 = 1 + s² ≠ 0` when `W r² = 1`. -/
theorem decodeNat_u2_ne_zero (s r : ZMod p)
    (hr : (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2) * (1 + s ^ 2) ^ 2 * r ^ 2 = 1) :
    1 + s ^ 2 ≠ 0 := by
  intro h
  rw [h] at hr
  exact one_ne_zero (by linear_combination -hr)

/-- The decoded `y = u1 (r (r u2) v)` is `u1 / u2`. -/
theorem decodeNat_y_eq (s r : ZMod p)
    (hr : (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2) * (1 + s ^ 2) ^ 2 * r ^ 2 = 1) :
    (1 - s ^ 2) * (r * (r * (1 + s ^ 2)) * (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2)) =
      (1 - s ^ 2) / (1 + s ^ 2) := by
  rw [eq_div_iff (decodeNat_u2_ne_zero s r hr)]
  linear_combination (1 - s ^ 2) * hr

/-- The decoded `x = |2 s (r u2)|` has `x² v = 4 s²`. -/
theorem decodeNat_x_sq_mul_v (s r : ZMod p)
    (hr : (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2) * (1 + s ^ 2) ^ 2 * r ^ 2 = 1) :
    (2 * s * (r * (1 + s ^ 2))).abs ^ 2 * (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2) =
      4 * s ^ 2 := by
  rw [ZMod.abs_sq]
  linear_combination (4 * s ^ 2) * hr

/-- The decoded point is on the model. -/
theorem decodeNat_equation (s r : ZMod p)
    (hr : (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2) * (1 + s ^ 2) ^ 2 * r ^ 2 = 1) :
    edwards.Equation (2 * s * (r * (1 + s ^ 2))).abs
      ((1 - s ^ 2) * (r * (r * (1 + s ^ 2)) * (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2))) := by
  have hv := decodeNat_v_ne_zero s
  have hu2 := decodeNat_u2_ne_zero s r hr
  have hx : (2 * s * (r * (1 + s ^ 2))).abs ^ 2 =
      4 * s ^ 2 / (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2) := by
    rw [eq_div_iff hv]
    exact decodeNat_x_sq_mul_v s r hr
  unfold Equation
  rw [edwards_a_eq_neg_one, edwards_d, decodeNat_y_eq s r hr, hx]
  field_simp
  ring

/-- A point with `y = u1 / u2` has `x² v = 4 s²`. -/
theorem x_sq_mul_v_eq {x y : ZMod p} (s : ZMod p) (hc : edwards.Equation x y)
    (hy : y * (1 + s ^ 2) = 1 - s ^ 2) :
    x ^ 2 * (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2) = 4 * s ^ 2 := by
  unfold Equation at hc
  rw [edwards_a_eq_neg_one, edwards_d] at hc
  linear_combination (1 + s ^ 2) ^ 2 * hc + ((y * (1 + s ^ 2) + (1 - s ^ 2)) * (d * x ^ 2 - 1)) * hy

/-- `S² = (1 - y) / (1 + y)` gives `(1 - S²) / (1 + S²) = y`. -/
theorem div_eq_of_sq_eq_div {F : Type*} [Field F] [NeZero (2 : F)] {S y : F} (hy : 1 + y ≠ 0)
    (hS : S ^ 2 = (1 - y) / (1 + y)) :
    (1 - S ^ 2) / (1 + S ^ 2) = y := by
  have e1 : 1 + S ^ 2 = 2 / (1 + y) := by
    rw [hS, eq_div_iff hy]
    field_simp
    ring
  have e2 : 1 - S ^ 2 = 2 * y / (1 + y) := by
    rw [hS, eq_div_iff hy]
    field_simp
    ring
  rw [e1, e2, div_div_div_cancel_right₀ hy, mul_div_cancel_left₀ y two_ne_zero]

/-- `D² (1 - y²) = 1` gives `(D (1 - y))² = (1 - y) / (1 + y)`. -/
theorem mul_one_sub_sq_eq_div {F : Type*} [Field F] {D y : F} (h : D ^ 2 * (1 - y ^ 2) = 1) :
    (D * (1 - y)) ^ 2 = (1 - y) / (1 + y) := by
  have hy : 1 + y ≠ 0 := by
    intro hy
    have : y = -1 := by linear_combination hy
    rw [this] at h
    exact one_ne_zero (by linear_combination -h)
  rw [eq_div_iff hy]
  linear_combination (1 - y) * h

/-! ### Encoding (RFC 9496 §4.3.2) -/

/-- The `rotate = false` branch: `den2 = I u2` has `den2² (1 - y²) = 1`. -/
theorem enc_den2_sq {F : Type*} [Field F] (x y I : F)
    (hI : (1 + y) * (1 - y) * (x * y) ^ 2 * I ^ 2 = 1) : (I * (x * y)) ^ 2 * (1 - y ^ 2) = 1 := by
  linear_combination hI

/-- The `rotate = true` branch: `den1 K = I u1 K` with `K² (a - d) = 1` has
`(den1 K)² (1 - (x i)²) = 1`, by the curve equation. -/
theorem enc_den1_sq {F : Type*} [Field F] (dd i x y I K : F) (hi : i ^ 2 = -1)
    (hc : -x ^ 2 + y ^ 2 = 1 + dd * x ^ 2 * y ^ 2)
    (hI : (1 + y) * (1 - y) * (x * y) ^ 2 * I ^ 2 = 1) (hK : K ^ 2 * (-1 - dd) = 1) :
    (I * ((1 + y) * (1 - y)) * K) ^ 2 * (1 - (x * i) ^ 2) = 1 := by
  rw [mul_pow x i, hi]
  linear_combination (K ^ 2 * (-1 - dd)) * hI + hK - (I ^ 2 * ((1 + y) * (1 - y)) * K ^ 2) * hc

/-- `z_inv = den1 den2 t = I² u1 u2 (x y) = 1`. -/
theorem enc_zInv_eq_one {F : Type*} [Field F] (x y I : F)
    (hI : (1 + y) * (1 - y) * (x * y) ^ 2 * I ^ 2 = 1) :
    I * ((1 + y) * (1 - y)) * (I * (x * y)) * (x * y) = 1 := by
  linear_combination hI

/-- `W = (1 + y)(1 - y)(x y)²` is a square when `1 - y²` is (for an even point, by the
2-descent). -/
theorem enc_W_isSquare {F : Type*} [Field F] {x y q : F} (hq : 1 - y ^ 2 = q * q) :
    IsSquare ((1 + y) * (1 - y) * (x * y) ^ 2) :=
  ⟨q * (x * y), by linear_combination (x * y) ^ 2 * hq⟩

end curve25519.Proofs
