/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Ristretto.Encoding
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
public section

/-! # The Ristretto encoding on projective coordinates

`RistrettoPoint::compress` evaluates RFC 9496 §4.3.2 on the extended coordinates `(X : Y : Z : T)`
of a point, not on `(x, y, 1, x y)` as `encodeRepNat` does. `compressProj X Y Z T` is that
computation; `compressProj_eq_encodeRepNat` shows that it does not depend on the representative.
Scaling the coordinates by `Z` scales the inverse square root by `± 1 / Z³` (`λ⁶` is a square), so
every quantity of the encoding except the last factor depends only on its square, and the result
changes by a sign, which the final absolute value removes. -/

open curve25519 curve25519.Ristretto

namespace Curve25519Dalek.RistrettoCompress

/-- `λ⁶ w` is a square iff `w` is (`λ ≠ 0`). -/
theorem isSquare_pow_six_mul_iff {w l : ZMod p} (hl : l ≠ 0) :
    IsSquare (l ^ 6 * w) ↔ IsSquare w := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / l ^ 3, ?_⟩
    have hl3 : l ^ 3 ≠ 0 := pow_ne_zero 3 hl
    field_simp
    linear_combination hr
  · rintro ⟨r, hr⟩
    exact ⟨l ^ 3 * r, by rw [hr]; ring⟩

/-- **The inverse square root under scaling**: `invsqrt (λ⁶ w)² · λ⁶ = invsqrt (w)²`. -/
theorem sq_sqrtRatioM1_one_pow_six_mul (w l : ZMod p) (hl : l ≠ 0) :
    (sqrtRatioM1 1 (l ^ 6 * w)).2 ^ 2 * l ^ 6 = (sqrtRatioM1 1 w).2 ^ 2 := by
  have hl6 : l ^ 6 ≠ 0 := pow_ne_zero 6 hl
  by_cases hw : w = 0
  · rw [hw, mul_zero, sqrtRatioM1_one_zero]
    ring
  have hw' : l ^ 6 * w ≠ 0 := mul_ne_zero hl6 hw
  by_cases hsq : IsSquare w
  · have h1 := sqrtRatioM1_one_of_isSquare hw hsq
    have h2 := sqrtRatioM1_one_of_isSquare hw' ((isSquare_pow_six_mul_iff hl).mpr hsq)
    apply mul_left_cancel₀ hw
    linear_combination h2 - h1
  · have hnsq : ¬ IsSquare (1 / w) := by rwa [one_div, isSquare_inv]
    have hnsq' : ¬ IsSquare (1 / (l ^ 6 * w)) := by
      rwa [one_div, isSquare_inv, isSquare_pow_six_mul_iff hl]
    have h1 := (sqrtRatioM1_of_not_isSquare hw hnsq).2
    have h2 := (sqrtRatioM1_of_not_isSquare hw' hnsq').2
    apply mul_left_cancel₀ hw
    linear_combination h2 - h1

/-- RFC 9496 §4.3.2 on extended coordinates `(X : Y : Z : T)`, in `RistrettoPoint::compress`'s
order of operations, with `c` for `INVSQRT_A_MINUS_D`; the result is the canonical non-negative
field element. -/
@[expose] noncomputable def compressProj (c X Y Z T : ZMod p) : ZMod p :=
  let u1 := (Z + Y) * (Z - Y)
  let u2 := X * Y
  let invsqrt := (sqrtRatioM1 1 (u1 * u2 ^ 2)).2
  let i1 := invsqrt * u1
  let i2 := invsqrt * u2
  let zInv := i1 * (i2 * T)
  let iX := X * sqrtM1
  let iY := Y * sqrtM1
  let enchanted := i1 * c
  let rotate := (T * zInv).IsNeg
  let X' := if rotate then iY else X
  let Y' := if rotate then iX else Y
  let den := if rotate then enchanted else i2
  let Y'' := if (X' * zInv).IsNeg then -Y' else Y'
  (den * (Z - Y'')).abs

/-- **`compress` does not depend on the representative**: on extended coordinates of `P`
(`Z ≠ 0`, `X Y = Z T`, `x = X / Z`, `y = Y / Z`) it is `encodeRepNat P`, for either square root
`c` of `1 / (a - d)`. -/
theorem compressProj_eq_encodeRepNat (P : edwards.Point) {c X Y Z T : ZMod p}
    (hc : c ^ 2 = (invsqrtAMinusD : ZMod p) ^ 2) (hZ : Z ≠ 0) (hT : X * Y = Z * T)
    (hx : P.x = X / Z) (hy : P.y = Y / Z) :
    (compressProj c X Y Z T).val = encodeRepNat P := by
  have hX : X = Z * P.x := by rw [hx]; field_simp
  have hY : Y = Z * P.y := by rw [hy]; field_simp
  have hT' : T = Z * (P.x * P.y) := by
    apply mul_left_cancel₀ hZ
    rw [← hT, hX, hY]
    ring
  subst hX hY hT'
  rw [encodeRepNat_eq]
  generalize P.x = x
  generalize P.y = y
  dsimp only [compressProj]
  have hu1 : (Z + Z * y) * (Z - Z * y) = Z ^ 2 * ((1 + y) * (1 - y)) := by ring
  have hu2 : Z * x * (Z * y) = Z ^ 2 * (x * y) := by ring
  have hw : (Z + Z * y) * (Z - Z * y) * (Z * x * (Z * y)) ^ 2 =
      Z ^ 6 * ((1 + y) * (1 - y) * (x * y) ^ 2) := by ring
  have hkey := sq_sqrtRatioM1_one_pow_six_mul ((1 + y) * (1 - y) * (x * y) ^ 2) Z hZ
  rw [← hw] at hkey
  generalize (sqrtRatioM1 1 ((Z + Z * y) * (Z - Z * y) * (Z * x * (Z * y)) ^ 2)).2 = iP at hkey ⊢
  generalize (sqrtRatioM1 1 ((1 + y) * (1 - y) * (x * y) ^ 2)).2 = iA at hkey ⊢
  clear hu1 hu2 hw
  set zP := iP * ((Z + Z * y) * (Z - Z * y)) * (iP * (Z * x * (Z * y)) * (Z * (x * y))) with hzP
  set zA := iA * ((1 + y) * (1 - y)) * (iA * (x * y)) * (x * y) with hzA
  have hz : Z * zP = zA := by
    rw [hzP, hzA]
    linear_combination ((1 + y) * (1 - y) * (x * y) ^ 2) * hkey
  have hr : Z * (x * y) * zP = x * y * zA := by rw [← hz]; ring
  have hn1 : Z * y * (sqrtM1 : ZMod p) * zP = y * sqrtM1 * zA := by rw [← hz]; ring
  have hn2 : Z * x * zP = x * zA := by rw [← hz]; ring
  rw [hr]
  congr 1
  apply ZMod.abs_eq_abs_of_sq_eq
  simp only [ite_mul, hn1, hn2]
  split_ifs
  · linear_combination ((1 + y) * (1 - y) * c * (1 - -(x * sqrtM1))) ^ 2 * hkey +
      (iA * ((1 + y) * (1 - y)) * (1 - -(x * sqrtM1))) ^ 2 * hc
  · linear_combination ((1 + y) * (1 - y) * c * (1 - x * sqrtM1)) ^ 2 * hkey +
      (iA * ((1 + y) * (1 - y)) * (1 - x * sqrtM1)) ^ 2 * hc
  · linear_combination (x * y * (1 - -y)) ^ 2 * hkey
  · linear_combination (x * y * (1 - y)) ^ 2 * hkey

/-! ### The batch encoding of doubled points -/

/-- `double_and_compress_batch` on one point: RFC 9496 §4.3.2 for `2 P`, from the doubling
quantities `e = 2 X Y`, `f = Z² + d T²`, `g = Y² + X²`, `h = Z² - d T²` of `P` and the batch inverse
`(e g · f h)⁻¹`, with `c` for `INVSQRT_A_MINUS_D`. -/
@[expose] noncomputable def doubleCompress (c e f g h : ZMod p) : ZMod p :=
  let eg := e * g
  let fh := f * h
  let inv := (eg * fh)⁻¹
  let zInv := eg * inv
  let tInv := fh * inv
  let neg1 := (eg * zInv).IsNeg
  let e' := if neg1 then g else e
  let g' := if neg1 then -e else g
  let h' := if neg1 then f * sqrtM1 else h
  let magic := if neg1 then (sqrtM1 : ZMod p) else c
  let g'' := if (h' * e' * zInv).IsNeg then -g' else g'
  ((h' - g'') * (magic * (g'' * tInv))).abs

/-- **The batch formula is the encoding of the doubled point**: with `h² - g² = (a - d) e²` (which
holds for the doubling quantities of a point on the curve), `doubleCompress` is `compressProj` on
the extended coordinates `(e h : g f : f h : e g)` of `2 P`. -/
theorem doubleCompress_eq_compressProj {c e f g h : ZMod p} (hc : c ^ 2 * (a - d) = 1)
    (hcurve : h ^ 2 - g ^ 2 = (a - d) * e ^ 2) :
    doubleCompress c e f g h = compressProj c (e * h) (g * f) (f * h) (e * g) := by
  dsimp only [doubleCompress, compressProj]
  have hi : (sqrtM1 : ZMod p) ^ 2 = -1 := sqrtM1_sq
  have hu1 : (f * h + g * f) * (f * h - g * f) = f ^ 2 * ((a - d) * e ^ 2) := by
    rw [← hcurve]
    ring
  rw [hu1]
  by_cases h0 : e * f * g * h = 0
  · -- degenerate: both sides vanish
    have hw : f ^ 2 * ((a - d) * e ^ 2) * (e * h * (g * f)) ^ 2 = 0 := by
      rw [show f ^ 2 * ((a - d) * e ^ 2) * (e * h * (g * f)) ^ 2 =
        (a - d) * f ^ 2 * e ^ 2 * (e * f * g * h) ^ 2 by ring, h0]
      ring
    have hinv : (e * g * (f * h))⁻¹ = 0 := by
      rw [show e * g * (f * h) = e * f * g * h by ring, h0, inv_zero]
    rw [hw, sqrtRatioM1_one_zero, hinv]
    simp
  · have ha : (a : ZMod p) - d ≠ 0 := fun h' => by rw [h', mul_zero] at hc; exact zero_ne_one hc
    have hc0 : c ≠ 0 := fun h' => by
      rw [h', zero_pow two_ne_zero, zero_mul] at hc; exact zero_ne_one hc
    have hw0 : f ^ 2 * ((a - d) * e ^ 2) * (e * h * (g * f)) ^ 2 ≠ 0 := by
      rw [show f ^ 2 * ((a - d) * e ^ 2) * (e * h * (g * f)) ^ 2 =
        (a - d) * (e * f) ^ 2 * (e * f * g * h) ^ 2 by ring]
      refine mul_ne_zero (mul_ne_zero ha ?_) (pow_ne_zero 2 h0)
      exact pow_ne_zero 2 (left_ne_zero_of_mul (left_ne_zero_of_mul h0))
    have hwsq : IsSquare (f ^ 2 * ((a - d) * e ^ 2) * (e * h * (g * f)) ^ 2) := by
      refine ⟨c⁻¹ * (e * f * (e * f * g * h)), ?_⟩
      field_simp
      linear_combination (e * f) ^ 2 * (e * f * g * h) ^ 2 * hc
    have hI := sqrtRatioM1_one_of_isSquare hw0 hwsq
    generalize (sqrtRatioM1 1 (f ^ 2 * ((a - d) * e ^ 2) * (e * h * (g * f)) ^ 2)).2 = I at hI ⊢
    have hfh : f * h ≠ 0 := fun h' => h0 (by linear_combination e * g * h')
    have hinv : e * g * (f * h) * (e * g * (f * h))⁻¹ = 1 :=
      mul_inv_cancel₀ (fun h' => h0 (by linear_combination h'))
    generalize (e * g * (f * h))⁻¹ = inv at hinv ⊢
    -- `I² (e² f² g h)² = c²` and `I² e² f² = c² inv²`
    have R1 : I ^ 2 * (e ^ 2 * f ^ 2 * g * h) ^ 2 = c ^ 2 := by
      linear_combination c ^ 2 * hI - I ^ 2 * (e ^ 2 * f ^ 2 * g * h) ^ 2 * hc
    have R6 : I ^ 2 * e ^ 2 * f ^ 2 = c ^ 2 * inv ^ 2 := by
      linear_combination inv ^ 2 * R1 +
        (-(I ^ 2 * e ^ 2 * f ^ 2) * (e * f * g * h * inv + 1)) * hinv
    have hz : I * (f ^ 2 * ((a - d) * e ^ 2)) * (I * (e * h * (g * f)) * (e * g)) =
        e * g * inv := by
      apply mul_right_cancel₀ hfh
      linear_combination (a - d) * e ^ 2 * f ^ 2 * g ^ 2 * h ^ 2 * R6 +
        e ^ 2 * f ^ 2 * g ^ 2 * h ^ 2 * inv ^ 2 * hc + (e * f * g * h * inv) * hinv
    rw [hz]
    apply ZMod.abs_eq_abs_of_sq_eq
    by_cases hr : (e * g * (e * g * inv)).IsNeg
    · simp only [ite_eq_left hr]
      rw [show f * (sqrtM1 : ZMod p) * g = g * f * sqrtM1 by ring]
      by_cases hn : (g * f * (sqrtM1 : ZMod p) * (e * g * inv)).IsNeg
      · simp only [ite_eq_left hn]
        linear_combination (inv ^ 2 * e ^ 2 * f ^ 2 * h ^ 2 *
            (f ^ 2 * ((sqrtM1 : ZMod p) ^ 2 - 1) - 2 * e * f * sqrtM1)) * hi -
          (inv ^ 2 * f ^ 2 * e ^ 2 * h ^ 2 * (f + e * sqrtM1) ^ 2 * (c ^ 2 * (a - d) + 1)) * hc -
          (f ^ 2 * (a - d) ^ 2 * e ^ 2 * c ^ 2 * h ^ 2 * (f + e * sqrtM1) ^ 2) * R6
      · simp only [ite_eq_right hn]
        linear_combination (inv ^ 2 * e ^ 2 * f ^ 2 * h ^ 2 *
            (f ^ 2 * ((sqrtM1 : ZMod p) ^ 2 - 1) + 2 * e * f * sqrtM1)) * hi -
          (inv ^ 2 * f ^ 2 * e ^ 2 * h ^ 2 * (f - e * sqrtM1) ^ 2 * (c ^ 2 * (a - d) + 1)) * hc -
          (f ^ 2 * (a - d) ^ 2 * e ^ 2 * c ^ 2 * h ^ 2 * (f - e * sqrtM1) ^ 2) * R6
    · simp only [ite_eq_right hr]
      rw [show h * e = e * h by ring]
      by_cases hn : (e * h * (e * g * inv)).IsNeg
      · simp only [ite_eq_left hn]
        linear_combination (-(h + g) ^ 2 * g ^ 2 * h ^ 2 * f ^ 2) * R6
      · simp only [ite_eq_right hn]
        linear_combination (-(h - g) ^ 2 * g ^ 2 * h ^ 2 * f ^ 2) * R6

/-- **`double_and_compress_batch` on one point is the encoding of its double**: from the extended
coordinates `(X : Y : Z : T)` of `P` (`Z ≠ 0`, `X Y = Z T`), with `e = X (Y + Y)`,
`f = Z² + T² d`, `g = Y² + X²`, `h = Z² - T² d` as the code forms them. -/
theorem doubleCompress_eq_encodeRepNat (P : edwards.Point) {c X Y Z T : ZMod p}
    (hc : c ^ 2 * (a - d) = 1) (hZ : Z ≠ 0) (hT : X * Y = Z * T) (hx : P.x = X / Z)
    (hy : P.y = Y / Z) :
    (doubleCompress c (X * (Y + Y)) (Z ^ 2 + T ^ 2 * d) (Y ^ 2 + X ^ 2) (Z ^ 2 - T ^ 2 * d)).val =
      encodeRepNat (2 • P) := by
  have hX : X = Z * P.x := by rw [hx]; field_simp
  have hY : Y = Z * P.y := by rw [hy]; field_simp
  have hT' : T = Z * (P.x * P.y) := by
    apply mul_left_cancel₀ hZ
    rw [← hT, hX, hY]
    ring
  subst hX hY hT'
  have heq := P.equation
  rw [TwistedEdwardsModel.Equation, edwards_a_eq_neg_one, edwards_d] at heq
  have hd1 := edwards.addDen₁_ne_zero P P
  have hd2 := edwards.addDen₂_ne_zero P P
  rw [TwistedEdwardsModel.addDen₁, edwards_d] at hd1
  rw [TwistedEdwardsModel.addDen₂, edwards_d] at hd2
  have hQx := edwards.two_nsmul_x P
  have hQy := edwards.two_nsmul_y P
  rw [TwistedEdwardsModel.addX, TwistedEdwardsModel.addDen₁, edwards_d] at hQx
  rw [TwistedEdwardsModel.addY, TwistedEdwardsModel.addDen₂, edwards_d, edwards_a_eq_neg_one] at hQy
  generalize 2 • P = Q at hQx hQy
  generalize P.x = x at *
  generalize P.y = y at *
  have hZ2 : Z ^ 2 ≠ 0 := pow_ne_zero 2 hZ
  have hf : Z ^ 2 + (Z * (x * y)) ^ 2 * d = Z ^ 2 * (1 + d * x * x * y * y) := by ring
  have hh : Z ^ 2 - (Z * (x * y)) ^ 2 * d = Z ^ 2 * (1 - d * x * x * y * y) := by ring
  have hc' : c ^ 2 = (invsqrtAMinusD : ZMod p) ^ 2 := by
    have ha : (a : ZMod p) - d ≠ 0 := fun h' => by rw [h', mul_zero] at hc; exact zero_ne_one hc
    apply mul_right_cancel₀ ha
    rw [hc, invsqrtAMinusD_sq_mul]
  have hcurve : (Z ^ 2 - (Z * (x * y)) ^ 2 * d) ^ 2 - ((Z * y) ^ 2 + (Z * x) ^ 2) ^ 2 =
      (a - d) * (Z * x * (Z * y + Z * y)) ^ 2 := by
    rw [a_def]
    linear_combination (-Z ^ 4 * (1 + d * x ^ 2 * y ^ 2 + y ^ 2 - x ^ 2)) * heq
  rw [doubleCompress_eq_compressProj hc hcurve, compressProj_eq_encodeRepNat Q hc'
    (mul_ne_zero (by rw [hf]; exact mul_ne_zero hZ2 hd1) (by rw [hh]; exact mul_ne_zero hZ2 hd2))
    (by ring)]
  · rw [hQx, hf, hh, div_eq_div_iff hd1 (mul_ne_zero (mul_ne_zero hZ2 hd1) (mul_ne_zero hZ2 hd2))]
    ring
  · rw [hQy, hf, hh, div_eq_div_iff hd2 (mul_ne_zero (mul_ne_zero hZ2 hd1) (mul_ne_zero hZ2 hd2))]
    ring

end Curve25519Dalek.RistrettoCompress
