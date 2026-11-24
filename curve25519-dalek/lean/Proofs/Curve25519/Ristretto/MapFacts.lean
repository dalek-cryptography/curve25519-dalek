module
public import Proofs.Curve25519.Ristretto.SqrtRatio
public import ForHumans.Specs.X25519
import Proofs.Curve25519.Ristretto.Algebra
import Proofs.Curve25519.Ristretto.Elligator
import Proofs.Curve25519.Ristretto.Even
import Mathlib.Tactic.LinearCombination
public section

/-! # The ristretto255 map (RFC 9496 §4.3.4)

`Ristretto.mapRepField r₀` is RFC 9496's `MAP(r₀)`, the Elligator-style map of a field element to an
even point of `edwards` (hidden; coordinates `mapRepField_x`, `mapRepField_y`, with the
`sqrtRatioM1` case split, and `even_mapRepField`), and `Ristretto.fromUniformRepNat n` the one-way
map of §4.3.4 on the little-endian value `n` of 64 uniform bytes: `MAP(r₀) + MAP(r₁)` for the two
32-byte halves masked to 255 bits (`decodeU`), an even point (`even_fromUniformRepNat`). The field
identities behind the on-curve proof of `mapRepField` are in
`Proofs.Curve25519.Ristretto.Elligator` (not audited). -/

namespace curve25519.Ristretto

open TwistedEdwardsModel

/-! The intermediate quantities of RFC 9496 §4.3.4, internal: `r = √-1 r₀²`,
`u = (r + 1) ONE_MINUS_D_SQ`, `v = (-1 - r d)(r + d)`, the selected root `s`, the selector `c`
and `N = c (r - 1) D_MINUS_ONE_SQ - v`. -/

private noncomputable def mapR (r₀ : ZMod p) : ZMod p := sqrtM1 * r₀ ^ 2

private noncomputable def mapU (r₀ : ZMod p) : ZMod p := (mapR r₀ + 1) * oneMinusDSq

private noncomputable def mapV (r₀ : ZMod p) : ZMod p := (-1 - mapR r₀ * d) * (mapR r₀ + d)

private noncomputable def mapS (r₀ : ZMod p) : ZMod p :=
  if (sqrtRatioM1 (mapU r₀) (mapV r₀)).1 then (sqrtRatioM1 (mapU r₀) (mapV r₀)).2
  else -((sqrtRatioM1 (mapU r₀) (mapV r₀)).2 * r₀).abs

private noncomputable def mapC (r₀ : ZMod p) : ZMod p :=
  if (sqrtRatioM1 (mapU r₀) (mapV r₀)).1 then -1 else mapR r₀

private noncomputable def mapN (r₀ : ZMod p) : ZMod p :=
  mapC r₀ * (mapR r₀ - 1) * dMinusOneSq - mapV r₀

/-- `u = (r + 1)(1 - d²) ≠ 0`: `r = -1` would make `√-1` a square. -/
private theorem mapU_ne_zero (r₀ : ZMod p) : mapU r₀ ≠ 0 := by
  unfold mapU
  refine mul_ne_zero ?_ (by rw [oneMinusDSq_eq]; exact Proofs.one_sub_d_sq_ne_zero)
  intro h
  apply not_isSquare_sqrtM1
  refine ⟨r₀, ?_⟩
  unfold mapR at h
  linear_combination sqrtM1 * h - r₀ ^ 2 * sqrtM1_sq

/-- The denominator `N K` is nonzero, `1 + s² ≠ 0`, and the point is on the model. -/
private theorem map_facts (r₀ : ZMod p) :
    mapN r₀ * sqrtAdMinusOne ≠ 0 ∧ 1 + mapS r₀ ^ 2 ≠ 0 ∧
      edwards.Equation (2 * mapS r₀ * mapV r₀ / (mapN r₀ * sqrtAdMinusOne))
        ((1 - mapS r₀ ^ 2) / (1 + mapS r₀ ^ 2)) := by
  have hU : mapU r₀ = (mapR r₀ + 1) * (1 - d ^ 2) := by
    unfold mapU
    rw [oneMinusDSq_eq]
  have hns : (mapR r₀ + 1) * (1 - d ^ 2) ≠ 0 := hU ▸ mapU_ne_zero r₀
  have hN : mapN r₀ = mapC r₀ * (mapR r₀ - 1) * (d - 1) ^ 2 - mapV r₀ := by
    unfold mapN
    rw [dMinusOneSq_eq]
  rw [hN]
  refine Proofs.map_equation_of_branch (mapR r₀) (mapS r₀) (mapC r₀)
    (if (sqrtRatioM1 (mapU r₀) (mapV r₀)).1 then 1 else mapR r₀) (mapV r₀) rfl hns ?_
  by_cases hv : mapV r₀ = 0
  · right
    refine ⟨hv, ?_, ?_⟩
    · unfold mapS
      rw [hv, sqrtRatioM1_zero_right (mapU_ne_zero r₀), ite_eq_right (by decide), zero_mul,
        ZMod.abs_zero, neg_zero]
    · unfold mapC
      rw [hv, sqrtRatioM1_zero_right (mapU_ne_zero r₀), ite_eq_right (by decide)]
  · left
    refine ⟨hv, ?_, ?_⟩
    · by_cases hsq : (sqrtRatioM1 (mapU r₀) (mapV r₀)).1 = true
      · left
        unfold mapC
        rw [ite_eq_left hsq, ite_eq_left hsq]
        exact ⟨rfl, rfl⟩
      · right
        unfold mapC
        rw [ite_eq_right hsq, ite_eq_right hsq]
        exact ⟨rfl, rfl⟩
    · by_cases hsq : IsSquare (mapU r₀ / mapV r₀)
      · obtain ⟨h1, h2⟩ := sqrtRatioM1_of_isSquare hv hsq
        unfold mapS
        rw [ite_eq_left h1, ite_eq_left h1, one_mul, ← hU]
        linear_combination h2
      · obtain ⟨h1, h2⟩ := sqrtRatioM1_of_not_isSquare hv hsq
        have h1' : ¬ (sqrtRatioM1 (mapU r₀) (mapV r₀)).1 = true := by
          rw [h1]
          decide
        unfold mapS
        rw [ite_eq_right h1', ite_eq_right h1', neg_sq, ZMod.abs_sq, mul_pow, ← hU]
        unfold mapR
        linear_combination r₀ ^ 2 * h2

/-- The point `MAP(r₀)` of RFC 9496 §4.3.4 is on the model: with `r = √-1 r₀²`,
`u = (r + 1)(1 - d²)`, `v = (-1 - r d)(r + d)`, `(wasSquare, s₀) = SQRT_RATIO_M1(u, v)`,
`s = s₀` if `wasSquare` else `-|s₀ r₀|`, `c = -1` if `wasSquare` else `r`,
`N = c (r - 1)(d - 1)² - v`: the point `(2 s v / (N √(a d - 1)), (1 - s²) / (1 + s²))`. -/
theorem mapRepField_equation (r₀ : ZMod p) :
    let r := sqrtM1 * r₀ ^ 2
    let u := (r + 1) * oneMinusDSq
    let v := (-1 - r * d) * (r + d)
    let s := if (sqrtRatioM1 u v).1 then (sqrtRatioM1 u v).2
      else -((sqrtRatioM1 u v).2 * r₀).abs
    let c := if (sqrtRatioM1 u v).1 then -1 else r
    let N := c * (r - 1) * dMinusOneSq - v
    edwards.Equation (2 * s * v / (N * sqrtAdMinusOne)) ((1 - s ^ 2) / (1 + s ^ 2)) :=
  (map_facts r₀).2.2

end curve25519.Ristretto
