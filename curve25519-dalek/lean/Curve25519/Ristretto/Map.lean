/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Ristretto.Encoding
public import Curve25519.X25519
import Curve25519.Proofs.Ristretto.Algebra
import Curve25519.Proofs.Ristretto.Elligator
import Curve25519.Ristretto.Even
import Mathlib.Tactic.LinearCombination
public section

/-! # The ristretto255 map (RFC 9496 §4.3.4)

`Ristretto.mapRepField r₀` is RFC 9496's `MAP(r₀)`, the Elligator-style map of a field element to an
even point of `edwards` (hidden; coordinates `mapRepField_x`, `mapRepField_y`, with the
`sqrtRatioM1` case split, and `even_mapRepField`), and `Ristretto.fromUniformRepNat n` the one-way
map of §4.3.4 on the little-endian value `n` of 64 uniform bytes: `MAP(r₀) + MAP(r₁)` for the two
32-byte halves masked to 255 bits (`decodeU`), an even point (`even_fromUniformRepNat`). The field
identities behind the on-curve proof of `mapRepField` are in `Curve25519.Proofs.Ristretto.Elligator`
(not audited). -/

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

/-- RFC 9496 §4.3.4 `MAP(r₀)`: the even point `(2 s v / (N √(a d - 1)), (1 - s²) / (1 + s²))`
of `mapRepField_equation` (the RFC's `(w0 w3 : w2 w1 : w1 w3 : w0 w2)` in affine form). Hidden; see
`mapRepField_x`, `mapRepField_y`, `even_mapRepField`. -/
noncomputable def mapRepField (r₀ : ZMod p) : edwards.Point :=
  let r := sqrtM1 * r₀ ^ 2
  let u := (r + 1) * oneMinusDSq
  let v := (-1 - r * d) * (r + d)
  let s := if (sqrtRatioM1 u v).1 then (sqrtRatioM1 u v).2
    else -((sqrtRatioM1 u v).2 * r₀).abs
  let c := if (sqrtRatioM1 u v).1 then -1 else r
  let N := c * (r - 1) * dMinusOneSq - v
  ⟨2 * s * v / (N * sqrtAdMinusOne), (1 - s ^ 2) / (1 + s ^ 2), mapRepField_equation r₀⟩

/-- The `x`-coordinate of `MAP(r₀)`: `2 s v / (N √(a d - 1))`, i.e. the RFC's `w0 / w1`. -/
theorem mapRepField_x (r₀ : ZMod p) :
    (mapRepField r₀).x =
      let r := sqrtM1 * r₀ ^ 2
      let u := (r + 1) * oneMinusDSq
      let v := (-1 - r * d) * (r + d)
      let s := if (sqrtRatioM1 u v).1 then (sqrtRatioM1 u v).2
        else -((sqrtRatioM1 u v).2 * r₀).abs
      let c := if (sqrtRatioM1 u v).1 then -1 else r
      let N := c * (r - 1) * dMinusOneSq - v
      2 * s * v / (N * sqrtAdMinusOne) := by
  unfold mapRepField
  rfl

/-- The `y`-coordinate of `MAP(r₀)`: `(1 - s²) / (1 + s²)`, i.e. the RFC's `w2 / w3`. -/
theorem mapRepField_y (r₀ : ZMod p) :
    (mapRepField r₀).y =
      let r := sqrtM1 * r₀ ^ 2
      let u := (r + 1) * oneMinusDSq
      let v := (-1 - r * d) * (r + d)
      let s := if (sqrtRatioM1 u v).1 then (sqrtRatioM1 u v).2
        else -((sqrtRatioM1 u v).2 * r₀).abs
      (1 - s ^ 2) / (1 + s ^ 2) := by
  unfold mapRepField
  rfl

/-- The denominator `w1 = N √(a d - 1)` of `MAP(r₀)` is nonzero. -/
theorem mapRepField_den_ne_zero (r₀ : ZMod p) :
    let r := sqrtM1 * r₀ ^ 2
    let u := (r + 1) * oneMinusDSq
    let v := (-1 - r * d) * (r + d)
    let c := if (sqrtRatioM1 u v).1 then -1 else r
    let N := c * (r - 1) * dMinusOneSq - v
    N * sqrtAdMinusOne ≠ 0 :=
  (map_facts r₀).1

/-- The denominator `w3 = 1 + s²` of `MAP(r₀)` is nonzero. -/
theorem mapRepField_one_add_sq_ne_zero (r₀ : ZMod p) :
    let r := sqrtM1 * r₀ ^ 2
    let u := (r + 1) * oneMinusDSq
    let v := (-1 - r * d) * (r + d)
    let s := if (sqrtRatioM1 u v).1 then (sqrtRatioM1 u v).2
      else -((sqrtRatioM1 u v).2 * r₀).abs
    1 + s ^ 2 ≠ 0 :=
  (map_facts r₀).2.1

/-- **`MAP(r₀)` is even**: `1 - y² = (2 s / (1 + s²))²`. -/
theorem even_mapRepField (r₀ : ZMod p) : Even (mapRepField r₀) :=
  even_of_y_eq_div (map_facts r₀).2.1 rfl

/-! ### The one-way map -/

/-- RFC 9496 §4.3.4, the one-way map on the little-endian value `n` of 64 uniform bytes, as a
representative: `MAP(r₀) + MAP(r₁)` for the two 32-byte halves `r₀ = n % 2^256`,
`r₁ = n / 2^256`, each masked to 255 bits and reduced (`decodeU`). Meant for `n < 2^512` (64
bytes); for larger `n` the high half `n / 2^256` keeps all the upper bits before masking. -/
noncomputable def fromUniformRepNat (n : ℕ) : edwards.Point :=
  mapRepField (decodeU (n % 2 ^ 256)) + mapRepField (decodeU (n / 2 ^ 256))

theorem fromUniformRepNat_def (n : ℕ) :
    fromUniformRepNat n = mapRepField (decodeU (n % 2 ^ 256)) + mapRepField
        (decodeU (n / 2 ^ 256)) := by
  unfold fromUniformRepNat
  rfl

theorem even_fromUniformRepNat (n : ℕ) : Even (fromUniformRepNat n) := by
  rw [fromUniformRepNat_def]
  exact (even_mapRepField _).add (even_mapRepField _)

/-- RFC 9496 §4.3.4 `MAP` on a 32-byte string, as a representative: the most significant bit of
the final byte masked, the little-endian value reduced modulo `p`, then `mapRepField`. -/
@[expose] noncomputable def mapRep (b : Vector UInt8 32) : edwards.Point :=
  mapRepField ((decodeLittleEndian b % 2 ^ 255 : ℕ) : ZMod p)

theorem mapRep_eq (b : Vector UInt8 32) : mapRep b = mapRepField (decodeU (decodeLittleEndian b)) :=
  rfl

/-- RFC 9496 §4.3.4, the one-way map on 64 uniform bytes, as a representative:
`MAP(b[0:32]) + MAP(b[32:64])`. -/
@[expose] noncomputable def fromUniformRep (b : Vector UInt8 64) : edwards.Point :=
  mapRep (b.extract 0 32) + mapRep (b.extract 32 64)

/-- The value of 64 bytes from those of their two halves. -/
private theorem decodeLittleEndian_split (b : Vector UInt8 64) :
    decodeLittleEndian b =
      decodeLittleEndian (b.extract 0 32) + 2 ^ 256 * decodeLittleEndian (b.extract 32 64) := by
  have hl : b.toList = (b.extract 0 32).toList ++ (b.extract 32 64).toList := by
    rw [Vector.toList_extract, Vector.toList_extract, List.drop_zero, Nat.sub_zero,
      List.take_of_length_le (l := List.drop 32 b.toList) (by simp), List.take_append_drop]
  simp only [decodeLittleEndian]
  rw [hl, List.map_append, Nat.ofDigits_append]
  simp

private theorem decodeLittleEndian_extract_low (b : Vector UInt8 64) :
    decodeLittleEndian (b.extract 0 32) = decodeLittleEndian b % 2 ^ 256 := by
  have hlo : decodeLittleEndian (b.extract 0 32) < 2 ^ 256 := by
    simpa using decodeLittleEndian_lt (b.extract 0 32)
  rw [decodeLittleEndian_split b, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]

private theorem decodeLittleEndian_extract_high (b : Vector UInt8 64) :
    decodeLittleEndian (b.extract 32 64) = decodeLittleEndian b / 2 ^ 256 := by
  have hlo : decodeLittleEndian (b.extract 0 32) < 2 ^ 256 := by
    simpa using decodeLittleEndian_lt (b.extract 0 32)
  rw [decodeLittleEndian_split b, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hlo,
    zero_add]

/-- The one-way map is `fromUniformRepNat` on the value of the 64 bytes. -/
theorem fromUniformRep_eq (b : Vector UInt8 64) :
    fromUniformRep b = fromUniformRepNat (decodeLittleEndian b) := by
  rw [fromUniformRep, fromUniformRepNat_def, mapRep_eq, mapRep_eq, decodeLittleEndian_extract_low,
    decodeLittleEndian_extract_high, decodeU_mod_two_pow]

theorem even_fromUniformRep (b : Vector UInt8 64) : Even (fromUniformRep b) := by
  rw [fromUniformRep_eq]
  exact even_fromUniformRepNat _

end curve25519.Ristretto
