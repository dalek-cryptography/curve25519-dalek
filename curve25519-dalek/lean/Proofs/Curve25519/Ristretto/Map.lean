/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Ristretto
import all ForHumans.Specs.Ristretto
public import Proofs.Curve25519.Ristretto.MapFacts
import all Proofs.Curve25519.Ristretto.MapFacts
public import Proofs.Curve25519.Ristretto.Encoding
public import Proofs.Curve25519.X25519
import Proofs.Curve25519.Proofs.Ristretto.Algebra
import Proofs.Curve25519.Proofs.Ristretto.Elligator
import Proofs.Curve25519.Ristretto.Even
import Mathlib.Tactic.LinearCombination
public section

namespace curve25519

open TwistedEdwardsModel

end curve25519

namespace curve25519

open TwistedEdwardsModel

end curve25519

namespace curve25519

open TwistedEdwardsModel

end curve25519

namespace curve25519.Ristretto

open TwistedEdwardsModel

/-- RFC 9496 §4.3.4, the one-way map on the little-endian value `n` of 64 uniform bytes, as a
representative: `MAP(r₀) + MAP(r₁)` for the two 32-byte halves `r₀ = n % 2^256`,
`r₁ = n / 2^256`, each masked to 255 bits and reduced (`decodeU`). Meant for `n < 2^512` (64
bytes); for larger `n` the high half `n / 2^256` keeps all the upper bits before masking. -/
noncomputable def fromUniformRepNat (n : ℕ) : edwards.Point :=
  mapRepField (decodeU (n % 2 ^ 256)) + mapRepField (decodeU (n / 2 ^ 256))

end curve25519.Ristretto

namespace curve25519.Ristretto

open TwistedEdwardsModel

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

theorem fromUniformRepNat_def (n : ℕ) :
    fromUniformRepNat n = mapRepField (decodeU (n % 2 ^ 256)) + mapRepField
        (decodeU (n / 2 ^ 256)) := by
  unfold fromUniformRepNat
  rfl

theorem even_fromUniformRepNat (n : ℕ) : Even (fromUniformRepNat n) := by
  rw [fromUniformRepNat_def]
  exact (even_mapRepField _).add (even_mapRepField _)

theorem mapRep_eq (b : Vector UInt8 32) : mapRep b = mapRepField (decodeU (decodeLittleEndian b)) :=
  rfl

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
