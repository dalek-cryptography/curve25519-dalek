/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Edwards
public import ForHumans.Specs.X25519
import Proofs.Curve25519.Ristretto.SqrtRatio
import Proofs.Curve25519.Ristretto.MapFacts
public section

/-! # ristretto255 (RFC 9496)

A ristretto255 element is a class of `TwistedEdwardsModel.Rel edwards`
(`ForHumans/Specs/Models.lean`); dalek represents it by any Edwards point of the class. The
decoding (§4.3.1) and the encoding (§4.3.2) of representatives, and the one-way map from uniform
bytes (§4.3.4). -/

namespace curve25519.Ristretto

/-! ### Decoding and encoding (§4.3.1, §4.3.2) -/

/-- RFC 9496 §4.3.1, the decoding of a representative: `none` unless `s < p` and `s` is
non-negative; then with `u1 = 1 - s²`, `u2 = 1 + s²`, `v = -(d u1²) - u2²`,
`(wasSquare, r) = SQRT_RATIO_M1(1, v u2²)`, `x = |2 s r u2|`, `y = u1 r (r u2) v`: `none` if
`¬ wasSquare`, `x y` is negative or `y = 0`, else `some (x, y)`. -/
noncomputable def decodeRepNat (s : ℕ) : Option edwards.Point :=
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
      some ⟨x, y, decodeRepNat_equation s' r (sqrtRatioM1_one_of_fst h.1)⟩
    else none
  else none

/-- RFC 9496 §4.3.1 `Decode` of 32 bytes to a representative: `decodeRepNat` of their value. -/
@[expose] noncomputable def decodeRep (b : Vector UInt8 32) : Option edwards.Point :=
  decodeRepNat (decodeLittleEndian b)

/-- RFC 9496 §4.3.2, the encoding of a representative, on the extended coordinates
`(x, y, 1, x y)` of the point: with `u1 = (1 + y)(1 - y)`, `u2 = x y`,
`(_, invsqrt) = SQRT_RATIO_M1(1, u1 u2²)`, `den1 = invsqrt u1`, `den2 = invsqrt u2`,
`zInv = den1 den2 t`, `rotate = IS_NEGATIVE(t zInv)`; `(x', y', denInv) = (y √-1, x √-1,
den1 · INVSQRT_A_MINUS_D)` if `rotate` else `(x, y, den2)`; `y'' = -y'` if `x' zInv` is negative
else `y'`; the result is `|denInv (1 - y'')|` as a natural number below `p`. -/
noncomputable def encodeRepNat (P : edwards.Point) : ℕ :=
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

/-- RFC 9496 §4.3.2 `Encode` of a representative: the 32 little-endian bytes of
`encodeRepNat`. -/
@[expose] noncomputable def encodeRep (P : edwards.Point) : Vector UInt8 32 :=
  encodeLittleEndian 32 (encodeRepNat P)

/-! ### The one-way map (§4.3.4) -/

/-- RFC 9496 §4.3.4 `MAP(r₀)`: the even point `(2 s v / (N √(a d - 1)), (1 - s²) / (1 + s²))`
of `mapRepField_equation` (the RFC's `(w0 w3 : w2 w1 : w1 w3 : w0 w2)` in affine form). -/
noncomputable def mapRepField (r₀ : ZMod p) : edwards.Point :=
  let r := sqrtM1 * r₀ ^ 2
  let u := (r + 1) * oneMinusDSq
  let v := (-1 - r * d) * (r + d)
  let s := if (sqrtRatioM1 u v).1 then (sqrtRatioM1 u v).2
    else -((sqrtRatioM1 u v).2 * r₀).abs
  let c := if (sqrtRatioM1 u v).1 then -1 else r
  let N := c * (r - 1) * dMinusOneSq - v
  ⟨2 * s * v / (N * sqrtAdMinusOne), (1 - s ^ 2) / (1 + s ^ 2), mapRepField_equation r₀⟩

/-- RFC 9496 §4.3.4 `MAP` on a 32-byte string, as a representative: the most significant bit of
the final byte masked, the little-endian value reduced modulo `p`, then `mapRepField`. -/
@[expose] noncomputable def mapRep (b : Vector UInt8 32) : edwards.Point :=
  mapRepField ((decodeLittleEndian b % 2 ^ 255 : ℕ) : ZMod p)

/-- RFC 9496 §4.3.4, the one-way map on 64 uniform bytes, as a representative:
`MAP(b[0:32]) + MAP(b[32:64])`. -/
@[expose] noncomputable def fromUniformRep (b : Vector UInt8 64) : edwards.Point :=
  mapRep (b.extract 0 32) + mapRep (b.extract 32 64)

end curve25519.Ristretto
