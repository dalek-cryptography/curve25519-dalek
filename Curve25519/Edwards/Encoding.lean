/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public section

/-! # The RFC 8032 point encoding of edwards25519

The generic encoding of `Curve25519.Models.TwistedEdwards.Encoding.*` at `edwards` with
`bits = 255`: `encode P = P.y.val + 2 ^ 255 * sign(P.x)` (RFC 8032 §5.1.2, the little-endian
value of the 32 bytes of `CompressedEdwardsY`), and the strict decoder `decode` (§5.1.3). The
lemmas are the generic ones instantiated (`encode_lt_two_pow_256`, `decode_encode`,
`encode_decode`, `decode_eq_some_iff`, `decode_eq_none_iff`, `encode_injective`), the sign of
the basepoint (`not_isNeg_basepoint_x`), and the encodings of the basepoint
(`encode_basepoint`, dalek's `ED25519_BASEPOINT_COMPRESSED`) and of `0`.

`encode` and `decode` are abbreviations of the generic functions, so every generic lemma
applies to them directly. -/

namespace curve25519

open TwistedEdwardsModel

/-- `p < 2 ^ 255`: the `y`-coordinate fits in `255` bits. -/
instance instFactPLtTwoPow255 : Fact (p < 2 ^ 255) := ⟨p_lt_two_pow_255⟩

/-- RFC 8032 §5.1.2: the encoding of a point of edwards25519, `y.val + 2 ^ 255 * sign(x)`. -/
noncomputable abbrev encode : edwards.Point → ℕ :=
  TwistedEdwardsModel.encode edwards 255

/-- RFC 8032 §5.1.3, strict: the decoding of a `256`-bit value, `none` unless it is the encoding
of a point (`decode_eq_some_iff_encode_eq`). -/
noncomputable abbrev decode : ℕ → Option edwards.Point :=
  TwistedEdwardsModel.decode edwards 255

theorem encode_eq (P : edwards.Point) :
    encode P = P.y.val + 2 ^ 255 * (if P.x.IsNeg then 1 else 0) :=
  rfl

/-! ### The generic lemmas at `edwards`, `bits = 255` -/

theorem encode_lt_two_pow_256 (P : edwards.Point) : encode P < 2 ^ 256 :=
  TwistedEdwardsModel.encode_lt edwards 255 P

/-- The low `255` bits of an encoding are `y.val`. -/
theorem encode_mod_two_pow_255 (P : edwards.Point) : encode P % 2 ^ 255 = P.y.val :=
  TwistedEdwardsModel.encode_mod_two_pow edwards 255 P

/-- Bit `255` of an encoding is the sign of `x`. -/
theorem encode_div_two_pow_255 (P : edwards.Point) :
    encode P / 2 ^ 255 = if P.x.IsNeg then 1 else 0 :=
  TwistedEdwardsModel.encode_div_two_pow edwards 255 P

theorem encode_injective : Function.Injective encode :=
  TwistedEdwardsModel.encode_injective edwards 255

theorem decode_encode (P : edwards.Point) : decode (encode P) = some P :=
  TwistedEdwardsModel.decode_encode edwards 255 P

theorem encode_decode {n : ℕ} {P : edwards.Point} (h : decode n = some P) : encode P = n :=
  TwistedEdwardsModel.encode_decode edwards 255 h

/-- `decode n = some P` iff `n < 2 ^ 256`, the low `255` bits of `n` are below `p`, `P.y` is
that value, and the sign of `P.x` is bit `255` of `n`. -/
theorem decode_eq_some_iff {n : ℕ} {P : edwards.Point} :
    decode n = some P ↔
      n < 2 ^ 256 ∧ n % 2 ^ 255 < p ∧ P.y = ((n % 2 ^ 255 : ℕ) : ZMod p) ∧
        (P.x.IsNeg ↔ n / 2 ^ 255 = 1) :=
  TwistedEdwardsModel.decode_eq_some_iff edwards 255

theorem decode_eq_some_iff_encode_eq {n : ℕ} {P : edwards.Point} :
    decode n = some P ↔ encode P = n :=
  TwistedEdwardsModel.decode_eq_some_iff_encode_eq edwards 255

/-- The rejection reasons of strict decoding: `n ≥ 2 ^ 256`, `y ≥ p`, no square root of
`(y² - 1) / (d y² + 1)`, or `y² = 1` with the sign bit set. -/
theorem decode_eq_none_iff {n : ℕ} :
    decode n = none ↔
      2 ^ 256 ≤ n ∨ p ≤ n % 2 ^ 255 ∨
        ¬ IsSquare (edwards.xSq ((n % 2 ^ 255 : ℕ) : ZMod p)) ∨
        (((n % 2 ^ 255 : ℕ) : ZMod p) ^ 2 = 1 ∧ n / 2 ^ 255 = 1) :=
  TwistedEdwardsModel.decode_eq_none_iff edwards 255

theorem decode_isSome_iff {n : ℕ} : (decode n).isSome ↔ ∃ P, encode P = n :=
  TwistedEdwardsModel.decode_isSome_iff edwards 255

/-- `x² = (y² - 1) / (d y² + 1)` on edwards25519 (`a = -1`). -/
theorem edwards_xSq (y : ZMod p) : edwards.xSq y = (y ^ 2 - 1) / (d * y ^ 2 + 1) := by
  unfold xSq
  rw [edwards_a_eq_neg_one, edwards_d, sub_neg_eq_add]

/-! ### The basepoint -/

/-- The basepoint has even `x`: RFC 8032's "positive" square root. -/
theorem not_isNeg_basepoint_x : ¬ basepoint.x.IsNeg :=
  ZMod.not_isNeg_iff.mpr basepoint_x_val_even

/-- **The encoding of the basepoint**: dalek's `ED25519_BASEPOINT_COMPRESSED`, the bytes
`58 66 66 … 66`, i.e. `y = 4/5` with the sign bit `0`. -/
theorem encode_basepoint : encode basepoint =
    46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
  rw [encode_eq, ite_eq_right not_isNeg_basepoint_x, mul_zero, add_zero, basepoint_y_eq,
    ZMod.val_ofNat_of_lt (by rw [p_eq_numeral]; decide)]

/-! ### The zero -/

theorem encode_zero : encode 0 = 1 :=
  TwistedEdwardsModel.encode_zero edwards 255

end curve25519
