/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Bytes
public import Curve25519.Edwards.Basepoint
import Curve25519.ToEllipticCurve.TwistedEdwards.Lemmas
public section

/-! # The RFC 8032 point encoding of edwards25519

RFC 8032 on 32-byte strings (`Vector UInt8 32`): the encoding `encode` (§5.1.2), the strict
decoding `decode` (§5.1.3), and the lenient decoding `decodeLenient`, which also accepts the
non-canonical encodings (`y ≥ p`, reduced, and `x = 0` with the sign bit set); `decode_encode`,
`decodeLenient_encode`, `eq_encode_iff`.

They are computed by arithmetic cores on the little-endian value of the bytes
(`decodeLittleEndian`): the generic encoding of `Curve25519.Models.TwistedEdwards.Encoding.*` at
`edwards` with `bits = 255`, `encodeNat P = P.y.val + 2 ^ 255 * sign(P.x)` and the strict
`decodeNat`, with the generic lemmas instantiated (`encodeNat_lt_two_pow_256`,
`decodeNat_encodeNat`, `encodeNat_decodeNat`, `decodeNat_eq_some_iff`, `decodeNat_eq_none_iff`,
`encodeNat_injective`), and the lenient `decodeLenientNat` with its meaning
(`decodeLenientNat_eq_some_iff`, `decodeLenientNat_eq_none_iff`) and its relation to `decodeNat`
and `encodeNat`. Also the sign of the basepoint (`not_isNeg_basepoint_x`) and the encodings of the
basepoint (`encodeNat_basepoint`, dalek's `ED25519_BASEPOINT_COMPRESSED`) and of `0`.

`encodeNat` and `decodeNat` are abbreviations of the generic functions, so every generic lemma
applies to them directly. -/

namespace curve25519

open TwistedEdwardsModel

/-- `p < 2 ^ 255`: the `y`-coordinate fits in `255` bits. -/
instance instFactPLtTwoPow255 : Fact (p < 2 ^ 255) := ⟨p_lt_two_pow_255⟩

/-- RFC 8032 §5.1.2: the encoding of a point of edwards25519, `y.val + 2 ^ 255 * sign(x)`. -/
noncomputable abbrev encodeNat : edwards.Point → ℕ :=
  TwistedEdwardsModel.encode edwards 255

/-- RFC 8032 §5.1.3, strict: the decoding of a `256`-bit value, `none` unless it is the encoding
of a point (`decodeNat_eq_some_iff_encodeNat_eq`). -/
noncomputable abbrev decodeNat : ℕ → Option edwards.Point :=
  TwistedEdwardsModel.decode edwards 255

theorem encodeNat_eq (P : edwards.Point) :
    encodeNat P = P.y.val + 2 ^ 255 * (if P.x.IsNeg then 1 else 0) :=
  rfl

/-! ### The generic lemmas at `edwards`, `bits = 255` -/

theorem encodeNat_lt_two_pow_256 (P : edwards.Point) : encodeNat P < 2 ^ 256 :=
  TwistedEdwardsModel.encode_lt edwards 255 P

/-- The low `255` bits of an encoding are `y.val`. -/
theorem encodeNat_mod_two_pow_255 (P : edwards.Point) : encodeNat P % 2 ^ 255 = P.y.val :=
  TwistedEdwardsModel.encode_mod_two_pow edwards 255 P

/-- Bit `255` of an encoding is the sign of `x`. -/
theorem encodeNat_div_two_pow_255 (P : edwards.Point) :
    encodeNat P / 2 ^ 255 = if P.x.IsNeg then 1 else 0 :=
  TwistedEdwardsModel.encode_div_two_pow edwards 255 P

theorem encodeNat_injective : Function.Injective encodeNat :=
  TwistedEdwardsModel.encode_injective edwards 255

theorem decodeNat_encodeNat (P : edwards.Point) : decodeNat (encodeNat P) = some P :=
  TwistedEdwardsModel.decode_encode edwards 255 P

theorem encodeNat_decodeNat {n : ℕ} {P : edwards.Point} (h : decodeNat n = some P) : encodeNat
    P = n :=
  TwistedEdwardsModel.encode_decode edwards 255 h

/-- `decodeNat n = some P` iff `n < 2 ^ 256`, the low `255` bits of `n` are below `p`, `P.y` is
that value, and the sign of `P.x` is bit `255` of `n`. -/
theorem decodeNat_eq_some_iff {n : ℕ} {P : edwards.Point} :
    decodeNat n = some P ↔
      n < 2 ^ 256 ∧ n % 2 ^ 255 < p ∧ P.y = ((n % 2 ^ 255 : ℕ) : ZMod p) ∧
        (P.x.IsNeg ↔ n / 2 ^ 255 = 1) :=
  TwistedEdwardsModel.decode_eq_some_iff edwards 255

theorem decodeNat_eq_some_iff_encodeNat_eq {n : ℕ} {P : edwards.Point} :
    decodeNat n = some P ↔ encodeNat P = n :=
  TwistedEdwardsModel.decode_eq_some_iff_encode_eq edwards 255

/-- The rejection reasons of strict decoding: `n ≥ 2 ^ 256`, `y ≥ p`, no square root of
`(y² - 1) / (d y² + 1)`, or `y² = 1` with the sign bit set. -/
theorem decodeNat_eq_none_iff {n : ℕ} :
    decodeNat n = none ↔
      2 ^ 256 ≤ n ∨ p ≤ n % 2 ^ 255 ∨
        ¬ IsSquare (edwards.xSq ((n % 2 ^ 255 : ℕ) : ZMod p)) ∨
        (((n % 2 ^ 255 : ℕ) : ZMod p) ^ 2 = 1 ∧ n / 2 ^ 255 = 1) :=
  TwistedEdwardsModel.decode_eq_none_iff edwards 255

theorem decodeNat_isSome_iff {n : ℕ} : (decodeNat n).isSome ↔ ∃ P, encodeNat P = n :=
  TwistedEdwardsModel.decode_isSome_iff edwards 255

/-- `x² = (y² - 1) / (d y² + 1)` on edwards25519 (`a = -1`). -/
theorem edwards_xSq (y : ZMod p) : edwards.xSq y = (y ^ 2 - 1) / (d * y ^ 2 + 1) := by
  unfold xSq
  rw [edwards_a_eq_neg_one, edwards_d, sub_neg_eq_add]

/-! ### The lenient decoder -/

open scoped Classical in
/-- Lenient decoding of the value `n` of the 32 bytes: `y := n % 2^255` reduced modulo `p`,
sign `s := n / 2^255`; `none` if no point has this `y`, otherwise the point `(x, y)` with `x = 0`
or `x` of sign `s`. Unlike the strict `decodeNat`, it accepts `y ≥ p` (reduced) and `x = 0` with
`s = 1`; on canonical inputs the two agree (`decodeLenientNat_eq_decodeNat_of_canonical`). This is
dalek's `CompressedEdwardsY::decompress`. -/
noncomputable def decodeLenientNat (n : ℕ) : Option edwards.Point :=
  if h : ∃ x : ZMod p, edwards.Equation x ((n % 2 ^ 255 : ℕ) : ZMod p) ∧
      (x = 0 ∨ (x.IsNeg ↔ n / 2 ^ 255 = 1)) then
    some ⟨Classical.choose h, ((n % 2 ^ 255 : ℕ) : ZMod p), (Classical.choose_spec h).1⟩
  else none

open scoped Classical in
theorem decodeLenientNat_def (n : ℕ) :
    decodeLenientNat n =
      if h : ∃ x : ZMod p, edwards.Equation x ((n % 2 ^ 255 : ℕ) : ZMod p) ∧
          (x = 0 ∨ (x.IsNeg ↔ n / 2 ^ 255 = 1)) then
        some ⟨Classical.choose h, ((n % 2 ^ 255 : ℕ) : ZMod p), (Classical.choose_spec h).1⟩
      else none := by
  unfold decodeLenientNat
  rfl

/-- **The meaning of lenient decoding**: `decodeLenientNat n = some P` iff `P.y` is the value of
the low `255` bits of `n` (reduced modulo `p`) and `P.x` is `0` or has the sign of bit `255`. -/
theorem decodeLenientNat_eq_some_iff {n : ℕ} {P : edwards.Point} :
    decodeLenientNat n = some P ↔
      P.y = ((n % 2 ^ 255 : ℕ) : ZMod p) ∧ (P.x = 0 ∨ (P.x.IsNeg ↔ n / 2 ^ 255 = 1)) := by
  rw [decodeLenientNat_def]
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨rfl, (Classical.choose_spec h).2⟩
    · rintro ⟨hy, hs⟩
      obtain ⟨hx, hsx⟩ := Classical.choose_spec h
      refine (Point.ext ?_ hy).symm
      have hsq : P.x ^ 2 = (Classical.choose h) ^ 2 := by
        rw [P.sq_x_eq_xSq, hy, ← equation_iff_sq_eq_xSq.mp hx]
      rcases hs with hs | hs
      · rw [hs, zero_pow two_ne_zero] at hsq
        rw [hs]
        exact ((pow_eq_zero_iff two_ne_zero).mp hsq.symm).symm
      · rcases hsx with h0 | h0
        · rw [h0, zero_pow two_ne_zero] at hsq
          change P.x = Classical.choose h
          rw [h0]
          exact (pow_eq_zero_iff two_ne_zero).mp hsq
        · exact ZMod.eq_of_sq_eq_of_isNeg_iff hsq (hs.trans h0.symm)
  · refine iff_of_false (by simp) ?_
    rintro ⟨hy, hs⟩
    exact h ⟨P.x, hy ▸ P.equation, hs⟩

/-- Lenient decoding fails iff no point has the given `y`: `xSq y` is not a square. -/
theorem decodeLenientNat_eq_none_iff {n : ℕ} :
    decodeLenientNat n = none ↔
      ¬ IsSquare (edwards.xSq ((n % 2 ^ 255 : ℕ) : ZMod p)) := by
  rw [decodeLenientNat_def, isSquare_xSq_iff]
  split_ifs with h
  · refine iff_of_false (by simp) ?_
    obtain ⟨x, hx, -⟩ := h
    exact fun h' => h' ⟨x, hx⟩
  · refine iff_of_true rfl ?_
    rintro ⟨x, hx⟩
    apply h
    by_cases hx0 : x = 0
    · exact ⟨x, hx, Or.inl hx0⟩
    by_cases hs : n / 2 ^ 255 = 1
    · rcases ZMod.isNeg_or_isNeg_neg hx0 with hneg | hneg
      · exact ⟨x, hx, Or.inr (iff_of_true hneg hs)⟩
      · exact ⟨-x, equation_neg hx, Or.inr (iff_of_true hneg hs)⟩
    · rcases ZMod.isNeg_or_isNeg_neg hx0 with hneg | hneg
      · exact ⟨-x, equation_neg hx,
          Or.inr (iff_of_false (ZMod.not_isNeg_neg_of_isNeg hneg) hs)⟩
      · exact ⟨x, hx, Or.inr (iff_of_false (fun h' =>
          ZMod.not_isNeg_neg_of_isNeg h' hneg) hs)⟩

theorem decodeLenientNat_isSome_iff {n : ℕ} :
    (decodeLenientNat n).isSome ↔ IsSquare (edwards.xSq ((n % 2 ^ 255 : ℕ) : ZMod p)) := by
  rw [← Option.ne_none_iff_isSome, ne_eq, decodeLenientNat_eq_none_iff, not_not]

/-- On canonical inputs (`y < p`, and not `y² = 1` with the sign bit set), lenient and strict
decoding agree. -/
theorem decodeLenientNat_eq_decodeNat_of_canonical {n : ℕ} (hn : n < 2 ^ 256) (hy : n % 2 ^ 255 < p)
    (hs : ¬ (((n % 2 ^ 255 : ℕ) : ZMod p) ^ 2 = 1 ∧ n / 2 ^ 255 = 1)) :
    decodeLenientNat n = decodeNat n := by
  rcases hd : decodeNat n with _ | P
  · rw [decodeNat_eq_none_iff] at hd
    rw [decodeLenientNat_eq_none_iff]
    rcases hd with h | h | h | h
    · exact absurd hn (not_lt.mpr h)
    · exact absurd hy (not_lt.mpr h)
    · exact h
    · exact absurd h hs
  · obtain ⟨-, -, hy', hs'⟩ := decodeNat_eq_some_iff.mp hd
    exact decodeLenientNat_eq_some_iff.mpr ⟨hy', Or.inr hs'⟩

/-- Lenient decoding inverts encoding. -/
theorem decodeLenientNat_encodeNat (P : edwards.Point) :
    decodeLenientNat (encodeNat P) = some P := by
  rw [decodeLenientNat_eq_some_iff, encodeNat_mod_two_pow_255, ZMod.natCast_zmod_val,
    encodeNat_div_two_pow_255]
  refine ⟨rfl, Or.inr ?_⟩
  by_cases h : P.x.IsNeg <;> simp [h]

/-- On canonical inputs, encoding inverts lenient decoding. -/
theorem encodeNat_of_decodeLenientNat {n : ℕ} {P : edwards.Point}
    (h : decodeLenientNat n = some P) (hn : n < 2 ^ 256) (hy : n % 2 ^ 255 < p)
    (hs : ¬ (P.x = 0 ∧ n / 2 ^ 255 = 1)) : encodeNat P = n := by
  obtain ⟨hy', hsx⟩ := decodeLenientNat_eq_some_iff.mp h
  refine encodeNat_decodeNat (decodeNat_eq_some_iff.mpr ⟨hn, hy, hy', ?_⟩)
  rcases hsx with hx | hx
  · have hs' : ¬ n / 2 ^ 255 = 1 := fun h1 => hs ⟨hx, h1⟩
    rw [hx]
    exact iff_of_false ZMod.not_isNeg_zero hs'
  · exact hx

/-- The `y`-coordinate of a leniently decoded point. -/
theorem decodeLenientNat_y {n : ℕ} {P : edwards.Point} (h : decodeLenientNat n = some P) :
    P.y = ((n % 2 ^ 255 : ℕ) : ZMod p) :=
  (decodeLenientNat_eq_some_iff.mp h).1

/-- The sign of the `x`-coordinate of a leniently decoded point: bit `255`, unless `x = 0`. -/
theorem decodeLenientNat_x_eq_zero_or_isNeg_iff {n : ℕ} {P : edwards.Point}
    (h : decodeLenientNat n = some P) : P.x = 0 ∨ (P.x.IsNeg ↔ n / 2 ^ 255 = 1) :=
  (decodeLenientNat_eq_some_iff.mp h).2

/-- What `decompress` computes: the non-negative root `x`, negated when bit `255` is set. -/
theorem decodeLenientNat_eq_some_of_sign {n : ℕ} {x : ZMod p} (hneg : ¬ x.IsNeg)
    (P : edwards.Point) (hPy : P.y = ((n % 2 ^ 255 : ℕ) : ZMod p))
    (hP0 : n / 2 ^ 255 = 0 → P.x = x) (hP1 : n / 2 ^ 255 = 1 → P.x = -x) (hn : n / 2 ^ 255 ≤ 1) :
    decodeLenientNat n = some P := by
  rw [decodeLenientNat_eq_some_iff]
  refine ⟨hPy, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with h | h
  · rw [hP0 h, h]
    exact Or.inr (iff_of_false hneg zero_ne_one)
  · by_cases hx0 : x = 0
    · rw [hP1 h, hx0, neg_zero]
      exact Or.inl rfl
    · rw [hP1 h, h]
      exact Or.inr (iff_of_true (ZMod.isNeg_neg_of_not_isNeg hx0 hneg) rfl)

/-! ### RFC 8032 on 32-byte strings -/

/-- RFC 8032 §5.1.2: the 32-byte encoding of a point, the little-endian bytes of `encodeNat`. -/
@[expose] noncomputable def encode (P : edwards.Point) : Vector UInt8 32 :=
  encodeLittleEndian 32 (encodeNat P)

/-- RFC 8032 §5.1.3: the strict decoding of 32 bytes, `decodeNat` of their value. -/
@[expose] noncomputable def decode (b : Vector UInt8 32) : Option edwards.Point :=
  decodeNat (decodeLittleEndian b)

/-- The lenient decoding of 32 bytes, `decodeLenientNat` of their value. -/
@[expose] noncomputable def decodeLenient (b : Vector UInt8 32) : Option edwards.Point :=
  decodeLenientNat (decodeLittleEndian b)

/-- `b` is the encoding of `P` iff its value is `encodeNat P`. -/
theorem eq_encode_iff (b : Vector UInt8 32) (P : edwards.Point) :
    b = encode P ↔ decodeLittleEndian b = encodeNat P :=
  eq_encodeLittleEndian_iff b (by simpa using encodeNat_lt_two_pow_256 P)

/-- Strict decoding inverts encoding. -/
theorem decode_encode (P : edwards.Point) : decode (encode P) = some P := by
  rw [decode, encode, decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (by simpa using encodeNat_lt_two_pow_256 P), decodeNat_encodeNat]

/-- Lenient decoding inverts encoding. -/
theorem decodeLenient_encode (P : edwards.Point) : decodeLenient (encode P) = some P := by
  rw [decodeLenient, encode, decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (by simpa using encodeNat_lt_two_pow_256 P), decodeLenientNat_encodeNat]

/-! ### The basepoint -/

/-- The basepoint has even `x`: RFC 8032's "positive" square root. -/
theorem not_isNeg_basepoint_x : ¬ basepoint.x.IsNeg :=
  ZMod.not_isNeg_iff.mpr basepoint_x_val_even

/-- **The encoding of the basepoint**: dalek's `ED25519_BASEPOINT_COMPRESSED`, the bytes
`58 66 66 … 66`, i.e. `y = 4/5` with the sign bit `0`. -/
theorem encodeNat_basepoint : encodeNat basepoint =
    46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
  rw [encodeNat_eq, ite_eq_right not_isNeg_basepoint_x, mul_zero, add_zero, basepoint_y_eq,
    ZMod.val_ofNat_of_lt (by rw [p_eq_numeral]; decide)]

/-! ### The zero -/

theorem encodeNat_zero : encodeNat 0 = 1 :=
  TwistedEdwardsModel.encode_zero edwards 255

end curve25519
