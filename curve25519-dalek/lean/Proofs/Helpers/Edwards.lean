/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Encoding
public import Defs.Edwards
import Proofs.Helpers.AsNat
import Proofs.Helpers.Array
public section

/-! # The lenient decoder

`decodeLenient` (dalek's `CompressedEdwardsY::decompress`) against RFC 8032's strict
`curve25519.decode`: its meaning (`decodeLenient_eq_some_iff`, `decodeLenient_eq_none_iff`), it
agrees with `decode` on canonical inputs (`decodeLenient_eq_decode_of_canonical`), it inverts
`encode` (`decodeLenient_encode`), and `encode` inverts it on canonical inputs
(`encode_of_decodeLenient`). `decodeLenient_eq_some_of_sign` is the form `decompress` establishes.
Also the bytes of a `CompressedEdwardsY`: its value is below `2^256`, and the top bit of its last
byte is bit `255` of the value (the sign bit of `decompress`). -/

open curve25519 TwistedEdwardsModel

namespace Curve25519Dalek.edwards

/-- **The meaning of lenient decoding**: `decodeLenient n = some P` iff `P.y` is the value of
the low `255` bits of `n` (reduced modulo `p`) and `P.x` is `0` or has the sign of bit `255`. -/
theorem decodeLenient_eq_some_iff {n : ℕ} {P : curve25519.edwards.Point} :
    decodeLenient n = some P ↔
      P.y = ((n % 2 ^ 255 : ℕ) : ZMod p) ∧ (P.x = 0 ∨ (P.x.IsNeg ↔ n / 2 ^ 255 = 1)) := by
  rw [decodeLenient_def]
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
theorem decodeLenient_eq_none_iff {n : ℕ} :
    decodeLenient n = none ↔
      ¬ IsSquare (curve25519.edwards.xSq ((n % 2 ^ 255 : ℕ) : ZMod p)) := by
  rw [decodeLenient_def, isSquare_xSq_iff]
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

theorem decodeLenient_isSome_iff {n : ℕ} :
    (decodeLenient n).isSome ↔ IsSquare (curve25519.edwards.xSq ((n % 2 ^ 255 : ℕ) : ZMod p)) := by
  rw [← Option.ne_none_iff_isSome, ne_eq, decodeLenient_eq_none_iff, not_not]

/-- On canonical inputs (`y < p`, and not `y² = 1` with the sign bit set), lenient and strict
decoding agree. -/
theorem decodeLenient_eq_decode_of_canonical {n : ℕ} (hn : n < 2 ^ 256) (hy : n % 2 ^ 255 < p)
    (hs : ¬ (((n % 2 ^ 255 : ℕ) : ZMod p) ^ 2 = 1 ∧ n / 2 ^ 255 = 1)) :
    decodeLenient n = decode n := by
  rcases hd : decode n with _ | P
  · rw [decode_eq_none_iff] at hd
    rw [decodeLenient_eq_none_iff]
    rcases hd with h | h | h | h
    · exact absurd hn (not_lt.mpr h)
    · exact absurd hy (not_lt.mpr h)
    · exact h
    · exact absurd h hs
  · obtain ⟨-, -, hy', hs'⟩ := decode_eq_some_iff.mp hd
    exact decodeLenient_eq_some_iff.mpr ⟨hy', Or.inr hs'⟩

/-- Lenient decoding inverts encoding. -/
theorem decodeLenient_encode (P : curve25519.edwards.Point) :
    decodeLenient (encode P) = some P := by
  rw [decodeLenient_eq_some_iff, encode_mod_two_pow_255, ZMod.natCast_zmod_val,
    encode_div_two_pow_255]
  refine ⟨rfl, Or.inr ?_⟩
  by_cases h : P.x.IsNeg <;> simp [h]

/-- On canonical inputs, encoding inverts lenient decoding. -/
theorem encode_of_decodeLenient {n : ℕ} {P : curve25519.edwards.Point}
    (h : decodeLenient n = some P) (hn : n < 2 ^ 256) (hy : n % 2 ^ 255 < p)
    (hs : ¬ (P.x = 0 ∧ n / 2 ^ 255 = 1)) : encode P = n := by
  obtain ⟨hy', hsx⟩ := decodeLenient_eq_some_iff.mp h
  refine encode_decode (decode_eq_some_iff.mpr ⟨hn, hy, hy', ?_⟩)
  rcases hsx with hx | hx
  · have hs' : ¬ n / 2 ^ 255 = 1 := fun h1 => hs ⟨hx, h1⟩
    rw [hx]
    exact iff_of_false ZMod.not_isNeg_zero hs'
  · exact hx

/-- The `y`-coordinate of a leniently decoded point. -/
theorem decodeLenient_y {n : ℕ} {P : curve25519.edwards.Point} (h : decodeLenient n = some P) :
    P.y = ((n % 2 ^ 255 : ℕ) : ZMod p) :=
  (decodeLenient_eq_some_iff.mp h).1

/-- The sign of the `x`-coordinate of a leniently decoded point: bit `255`, unless `x = 0`. -/
theorem decodeLenient_x_eq_zero_or_isNeg_iff {n : ℕ} {P : curve25519.edwards.Point}
    (h : decodeLenient n = some P) : P.x = 0 ∨ (P.x.IsNeg ↔ n / 2 ^ 255 = 1) :=
  (decodeLenient_eq_some_iff.mp h).2

/-- What `decompress` computes: the non-negative root `x`, negated when bit `255` is set. -/
theorem decodeLenient_eq_some_of_sign {n : ℕ} {x : ZMod p} (hneg : ¬ x.IsNeg)
    (P : curve25519.edwards.Point) (hPy : P.y = ((n % 2 ^ 255 : ℕ) : ZMod p))
    (hP0 : n / 2 ^ 255 = 0 → P.x = x) (hP1 : n / 2 ^ 255 = 1 → P.x = -x) (hn : n / 2 ^ 255 ≤ 1) :
    decodeLenient n = some P := by
  rw [decodeLenient_eq_some_iff]
  refine ⟨hPy, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with h | h
  · rw [hP0 h, h]
    exact Or.inr (iff_of_false hneg zero_ne_one)
  · by_cases hx0 : x = 0
    · rw [hP1 h, hx0, neg_zero]
      exact Or.inl rfl
    · rw [hP1 h, h]
      exact Or.inr (iff_of_true (ZMod.isNeg_neg_of_not_isNeg hx0 hneg) rfl)

/-! ### The bytes of a `CompressedEdwardsY` -/

namespace CompressedEdwardsY

theorem asNat_lt (self : CompressedEdwardsY) : self.asNat < 2 ^ 256 := by
  rw [asNat_def]
  exact Aeneas.Std.Array.asNat_lt 8 self fun i _ => by scalar_tac

theorem asNat_div_two_pow_le_one (self : CompressedEdwardsY) : self.asNat / 2 ^ 255 ≤ 1 :=
  Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by rw [← pow_succ]; exact self.asNat_lt))

/-- The top bit of the last byte is bit `255` of the value. -/
theorem getElem!_31_shiftRight_7 (self : CompressedEdwardsY) :
    self[31]!.val >>> 7 = self.asNat / 2 ^ 255 := by
  have h := Aeneas.Std.Array.getElem!_last_eq_asNat_div 8 self (fun i _ => by scalar_tac)
    (by decide)
  rw [show (32#usize).val - 1 = 31 from rfl] at h
  rw [h, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, asNat_def]
  norm_num

end CompressedEdwardsY

end Curve25519Dalek.edwards
