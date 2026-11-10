/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Bytes
public import Curve25519.Edwards.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
public section

/-! # X25519 (RFC 7748 §5)

RFC 7748 on 32-byte strings (`Vector UInt8 32`): `decodeScalar25519` (the clamped value of the
bytes), `decodeUCoordinate` (their value with bit `255` masked, as a field element),
`encodeUCoordinate` (the 32 bytes of the canonical representative) and `X25519 k u`, the
Montgomery ladder of `montgomery` over `255` bits (`MontgomeryModel.ladder`, `a24 = 121665`) on the
decoded scalar and coordinate, encoded. The RFC's final `x_2 * z_2^(p - 2)` is `x_2 / z_2` with
`x / 0 = 0` (`toU_eq_mul_pow_sub_two`).

They are computed by arithmetic cores on the little-endian values of the bytes
(`decodeLittleEndian`): `clamp`, `decodeU`, `encodeU` and `x25519Nat k u = encodeU (ladder 255
(clamp k) (decodeU u))`, so that `X25519 k u` is the encoding of `x25519Nat` on the values
(`X25519_eq_x25519Nat`, `eq_X25519_iff`).

The meaning: `x25519Nat k u` is the `u`-coordinate of `clamp k • Q` for any point `Q` of
`montgomery` or of its quadratic twist `montgomeryTwist = montgomery.twist 2` with
`u`-coordinate `decodeU u` (`x25519Nat_eq_xMul` with `MontgomeryModel.xMul_eq_u_nsmul`,
`MontgomeryModel.xMul_eq_u_nsmul_twist`; `2` is not a square modulo `p`, `not_isSquare_two`).
On bytes, `X25519 k u` is the encoded `u`-coordinate of `decodeScalar25519 k • Q`
(`X25519_eq_u_nsmul`, `X25519_eq_u_nsmul_twist`), and Diffie–Hellman agreement holds:
`X25519 a (X25519 b u) = X25519 b (X25519 a u)` (`X25519_X25519_comm`).

The definitions are exposed, so that they unfold (the kernel evaluates `x25519Nat` only where `p`
unfolds too: the test vectors import `Curve25519.Basic` with `import all`); `montgomeryTwist` is
hidden (`montgomeryTwist_def`, `montgomeryTwist_A`, `montgomeryTwist_B`). -/

namespace curve25519

/-! ### Clamping and coordinate coding -/

/-- RFC 7748 `decodeScalar25519` on the little-endian value `k` of the 32 bytes: clear the
bits `0`, `1`, `2` and `255`, set the bit `254`. Matches dalek's `clamp_integer`
(`clamp_add_mod_eight`). Its properties are the lemmas that follow: `clamp_lt`,
`two_pow_254_le_clamp`, `clamp_mod_eight`, `clamp_add_mod_eight`, `clamp_mod_two_pow`. -/
@[expose] def clamp (k : ℕ) : ℕ :=
  2 ^ 254 + 8 * (k % 2 ^ 254 / 8)

theorem clamp_lt (k : ℕ) : clamp k < 2 ^ 255 := by
  unfold clamp
  omega

theorem two_pow_254_le_clamp (k : ℕ) : 2 ^ 254 ≤ clamp k := by
  unfold clamp
  omega

theorem clamp_mod_eight (k : ℕ) : clamp k % 8 = 0 := by
  unfold clamp
  omega

/-- The specification of dalek's `clamp_integer`: `clamp k + k % 8 = 2^254 + k % 2^254`. -/
theorem clamp_add_mod_eight (k : ℕ) : clamp k + k % 8 = 2 ^ 254 + k % 2 ^ 254 := by
  unfold clamp
  omega

/-- Only the 32 bytes matter: `clamp` ignores the bits above `255`. -/
theorem clamp_mod_two_pow (k : ℕ) : clamp (k % 2 ^ 256) = clamp k := by
  unfold clamp
  omega

/-- RFC 7748 `decodeUCoordinate` on the little-endian value `n` of the 32 bytes: mask the bit
`255`, then reduce modulo `p`. -/
@[expose] def decodeU (n : ℕ) : ZMod p :=
  ((n % 2 ^ 255 : ℕ) : ZMod p)

/-- RFC 7748 `encodeUCoordinate`: the canonical representative below `p`. -/
@[expose] def encodeU (u : ZMod p) : ℕ :=
  u.val

theorem encodeU_lt (u : ZMod p) : encodeU u < p :=
  ZMod.val_lt u

/-- The encoding of the basepoint coordinate `9`. -/
theorem encodeU_nine : encodeU 9 = 9 := by
  unfold encodeU
  exact ZMod.val_ofNat_of_lt nine_lt_p

theorem decodeU_of_lt {n : ℕ} (hn : n < 2 ^ 255) : decodeU n = (n : ZMod p) := by
  unfold decodeU
  rw [Nat.mod_eq_of_lt hn]

theorem decodeU_encodeU (u : ZMod p) : decodeU (encodeU u) = u := by
  rw [decodeU_of_lt ((encodeU_lt u).trans p_lt_two_pow_255)]
  exact ZMod.natCast_zmod_val u

/-- Only the 32 bytes matter: `decodeU` ignores the bits above `255`. -/
theorem decodeU_mod_two_pow (n : ℕ) : decodeU (n % 2 ^ 256) = decodeU n := by
  unfold decodeU
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num))]

/-! ### The RFC's final inversion -/

/-- `x / z = x · z^(p - 2)` in `ZMod p`, including `z = 0` (both sides are `0`): the RFC's
`x_2 * z_2^(p - 2)` is the `toU` of the ladder. -/
theorem toU_eq_mul_pow_sub_two (P : MontgomeryModel.XZ (ZMod p)) :
    P.toU = P.U * P.W ^ (p - 2) := by
  have h2 := two_lt_p
  unfold MontgomeryModel.XZ.toU
  by_cases h : P.W = 0
  · rw [h, div_zero, zero_pow (by omega), mul_zero]
  · rw [div_eq_mul_inv]
    congr 1
    have h1 := ZMod.pow_card_sub_one_eq_one h
    rw [show p - 1 = p - 2 + 1 by omega, pow_succ] at h1
    exact (eq_inv_of_mul_eq_one_left h1).symm

/-! ### X25519 -/

/-- RFC 7748 §5 `X25519(k, u)` on the little-endian values of the two 32-byte strings: the
Montgomery ladder of curve25519 over 255 bits on the clamped scalar and the decoded
coordinate, encoded. -/
@[expose] def x25519Nat (k u : ℕ) : ℕ :=
  encodeU (montgomery.ladder 255 (clamp k) (decodeU u))

theorem x25519Nat_lt (k u : ℕ) : x25519Nat k u < p :=
  encodeU_lt _

/-! ### RFC 7748 on 32-byte strings -/

/-- RFC 7748 `decodeScalar25519`: the clamped little-endian value of the 32 bytes. -/
@[expose] def decodeScalar25519 (k : Vector UInt8 32) : ℕ :=
  clamp (decodeLittleEndian k)

/-- RFC 7748 `decodeUCoordinate`: the little-endian value of the 32 bytes with bit `255`
masked, as a field element (the RFC processes non-canonical values as reduced modulo `p`). -/
@[expose] def decodeUCoordinate (u : Vector UInt8 32) : ZMod p :=
  ((decodeLittleEndian u % 2 ^ 255 : ℕ) : ZMod p)

/-- RFC 7748 `encodeUCoordinate`: the 32 little-endian bytes of the canonical representative
(the RFC reduces its integer argument modulo `p`; here the argument is the field element). -/
@[expose] def encodeUCoordinate (u : ZMod p) : Vector UInt8 32 :=
  encodeLittleEndian 32 (encodeU u)

/-- RFC 7748 §5 `X25519(k, u)` on 32-byte strings: the Montgomery ladder of `montgomery` over
`255` bits on the clamped scalar and the decoded coordinate, encoded. -/
@[expose] def X25519 (k u : Vector UInt8 32) : Vector UInt8 32 :=
  encodeUCoordinate (montgomery.ladder 255 (decodeScalar25519 k) (decodeUCoordinate u))

/-- The decoded coordinate is `decodeU` of the value of the bytes. -/
theorem decodeUCoordinate_eq (u : Vector UInt8 32) :
    decodeUCoordinate u = decodeU (decodeLittleEndian u) :=
  rfl

/-- `X25519` is `x25519Nat` on the values of the bytes. -/
theorem X25519_eq_x25519Nat (k u : Vector UInt8 32) :
    X25519 k u = encodeLittleEndian 32 (x25519Nat (decodeLittleEndian k) (decodeLittleEndian u)) :=
  rfl

/-- The canonical encodings fit in 32 bytes. -/
theorem encodeU_lt_two_pow_256 (u : ZMod p) : encodeU u < 256 ^ 32 :=
  (encodeU_lt u).trans (p_lt_two_pow_255.trans (by norm_num))

/-- `b` is the encoding of `u` iff its value is the canonical representative of `u`. -/
theorem eq_encodeUCoordinate_iff (b : Vector UInt8 32) (u : ZMod p) :
    b = encodeUCoordinate u ↔ decodeLittleEndian b = encodeU u :=
  eq_encodeLittleEndian_iff b (encodeU_lt_two_pow_256 u)

theorem encodeU_zero : encodeU 0 = 0 :=
  ZMod.val_zero

theorem decodeLittleEndian_encodeUCoordinate (u : ZMod p) :
    decodeLittleEndian (encodeUCoordinate u) = encodeU u := by
  rw [encodeUCoordinate, decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (encodeU_lt_two_pow_256 u)]

/-- `b` is `X25519 k u` iff its value is `x25519Nat` of the values of `k` and `u`. -/
theorem eq_X25519_iff (b k u : Vector UInt8 32) :
    b = X25519 k u ↔ decodeLittleEndian b = x25519Nat (decodeLittleEndian k)
        (decodeLittleEndian u) := by
  rw [X25519_eq_x25519Nat]
  exact eq_encodeLittleEndian_iff b (encodeU_lt_two_pow_256 _)

/-- `X25519` sends `u` to the encoding of `0` for every scalar iff `x25519Nat` sends its value to
`0` for every natural scalar: only the low `256` bits of a scalar matter (`clamp_mod_two_pow`). -/
theorem forall_X25519_eq_zero_iff (u : Vector UInt8 32) :
    (∀ k, X25519 k u = encodeUCoordinate 0) ↔ ∀ k : ℕ, x25519Nat k (decodeLittleEndian u) = 0 := by
  have hzero (k : Vector UInt8 32) :
      X25519 k u = encodeUCoordinate 0 ↔ x25519Nat (decodeLittleEndian k) (decodeLittleEndian u)
          = 0 := by
    rw [eq_comm, eq_X25519_iff, decodeLittleEndian_encodeUCoordinate, encodeU_zero, eq_comm]
  simp only [hzero]
  constructor
  · intro h k
    have hk := h (encodeLittleEndian 32 k)
    rwa [decodeLittleEndian_encodeLittleEndian, x25519Nat, show (256 : ℕ) ^ 32 = 2 ^ 256 by
        norm_num,
      clamp_mod_two_pow] at hk
  · exact fun h k => h _

theorem decodeUCoordinate_encodeUCoordinate (u : ZMod p) :
    decodeUCoordinate (encodeUCoordinate u) = u := by
  rw [decodeUCoordinate_eq, encodeUCoordinate, decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (encodeU_lt_two_pow_256 u), decodeU_encodeU]

/-- The ladder constant of curve25519 is `121665`. -/
theorem montgomery_a24_eq : montgomery.a24 = 121665 := by
  rw [MontgomeryModel.a24, montgomery_A_eq, div_eq_iff four_ne_zero]
  norm_num

/-! ### The quadratic twist -/

/-- The quadratic twist `2 v² = u³ + A u² + u` of `montgomery`: the other curve on which the
ladder computes (`x25519Nat_eq_xMul`). -/
noncomputable def montgomeryTwist : MontgomeryModel (ZMod p) :=
  montgomery.twist 2

theorem montgomeryTwist_def : montgomeryTwist = montgomery.twist 2 := by
  unfold montgomeryTwist
  rfl

theorem montgomeryTwist_A : montgomeryTwist.A = (A : ZMod p) := by
  rw [montgomeryTwist_def, MontgomeryModel.twist_A, montgomery_A]

theorem montgomeryTwist_B : montgomeryTwist.B = 2 := by
  rw [montgomeryTwist_def, MontgomeryModel.twist_B, montgomery_B, one_mul]

/-- The twist is nonsingular. -/
instance instIsNonsingularMontgomeryTwist : montgomeryTwist.IsNonsingular := by
  rw [montgomeryTwist_def]
  exact montgomery.isNonsingular_twist two_ne_zero

/-! ### The meaning of `x25519Nat` -/

/-- `x25519Nat k u` is the x-only multiplication `xMul` by `clamp k` of `decodeU u`, which is
`u(clamp k • Q)` for a point `Q` of `montgomery` or of `montgomeryTwist` with `u`-coordinate
`decodeU u` (`MontgomeryModel.xMul_eq_u_nsmul`, `MontgomeryModel.xMul_eq_u_nsmul_twist`). -/
theorem x25519Nat_eq_xMul (k u : ℕ) :
    x25519Nat k u = encodeU (montgomery.xMul 2 (clamp k) (decodeU u)) := by
  unfold x25519Nat
  rw [MontgomeryModel.ladder_eq_xMul not_isSquare_two (clamp_lt k)]

/-- `x25519Nat` on the `u`-coordinate of a point `Q` of `montgomery` is the `u`-coordinate of
`clamp k • Q`. -/
theorem x25519Nat_eq_u_nsmul (k : ℕ) (Q : montgomery.Point) :
    x25519Nat k (encodeU Q.u) = encodeU (clamp k • Q).u := by
  rw [x25519Nat_eq_xMul, decodeU_encodeU, MontgomeryModel.xMul_eq_u_nsmul]

/-- `x25519Nat` on the `u`-coordinate of a point `Q` of the twist is the `u`-coordinate of
`clamp k • Q`. -/
theorem x25519Nat_eq_u_nsmul_twist (k : ℕ) (Q : montgomeryTwist.Point) :
    x25519Nat k (encodeU Q.u) = encodeU (clamp k • Q).u := by
  rw [x25519Nat_eq_xMul, decodeU_encodeU]
  have : (montgomery.twist 2).IsNonsingular := instIsNonsingularMontgomeryTwist
  exact congrArg encodeU
    (MontgomeryModel.xMul_eq_u_nsmul_twist (M := montgomery) not_isSquare_two (clamp k) Q)

/-- A coordinate whose `u ↦ u(8 • Q)` image is `0` (a point of order dividing `8` on the curve
or the twist, or `u = 0`) is sent to `0` by `x25519Nat` for every scalar, since clamped scalars
are multiples of `8`. -/
theorem x25519Nat_eq_zero_of_xMul_eight {u : ℕ} (h : montgomery.xMul 2 8 (decodeU u) = 0) (k : ℕ) :
    x25519Nat k u = 0 := by
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero (clamp_mod_eight k)
  rw [x25519Nat_eq_xMul, hm, Nat.mul_comm, MontgomeryModel.xMul_mul not_isSquare_two, h,
    MontgomeryModel.xMul_zero_right, encodeU, ZMod.val_zero]

/-! ### The meaning of `X25519` -/

/-- The decoded scalar is below `2 ^ 255`, so the ladder over `255` bits sees all of it. -/
theorem decodeScalar25519_lt (k : Vector UInt8 32) : decodeScalar25519 k < 2 ^ 255 :=
  clamp_lt _

/-- The decoded scalar is a multiple of the cofactor `8`. -/
theorem decodeScalar25519_mod_eight (k : Vector UInt8 32) : decodeScalar25519 k % 8 = 0 :=
  clamp_mod_eight _

/-- `X25519 k u` is the x-only multiplication `xMul` of the decoded coordinate by the decoded
scalar. -/
theorem X25519_eq_xMul (k u : Vector UInt8 32) :
    X25519 k u =
      encodeUCoordinate (montgomery.xMul 2 (decodeScalar25519 k) (decodeUCoordinate u)) := by
  rw [X25519, MontgomeryModel.ladder_eq_xMul not_isSquare_two (decodeScalar25519_lt k)]

/-- On the coordinate of a point `Q` of `montgomery`, `X25519 k` gives the coordinate of
`decodeScalar25519 k • Q`. -/
theorem X25519_eq_u_nsmul (k u : Vector UInt8 32) (Q : montgomery.Point)
    (hQ : Q.u = decodeUCoordinate u) :
    X25519 k u = encodeUCoordinate (decodeScalar25519 k • Q).u := by
  rw [X25519_eq_xMul, ← hQ, MontgomeryModel.xMul_eq_u_nsmul]

/-- On the coordinate of a point `Q` of the twist, `X25519 k` gives the coordinate of
`decodeScalar25519 k • Q`. -/
theorem X25519_eq_u_nsmul_twist (k u : Vector UInt8 32) (Q : montgomeryTwist.Point)
    (hQ : Q.u = decodeUCoordinate u) :
    X25519 k u = encodeUCoordinate (decodeScalar25519 k • Q).u := by
  rw [X25519_eq_xMul, ← hQ]
  have : (montgomery.twist 2).IsNonsingular := instIsNonsingularMontgomeryTwist
  exact congrArg encodeUCoordinate
    (MontgomeryModel.xMul_eq_u_nsmul_twist (M := montgomery) not_isSquare_two _ Q)

/-- **Diffie–Hellman agreement**: applying X25519 with `a` then `b`, or `b` then `a`, gives the
same bytes, for every coordinate `u` (with `u = 9`, both parties compute the same shared
secret). -/
theorem X25519_X25519_comm (a b u : Vector UInt8 32) :
    X25519 a (X25519 b u) = X25519 b (X25519 a u) := by
  simp only [X25519_eq_xMul, decodeUCoordinate_encodeUCoordinate,
    ← MontgomeryModel.xMul_mul not_isSquare_two]
  rw [Nat.mul_comm]

/-! ### The ladder over a sequence of bits -/

/-- The ladder over the bits `bs`, most significant first, is the x-only multiplication `xMul`
by the integer `n = Nat.ofDigits 2 (bs.reverse.map Bool.toNat)` with these bits: only `n`
matters, not leading zeros or the number of bits. -/
theorem montgomery_ladderBits_eq_xMul (bs : List Bool) (u : ZMod p) :
    montgomery.ladderBits bs u =
      montgomery.xMul 2 (Nat.ofDigits 2 (bs.reverse.map Bool.toNat)) u :=
  MontgomeryModel.ladderBits_eq_xMul not_isSquare_two bs u

/-- On the coordinate of a point `Q` of `montgomery`, the ladder over the bits `bs` gives the
coordinate of `n • Q`, for the integer `n` with the big-endian bits `bs`. -/
theorem montgomery_ladderBits_eq_u_nsmul (bs : List Bool) (Q : montgomery.Point) :
    montgomery.ladderBits bs Q.u = (Nat.ofDigits 2 (bs.reverse.map Bool.toNat) • Q).u := by
  rw [montgomery_ladderBits_eq_xMul, MontgomeryModel.xMul_eq_u_nsmul]

/-- On the coordinate of a point `Q` of the twist, the ladder over the bits `bs` gives the
coordinate of `n • Q`, for the integer `n` with the big-endian bits `bs`. -/
theorem montgomery_ladderBits_eq_u_nsmul_twist (bs : List Bool) (Q : montgomeryTwist.Point) :
    montgomery.ladderBits bs Q.u = (Nat.ofDigits 2 (bs.reverse.map Bool.toNat) • Q).u := by
  rw [montgomery_ladderBits_eq_xMul]
  have : (montgomery.twist 2).IsNonsingular := instIsNonsingularMontgomeryTwist
  exact MontgomeryModel.xMul_eq_u_nsmul_twist (M := montgomery) not_isSquare_two _ Q

end curve25519
