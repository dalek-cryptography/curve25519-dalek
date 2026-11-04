/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
public section

/-! # X25519 (RFC 7748 §5) on numbers

The function `X25519(k, u)` of RFC 7748 §5 on 32-byte strings, read as little-endian natural
numbers (`Array.asNat 8` on the dalek side): the scalar clamping `clamp` (`decodeScalar25519`:
clear bits `0`, `1`, `2` and `255`, set bit `254`), the coordinate decoding `decodeU`
(`decodeUCoordinate`: mask bit `255`, reduce modulo `p`), the encoding `encodeU`
(`encodeUCoordinate`: the canonical representative), and `x25519 k u = encodeU (ladder 255
(clamp k) (decodeU u))` with the Montgomery ladder of `montgomery` (`MontgomeryModel.ladder`,
RFC 7748 §5 with `a24 = 121665`). The RFC's final `x_2 * z_2^(p - 2)` is `x_2 / z_2` with
`x / 0 = 0` (`toU_eq_mul_pow_sub_two`).

The meaning: `x25519 k u` is the `u`-coordinate of `clamp k • Q` for any point `Q` of
`montgomery` or of its quadratic twist `montgomeryTwist = montgomery.twist 2` with
`u`-coordinate `decodeU u` (`x25519_eq_xMul` with `MontgomeryModel.xMul_eq_u_nsmul`,
`MontgomeryModel.xMul_eq_u_nsmul_twist`; `2` is not a square modulo `p`, `not_isSquare_two`).

`clamp`, `decodeU`, `encodeU` and `x25519` are exposed, so that they unfold (the kernel evaluates
`x25519` only where `p` unfolds too: the test vectors import `Curve25519.Basic` with `import all`);
`montgomeryTwist` is hidden (`montgomeryTwist_def`, `montgomeryTwist_A`, `montgomeryTwist_B`). -/

namespace curve25519

/-! ### Clamping and coordinate coding -/

/-- RFC 7748 `decodeScalar25519` on the little-endian value `k` of the 32 bytes: clear the
bits `0`, `1`, `2` and `255`, set the bit `254`. Matches dalek's `clamp_integer`
(`clamp_add_mod_eight`). -/
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
@[expose] noncomputable def x25519 (k u : ℕ) : ℕ :=
  encodeU (montgomery.ladder 255 (clamp k) (decodeU u))

theorem x25519_lt (k u : ℕ) : x25519 k u < p :=
  encodeU_lt _

/-- The ladder constant of curve25519 is `121665`. -/
theorem montgomery_a24_eq : montgomery.a24 = 121665 := by
  rw [MontgomeryModel.a24, montgomery_A_eq, div_eq_iff four_ne_zero]
  norm_num

/-! ### The quadratic twist -/

/-- The quadratic twist `2 v² = u³ + A u² + u` of `montgomery`: the other curve on which the
ladder computes (`x25519_eq_xMul`). -/
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

/-! ### The meaning of `x25519` -/

/-- `x25519 k u` is the x-only multiplication `xMul` by `clamp k` of `decodeU u`, which is
`u(clamp k • Q)` for a point `Q` of `montgomery` or of `montgomeryTwist` with `u`-coordinate
`decodeU u` (`MontgomeryModel.xMul_eq_u_nsmul`, `MontgomeryModel.xMul_eq_u_nsmul_twist`). -/
theorem x25519_eq_xMul (k u : ℕ) :
    x25519 k u = encodeU (montgomery.xMul 2 (clamp k) (decodeU u)) := by
  unfold x25519
  rw [MontgomeryModel.ladder_eq_xMul not_isSquare_two (clamp_lt k)]

/-- `x25519` on the `u`-coordinate of a point `Q` of `montgomery` is the `u`-coordinate of
`clamp k • Q`. -/
theorem x25519_eq_u_nsmul (k : ℕ) (Q : montgomery.Point) :
    x25519 k (encodeU Q.u) = encodeU (clamp k • Q).u := by
  rw [x25519_eq_xMul, decodeU_encodeU, MontgomeryModel.xMul_eq_u_nsmul]

/-- `x25519` on the `u`-coordinate of a point `Q` of the twist is the `u`-coordinate of
`clamp k • Q`. -/
theorem x25519_eq_u_nsmul_twist (k : ℕ) (Q : montgomeryTwist.Point) :
    x25519 k (encodeU Q.u) = encodeU (clamp k • Q).u := by
  rw [x25519_eq_xMul, decodeU_encodeU]
  have : (montgomery.twist 2).IsNonsingular := instIsNonsingularMontgomeryTwist
  exact congrArg encodeU
    (MontgomeryModel.xMul_eq_u_nsmul_twist (M := montgomery) not_isSquare_two (clamp k) Q)

/-- A coordinate whose `u ↦ u(8 • Q)` image is `0` (a point of order dividing `8` on the curve
or the twist, or `u = 0`) is sent to `0` by `x25519` for every scalar, since clamped scalars
are multiples of `8`. -/
theorem x25519_eq_zero_of_xMul_eight {u : ℕ} (h : montgomery.xMul 2 8 (decodeU u) = 0) (k : ℕ) :
    x25519 k u = 0 := by
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero (clamp_mod_eight k)
  rw [x25519_eq_xMul, hm, Nat.mul_comm, MontgomeryModel.xMul_mul not_isSquare_two, h,
    MontgomeryModel.xMul_zero_right, encodeU, ZMod.val_zero]

end curve25519
