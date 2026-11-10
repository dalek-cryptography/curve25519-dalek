/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import all Curve25519.Basic
import Curve25519.X25519.LowOrder
public import Proofs.Helpers.ByteValues
public section

/-! # `X25519_LOW_ORDER_POINTS`

`X25519_LOW_ORDER_POINTS_spec`: a point is sent to `0` by every scalar iff its coordinate is
that of one of the seven entries.

The seven are sent to `0`: each coordinate is sent to `0` by `u ↦ u(8 • Q)`, a kernel evaluation
(`decide +kernel`) of the 4-bit ladder on `8` in projective form (`XZ.ladderXZ`, no field
inversion) ending at infinity (`W = 0`), and clamped scalars are multiples of `8`
(`curve25519.x25519Nat_eq_zero_of_xMul_eight`). No other coordinate is: a coordinate sent to `0` by
every scalar is one of `0`, `1`, `-1`, `u₈`, `u₈⁻¹` (`curve25519.x25519Nat_eq_zero_iff`), and a
kernel evaluation decodes the entries `0` to `4` to these five. `Curve25519.Basic` is imported
with `import all` so that the kernel can unfold `p`. -/

open Aeneas Aeneas.Std curve25519 MontgomeryModel

namespace Curve25519Dalek.constants

/-- `u(8 • Q) = 0` from a kernel check of the projective ladder on `8`. -/
private theorem xMul_eight_eq_zero {u : ZMod p} (h : (XZ.ladderXZ 121665 4 8 u).W = 0) :
    montgomery.xMul 2 8 u = 0 := by
  rw [← ladder_eq_xMul not_isSquare_two (by norm_num : 8 < 2 ^ 4)]
  unfold MontgomeryModel.ladder XZ.ladder
  rw [montgomery_a24_eq, XZ.toU, h, div_zero]

/-- X25519 sends each of the seven points to `0`, whatever the scalar. -/
private theorem x25519Nat_entry_eq_zero :
    ∀ i : Fin 7, ∀ k : ℕ, x25519Nat k X25519_LOW_ORDER_POINTS[i.val]!.asNat = 0 := by
  have h : ∀ i : Fin 7, (XZ.ladderXZ 121665 4 8
      (decodeU (Nat.ofDigits (2 ^ 8) (X25519_LOW_ORDER_POINTS[i.val]!.val.map (·.val))))).W =
      0 := by
    unfold X25519_LOW_ORDER_POINTS
    decide +kernel
  intro i k
  rw [montgomery.MontgomeryPoint.asNat_def, Array.asNat_def]
  exact x25519Nat_eq_zero_of_xMul_eight (xMul_eight_eq_zero (h i)) k

/-- The `u`-coordinates of the entries `0` to `4`: `0`, `1`, `u₈`, `u₈⁻¹` and `-1` (the entries
`5` and `6` are the non-canonical encodings `p` and `p + 1` of `0` and `1`). -/
private theorem u_entries :
    decodeUCoordinate X25519_LOW_ORDER_POINTS[0]!.toVector = 0 ∧
      decodeUCoordinate X25519_LOW_ORDER_POINTS[1]!.toVector = 1 ∧
      decodeUCoordinate X25519_LOW_ORDER_POINTS[2]!.toVector = u8 ∧
      decodeUCoordinate X25519_LOW_ORDER_POINTS[3]!.toVector = u8⁻¹ ∧
      decodeUCoordinate X25519_LOW_ORDER_POINTS[4]!.toVector = -1 := by
  simp only [montgomery.MontgomeryPoint.decodeUCoordinate_toVector,
    montgomery.MontgomeryPoint.asNat_def, Array.asNat_def, u8_inv]
  unfold X25519_LOW_ORDER_POINTS
  decide +kernel

/-- `X25519_LOW_ORDER_POINTS`: a point is sent to `0` by X25519 for every scalar iff it is equal
to one of the seven points as a `MontgomeryPoint`, that is with `==`, which compares the decoded
coordinates (`decodeUCoordinate`; not the bytes: other encodings of the same coordinate count). In
particular each of the seven points is sent to `0`. -/
theorem X25519_LOW_ORDER_POINTS_spec (Q : montgomery.MontgomeryPoint) :
    (∀ k : Vector UInt8 32, X25519 k Q.toVector = encodeUCoordinate 0) ↔
      ∃ i : Fin 7, decodeUCoordinate Q.toVector =
        decodeUCoordinate X25519_LOW_ORDER_POINTS[i.val]!.toVector := by
  rw [forall_X25519_eq_zero_iff, montgomery.MontgomeryPoint.decodeLittleEndian_toVector]
  constructor
  · intro h
    obtain ⟨h0, h1, h2, h3, h4⟩ := u_entries
    rcases (x25519Nat_eq_zero_iff Q.asNat).mp h with h | h | h | h | h <;>
      rw [← montgomery.MontgomeryPoint.decodeUCoordinate_toVector] at h
    · exact ⟨0, h.trans h0.symm⟩
    · exact ⟨1, h.trans h1.symm⟩
    · exact ⟨4, h.trans h4.symm⟩
    · exact ⟨2, h.trans h2.symm⟩
    · exact ⟨3, h.trans h3.symm⟩
  · rintro ⟨i, hi⟩ k
    have hk := x25519Nat_entry_eq_zero i k
    rw [x25519Nat_eq_xMul] at hk ⊢
    rwa [← montgomery.MontgomeryPoint.decodeUCoordinate_toVector, hi,
      montgomery.MontgomeryPoint.decodeUCoordinate_toVector]

end Curve25519Dalek.constants
