/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import all Curve25519.Basic
public section

/-! # `X25519_LOW_ORDER_POINTS`

Each of the seven coordinates is sent to `0` by `u ↦ u(8 • Q)`: a kernel evaluation
(`decide +kernel`) of the 4-bit ladder on `8` in projective form (`XZ.ladderXZ`, no field
inversion) ends at infinity (`W = 0`). Clamped scalars are multiples of `8`, so `x25519` sends
them to `0` (`curve25519.x25519_eq_zero_of_xMul_eight`). `Curve25519.Basic` is imported with
`import all` so that the kernel can unfold `p`. -/

open Aeneas Aeneas.Std curve25519 MontgomeryModel

namespace Curve25519Dalek.constants

/-- `u(8 • Q) = 0` from a kernel check of the projective ladder on `8`. -/
private theorem xMul_eight_eq_zero {u : ZMod p} (h : (XZ.ladderXZ 121665 4 8 u).W = 0) :
    montgomery.xMul 2 8 u = 0 := by
  rw [← ladder_eq_xMul not_isSquare_two (by norm_num : 8 < 2 ^ 4)]
  unfold MontgomeryModel.ladder XZ.ladder
  rw [montgomery_a24_eq, XZ.toU, h, div_zero]

/-- `X25519_LOW_ORDER_POINTS`: X25519 sends each of the seven points to `0`, whatever the
scalar. -/
theorem X25519_LOW_ORDER_POINTS_spec :
    ∀ P ∈ X25519_LOW_ORDER_POINTS.val, ∀ k : ℕ, x25519 k P.asNat = 0 := by
  have h : ∀ P ∈ X25519_LOW_ORDER_POINTS.val,
      (XZ.ladderXZ 121665 4 8 (decodeU (Nat.ofDigits (2 ^ 8) (P.val.map (·.val))))).W = 0 := by
    unfold X25519_LOW_ORDER_POINTS
    decide +kernel
  intro P hP k
  rw [montgomery.MontgomeryPoint.asNat_def, Array.asNat_def]
  exact x25519_eq_zero_of_xMul_eight (xMul_eight_eq_zero (h P hP)) k

end Curve25519Dalek.constants
