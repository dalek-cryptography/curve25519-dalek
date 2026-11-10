/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Order
public import Curve25519.X25519
import Curve25519.Proofs.Edwards.Certs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
public section

/-! # The Montgomery model of curve25519 and its twist

The birational isomorphism `edwardsToMontgomery : edwards.Point ≃+ montgomery.Point` of
RFC 7748 §4.1, `(x, y) ↦ (u, v) = ((1 + y) / (1 - y), √(-486664) · u / x)` with the inverse
`(u, v) ↦ (√(-486664) · u / v, (u - 1) / (u + 1))`: the generic `toMontgomeryEquiv` of `edwards`
onto its Montgomery model `(A, 4 / (a - d))`, followed by the rescaling `v ↦ sqrtNegAAddTwo · v`
onto `montgomery = (A, 1)` (`MontgomeryModel.rescaleEquiv`), where `sqrtNegAAddTwo` is the square
root of `-486664` that RFC 7748's base points determine. It is hidden, pinned in both
directions by `u_edwardsToMontgomery`, `v_edwardsToMontgomery`, `edwardsToMontgomery_of_y_eq_one`,
`edwardsToMontgomery_of_y_eq_neg_one`, `edwardsToMontgomery_symm_x`, `edwardsToMontgomery_symm_y`.

The Montgomery basepoint `montgomeryBasepoint = edwardsToMontgomery basepoint` is RFC 7748's
base point `(9, V(P))` (`u_montgomeryBasepoint`, `v_montgomeryBasepoint`) and has order `L`, and
`x25519Nat k 9` is the `u`-coordinate of `clamp k • montgomeryBasepoint` (`x25519Nat_basepoint`),
i.e. of `edwardsToMontgomery (clamp k • basepoint)` (`x25519Nat_basepoint_edwards`); more
generally `x25519Nat_edwards`. On bytes: `X25519_basepoint`, `X25519_edwards`.

The quadratic twist `montgomeryTwist = montgomery.twist 2` has `4 L'` points with
`L' = twistL = 2^253 - 55484635554744707071703875581767296995` (`card_twist`, from the generic
count `MontgomeryModel.card_add_card_twist` and `card_montgomery = 8 L`), and every `u` is the
`u`-coordinate of a point of `montgomery` or of `montgomeryTwist`
(`exists_montgomery_point_u_or_twist`). As the decoded scalar is a multiple of the cofactor `8`,
the output of X25519 is the `u`-coordinate of a point of order dividing `L` on the curve or `L'`
on the twist (`X25519_eq_u_of_nsmul_eq_zero`). -/

namespace curve25519

open MontgomeryModel TwistedEdwardsModel

/-! ### The equivalence `edwards ≃+ montgomery` -/

/-- `montgomery = (A, 1)` is the rescaling of the Montgomery model `(A, sqrtNegAAddTwo²)` of
`edwards` by `sqrtNegAAddTwo`. -/
theorem montgomery_B_mul_sqrtNegAAddTwo_sq :
    montgomery.B * (sqrtNegAAddTwo : ZMod p) ^ 2 = edwards.toMontgomery.B := by
  rw [montgomery_B, edwards_toMontgomery_B, one_mul]

/-- The group isomorphism `edwards.Point ≃+ montgomery.Point` of RFC 7748 §4.1,
`(x, y) ↦ ((1 + y) / (1 - y), sqrtNegAAddTwo · (1 + y) / ((1 - y) x))`. Hidden; characterised by
`u_edwardsToMontgomery`, `v_edwardsToMontgomery`, `edwardsToMontgomery_of_y_eq_one`,
`edwardsToMontgomery_of_y_eq_neg_one`, `edwardsToMontgomery_symm_x`,
`edwardsToMontgomery_symm_y`. -/
noncomputable def edwardsToMontgomery : edwards.Point ≃+ montgomery.Point :=
  edwards.toMontgomeryEquiv.trans
    (rescaleEquiv edwards.toMontgomery montgomery edwards_toMontgomery_A.symm sqrtNegAAddTwo
      sqrtNegAAddTwo_ne_zero montgomery_B_mul_sqrtNegAAddTwo_sq)

private theorem edwardsToMontgomery_apply (P : edwards.Point) :
    edwardsToMontgomery P =
      rescaleEquiv edwards.toMontgomery montgomery edwards_toMontgomery_A.symm sqrtNegAAddTwo
        sqrtNegAAddTwo_ne_zero montgomery_B_mul_sqrtNegAAddTwo_sq
        (edwards.toMontgomeryEquiv P) := by
  rfl

private theorem edwardsToMontgomery_symm_apply (Q : montgomery.Point) :
    edwardsToMontgomery.symm Q =
      edwards.toMontgomeryEquiv.symm
        ((rescaleEquiv edwards.toMontgomery montgomery edwards_toMontgomery_A.symm sqrtNegAAddTwo
          sqrtNegAAddTwo_ne_zero montgomery_B_mul_sqrtNegAAddTwo_sq).symm Q) := by
  rfl

/-- The `u`-coordinate of the image of `P` is `(1 + y) / (1 - y)` (`0` at `(0, 1)`, whose image
is `∞`). -/
theorem u_edwardsToMontgomery (P : edwards.Point) :
    (edwardsToMontgomery P).u = (1 + P.y) / (1 - P.y) := by
  rw [edwardsToMontgomery_apply, u_rescaleEquiv, u_toMontgomeryEquiv]

/-- The `v`-coordinate of the image of `P` is `sqrtNegAAddTwo · (1 + y) / ((1 - y) x)` away
from `(0, 1)`: RFC 7748's `v = √(-486664) · u / x`. -/
theorem v_edwardsToMontgomery (P : edwards.Point) (hy : P.y ≠ 1) :
    (edwardsToMontgomery P).v = sqrtNegAAddTwo * ((1 + P.y) / ((1 - P.y) * P.x)) := by
  rw [edwardsToMontgomery_apply, v_rescaleEquiv, v_toMontgomeryEquiv P hy]

/-- The image of `(0, 1)` is the point at infinity. -/
theorem edwardsToMontgomery_of_y_eq_one (P : edwards.Point) (h : P.y = 1) :
    edwardsToMontgomery P = 0 := by
  rw [edwardsToMontgomery_apply, toMontgomeryEquiv_of_y_eq_one P h, map_zero]

/-- The image of `(0, -1)` (the only point with `y = -1`) is `(0, 0)`. -/
theorem edwardsToMontgomery_of_y_eq_neg_one (P : edwards.Point) (hy : P.y = -1) :
    edwardsToMontgomery P = .some 0 0 montgomery.equation_zero_zero := by
  rw [edwardsToMontgomery_apply,
    toMontgomeryEquiv_of_x_eq_zero P (x_eq_zero_of_y_eq_neg_one P.equation hy) hy,
    rescaleEquiv_some, Point.some.injEq]
  exact ⟨rfl, mul_zero _⟩

/-- The `x`-coordinate of the preimage of a Montgomery point `Q` with `v ≠ 0` is
`sqrtNegAAddTwo · u / v`: RFC 7748's `x = √(-486664) · u / v`. -/
theorem edwardsToMontgomery_symm_x (Q : montgomery.Point) (hv : Q.v ≠ 0) :
    (edwardsToMontgomery.symm Q).x = sqrtNegAAddTwo * Q.u / Q.v := by
  rw [edwardsToMontgomery_symm_apply, toMontgomeryEquiv_symm_x _ (by
    rw [v_rescaleEquiv_symm]
    exact div_ne_zero hv sqrtNegAAddTwo_ne_zero), u_rescaleEquiv_symm, v_rescaleEquiv_symm,
    div_div_eq_mul_div, mul_comm]

/-- The `y`-coordinate of the preimage of an affine Montgomery point `Q` is `(u - 1) / (u + 1)`
(the preimage of `∞` is `(0, 1)`). -/
theorem edwardsToMontgomery_symm_y (Q : montgomery.Point) (hQ : Q ≠ 0) :
    (edwardsToMontgomery.symm Q).y = (Q.u - 1) / (Q.u + 1) := by
  rw [edwardsToMontgomery_symm_apply,
    toMontgomeryEquiv_symm_y _ ((AddEquiv.map_ne_zero_iff _).mpr hQ), u_rescaleEquiv_symm]

/-! ### The Montgomery basepoint -/

/-- The basepoint of `montgomery`: the image of `basepoint`, with `u = 9` (RFC 7748 §4.1). -/
noncomputable def montgomeryBasepoint : montgomery.Point :=
  edwardsToMontgomery basepoint

theorem montgomeryBasepoint_def : montgomeryBasepoint = edwardsToMontgomery basepoint := by
  unfold montgomeryBasepoint
  rfl

/-- The Montgomery basepoint has `u = 9`: `(1 + 4/5) / (1 - 4/5) = 9`. -/
theorem u_montgomeryBasepoint : montgomeryBasepoint.u = 9 := by
  have h5 : (5 : ZMod p) ≠ 0 := NeZero.ne 5
  have h15 : (1 : ZMod p) - 4 / 5 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [eq_div_iff h5] at h
    exact one_ne_zero (by linear_combination h)
  rw [montgomeryBasepoint_def, u_edwardsToMontgomery, basepoint_y, div_eq_iff h15]
  field_simp
  ring

/-- RFC 7748 §4.1: the Montgomery basepoint has `v = V(P)`, the RFC's base point. -/
theorem v_montgomeryBasepoint : montgomeryBasepoint.v =
    14781619447589544791020593568409986887264606134616475288964881837755586237401 := by
  have hden := Proofs.basepoint_den_ne_zero
  have hy : basepoint.y ≠ 1 := by
    intro h
    apply hden
    rw [← basepoint_y_eq, h, sub_self, zero_mul]
  rw [montgomeryBasepoint_def, v_edwardsToMontgomery _ hy, basepoint_x_eq, basepoint_y_eq,
    mul_div_assoc', div_eq_iff hden]
  exact Proofs.basepoint_v_mul_den.symm

/-- The Montgomery basepoint has prime order `L`. -/
theorem addOrderOf_montgomeryBasepoint : addOrderOf montgomeryBasepoint = L := by
  rw [montgomeryBasepoint_def, AddEquiv.addOrderOf_eq, addOrderOf_basepoint]

/-! ### `x25519Nat` on the basepoint and on Edwards points -/

/-- `x25519Nat k 9` is the `u`-coordinate of `clamp k • montgomeryBasepoint`. -/
theorem x25519Nat_basepoint (k : ℕ) : x25519Nat k 9 = encodeU
    (clamp k • montgomeryBasepoint).u := by
  have h := x25519Nat_eq_u_nsmul k montgomeryBasepoint
  rwa [u_montgomeryBasepoint, encodeU_nine] at h

/-- `x25519Nat k 9` is the `u`-coordinate of the image in `montgomery` of `clamp k • basepoint`:
the meaning of dalek's `mul_base_clamped` followed by `to_montgomery`. -/
theorem x25519Nat_basepoint_edwards (k : ℕ) :
    x25519Nat k 9 = encodeU (edwardsToMontgomery (clamp k • basepoint)).u := by
  rw [x25519Nat_basepoint, montgomeryBasepoint_def, map_nsmul]

/-- `x25519Nat` on the `u`-coordinate of the image of an Edwards point `P` is the `u`-coordinate
of the image of `clamp k • P`. -/
theorem x25519Nat_edwards (k : ℕ) (P : edwards.Point) :
    x25519Nat k (encodeU (edwardsToMontgomery P).u) =
      encodeU (edwardsToMontgomery (clamp k • P)).u := by
  rw [x25519Nat_eq_u_nsmul, map_nsmul]

/-- `X25519 k` on the coordinate `9` gives the coordinate of
`decodeScalar25519 k • montgomeryBasepoint`. -/
theorem X25519_basepoint (k : Vector UInt8 32) :
    X25519 k (encodeUCoordinate 9) =
      encodeUCoordinate (decodeScalar25519 k • montgomeryBasepoint).u :=
  X25519_eq_u_nsmul k _ _ (by rw [decodeUCoordinate_encodeUCoordinate, u_montgomeryBasepoint])

/-- `X25519 k` on the coordinate of the image of an Edwards point `P` gives the coordinate of the
image of `decodeScalar25519 k • P`. -/
theorem X25519_edwards (k : Vector UInt8 32) (P : edwards.Point) :
    X25519 k (encodeUCoordinate (edwardsToMontgomery P).u) =
      encodeUCoordinate (edwardsToMontgomery (decodeScalar25519 k • P)).u := by
  rw [X25519_eq_u_nsmul k _ _ (decodeUCoordinate_encodeUCoordinate _).symm, map_nsmul]

/-! ### The twist -/

/-- `montgomery` and its twist have `2 p + 2` points in total (the generic
`MontgomeryModel.card_add_card_twist`, as `2` is not a square). -/
theorem card_montgomery_add_card_twist :
    Nat.card montgomery.Point + Nat.card montgomeryTwist.Point = 2 * p + 2 := by
  have h := card_add_card_twist montgomery two_ne_zero IsNonsingular.B_ne_zero not_isSquare_two
  rwa [← montgomeryTwist_def, ZMod.card] at h

/-- **The cardinality of the twist**: `4 L'` points, `L' = twistL`. -/
theorem card_twist : Nat.card montgomeryTwist.Point = 4 * twistL := by
  have h := card_montgomery_add_card_twist
  rw [card_montgomery, two_mul_p_add_two] at h
  omega

/-- Every `u` is the `u`-coordinate of a point of `montgomery` or of `montgomeryTwist`
(`MontgomeryModel.exists_point_u_or_twist`, as `2` is not a square). -/
theorem exists_montgomery_point_u_or_twist (u : ZMod p) :
    (∃ P : montgomery.Point, P.u = u) ∨ ∃ P : montgomeryTwist.Point, P.u = u := by
  rw [montgomeryTwist_def]
  exact exists_point_u_or_twist not_isSquare_two u

/-! ### Small-subgroup safety -/

/-- In a group with `c * N` elements, `N • n • Q = 0` when `n` is a multiple of `c`. -/
private theorem nsmul_nsmul_eq_zero {G : Type*} [AddCommGroup G] {N c n : ℕ}
    (hcard : Nat.card G = c * N) (hn : n % c = 0) (Q : G) : N • n • Q = 0 := by
  obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero hn
  rw [smul_smul, show N * (c * m) = m * Nat.card G by rw [hcard]; ring, ← smul_smul,
    card_nsmul_eq_zero', smul_zero]

/-- **Small-subgroup safety**: as the decoded scalar is a multiple of the cofactor `8`, the
output of X25519 is the coordinate of a point of order dividing `L` on the curve, or of a point
of order dividing `L' = twistL` on the twist (whatever the input: a point of small order
contributes nothing). -/
theorem X25519_eq_u_of_nsmul_eq_zero (k u : Vector UInt8 32) :
    (∃ R : montgomery.Point, L • R = 0 ∧ X25519 k u = encodeUCoordinate R.u) ∨
      ∃ R : montgomeryTwist.Point, twistL • R = 0 ∧ X25519 k u = encodeUCoordinate R.u := by
  rcases exists_montgomery_point_u_or_twist (decodeUCoordinate u) with ⟨Q, hQ⟩ | ⟨Q, hQ⟩
  · exact Or.inl ⟨decodeScalar25519 k • Q,
      nsmul_nsmul_eq_zero card_montgomery (decodeScalar25519_mod_eight k) Q,
      X25519_eq_u_nsmul k u Q hQ⟩
  · have h4 : decodeScalar25519 k % 4 = 0 := by
      have := decodeScalar25519_mod_eight k
      omega
    exact Or.inr ⟨decodeScalar25519 k • Q, nsmul_nsmul_eq_zero card_twist h4 Q,
      X25519_eq_u_nsmul_twist k u Q hQ⟩

end curve25519
