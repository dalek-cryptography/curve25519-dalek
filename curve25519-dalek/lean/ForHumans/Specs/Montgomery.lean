/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Edwards
public section

namespace curve25519

open MontgomeryModel TwistedEdwardsModel

/-- The group isomorphism `edwards.Point ≃+ montgomery.Point` of RFC 7748 §4.1, `(x, y) ↦ ((1 + y) /
(1 - y), sqrtNegAAddTwo · (1 + y) / ((1 - y) x))`. Hidden; characterised by `u_edwardsToMontgomery`,
`v_edwardsToMontgomery`, `edwardsToMontgomery_of_y_eq_one`, `edwardsToMontgomery_of_y_eq_neg_one`,
`edwardsToMontgomery_symm_x`, `edwardsToMontgomery_symm_y`. -/
noncomputable def edwardsToMontgomery : edwards.Point ≃+ montgomery.Point :=
  edwards.toMontgomeryEquiv.trans
    (rescaleEquiv edwards.toMontgomery montgomery edwards_toMontgomery_A.symm sqrtNegAAddTwo
      sqrtNegAAddTwo_ne_zero montgomery_B_mul_sqrtNegAAddTwo_sq)

/-- The basepoint of `montgomery`: the image of `basepoint`, with `u = 9` (RFC 7748 §4.1). -/
noncomputable def montgomeryBasepoint : montgomery.Point :=
  edwardsToMontgomery basepoint

end curve25519
