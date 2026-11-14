/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs.Edwards
public section

/-! # The isomorphism between edwards25519 and curve25519

RFC 7748 §4.1's map from the Edwards model to the Montgomery model, as a group isomorphism, and the
Montgomery basepoint. -/

namespace curve25519

open MontgomeryModel TwistedEdwardsModel

/-- The group isomorphism `edwards.Point ≃+ montgomery.Point` of RFC 7748 §4.1,
`(x, y) ↦ ((1 + y) / (1 - y), sqrtNegAAddTwo · (1 + y) / ((1 - y) x))`: the `EllipticCurve`
library's isomorphism to the Montgomery model `(A, 4 / (a - d))` of `edwards`, rescaled to
`montgomery = (A, 1)` by `v ↦ v / sqrtNegAAddTwo`. The formula is proved in
`Proofs/Curve25519/Montgomery.lean` (`u_edwardsToMontgomery`, `v_edwardsToMontgomery`). -/
noncomputable def edwardsToMontgomery : edwards.Point ≃+ montgomery.Point :=
  edwards.toMontgomeryEquiv.trans
    (rescaleEquiv edwards.toMontgomery montgomery edwards_toMontgomery_A.symm sqrtNegAAddTwo
      sqrtNegAAddTwo_ne_zero montgomery_B_mul_sqrtNegAAddTwo_sq)

/-- The basepoint of `montgomery`: the image of `basepoint`, with `u = 9` (RFC 7748 §4.1). -/
noncomputable def montgomeryBasepoint : montgomery.Point :=
  edwardsToMontgomery basepoint

end curve25519
