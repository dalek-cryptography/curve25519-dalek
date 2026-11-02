/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Defs
public section

/-! # Twisted Edwards models: the equation solved for `x²` (staged for `EllipticCurve`)

`E.xSq y = (y² - 1) / (d y² - a)`: the equation `a x² + y² = 1 + d x² y²` solved for `x²`. On a
complete model, `(x, y)` is on the model iff `x ^ 2 = E.xSq y` (`equation_iff_sq_eq_xSq` in
`Curve25519.ToEllipticCurve.TwistedEdwards.Lemmas`). Point decoding (RFC 8032) recovers `x`
from `y` through it.

Staged here for upstreaming to the `EllipticCurve` library: it depends only on the model. -/

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F)

/-- `x²` as a function of `y` on the model: `(y² - 1) / (d y² - a)`, the equation
`a x² + y² = 1 + d x² y²` solved for `x²` (for `a = -1`, RFC 8032's `(y² - 1) / (d y² + 1)`).
On a complete model, `(x, y)` is on the model iff `x ^ 2 = E.xSq y`
(`equation_iff_sq_eq_xSq`). -/
@[expose] def xSq (y : F) : F :=
  (y ^ 2 - 1) / (E.d * y ^ 2 - E.a)

end TwistedEdwardsModel
