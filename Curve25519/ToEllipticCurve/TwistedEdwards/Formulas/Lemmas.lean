/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import EllipticCurve.TwistedEdwards.Coords.Lemmas
public import EllipticCurve.TwistedEdwards.Formulas.Lemmas
public section

/-! # Scalar multiplication in extended coordinates and the group law (staged for `EllipticCurve`)

For points `P`, `Q` of a complete model away from `6`, `n • P = Q` iff the extended-coordinate
scalar multiple `Extended.nsmul n P.toExtended` is projectively equal to `Q.toExtended`
(`Point.nsmul_eq_iff_projEq`), and `n • P = 0` iff it passes the zero test
(`Point.nsmul_eq_zero_iff_isZero`). Both right-hand sides are free of field inversion, so the
kernel can decide them on constants: this is how group facts about given points (orders,
multiples) are certified.

Staged here for upstreaming to the `EllipticCurve` library: these depend only on the model and
on its coordinates. -/

universe u

namespace TwistedEdwardsModel.Point

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F} [E.IsComplete] [NeZero (6 : F)]

/-- `n • P = Q` iff `n • P` in extended coordinates is projectively equal to `Q`. -/
theorem nsmul_eq_iff_projEq (n : ℕ) (P Q : E.Point) :
    n • P = Q ↔ (Extended.nsmul n P.toExtended).ProjEq Q.toExtended := by
  rw [Extended.projEq_iff_toPoint_eq (Extended.nsmul_onCurve (onCurve_toExtended P) n)
    (onCurve_toExtended Q), Extended.toPoint_nsmul (onCurve_toExtended P), toPoint_toExtended,
    toPoint_toExtended]

/-- `n • P = 0` iff `n • P` in extended coordinates passes the zero test. -/
theorem nsmul_eq_zero_iff_isZero (n : ℕ) (P : E.Point) :
    n • P = 0 ↔ (Extended.nsmul n P.toExtended).IsZero := by
  rw [Extended.isZero_iff (Extended.nsmul_onCurve (onCurve_toExtended P) n),
    Extended.toPoint_nsmul (onCurve_toExtended P), toPoint_toExtended]

end TwistedEdwardsModel.Point
