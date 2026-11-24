module
public import Proofs.Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Backend.VartimeTripleBaseMul128128256
public section

/-! # `EdwardsPoint::vartime_triple_scalar_mul_basepoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (`a1, a2 < 2^128`, the `HalfWidthScalar` invariant; any `b`, which the code splits
into two `128`-bit halves); limbs `< 2^52`. -/
@[step]
theorem vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«64bit-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«64bit-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold vartime_triple_scalar_mul_basepoint
  step*

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (`a1, a2 < 2^128`, the `HalfWidthScalar` invariant; any `b`, which the code splits
into two `128`-bit halves); limbs `< 2^26`. -/
@[step]
theorem vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«32bit-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«32bit-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold vartime_triple_scalar_mul_basepoint
  step*

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (`a1, a2 < 2^128`, the `HalfWidthScalar` invariant; any `b`, which the code splits
into two `128`-bit halves); limbs `< 2^52`. -/
@[step]
theorem vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«64bit-notables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«64bit-notables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold vartime_triple_scalar_mul_basepoint
  step*

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (`a1, a2 < 2^128`, the `HalfWidthScalar` invariant; any `b`, which the code splits
into two `128`-bit halves); limbs `< 2^26`. -/
@[step]
theorem vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«32bit-notables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«32bit-notables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold vartime_triple_scalar_mul_basepoint
  step*

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
