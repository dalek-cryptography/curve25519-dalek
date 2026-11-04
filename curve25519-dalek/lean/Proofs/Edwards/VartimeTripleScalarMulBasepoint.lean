/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Backend.VartimeTripleBaseMul128128256
public section

/-! # `EdwardsPoint::vartime_triple_scalar_mul_basepoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (`a1, a2 < 2^128`, the `HalfWidthScalar` invariant); limbs `< 2^52`. -/
@[step]
theorem vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«x86_64-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«x86_64-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold vartime_triple_scalar_mul_basepoint
  step*

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (`a1, a2 < 2^128`, the `HalfWidthScalar` invariant); limbs `< 2^26`. -/
@[step]
theorem vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«i686-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«i686-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold vartime_triple_scalar_mul_basepoint
  step*

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (`a1, a2 < 2^128`, the `HalfWidthScalar` invariant); limbs `< 2^52`. -/
@[step]
theorem vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«x86_64-no-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«x86_64-no-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold vartime_triple_scalar_mul_basepoint
  step*

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

/-- `EdwardsPoint::vartime_triple_scalar_mul_basepoint`: `a1 • A1 + a2 • A2 + b • B` for the
basepoint `B` (`a1, a2 < 2^128`, the `HalfWidthScalar` invariant); limbs `< 2^26`. -/
@[step]
theorem vartime_triple_scalar_mul_basepoint_spec (a1 : scalar.HalfWidthScalar)
    (A1 : EdwardsPoint.«i686-no-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : EdwardsPoint.«i686-no-tables»)
    (b : scalar.Scalar) (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    vartime_triple_scalar_mul_basepoint a1 A1 a2 A2 b ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧
        r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint + b.asNat • basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold vartime_triple_scalar_mul_basepoint
  step*

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
