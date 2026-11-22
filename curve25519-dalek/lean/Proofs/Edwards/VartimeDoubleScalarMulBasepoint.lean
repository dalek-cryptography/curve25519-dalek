/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Backend.VartimeDoubleBaseMul
public section

/-! # `EdwardsPoint::vartime_double_scalar_mul_basepoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«64bit-tables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.LimbsLt 52) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with backend.«64bit-tables».vartime_double_base_mul_spec as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hr, hrb⟩

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«32bit-tables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.LimbsLt 26) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with backend.«32bit-tables».vartime_double_base_mul_spec as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hr, hrb⟩

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«64bit-notables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.LimbsLt 52) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step*

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

/-- `EdwardsPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : EdwardsPoint.«32bit-notables») (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255)
    (hA : A.LimbsLt 26) (hon : A.OnCurve) (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step*

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
