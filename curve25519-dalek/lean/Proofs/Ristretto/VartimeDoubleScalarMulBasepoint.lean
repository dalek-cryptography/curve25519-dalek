/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
public import Proofs.Curve25519.Edwards.Basepoint
public import Proofs.External.Subtle
import Proofs.Edwards.VartimeDoubleScalarMulBasepoint
public section

/-! # `RistrettoPoint::vartime_double_scalar_mul_basepoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.«RistrettoPoint64bit-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«64bit-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with edwards.«EdwardsPoint64bit-tables».vartime_double_scalar_mul_basepoint_spec
    a A b ha hA hon hb as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoPoint64bit-tables»

namespace ristretto.«RistrettoPoint32bit-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«32bit-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with edwards.«EdwardsPoint32bit-tables».vartime_double_scalar_mul_basepoint_spec
    a A b ha hA hon hb as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoPoint32bit-tables»

namespace ristretto.«RistrettoPoint64bit-notables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«64bit-notables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with edwards.«EdwardsPoint64bit-notables».vartime_double_scalar_mul_basepoint_spec
    a A b ha hA hon hb as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoPoint64bit-notables»

namespace ristretto.«RistrettoPoint32bit-notables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«32bit-notables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with edwards.«EdwardsPoint32bit-notables».vartime_double_scalar_mul_basepoint_spec
    a A b ha hA hon hb as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoPoint32bit-notables»

end Curve25519Dalek
