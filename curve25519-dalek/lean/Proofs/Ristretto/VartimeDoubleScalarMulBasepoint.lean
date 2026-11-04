/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
public import Curve25519.Edwards.Basepoint
public import Subtle
import Proofs.Edwards.VartimeDoubleScalarMulBasepoint
public section

/-! # `RistrettoPoint::vartime_double_scalar_mul_basepoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.«RistrettoPointx86_64-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«x86_64-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with edwards.«EdwardsPointx86_64-tables».vartime_double_scalar_mul_basepoint_spec
    a A b ha hA hon hb as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoPointx86_64-tables»

namespace ristretto.«RistrettoPointi686-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«i686-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with edwards.«EdwardsPointi686-tables».vartime_double_scalar_mul_basepoint_spec
    a A b ha hA hon hb as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoPointi686-tables»

namespace ristretto.«RistrettoPointx86_64-no-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with edwards.«EdwardsPointx86_64-no-tables».vartime_double_scalar_mul_basepoint_spec
    a A b ha hA hon hb as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoPointx86_64-no-tables»

namespace ristretto.«RistrettoPointi686-no-tables»

/-- `RistrettoPoint::vartime_double_scalar_mul_basepoint`: `a • A + b • B` for the basepoint `B`
(unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem vartime_double_scalar_mul_basepoint_spec (a : scalar.Scalar)
    (A : ristretto.RistrettoPoint.«i686-no-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_scalar_mul_basepoint a A b ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_double_scalar_mul_basepoint
  step with edwards.«EdwardsPointi686-no-tables».vartime_double_scalar_mul_basepoint_spec
    a A b ha hA hon hb as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoPointi686-no-tables»

end Curve25519Dalek
