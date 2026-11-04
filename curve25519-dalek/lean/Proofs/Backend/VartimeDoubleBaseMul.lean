/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Backend.GetSelectedBackend
import Proofs.Backend.Serial.ScalarMul.VartimeDoubleBase.Mul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «x86_64-tables»

/-- `vartime_double_base_mul`: the serial `vartime_double_base::mul`, `a • A + b • B`;
limbs `< 2^52`. -/
@[step]
theorem vartime_double_base_mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«x86_64-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_base_mul.«x86_64-tables» a A b ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • curve25519.basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold vartime_double_base_mul.«x86_64-tables»
  step
  step with serial.scalar_mul.vartime_double_base.«x86_64-tables».mul_spec as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hr, hrb⟩

end «x86_64-tables»

namespace «i686-tables»

/-- `vartime_double_base_mul`: the serial `vartime_double_base::mul`, `a • A + b • B`;
limbs `< 2^26`. -/
@[step]
theorem vartime_double_base_mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«i686-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_base_mul.«i686-tables» a A b ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • curve25519.basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold vartime_double_base_mul.«i686-tables»
  step
  step with serial.scalar_mul.vartime_double_base.«i686-tables».mul_spec as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hr, hrb⟩

end «i686-tables»

namespace «x86_64-no-tables»

/-- `vartime_double_base_mul`: the serial `vartime_double_base::mul`, `a • A + b • B`;
limbs `< 2^52`. -/
@[step]
theorem vartime_double_base_mul_spec (a : scalar.Scalar)
    (A : edwards.EdwardsPoint.«x86_64-no-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_base_mul.«x86_64-no-tables» a A b
        ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • curve25519.basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold vartime_double_base_mul.«x86_64-no-tables»
  step*

end «x86_64-no-tables»

namespace «i686-no-tables»

/-- `vartime_double_base_mul`: the serial `vartime_double_base::mul`, `a • A + b • B`;
limbs `< 2^26`. -/
@[step]
theorem vartime_double_base_mul_spec (a : scalar.Scalar)
    (A : edwards.EdwardsPoint.«i686-no-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_base_mul.«i686-no-tables» a A b
        ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • curve25519.basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold vartime_double_base_mul.«i686-no-tables»
  step*

end «i686-no-tables»

end Curve25519Dalek.backend
