module
public import Proofs.Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Backend.GetSelectedBackend
import Proofs.Backend.Serial.ScalarMul.VartimeDoubleBase.Mul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «64bit-tables»

/-- `vartime_double_base_mul`: the serial `vartime_double_base::mul`, `a • A + b • B`;
limbs `< 2^52`. -/
@[step]
theorem vartime_double_base_mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«64bit-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_base_mul.«64bit-tables» a A b ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • curve25519.basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold vartime_double_base_mul.«64bit-tables»
  step
  step with serial.scalar_mul.vartime_double_base.«64bit-tables».mul_spec as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hr, hrb⟩

end «64bit-tables»

namespace «32bit-tables»

/-- `vartime_double_base_mul`: the serial `vartime_double_base::mul`, `a • A + b • B`;
limbs `< 2^26`. -/
@[step]
theorem vartime_double_base_mul_spec (a : scalar.Scalar) (A : edwards.EdwardsPoint.«32bit-tables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_base_mul.«32bit-tables» a A b ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • curve25519.basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold vartime_double_base_mul.«32bit-tables»
  step
  step with serial.scalar_mul.vartime_double_base.«32bit-tables».mul_spec as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hr, hrb⟩

end «32bit-tables»

namespace «64bit-notables»

/-- `vartime_double_base_mul`: the serial `vartime_double_base::mul`, `a • A + b • B`;
limbs `< 2^52`. -/
@[step]
theorem vartime_double_base_mul_spec (a : scalar.Scalar)
    (A : edwards.EdwardsPoint.«64bit-notables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 52) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_base_mul.«64bit-notables» a A b
        ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • curve25519.basepoint ∧
        r.LimbsLt 52 ⦄ := by
  unfold vartime_double_base_mul.«64bit-notables»
  step*

end «64bit-notables»

namespace «32bit-notables»

/-- `vartime_double_base_mul`: the serial `vartime_double_base::mul`, `a • A + b • B`;
limbs `< 2^26`. -/
@[step]
theorem vartime_double_base_mul_spec (a : scalar.Scalar)
    (A : edwards.EdwardsPoint.«32bit-notables»)
    (b : scalar.Scalar) (ha : a.asNat < 2 ^ 255) (hA : A.LimbsLt 26) (hon : A.OnCurve)
    (hb : b.asNat < 2 ^ 255) :
    vartime_double_base_mul.«32bit-notables» a A b
        ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = a.asNat • A.toPoint + b.asNat • curve25519.basepoint ∧
        r.LimbsLt 26 ⦄ := by
  unfold vartime_double_base_mul.«32bit-notables»
  step*

end «32bit-notables»

end Curve25519Dalek.backend
