module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Backend.GetSelectedBackend
import Proofs.Backend.Serial.ScalarMul.VariableBase.Mul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «64bit-tables»

/-- `variable_base_mul`: the serial `variable_base::mul`, `scalar • P` for
`scalar.asNat < 2^255`; limbs `< 2^52`. -/
@[step]
theorem variable_base_mul_spec (point : edwards.EdwardsPoint.«64bit-tables»)
    (scalar : scalar.Scalar) (hpoint : point.LimbsLt 52) (hon : point.OnCurve)
    (hscalar : scalar.asNat < 2 ^ 255) :
    variable_base_mul.«64bit-tables» point scalar
      ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
        r.OnCurve ∧ r.toPoint = scalar.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold variable_base_mul.«64bit-tables»
  step*

end «64bit-tables»

namespace «32bit-tables»

/-- `variable_base_mul`: the serial `variable_base::mul`, `scalar • P` for
`scalar.asNat < 2^255`; limbs `< 2^26`. -/
@[step]
theorem variable_base_mul_spec (point : edwards.EdwardsPoint.«32bit-tables»)
    (scalar : scalar.Scalar) (hpoint : point.LimbsLt 26) (hon : point.OnCurve)
    (hscalar : scalar.asNat < 2 ^ 255) :
    variable_base_mul.«32bit-tables» point scalar
      ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
        r.OnCurve ∧ r.toPoint = scalar.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold variable_base_mul.«32bit-tables»
  step*

end «32bit-tables»

namespace «64bit-notables»

/-- `variable_base_mul`: the serial `variable_base::mul`, `scalar • P` for
`scalar.asNat < 2^255`; limbs `< 2^52`. -/
@[step]
theorem variable_base_mul_spec (point : edwards.EdwardsPoint.«64bit-notables»)
    (scalar : scalar.Scalar) (hpoint : point.LimbsLt 52) (hon : point.OnCurve)
    (hscalar : scalar.asNat < 2 ^ 255) :
    variable_base_mul.«64bit-notables» point scalar
      ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
        r.OnCurve ∧ r.toPoint = scalar.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold variable_base_mul.«64bit-notables»
  step*

end «64bit-notables»

namespace «32bit-notables»

/-- `variable_base_mul`: the serial `variable_base::mul`, `scalar • P` for
`scalar.asNat < 2^255`; limbs `< 2^26`. -/
@[step]
theorem variable_base_mul_spec (point : edwards.EdwardsPoint.«32bit-notables»)
    (scalar : scalar.Scalar) (hpoint : point.LimbsLt 26) (hon : point.OnCurve)
    (hscalar : scalar.asNat < 2 ^ 255) :
    variable_base_mul.«32bit-notables» point scalar
      ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
        r.OnCurve ∧ r.toPoint = scalar.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold variable_base_mul.«32bit-notables»
  step*

end «32bit-notables»

end Curve25519Dalek.backend
