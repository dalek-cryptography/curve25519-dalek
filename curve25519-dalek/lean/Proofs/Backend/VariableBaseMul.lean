/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Backend.GetSelectedBackend
import Proofs.Backend.Serial.ScalarMul.VariableBase.Mul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «x86_64-tables»

/-- `variable_base_mul`: the serial `variable_base::mul`, `scalar • P` for
`scalar.asNat < 2^255`; limbs `< 2^52`. -/
@[step]
theorem variable_base_mul_spec (point : edwards.EdwardsPoint.«x86_64-tables»)
    (scalar : scalar.Scalar) (hpoint : point.LimbsLt 52) (hon : point.OnCurve)
    (hscalar : scalar.asNat < 2 ^ 255) :
    variable_base_mul.«x86_64-tables» point scalar
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = scalar.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold variable_base_mul.«x86_64-tables»
  step*

end «x86_64-tables»

namespace «i686-tables»

/-- `variable_base_mul`: the serial `variable_base::mul`, `scalar • P` for
`scalar.asNat < 2^255`; limbs `< 2^26`. -/
@[step]
theorem variable_base_mul_spec (point : edwards.EdwardsPoint.«i686-tables»)
    (scalar : scalar.Scalar) (hpoint : point.LimbsLt 26) (hon : point.OnCurve)
    (hscalar : scalar.asNat < 2 ^ 255) :
    variable_base_mul.«i686-tables» point scalar
      ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
        r.OnCurve ∧ r.toPoint = scalar.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold variable_base_mul.«i686-tables»
  step*

end «i686-tables»

namespace «x86_64-no-tables»

/-- `variable_base_mul`: the serial `variable_base::mul`, `scalar • P` for
`scalar.asNat < 2^255`; limbs `< 2^52`. -/
@[step]
theorem variable_base_mul_spec (point : edwards.EdwardsPoint.«x86_64-no-tables»)
    (scalar : scalar.Scalar) (hpoint : point.LimbsLt 52) (hon : point.OnCurve)
    (hscalar : scalar.asNat < 2 ^ 255) :
    variable_base_mul.«x86_64-no-tables» point scalar
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
        r.OnCurve ∧ r.toPoint = scalar.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold variable_base_mul.«x86_64-no-tables»
  step*

end «x86_64-no-tables»

namespace «i686-no-tables»

/-- `variable_base_mul`: the serial `variable_base::mul`, `scalar • P` for
`scalar.asNat < 2^255`; limbs `< 2^26`. -/
@[step]
theorem variable_base_mul_spec (point : edwards.EdwardsPoint.«i686-no-tables»)
    (scalar : scalar.Scalar) (hpoint : point.LimbsLt 26) (hon : point.OnCurve)
    (hscalar : scalar.asNat < 2 ^ 255) :
    variable_base_mul.«i686-no-tables» point scalar
      ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
        r.OnCurve ∧ r.toPoint = scalar.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold variable_base_mul.«i686-no-tables»
  step*

end «i686-no-tables»

end Curve25519Dalek.backend
