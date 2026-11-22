/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Backend.GetSelectedBackend
import Proofs.Backend.Serial.ScalarMul.VartimeTripleBase.Mul128128256
public section

/-! # `backend::vartime_triple_base_mul_128_128_256` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «64bit-tables»

/-- `vartime_triple_base_mul_128_128_256`: the serial `vartime_triple_base::mul_128_128_256`,
`a1 • A1 + a2 • A2 + b • B` (`a1, a2 < 2^128`); limbs `< 2^52`. -/
@[step]
theorem vartime_triple_base_mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«64bit-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«64bit-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    vartime_triple_base_mul_128_128_256.«64bit-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint +
        b.asNat • curve25519.basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_triple_base_mul_128_128_256.«64bit-tables»
  step*

end «64bit-tables»

namespace «32bit-tables»

/-- `vartime_triple_base_mul_128_128_256`: the serial `vartime_triple_base::mul_128_128_256`,
`a1 • A1 + a2 • A2 + b • B` (`a1, a2 < 2^128`); limbs `< 2^26`. -/
@[step]
theorem vartime_triple_base_mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«32bit-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«32bit-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    vartime_triple_base_mul_128_128_256.«32bit-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint +
        b.asNat • curve25519.basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_triple_base_mul_128_128_256.«32bit-tables»
  step*

end «32bit-tables»

namespace «64bit-notables»

/-- `vartime_triple_base_mul_128_128_256`: the serial `vartime_triple_base::mul_128_128_256`,
`a1 • A1 + a2 • A2 + b • B` (`a1, a2 < 2^128`); limbs `< 2^52`. -/
@[step]
theorem vartime_triple_base_mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«64bit-notables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«64bit-notables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    vartime_triple_base_mul_128_128_256.«64bit-notables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint +
        b.asNat • curve25519.basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_triple_base_mul_128_128_256.«64bit-notables»
  step*

end «64bit-notables»

namespace «32bit-notables»

/-- `vartime_triple_base_mul_128_128_256`: the serial `vartime_triple_base::mul_128_128_256`,
`a1 • A1 + a2 • A2 + b • B` (`a1, a2 < 2^128`); limbs `< 2^26`. -/
@[step]
theorem vartime_triple_base_mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«32bit-notables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«32bit-notables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    vartime_triple_base_mul_128_128_256.«32bit-notables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint +
        b.asNat • curve25519.basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_triple_base_mul_128_128_256.«32bit-notables»
  step*

end «32bit-notables»

end Curve25519Dalek.backend
