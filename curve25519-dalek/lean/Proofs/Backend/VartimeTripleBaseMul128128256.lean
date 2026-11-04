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
import Proofs.Backend.Serial.ScalarMul.VartimeTripleBase.Mul128128256
public section

/-! # `backend::vartime_triple_base_mul_128_128_256` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «x86_64-tables»

/-- `vartime_triple_base_mul_128_128_256`: the serial `vartime_triple_base::mul_128_128_256`,
`a1 • A1 + a2 • A2 + b • B` (`a1, a2 < 2^128`); limbs `< 2^52`. -/
@[step]
theorem vartime_triple_base_mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«x86_64-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«x86_64-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    vartime_triple_base_mul_128_128_256.«x86_64-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint +
        b.asNat • curve25519.basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_triple_base_mul_128_128_256.«x86_64-tables»
  step*

end «x86_64-tables»

namespace «i686-tables»

/-- `vartime_triple_base_mul_128_128_256`: the serial `vartime_triple_base::mul_128_128_256`,
`a1 • A1 + a2 • A2 + b • B` (`a1, a2 < 2^128`); limbs `< 2^26`. -/
@[step]
theorem vartime_triple_base_mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«i686-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«i686-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    vartime_triple_base_mul_128_128_256.«i686-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint +
        b.asNat • curve25519.basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_triple_base_mul_128_128_256.«i686-tables»
  step*

end «i686-tables»

namespace «x86_64-no-tables»

/-- `vartime_triple_base_mul_128_128_256`: the serial `vartime_triple_base::mul_128_128_256`,
`a1 • A1 + a2 • A2 + b • B` (`a1, a2 < 2^128`); limbs `< 2^52`. -/
@[step]
theorem vartime_triple_base_mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«x86_64-no-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«x86_64-no-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 52) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 52) (hA2_on : A2.OnCurve) :
    vartime_triple_base_mul_128_128_256.«x86_64-no-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint +
        b.asNat • curve25519.basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold vartime_triple_base_mul_128_128_256.«x86_64-no-tables»
  step*

end «x86_64-no-tables»

namespace «i686-no-tables»

/-- `vartime_triple_base_mul_128_128_256`: the serial `vartime_triple_base::mul_128_128_256`,
`a1 • A1 + a2 • A2 + b • B` (`a1, a2 < 2^128`); limbs `< 2^26`. -/
@[step]
theorem vartime_triple_base_mul_128_128_256_spec (a1 : scalar.HalfWidthScalar)
    (A1 : edwards.EdwardsPoint.«i686-no-tables») (a2 : scalar.HalfWidthScalar)
    (A2 : edwards.EdwardsPoint.«i686-no-tables») (b : scalar.Scalar)
    (ha1 : a1.asNat < 2 ^ 128) (hA1 : A1.LimbsLt 26) (hA1_on : A1.OnCurve)
    (ha2 : a2.asNat < 2 ^ 128) (hA2 : A2.LimbsLt 26) (hA2_on : A2.OnCurve) :
    vartime_triple_base_mul_128_128_256.«i686-no-tables» a1 A1 a2 A2 b
        ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = a1.asNat • A1.toPoint + a2.asNat • A2.toPoint +
        b.asNat • curve25519.basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold vartime_triple_base_mul_128_128_256.«i686-no-tables»
  step*

end «i686-no-tables»

end Curve25519Dalek.backend
