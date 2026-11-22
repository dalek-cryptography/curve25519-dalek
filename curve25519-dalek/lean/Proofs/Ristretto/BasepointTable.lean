/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
public import Proofs.Curve25519.Edwards.Basepoint
public import Proofs.External.Subtle
import Proofs.Edwards.BasepointTableCreate
import Proofs.Edwards.BasepointTableBasepoint
import Proofs.Edwards.BasepointTableMul
public section

/-! # `RistrettoBasepointTable` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.«RistrettoBasepointTable64bit-tables»

open edwards.EdwardsBasepointTable.«64bit-tables» in
/-- `RistrettoBasepointTable::create`: a table representing `basepoint`; limbs `< 2^52` in,
`< 2^54` out. -/
@[step]
theorem create_spec (basepoint : ristretto.RistrettoPoint.«64bit-tables»)
    (hbasepoint : basepoint.LimbsLt 52) (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : ristretto.RistrettoBasepointTable.«64bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  step with
    Insts.«Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables».create_spec
    basepoint hbasepoint hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoBasepointTable64bit-tables»

namespace ristretto.«RistrettoBasepointTable32bit-tables»

open edwards.EdwardsBasepointTable.«32bit-tables» in
/-- `RistrettoBasepointTable::create`: a table representing `basepoint`; limbs `< 2^26` in,
`< 2^27` out. -/
@[step]
theorem create_spec (basepoint : ristretto.RistrettoPoint.«32bit-tables»)
    (hbasepoint : basepoint.LimbsLt 26) (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : ristretto.RistrettoBasepointTable.«32bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  step with
    Insts.«Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables».create_spec
    basepoint hbasepoint hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoBasepointTable32bit-tables»

namespace ristretto.«RistrettoBasepointTable64bit-tables»

open edwards.EdwardsBasepointTable.«64bit-tables» in
/-- `RistrettoBasepointTable::basepoint`: the point the table represents. -/
@[step]
theorem basepoint_spec (self : ristretto.RistrettoBasepointTable.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable) :
    basepoint self ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with
    Insts.«Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables».basepoint_spec
    self hself hP as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoBasepointTable64bit-tables»

namespace ristretto.«RistrettoBasepointTable32bit-tables»

open edwards.EdwardsBasepointTable.«32bit-tables» in
/-- `RistrettoBasepointTable::basepoint`: the point the table represents. -/
@[step]
theorem basepoint_spec (self : ristretto.RistrettoBasepointTable.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable) :
    basepoint self ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with
    Insts.«Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables».basepoint_spec
    self hself hP as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoBasepointTable32bit-tables»

namespace «Shared0RistrettoBasepointTable64bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPoint64bit-tables»

open «SharedAEdwardsBasepointTable64bit-tables» in
/-- `Mul<&Scalar> for &RistrettoBasepointTable`: `scalar • self.point` for the table's
point (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoBasepointTable.«64bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 54)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    Insts.«CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables».mul_spec
    self scalar hself hP hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPoint64bit-tables»
end «Shared0RistrettoBasepointTable64bit-tables».Insts

namespace «Shared0RistrettoBasepointTable32bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPoint32bit-tables»

open «SharedAEdwardsBasepointTable32bit-tables» in
/-- `Mul<&Scalar> for &RistrettoBasepointTable`: `scalar • self.point` for the table's
point (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoBasepointTable.«32bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 27)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    Insts.«CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables».mul_spec
    self scalar hself hP hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPoint32bit-tables»
end «Shared0RistrettoBasepointTable32bit-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoBasepointTable64bit-tablesRistrettoPoint64bit-tables»

open SharedBScalar.Insts in
/-- `Mul<&RistrettoBasepointTable> for &Scalar`: as the other order. -/
@[step]
theorem mul_spec (self : scalar.Scalar)
    (basepoint_table : ristretto.RistrettoBasepointTable.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hbasepoint_table : basepoint_table.LimbsLt 54)
    (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    «CoreOpsArithMulSharedAEdwardsBasepointTable64bit-tablesEdwardsPoint64bit-tables».mul_spec
    self basepoint_table hself hbasepoint_table hP as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoBasepointTable64bit-tablesRistrettoPoint64bit-tables»

namespace «CoreOpsArithMulSharedARistrettoBasepointTable32bit-tablesRistrettoPoint32bit-tables»

open SharedBScalar.Insts in
/-- `Mul<&RistrettoBasepointTable> for &Scalar`: as the other order. -/
@[step]
theorem mul_spec (self : scalar.Scalar)
    (basepoint_table : ristretto.RistrettoBasepointTable.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hbasepoint_table : basepoint_table.LimbsLt 27)
    (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    «CoreOpsArithMulSharedAEdwardsBasepointTable32bit-tablesEdwardsPoint32bit-tables».mul_spec
    self basepoint_table hself hbasepoint_table hP as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoBasepointTable32bit-tablesRistrettoPoint32bit-tables»
end Shared0Scalar.Insts

end Curve25519Dalek
