/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
public import Curve25519.Edwards.Basepoint
public import Subtle
import Proofs.Edwards.BasepointTableCreate
import Proofs.Edwards.BasepointTableBasepoint
import Proofs.Edwards.BasepointTableMul
public section

/-! # `RistrettoBasepointTable` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.«RistrettoBasepointTablex86_64-tables»

open edwards.EdwardsBasepointTable.«x86_64-tables» in
/-- `RistrettoBasepointTable::create`: a table representing `basepoint`; limbs `< 2^52` in,
`< 2^54` out. -/
@[step]
theorem create_spec (basepoint : ristretto.RistrettoPoint.«x86_64-tables»)
    (hbasepoint : basepoint.LimbsLt 52) (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : ristretto.RistrettoBasepointTable.«x86_64-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  step with
    Insts.«Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables».create_spec
    basepoint hbasepoint hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoBasepointTablex86_64-tables»

namespace ristretto.«RistrettoBasepointTablei686-tables»

open edwards.EdwardsBasepointTable.«i686-tables» in
/-- `RistrettoBasepointTable::create`: a table representing `basepoint`; limbs `< 2^26` in,
`< 2^27` out. -/
@[step]
theorem create_spec (basepoint : ristretto.RistrettoPoint.«i686-tables»)
    (hbasepoint : basepoint.LimbsLt 26) (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : ristretto.RistrettoBasepointTable.«i686-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  step with
    Insts.«Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables».create_spec
    basepoint hbasepoint hon as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoBasepointTablei686-tables»

namespace ristretto.«RistrettoBasepointTablex86_64-tables»

open edwards.EdwardsBasepointTable.«x86_64-tables» in
/-- `RistrettoBasepointTable::basepoint`: the point the table represents. -/
@[step]
theorem basepoint_spec (self : ristretto.RistrettoBasepointTable.«x86_64-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable) :
    basepoint self ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with
    Insts.«Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables».basepoint_spec
    self hself hP as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoBasepointTablex86_64-tables»

namespace ristretto.«RistrettoBasepointTablei686-tables»

open edwards.EdwardsBasepointTable.«i686-tables» in
/-- `RistrettoBasepointTable::basepoint`: the point the table represents. -/
@[step]
theorem basepoint_spec (self : ristretto.RistrettoBasepointTable.«i686-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable) :
    basepoint self ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with
    Insts.«Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables».basepoint_spec
    self hself hP as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.«RistrettoBasepointTablei686-tables»

namespace «Shared0RistrettoBasepointTablex86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»

open «SharedAEdwardsBasepointTablex86_64-tables» in
/-- `Mul<&Scalar> for &RistrettoBasepointTable`: `scalar • self.point` for the table's
point (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoBasepointTable.«x86_64-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 54)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    Insts.«CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables».mul_spec
    self scalar hself hP hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»
end «Shared0RistrettoBasepointTablex86_64-tables».Insts

namespace «Shared0RistrettoBasepointTablei686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointi686-tables»

open «SharedAEdwardsBasepointTablei686-tables» in
/-- `Mul<&Scalar> for &RistrettoBasepointTable`: `scalar • self.point` for the table's
point (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoBasepointTable.«i686-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 27)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    Insts.«CoreOpsArithMulSharedBScalarEdwardsPointi686-tables».mul_spec
    self scalar hself hP hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPointi686-tables»
end «Shared0RistrettoBasepointTablei686-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoBasepointTablex86_64-tablesRistrettoPointx86_64-tables»

open SharedBScalar.Insts in
/-- `Mul<&RistrettoBasepointTable> for &Scalar`: as the other order. -/
@[step]
theorem mul_spec (self : scalar.Scalar)
    (basepoint_table : ristretto.RistrettoBasepointTable.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hbasepoint_table : basepoint_table.LimbsLt 54)
    (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    «CoreOpsArithMulSharedAEdwardsBasepointTablex86_64-tablesEdwardsPointx86_64-tables».mul_spec
    self basepoint_table hself hbasepoint_table hP as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoBasepointTablex86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulSharedARistrettoBasepointTablei686-tablesRistrettoPointi686-tables»

open SharedBScalar.Insts in
/-- `Mul<&RistrettoBasepointTable> for &Scalar`: as the other order. -/
@[step]
theorem mul_spec (self : scalar.Scalar)
    (basepoint_table : ristretto.RistrettoBasepointTable.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hbasepoint_table : basepoint_table.LimbsLt 27)
    (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    «CoreOpsArithMulSharedAEdwardsBasepointTablei686-tablesEdwardsPointi686-tables».mul_spec
    self basepoint_table hself hbasepoint_table hP as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoBasepointTablei686-tablesRistrettoPointi686-tables»
end Shared0Scalar.Insts

end Curve25519Dalek
