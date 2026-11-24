module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Edwards.BasepointTableMulBase
public section

/-! # `Mul<&Scalar> for &BasepointTable` and `Mul<&BasepointTable> for &Scalar`

Both forward to `BasepointTable::mul_base`, for each of the five basepoint tables. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.«SharedAEdwardsBasepointTable64bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTable`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTable.«64bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 54)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTable64bit-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTable32bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTable`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTable.«32bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 27)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTable32bit-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTable64bit-tablesEdwardsPoint64bit-tables» in
/-- `Mul<&EdwardsBasepointTable> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTable64bit-tablesEdwardsPoint64bit-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTable.«64bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTable32bit-tablesEdwardsPoint32bit-tables» in
/-- `Mul<&EdwardsBasepointTable> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTable32bit-tablesEdwardsPoint32bit-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTable.«32bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix3264bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix32`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix32.«64bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 54)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix3264bit-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix3232bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix32`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix32.«32bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 27)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix3232bit-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix3264bit-tablesEdwardsPoint64bit-tables» in
/-- `Mul<&EdwardsBasepointTableRadix32> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix3264bit-tablesEdwardsPoint64bit-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix32.«64bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix3232bit-tablesEdwardsPoint32bit-tables» in
/-- `Mul<&EdwardsBasepointTableRadix32> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix3232bit-tablesEdwardsPoint32bit-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix32.«32bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix6464bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix64`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix64.«64bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 54)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix6464bit-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix6432bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix64`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix64.«32bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 27)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix6432bit-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix6464bit-tablesEdwardsPoint64bit-tables» in
/-- `Mul<&EdwardsBasepointTableRadix64> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix6464bit-tablesEdwardsPoint64bit-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix64.«64bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix6432bit-tablesEdwardsPoint32bit-tables» in
/-- `Mul<&EdwardsBasepointTableRadix64> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix6432bit-tablesEdwardsPoint32bit-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix64.«32bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix12864bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix128`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix128.«64bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 54)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix12864bit-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix12832bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix128`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix128.«32bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 27)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix12832bit-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix12864bit-tablesEdwardsPoint64bit-tables» in
/-- `Mul<&EdwardsBasepointTableRadix128> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix12864bit-tablesEdwardsPoint64bit-tables».mul_spec
    (self : scalar.Scalar)
        (basepoint_table : edwards.EdwardsBasepointTableRadix128.«64bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix12832bit-tablesEdwardsPoint32bit-tables» in
/-- `Mul<&EdwardsBasepointTableRadix128> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix12832bit-tablesEdwardsPoint32bit-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix128.«32bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix25664bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix256`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix256.«64bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 54)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix25664bit-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix25632bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix256`: `mul_base`, i.e. `scalar • self.point`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix256.«32bit-tables»)
    (scalar : scalar.Scalar) (hself : self.LimbsLt 27)
    (hP : self.IsTable) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix25632bit-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix25664bit-tablesEdwardsPoint64bit-tables» in
/-- `Mul<&EdwardsBasepointTableRadix256> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix25664bit-tablesEdwardsPoint64bit-tables».mul_spec
    (self : scalar.Scalar)
        (basepoint_table : edwards.EdwardsBasepointTableRadix256.«64bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix25632bit-tablesEdwardsPoint32bit-tables» in
/-- `Mul<&EdwardsBasepointTableRadix256> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix25632bit-tablesEdwardsPoint32bit-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix256.«32bit-tables»)
        (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.IsTable) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • basepoint_table.point ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

