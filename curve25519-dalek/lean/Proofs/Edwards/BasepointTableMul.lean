/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Edwards.BasepointTableMulBase
public section

/-! # `Mul<&Scalar> for &BasepointTable` and `Mul<&BasepointTable> for &Scalar`

Both forward to `BasepointTable::mul_base`, for each of the five basepoint tables. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.«SharedAEdwardsBasepointTablex86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTable`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTable.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 54)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTablex86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTablei686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTable`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTable.«i686-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 27)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTablei686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTablex86_64-tablesEdwardsPointx86_64-tables» in
/-- `Mul<&EdwardsBasepointTable> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTablex86_64-tablesEdwardsPointx86_64-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTablei686-tablesEdwardsPointi686-tables» in
/-- `Mul<&EdwardsBasepointTable> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTablei686-tablesEdwardsPointi686-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTable.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix32`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix32.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 54)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32i686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix32`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix32.«i686-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 27)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix32i686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix32x86_64-tablesEdwardsPointx86_64-tables» in
/-- `Mul<&EdwardsBasepointTableRadix32> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix32x86_64-tablesEdwardsPointx86_64-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix32i686-tablesEdwardsPointi686-tables» in
/-- `Mul<&EdwardsBasepointTableRadix32> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix32i686-tablesEdwardsPointi686-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix32.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix64`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix64.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 54)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64i686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix64`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix64.«i686-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 27)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix64i686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix64x86_64-tablesEdwardsPointx86_64-tables» in
/-- `Mul<&EdwardsBasepointTableRadix64> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix64x86_64-tablesEdwardsPointx86_64-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix64i686-tablesEdwardsPointi686-tables» in
/-- `Mul<&EdwardsBasepointTableRadix64> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix64i686-tablesEdwardsPointi686-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix64.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix128`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix128.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 54)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128i686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix128`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix128.«i686-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 27)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix128i686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix128x86_64-tablesEdwardsPointx86_64-tables» in
/-- `Mul<&EdwardsBasepointTableRadix128> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix128x86_64-tablesEdwardsPointx86_64-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix128i686-tablesEdwardsPointi686-tables» in
/-- `Mul<&EdwardsBasepointTableRadix128> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix128i686-tablesEdwardsPointi686-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix128.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix256`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix256.«x86_64-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 54)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256x86_64-tables».Insts

namespace Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256i686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsBasepointTableRadix256`: `mul_base`, i.e. `scalar • P`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsBasepointTableRadix256.«i686-tables»)
    (scalar : scalar.Scalar) (P : curve25519.edwards.Point) (hself : self.LimbsLt 27)
    (hP : self.Represents P) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end Curve25519Dalek.«SharedAEdwardsBasepointTableRadix256i686-tables».Insts

namespace Curve25519Dalek.SharedBScalar.Insts

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix256x86_64-tablesEdwardsPointx86_64-tables» in
/-- `Mul<&EdwardsBasepointTableRadix256> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix256x86_64-tablesEdwardsPointx86_64-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 54) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

open «CoreOpsArithMulSharedAEdwardsBasepointTableRadix256i686-tablesEdwardsPointi686-tables» in
/-- `Mul<&EdwardsBasepointTableRadix256> for &Scalar`: as the other order. -/
@[step]
theorem
«CoreOpsArithMulSharedAEdwardsBasepointTableRadix256i686-tablesEdwardsPointi686-tables».mul_spec
    (self : scalar.Scalar) (basepoint_table : edwards.EdwardsBasepointTableRadix256.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.asNat < 2 ^ 255)
    (hbasepoint_table : basepoint_table.LimbsLt 27) (hP : basepoint_table.Represents P) :
    mul self basepoint_table ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • P ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end Curve25519Dalek.SharedBScalar.Insts

