/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Backend.VariableBaseMul
public section

/-! # `Mul` between `EdwardsPoint` and `Scalar`

`&EdwardsPoint * &Scalar` is `variable_base_mul`; the other seven forms (by value, and
`Scalar * EdwardsPoint`) forward to it. The scalar is not reduced: the result is
`s.asNat • P`, for `s.asNat < 2^255` (`as_radix_16`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek

namespace «Shared0EdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-tables»
end «Shared0EdwardsPointx86_64-tables».Insts

namespace «Shared0EdwardsPointi686-tables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«i686-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAScalarEdwardsPointi686-tables»
end «Shared0EdwardsPointi686-tables».Insts

namespace edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointx86_64-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPointx86_64-tables»
end edwards.EdwardsPoint.«x86_64-tables».Insts

namespace edwards.EdwardsPoint.«i686-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointi686-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPointi686-tables»
end edwards.EdwardsPoint.«i686-tables».Insts

namespace edwards.EdwardsPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables»
end edwards.EdwardsPoint.«x86_64-tables».Insts

namespace edwards.EdwardsPoint.«i686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-tables»
end edwards.EdwardsPoint.«i686-tables».Insts

namespace «SharedAEdwardsPointx86_64-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointx86_64-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPointx86_64-tables»
end «SharedAEdwardsPointx86_64-tables».Insts

namespace «SharedAEdwardsPointi686-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointi686-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPointi686-tables»
end «SharedAEdwardsPointi686-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 26) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPointi686-tablesEdwardsPointi686-tables»
end scalar.Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPointi686-tablesEdwardsPointi686-tables»
end SharedAScalar.Insts

namespace «Shared0EdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-no-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAScalarEdwardsPointx86_64-no-tables»
end «Shared0EdwardsPointx86_64-no-tables».Insts

namespace «Shared0EdwardsPointi686-no-tables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPointi686-no-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«i686-no-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAScalarEdwardsPointi686-no-tables»
end «Shared0EdwardsPointi686-no-tables».Insts

namespace edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»
end edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace edwards.EdwardsPoint.«i686-no-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointi686-no-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPointi686-no-tables»
end edwards.EdwardsPoint.«i686-no-tables».Insts

namespace edwards.EdwardsPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-no-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointx86_64-no-tables»
end edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace edwards.EdwardsPoint.«i686-no-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPointi686-no-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPointi686-no-tables»
end edwards.EdwardsPoint.«i686-no-tables».Insts

namespace «SharedAEdwardsPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPointx86_64-no-tables»
end «SharedAEdwardsPointx86_64-no-tables».Insts

namespace «SharedAEdwardsPointi686-no-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPointi686-no-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPointi686-no-tables»
end «SharedAEdwardsPointi686-no-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 26) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end scalar.Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end SharedAScalar.Insts

end Curve25519Dalek
