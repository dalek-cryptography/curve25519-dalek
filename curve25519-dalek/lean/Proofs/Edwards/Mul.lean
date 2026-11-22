/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Backend.VariableBaseMul
public section

/-! # `Mul` between `EdwardsPoint` and `Scalar`

`&EdwardsPoint * &Scalar` is `variable_base_mul`; the other seven forms (by value, and
`Scalar * EdwardsPoint`) forward to it. The scalar is not reduced: the result is
`s.asNat • P`, for `s.asNat < 2^255` (`as_radix_16`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek

namespace «Shared0EdwardsPoint64bit-tables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPoint64bit-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • self` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«64bit-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAScalarEdwardsPoint64bit-tables»
end «Shared0EdwardsPoint64bit-tables».Insts

namespace «Shared0EdwardsPoint32bit-tables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPoint32bit-tables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • self` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«32bit-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAScalarEdwardsPoint32bit-tables»
end «Shared0EdwardsPoint32bit-tables».Insts

namespace edwards.EdwardsPoint.«64bit-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPoint64bit-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«64bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPoint64bit-tables»
end edwards.EdwardsPoint.«64bit-tables».Insts

namespace edwards.EdwardsPoint.«32bit-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPoint32bit-tables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«32bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPoint32bit-tables»
end edwards.EdwardsPoint.«32bit-tables».Insts

namespace edwards.EdwardsPoint.«64bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«64bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables»
end edwards.EdwardsPoint.«64bit-tables».Insts

namespace edwards.EdwardsPoint.«32bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«32bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables»
end edwards.EdwardsPoint.«32bit-tables».Insts

namespace «SharedAEdwardsPoint64bit-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPoint64bit-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«64bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPoint64bit-tables»
end «SharedAEdwardsPoint64bit-tables».Insts

namespace «SharedAEdwardsPoint32bit-tables».Insts
namespace «CoreOpsArithMulScalarEdwardsPoint32bit-tables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«32bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPoint32bit-tables»
end «SharedAEdwardsPoint32bit-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

namespace «CoreOpsArithMulSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 26) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

namespace «CoreOpsArithMulEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end scalar.Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

namespace «CoreOpsArithMulSharedBEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

namespace «CoreOpsArithMulEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end SharedAScalar.Insts

namespace «Shared0EdwardsPoint64bit-notables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPoint64bit-notables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • self` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«64bit-notables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAScalarEdwardsPoint64bit-notables»
end «Shared0EdwardsPoint64bit-notables».Insts

namespace «Shared0EdwardsPoint32bit-notables».Insts
namespace «CoreOpsArithMulSharedAScalarEdwardsPoint32bit-notables»

/-- `Mul<&Scalar> for &EdwardsPoint`: `scalar • self` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«32bit-notables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAScalarEdwardsPoint32bit-notables»
end «Shared0EdwardsPoint32bit-notables».Insts

namespace edwards.EdwardsPoint.«64bit-notables».Insts
namespace «CoreOpsArithMulScalarEdwardsPoint64bit-notables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«64bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPoint64bit-notables»
end edwards.EdwardsPoint.«64bit-notables».Insts

namespace edwards.EdwardsPoint.«32bit-notables».Insts
namespace «CoreOpsArithMulScalarEdwardsPoint32bit-notables»

/-- `Mul<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«32bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPoint32bit-notables»
end edwards.EdwardsPoint.«32bit-notables».Insts

namespace edwards.EdwardsPoint.«64bit-notables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-notables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«64bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint64bit-notables»
end edwards.EdwardsPoint.«64bit-notables».Insts

namespace edwards.EdwardsPoint.«32bit-notables».Insts
namespace «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-notables»

/-- `Mul<&Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«32bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBScalarEdwardsPoint32bit-notables»
end edwards.EdwardsPoint.«32bit-notables».Insts

namespace «SharedAEdwardsPoint64bit-notables».Insts
namespace «CoreOpsArithMulScalarEdwardsPoint64bit-notables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«64bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPoint64bit-notables»
end «SharedAEdwardsPoint64bit-notables».Insts

namespace «SharedAEdwardsPoint32bit-notables».Insts
namespace «CoreOpsArithMulScalarEdwardsPoint32bit-notables»

/-- `Mul<Scalar> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_spec (self : edwards.EdwardsPoint.«32bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulScalarEdwardsPoint32bit-notables»
end «SharedAEdwardsPoint32bit-notables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

namespace «CoreOpsArithMulSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Mul<&EdwardsPoint> for &Scalar`: as `&EdwardsPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : edwards.EdwardsPoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 26) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

namespace «CoreOpsArithMulEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Mul<EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end scalar.Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

namespace «CoreOpsArithMulSharedBEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Mul<&EdwardsPoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulSharedBEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

namespace «CoreOpsArithMulEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Mul<EdwardsPoint> for &Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.EdwardsPoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end SharedAScalar.Insts

end Curve25519Dalek
