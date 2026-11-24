module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Edwards.Mul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek

namespace edwards.EdwardsPoint.«64bit-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • self` (unreduced, `< 2^255`). -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«64bit-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«64bit-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace edwards.EdwardsPoint.«32bit-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • self` (unreduced, `< 2^255`). -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«32bit-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«32bit-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace edwards.EdwardsPoint.«64bit-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«64bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«64bit-tables».Insts.CoreOpsArithMulAssignScalar

namespace edwards.EdwardsPoint.«32bit-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«32bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«32bit-tables».Insts.CoreOpsArithMulAssignScalar

namespace edwards.EdwardsPoint.«64bit-notables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • self` (unreduced, `< 2^255`). -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«64bit-notables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«64bit-notables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace edwards.EdwardsPoint.«32bit-notables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • self` (unreduced, `< 2^255`). -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«32bit-notables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«32bit-notables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace edwards.EdwardsPoint.«64bit-notables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«64bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«64bit-notables».Insts.CoreOpsArithMulAssignScalar

namespace edwards.EdwardsPoint.«32bit-notables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«32bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«32bit-notables».Insts.CoreOpsArithMulAssignScalar

end Curve25519Dalek
