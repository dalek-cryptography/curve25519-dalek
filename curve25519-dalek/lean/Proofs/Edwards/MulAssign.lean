/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Edwards.Mul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek

namespace edwards.EdwardsPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • P` (unreduced, `< 2^255`). -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace edwards.EdwardsPoint.«i686-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • P` (unreduced, `< 2^255`). -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«i686-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«i686-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace edwards.EdwardsPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignScalar

namespace edwards.EdwardsPoint.«i686-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«i686-tables».Insts.CoreOpsArithMulAssignScalar

namespace edwards.EdwardsPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • P` (unreduced, `< 2^255`). -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace edwards.EdwardsPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for EdwardsPoint`: as `Mul`, `scalar • P` (unreduced, `< 2^255`). -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«i686-no-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace edwards.EdwardsPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignScalar

namespace edwards.EdwardsPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem mul_assign_spec (self : edwards.EdwardsPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step*

end edwards.EdwardsPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignScalar

end Curve25519Dalek
