/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Montgomery
public import Defs.Scalar
import Proofs.Montgomery.Mul
public section

/-! # `MulAssign<&Scalar> for MontgomeryPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.montgomery.MontgomeryPoint.Insts

namespace CoreOpsArithMulAssignShared0Scalar

/-- `MulAssign<&Scalar> for MontgomeryPoint`: as `&MontgomeryPoint * &Scalar`. -/
@[step]
theorem mul_assign_spec (self : MontgomeryPoint) (scalar : scalar.Scalar) :
    mul_assign self scalar ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (scalar.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul_assign
  exact Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul_spec self
      scalar
   

end CoreOpsArithMulAssignShared0Scalar

namespace CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for MontgomeryPoint`: as `&MontgomeryPoint * &Scalar`. -/
@[step]
theorem mul_assign_spec (self : MontgomeryPoint) (rhs : scalar.Scalar) :
    mul_assign self rhs ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (montgomery.ladder 255 (rhs.asNat % 2 ^ 255) self.u) ⦄ := by
  unfold mul_assign
  exact CoreOpsArithMulAssignShared0Scalar.mul_assign_spec self rhs

end CoreOpsArithMulAssignScalar

end Curve25519Dalek.montgomery.MontgomeryPoint.Insts
