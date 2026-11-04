/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
public import Curve25519.Edwards.Basepoint
public import Subtle
import Proofs.Ristretto.Mul
public section

/-! # `MulAssign<Scalar>` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«i686-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«i686-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«i686-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«x86_64-tables».Insts.CoreOpsArithMulAssignScalar

namespace ristretto.RistrettoPoint.«i686-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«i686-tables».Insts.CoreOpsArithMulAssignScalar

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«i686-no-tables»)
    (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.CoreOpsArithMulAssignScalar

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«i686-no-tables».Insts.CoreOpsArithMulAssignScalar

end Curve25519Dalek
