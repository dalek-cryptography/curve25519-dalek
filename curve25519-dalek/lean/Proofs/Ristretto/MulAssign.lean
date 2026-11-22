/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
public import Proofs.Curve25519.Edwards.Basepoint
public import Proofs.External.Subtle
import Proofs.Ristretto.Mul
public section

/-! # `MulAssign<Scalar>` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.RistrettoPoint.«64bit-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«64bit-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«64bit-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«32bit-tables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«32bit-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«32bit-tables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«64bit-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«64bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«64bit-tables».Insts.CoreOpsArithMulAssignScalar

namespace ristretto.RistrettoPoint.«32bit-tables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«32bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«32bit-tables».Insts.CoreOpsArithMulAssignScalar

namespace ristretto.RistrettoPoint.«64bit-notables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«64bit-notables»)
    (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«64bit-notables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«32bit-notables».Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign<&Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«32bit-notables»)
    (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_assign self scalar ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«32bit-notables».Insts.CoreOpsArithMulAssignSharedAScalar

namespace ristretto.RistrettoPoint.«64bit-notables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«64bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«64bit-notables».Insts.CoreOpsArithMulAssignScalar

namespace ristretto.RistrettoPoint.«32bit-notables».Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for RistrettoPoint`: as `Mul`. -/
@[step]
theorem mul_assign_spec (self : ristretto.RistrettoPoint.«32bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«32bit-notables».Insts.CoreOpsArithMulAssignScalar

end Curve25519Dalek
