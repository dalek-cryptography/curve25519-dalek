/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
import Proofs.Edwards.Affine.ToEdwards
import Proofs.Edwards.Mul
public section

/-! # `Mul<AffinePoint> for Scalar`

`AffinePoint` is converted to extended coordinates (`to_edwards`) and multiplied by
`variable_base_mul`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.scalar.Scalar.Insts

namespace «CoreOpsArithMulShared0AffinePoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Mul<&AffinePoint> for Scalar`: `self • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with edwards.affine.«AffinePoint64bit-tables».to_edwards_spec
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «CoreOpsArithMulShared0AffinePoint64bit-tablesEdwardsPoint64bit-tables»

namespace «CoreOpsArithMulShared0AffinePoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Mul<&AffinePoint> for Scalar`: `self • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with edwards.affine.«AffinePoint32bit-tables».to_edwards_spec
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «CoreOpsArithMulShared0AffinePoint32bit-tablesEdwardsPoint32bit-tables»

namespace «CoreOpsArithMulAffinePoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Mul<AffinePoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulAffinePoint64bit-tablesEdwardsPoint64bit-tables»

namespace «CoreOpsArithMulAffinePoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Mul<AffinePoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulAffinePoint32bit-tablesEdwardsPoint32bit-tables»

namespace «CoreOpsArithMulShared0AffinePoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Mul<&AffinePoint> for Scalar`: `self • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with edwards.affine.«AffinePoint64bit-notables».to_edwards_spec
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «CoreOpsArithMulShared0AffinePoint64bit-notablesEdwardsPoint64bit-notables»

namespace «CoreOpsArithMulShared0AffinePoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Mul<&AffinePoint> for Scalar`: `self • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with edwards.affine.«AffinePoint32bit-notables».to_edwards_spec
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «CoreOpsArithMulShared0AffinePoint32bit-notablesEdwardsPoint32bit-notables»

namespace «CoreOpsArithMulAffinePoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Mul<AffinePoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulAffinePoint64bit-notablesEdwardsPoint64bit-notables»

namespace «CoreOpsArithMulAffinePoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Mul<AffinePoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulAffinePoint32bit-notablesEdwardsPoint32bit-notables»

end Curve25519Dalek.scalar.Scalar.Insts
