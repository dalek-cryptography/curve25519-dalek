/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Edwards.Affine.ToEdwards
import Proofs.Edwards.Mul
public section

/-! # `Mul<AffinePoint> for Scalar`

`AffinePoint` is converted to extended coordinates (`to_edwards`) and multiplied by
`variable_base_mul`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.scalar.Scalar.Insts

namespace «CoreOpsArithMulShared0AffinePointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<&AffinePoint> for Scalar`: `self • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with edwards.affine.«AffinePointx86_64-tables».to_edwards_spec_point
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «CoreOpsArithMulShared0AffinePointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulShared0AffinePointi686-tablesEdwardsPointi686-tables»

/-- `Mul<&AffinePoint> for Scalar`: `self • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with edwards.affine.«AffinePointi686-tables».to_edwards_spec_point
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «CoreOpsArithMulShared0AffinePointi686-tablesEdwardsPointi686-tables»

namespace «CoreOpsArithMulAffinePointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Mul<AffinePoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulAffinePointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithMulAffinePointi686-tablesEdwardsPointi686-tables»

/-- `Mul<AffinePoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulAffinePointi686-tablesEdwardsPointi686-tables»

namespace «CoreOpsArithMulShared0AffinePointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<&AffinePoint> for Scalar`: `self • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with edwards.affine.«AffinePointx86_64-no-tables».to_edwards_spec_point
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «CoreOpsArithMulShared0AffinePointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulShared0AffinePointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Mul<&AffinePoint> for Scalar`: `self • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with edwards.affine.«AffinePointi686-no-tables».to_edwards_spec_point
    as ⟨ep, hepon, hep, hepb⟩
  step as ⟨r, hron, hr, hrb⟩
  exact ⟨hron, hep ▸ hr, hrb⟩

end «CoreOpsArithMulShared0AffinePointi686-no-tablesEdwardsPointi686-no-tables»

namespace «CoreOpsArithMulAffinePointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Mul<AffinePoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulAffinePointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithMulAffinePointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Mul<AffinePoint> for Scalar`: as the borrowed form. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step*

end «CoreOpsArithMulAffinePointi686-no-tablesEdwardsPointi686-no-tables»

end Curve25519Dalek.scalar.Scalar.Insts
