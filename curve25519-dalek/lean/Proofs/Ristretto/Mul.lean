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
import Proofs.Edwards.Mul
public section

/-! # `Mul` between `RistrettoPoint` and `Scalar` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace «Shared0RistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    «x86_64-tables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPointx86_64-tables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables»
end «Shared0RistrettoPointx86_64-tables».Insts

namespace «Shared0RistrettoPointi686-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointi686-tables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«i686-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    «i686-tables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPointi686-tables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPointi686-tables»
end «Shared0RistrettoPointi686-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointi686-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts

namespace «SharedARistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointx86_64-tables»
end «SharedARistrettoPointx86_64-tables».Insts

namespace «SharedARistrettoPointi686-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointi686-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointi686-tables»
end «SharedARistrettoPointi686-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointi686-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«i686-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    SharedAScalar.Insts.«CoreOpsArithMulEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulSharedARistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 26) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    SharedAScalar.Insts.«CoreOpsArithMulEdwardsPointi686-tablesEdwardsPointi686-tables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPointi686-tablesRistrettoPointi686-tables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointi686-tablesRistrettoPointi686-tables»
end SharedAScalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

namespace «CoreOpsArithMulRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointi686-tablesRistrettoPointi686-tables»
end scalar.Scalar.Insts

namespace «Shared0RistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    «x86_64-no-tables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPointx86_64-no-tables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables»
end «Shared0RistrettoPointx86_64-no-tables».Insts

namespace «Shared0RistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    «i686-no-tables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPointi686-no-tables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables»
end «Shared0RistrettoPointi686-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-no-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPointi686-no-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts

namespace «SharedARistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»
end «SharedARistrettoPointx86_64-no-tables».Insts

namespace «SharedARistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointi686-no-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointi686-no-tables»
end «SharedARistrettoPointi686-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPointi686-no-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«i686-no-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

open SharedAScalar in
/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    Insts.«CoreOpsArithMulEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

namespace «CoreOpsArithMulSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

open SharedAScalar in
/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 26) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    Insts.«CoreOpsArithMulEdwardsPointi686-no-tablesEdwardsPointi686-no-tables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

namespace «CoreOpsArithMulSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

namespace «CoreOpsArithMulRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end SharedAScalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

namespace «CoreOpsArithMulRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end scalar.Scalar.Insts

end Curve25519Dalek
