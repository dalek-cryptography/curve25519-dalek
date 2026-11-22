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
import Proofs.Edwards.Mul
public section

/-! # `Mul` between `RistrettoPoint` and `Scalar` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace «Shared0RistrettoPoint64bit-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPoint64bit-tables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«64bit-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    «64bit-tables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPoint64bit-tables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPoint64bit-tables»
end «Shared0RistrettoPoint64bit-tables».Insts

namespace «Shared0RistrettoPoint32bit-tables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPoint32bit-tables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«32bit-tables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    «32bit-tables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPoint32bit-tables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPoint32bit-tables»
end «Shared0RistrettoPoint32bit-tables».Insts

namespace ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPoint64bit-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«64bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPoint64bit-tables»
end ristretto.RistrettoPoint.«64bit-tables».Insts

namespace ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPoint32bit-tables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«32bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPoint32bit-tables»
end ristretto.RistrettoPoint.«32bit-tables».Insts

namespace «SharedARistrettoPoint64bit-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPoint64bit-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«64bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPoint64bit-tables»
end «SharedARistrettoPoint64bit-tables».Insts

namespace «SharedARistrettoPoint32bit-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPoint32bit-tables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«32bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPoint32bit-tables»
end «SharedARistrettoPoint32bit-tables».Insts

namespace ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPoint64bit-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«64bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPoint64bit-tables»
end ristretto.RistrettoPoint.«64bit-tables».Insts

namespace ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «CoreOpsArithMulScalarRistrettoPoint32bit-tables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«32bit-tables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPoint32bit-tables»
end ristretto.RistrettoPoint.«32bit-tables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    SharedAScalar.Insts.«CoreOpsArithMulEdwardsPoint64bit-tablesEdwardsPoint64bit-tables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

namespace «CoreOpsArithMulSharedARistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 26) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    SharedAScalar.Insts.«CoreOpsArithMulEdwardsPoint32bit-tablesEdwardsPoint32bit-tables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

namespace «CoreOpsArithMulSharedBRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

namespace «CoreOpsArithMulRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end SharedAScalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

namespace «CoreOpsArithMulRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end scalar.Scalar.Insts

namespace «Shared0RistrettoPoint64bit-notables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPoint64bit-notables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«64bit-notables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    «64bit-notables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPoint64bit-notables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPoint64bit-notables»
end «Shared0RistrettoPoint64bit-notables».Insts

namespace «Shared0RistrettoPoint32bit-notables».Insts
namespace «CoreOpsArithMulSharedAScalarRistrettoPoint32bit-notables»

open edwards.EdwardsPoint in
/-- `Mul<&Scalar> for &RistrettoPoint`: `scalar • P` (unreduced, `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«32bit-notables») (scalar : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hscalar : scalar.asNat < 2 ^ 255) :
    mul self scalar ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = scalar.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    «32bit-notables».Insts.«CoreOpsArithMulSharedBScalarEdwardsPoint32bit-notables».mul_spec
    self scalar hself hon hscalar as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedAScalarRistrettoPoint32bit-notables»
end «Shared0RistrettoPoint32bit-notables».Insts

namespace ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPoint64bit-notables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«64bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPoint64bit-notables»
end ristretto.RistrettoPoint.«64bit-notables».Insts

namespace ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «CoreOpsArithMulSharedBScalarRistrettoPoint32bit-notables»

/-- `Mul<&Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«32bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBScalarRistrettoPoint32bit-notables»
end ristretto.RistrettoPoint.«32bit-notables».Insts

namespace «SharedARistrettoPoint64bit-notables».Insts
namespace «CoreOpsArithMulScalarRistrettoPoint64bit-notables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«64bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPoint64bit-notables»
end «SharedARistrettoPoint64bit-notables».Insts

namespace «SharedARistrettoPoint32bit-notables».Insts
namespace «CoreOpsArithMulScalarRistrettoPoint32bit-notables»

/-- `Mul<Scalar> for &RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«32bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPoint32bit-notables»
end «SharedARistrettoPoint32bit-notables».Insts

namespace ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «CoreOpsArithMulScalarRistrettoPoint64bit-notables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«64bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPoint64bit-notables»
end ristretto.RistrettoPoint.«64bit-notables».Insts

namespace ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «CoreOpsArithMulScalarRistrettoPoint32bit-notables»

/-- `Mul<Scalar> for RistrettoPoint`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : ristretto.RistrettoPoint.«32bit-notables») (rhs : scalar.Scalar)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) (hrhs : rhs.asNat < 2 ^ 255) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = rhs.asNat • self.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulScalarRistrettoPoint32bit-notables»
end ristretto.RistrettoPoint.«32bit-notables».Insts

namespace Shared0Scalar.Insts
namespace «CoreOpsArithMulSharedARistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

open SharedAScalar in
/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 52) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step with
    Insts.«CoreOpsArithMulEdwardsPoint64bit-notablesEdwardsPoint64bit-notables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

namespace «CoreOpsArithMulSharedARistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

open SharedAScalar in
/-- `Mul<&RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hpoint : point.LimbsLt 26) (hpoint_on : point.OnCurve) :
    mul self point ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • point.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step with
    Insts.«CoreOpsArithMulEdwardsPoint32bit-notablesEdwardsPoint32bit-notables».mul_spec
    self point hself hpoint hpoint_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedARistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end Shared0Scalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulSharedBRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

namespace «CoreOpsArithMulSharedBRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

/-- `Mul<&RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulSharedBRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end scalar.Scalar.Insts

namespace SharedAScalar.Insts
namespace «CoreOpsArithMulRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

namespace «CoreOpsArithMulRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

/-- `Mul<RistrettoPoint> for &Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end SharedAScalar.Insts

namespace scalar.Scalar.Insts
namespace «CoreOpsArithMulRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 52) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

namespace «CoreOpsArithMulRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

/-- `Mul<RistrettoPoint> for Scalar`: as `&RistrettoPoint * &Scalar`. -/
@[step]
theorem mul_spec (self : scalar.Scalar) (rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.asNat < 2 ^ 255) (hrhs : rhs.LimbsLt 26) (hrhs_on : rhs.OnCurve) :
    mul self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.asNat • rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold mul
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithMulRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end scalar.Scalar.Insts

end Curve25519Dalek
