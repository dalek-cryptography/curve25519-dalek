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
import Proofs.Ristretto.Sub
public section

/-! # `SubAssign` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubAssignShared0RistrettoPointx86_64-tables»

/-- `SubAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubAssignShared0RistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithSubAssignShared0RistrettoPointi686-tables»

/-- `SubAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubAssignShared0RistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubAssignRistrettoPointx86_64-tables»

/-- `SubAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubAssignRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithSubAssignRistrettoPointi686-tables»

/-- `SubAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubAssignRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubAssignShared0RistrettoPointx86_64-no-tables»

/-- `SubAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubAssignShared0RistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithSubAssignShared0RistrettoPointi686-no-tables»

/-- `SubAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubAssignShared0RistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubAssignRistrettoPointx86_64-no-tables»

/-- `SubAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_assign_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubAssignRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithSubAssignRistrettoPointi686-no-tables»

/-- `SubAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_assign_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubAssignRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts

end Curve25519Dalek
