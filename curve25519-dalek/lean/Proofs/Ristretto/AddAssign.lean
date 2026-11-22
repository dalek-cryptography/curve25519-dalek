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
import Proofs.Ristretto.Add
public section

/-! # `AddAssign` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPoint64bit-tables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignShared0RistrettoPoint64bit-tables»
end ristretto.RistrettoPoint.«64bit-tables».Insts

namespace ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPoint32bit-tables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignShared0RistrettoPoint32bit-tables»
end ristretto.RistrettoPoint.«32bit-tables».Insts

namespace ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «CoreOpsArithAddAssignRistrettoPoint64bit-tables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignRistrettoPoint64bit-tables»
end ristretto.RistrettoPoint.«64bit-tables».Insts

namespace ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «CoreOpsArithAddAssignRistrettoPoint32bit-tables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignRistrettoPoint32bit-tables»
end ristretto.RistrettoPoint.«32bit-tables».Insts

namespace ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPoint64bit-notables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignShared0RistrettoPoint64bit-notables»
end ristretto.RistrettoPoint.«64bit-notables».Insts

namespace ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «CoreOpsArithAddAssignShared0RistrettoPoint32bit-notables»

/-- `AddAssign<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignShared0RistrettoPoint32bit-notables»
end ristretto.RistrettoPoint.«32bit-notables».Insts

namespace ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «CoreOpsArithAddAssignRistrettoPoint64bit-notables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignRistrettoPoint64bit-notables»
end ristretto.RistrettoPoint.«64bit-notables».Insts

namespace ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «CoreOpsArithAddAssignRistrettoPoint32bit-notables»

/-- `AddAssign<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_assign_spec (self rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddAssignRistrettoPoint32bit-notables»
end ristretto.RistrettoPoint.«32bit-notables».Insts

end Curve25519Dalek
