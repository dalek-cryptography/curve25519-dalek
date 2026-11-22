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
import Proofs.Edwards.Add
public section

/-! # `Add` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace «Shared0RistrettoPoint64bit-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

open edwards.EdwardsPoint.«64bit-tables» in
/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self other : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step with
    Insts.«CoreOpsArithAddEdwardsPoint64bit-tablesEdwardsPoint64bit-tables».add_spec
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedARistrettoPoint64bit-tablesRistrettoPoint64bit-tables»
end «Shared0RistrettoPoint64bit-tables».Insts

namespace «Shared0RistrettoPoint32bit-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

open edwards.EdwardsPoint.«32bit-tables» in
/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self other : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step with
    Insts.«CoreOpsArithAddEdwardsPoint32bit-tablesEdwardsPoint32bit-tables».add_spec
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedARistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end «Shared0RistrettoPoint32bit-tables».Insts

namespace ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedBRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»
end ristretto.RistrettoPoint.«64bit-tables».Insts

namespace ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedBRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end ristretto.RistrettoPoint.«32bit-tables».Insts

namespace «SharedARistrettoPoint64bit-tables».Insts
namespace «CoreOpsArithAddRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»
end «SharedARistrettoPoint64bit-tables».Insts

namespace «SharedARistrettoPoint32bit-tables».Insts
namespace «CoreOpsArithAddRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end «SharedARistrettoPoint32bit-tables».Insts

namespace ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «CoreOpsArithAddRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»
end ristretto.RistrettoPoint.«64bit-tables».Insts

namespace ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «CoreOpsArithAddRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end ristretto.RistrettoPoint.«32bit-tables».Insts

namespace «Shared0RistrettoPoint64bit-notables».Insts
namespace «CoreOpsArithAddSharedARistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

open edwards.EdwardsPoint.«64bit-notables» in
/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self other : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step with
    Insts.«CoreOpsArithAddEdwardsPoint64bit-notablesEdwardsPoint64bit-notables».add_spec
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedARistrettoPoint64bit-notablesRistrettoPoint64bit-notables»
end «Shared0RistrettoPoint64bit-notables».Insts

namespace «Shared0RistrettoPoint32bit-notables».Insts
namespace «CoreOpsArithAddSharedARistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

open edwards.EdwardsPoint.«32bit-notables» in
/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self other : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step with
    Insts.«CoreOpsArithAddEdwardsPoint32bit-notablesEdwardsPoint32bit-notables».add_spec
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedARistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end «Shared0RistrettoPoint32bit-notables».Insts

namespace ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedBRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»
end ristretto.RistrettoPoint.«64bit-notables».Insts

namespace ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedBRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end ristretto.RistrettoPoint.«32bit-notables».Insts

namespace «SharedARistrettoPoint64bit-notables».Insts
namespace «CoreOpsArithAddRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»
end «SharedARistrettoPoint64bit-notables».Insts

namespace «SharedARistrettoPoint32bit-notables».Insts
namespace «CoreOpsArithAddRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end «SharedARistrettoPoint32bit-notables».Insts

namespace ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «CoreOpsArithAddRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»
end ristretto.RistrettoPoint.«64bit-notables».Insts

namespace ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «CoreOpsArithAddRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end ristretto.RistrettoPoint.«32bit-notables».Insts

end Curve25519Dalek
