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
import Proofs.Edwards.Sub
public section

/-! # `Sub` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace «Shared0RistrettoPoint64bit-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

open edwards.EdwardsPoint.«64bit-tables» in
/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self other : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step with
    Insts.«CoreOpsArithSubEdwardsPoint64bit-tablesEdwardsPoint64bit-tables».sub_spec
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedARistrettoPoint64bit-tablesRistrettoPoint64bit-tables»
end «Shared0RistrettoPoint64bit-tables».Insts

namespace «Shared0RistrettoPoint32bit-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

open edwards.EdwardsPoint.«32bit-tables» in
/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self other : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step with
    Insts.«CoreOpsArithSubEdwardsPoint32bit-tablesEdwardsPoint32bit-tables».sub_spec
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedARistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end «Shared0RistrettoPoint32bit-tables».Insts

namespace ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedBRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»
end ristretto.RistrettoPoint.«64bit-tables».Insts

namespace ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedBRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end ristretto.RistrettoPoint.«32bit-tables».Insts

namespace «SharedARistrettoPoint64bit-tables».Insts
namespace «CoreOpsArithSubRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»
end «SharedARistrettoPoint64bit-tables».Insts

namespace «SharedARistrettoPoint32bit-tables».Insts
namespace «CoreOpsArithSubRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end «SharedARistrettoPoint32bit-tables».Insts

namespace ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «CoreOpsArithSubRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»
end ristretto.RistrettoPoint.«64bit-tables».Insts

namespace ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «CoreOpsArithSubRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPoint32bit-tablesRistrettoPoint32bit-tables»
end ristretto.RistrettoPoint.«32bit-tables».Insts

namespace «Shared0RistrettoPoint64bit-notables».Insts
namespace «CoreOpsArithSubSharedARistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

open edwards.EdwardsPoint.«64bit-notables» in
/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self other : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step with
    Insts.«CoreOpsArithSubEdwardsPoint64bit-notablesEdwardsPoint64bit-notables».sub_spec
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedARistrettoPoint64bit-notablesRistrettoPoint64bit-notables»
end «Shared0RistrettoPoint64bit-notables».Insts

namespace «Shared0RistrettoPoint32bit-notables».Insts
namespace «CoreOpsArithSubSharedARistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

open edwards.EdwardsPoint.«32bit-notables» in
/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self other : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step with
    Insts.«CoreOpsArithSubEdwardsPoint32bit-notablesEdwardsPoint32bit-notables».sub_spec
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedARistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end «Shared0RistrettoPoint32bit-notables».Insts

namespace ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedBRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»
end ristretto.RistrettoPoint.«64bit-notables».Insts

namespace ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedBRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end ristretto.RistrettoPoint.«32bit-notables».Insts

namespace «SharedARistrettoPoint64bit-notables».Insts
namespace «CoreOpsArithSubRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»
end «SharedARistrettoPoint64bit-notables».Insts

namespace «SharedARistrettoPoint32bit-notables».Insts
namespace «CoreOpsArithSubRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end «SharedARistrettoPoint32bit-notables».Insts

namespace ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «CoreOpsArithSubRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPoint64bit-notablesRistrettoPoint64bit-notables»
end ristretto.RistrettoPoint.«64bit-notables».Insts

namespace ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «CoreOpsArithSubRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPoint32bit-notablesRistrettoPoint32bit-notables»
end ristretto.RistrettoPoint.«32bit-notables».Insts

end Curve25519Dalek
