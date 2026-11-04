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
import Proofs.Edwards.Sub
public section

/-! # `Sub` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace «Shared0RistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

open edwards.EdwardsPoint.«x86_64-tables» in
/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self other : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step with
    Insts.«CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».sub_spec_point
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end «Shared0RistrettoPointx86_64-tables».Insts

namespace «Shared0RistrettoPointi686-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPointi686-tablesRistrettoPointi686-tables»

open edwards.EdwardsPoint.«i686-tables» in
/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self other : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step with
    Insts.«CoreOpsArithSubEdwardsPointi686-tablesEdwardsPointi686-tables».sub_spec_point
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedARistrettoPointi686-tablesRistrettoPointi686-tables»
end «Shared0RistrettoPointi686-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts

namespace «SharedARistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end «SharedARistrettoPointx86_64-tables».Insts

namespace «SharedARistrettoPointi686-tables».Insts
namespace «CoreOpsArithSubRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPointi686-tablesRistrettoPointi686-tables»
end «SharedARistrettoPointi686-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithSubRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPointi686-tablesRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts

namespace «Shared0RistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

open edwards.EdwardsPoint.«x86_64-no-tables» in
/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self other : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step with
    Insts.«CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables».sub_spec_point
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end «Shared0RistrettoPointx86_64-no-tables».Insts

namespace «Shared0RistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithSubSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

open edwards.EdwardsPoint.«i686-no-tables» in
/-- `Sub<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self other : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step with
    Insts.«CoreOpsArithSubEdwardsPointi686-no-tablesEdwardsPointi686-no-tables».sub_spec_point
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end «Shared0RistrettoPointi686-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithSubSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Sub<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts

namespace «SharedARistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithSubRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end «SharedARistrettoPointx86_64-no-tables».Insts

namespace «SharedARistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithSubRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Sub<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end «SharedARistrettoPointi686-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithSubRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithSubRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Sub<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem sub_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithSubRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts

end Curve25519Dalek
