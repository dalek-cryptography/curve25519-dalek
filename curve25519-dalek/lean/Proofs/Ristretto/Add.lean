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
import Proofs.Edwards.Add
public section

/-! # `Add` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace «Shared0RistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

open edwards.EdwardsPoint.«x86_64-tables» in
/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self other : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step with
    Insts.«CoreOpsArithAddEdwardsPointx86_64-tablesEdwardsPointx86_64-tables».add_spec_point
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedARistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end «Shared0RistrettoPointx86_64-tables».Insts

namespace «Shared0RistrettoPointi686-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPointi686-tablesRistrettoPointi686-tables»

open edwards.EdwardsPoint.«i686-tables» in
/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self other : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step with
    Insts.«CoreOpsArithAddEdwardsPointi686-tablesEdwardsPointi686-tables».add_spec_point
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedARistrettoPointi686-tablesRistrettoPointi686-tables»
end «Shared0RistrettoPointi686-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedBRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedBRistrettoPointi686-tablesRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts

namespace «SharedARistrettoPointx86_64-tables».Insts
namespace «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end «SharedARistrettoPointx86_64-tables».Insts

namespace «SharedARistrettoPointi686-tables».Insts
namespace «CoreOpsArithAddRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPointi686-tablesRistrettoPointi686-tables»
end «SharedARistrettoPointi686-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts
namespace «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPointx86_64-tablesRistrettoPointx86_64-tables»
end ristretto.RistrettoPoint.«x86_64-tables».Insts

namespace ristretto.RistrettoPoint.«i686-tables».Insts
namespace «CoreOpsArithAddRistrettoPointi686-tablesRistrettoPointi686-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPointi686-tablesRistrettoPointi686-tables»
end ristretto.RistrettoPoint.«i686-tables».Insts

namespace «Shared0RistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

open edwards.EdwardsPoint.«x86_64-no-tables» in
/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self other : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step with
    Insts.«CoreOpsArithAddEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables».add_spec_point
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedARistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end «Shared0RistrettoPointx86_64-no-tables».Insts

namespace «Shared0RistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithAddSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

open edwards.EdwardsPoint.«i686-no-tables» in
/-- `Add<&RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self other : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step with
    Insts.«CoreOpsArithAddEdwardsPointi686-no-tablesEdwardsPointi686-no-tables».add_spec_point
    self other hself hother hself_on hother_on as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedARistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end «Shared0RistrettoPointi686-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedBRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithAddSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Add<&RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddSharedBRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts

namespace «SharedARistrettoPointx86_64-no-tables».Insts
namespace «CoreOpsArithAddRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end «SharedARistrettoPointx86_64-no-tables».Insts

namespace «SharedARistrettoPointi686-no-tables».Insts
namespace «CoreOpsArithAddRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Add<RistrettoPoint> for &RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end «SharedARistrettoPointi686-no-tables».Insts

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts
namespace «CoreOpsArithAddRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPointx86_64-no-tablesRistrettoPointx86_64-no-tables»
end ristretto.RistrettoPoint.«x86_64-no-tables».Insts

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts
namespace «CoreOpsArithAddRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»

/-- `Add<RistrettoPoint> for RistrettoPoint` on the represented points. -/
@[step]
theorem add_spec (self rhs : ristretto.RistrettoPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve)
    (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «CoreOpsArithAddRistrettoPointi686-no-tablesRistrettoPointi686-no-tables»
end ristretto.RistrettoPoint.«i686-no-tables».Insts

end Curve25519Dalek
