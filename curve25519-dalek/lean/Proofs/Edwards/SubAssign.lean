/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.Sub
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
  (sub_spec_point)

namespace edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  exact sub_spec_point self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-tables»

namespace «CoreOpsArithSubAssignEdwardsPointx86_64-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  exact «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-tables».sub_assign_spec_point self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignEdwardsPointx86_64-tables»
end edwards.EdwardsPoint.«x86_64-tables».Insts

namespace edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»
  (sub_spec_point)

namespace «CoreOpsArithSubAssignSharedAEdwardsPointi686-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec_point (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  exact sub_spec_point self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignSharedAEdwardsPointi686-tables»

namespace «CoreOpsArithSubAssignEdwardsPointi686-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec_point (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  exact «CoreOpsArithSubAssignSharedAEdwardsPointi686-tables».sub_assign_spec_point self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignEdwardsPointi686-tables»
end edwards.EdwardsPoint.«i686-tables».Insts

open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
  (sub_spec_point)

namespace edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-no-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  exact sub_spec_point self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithSubAssignEdwardsPointx86_64-no-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  exact «CoreOpsArithSubAssignSharedAEdwardsPointx86_64-no-tables».sub_assign_spec_point self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignEdwardsPointx86_64-no-tables»
end edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
  (sub_spec_point)

namespace «CoreOpsArithSubAssignSharedAEdwardsPointi686-no-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec_point (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  exact sub_spec_point self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignSharedAEdwardsPointi686-no-tables»

namespace «CoreOpsArithSubAssignEdwardsPointi686-no-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec_point (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  exact «CoreOpsArithSubAssignSharedAEdwardsPointi686-no-tables».sub_assign_spec_point self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignEdwardsPointi686-no-tables»
end edwards.EdwardsPoint.«i686-no-tables».Insts

end Curve25519Dalek
