/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.Sub
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
  (sub_spec)

namespace edwards.EdwardsPoint.«64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubAssignSharedAEdwardsPoint64bit-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_toExtended (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  exact sub_spec self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignSharedAEdwardsPoint64bit-tables»

namespace «CoreOpsArithSubAssignEdwardsPoint64bit-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_toExtended (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  exact «CoreOpsArithSubAssignSharedAEdwardsPoint64bit-tables».sub_assign_spec self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignEdwardsPoint64bit-tables»
end edwards.EdwardsPoint.«64bit-tables».Insts

namespace edwards.EdwardsPoint.«32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
  (sub_spec)

namespace «CoreOpsArithSubAssignSharedAEdwardsPoint32bit-tables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_toExtended (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  exact sub_spec self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignSharedAEdwardsPoint32bit-tables»

namespace «CoreOpsArithSubAssignEdwardsPoint32bit-tables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_toExtended (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  exact «CoreOpsArithSubAssignSharedAEdwardsPoint32bit-tables».sub_assign_spec self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignEdwardsPoint32bit-tables»
end edwards.EdwardsPoint.«32bit-tables».Insts

open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
  (sub_spec)

namespace edwards.EdwardsPoint.«64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubAssignSharedAEdwardsPoint64bit-notables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_toExtended (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  exact sub_spec self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignSharedAEdwardsPoint64bit-notables»

namespace «CoreOpsArithSubAssignEdwardsPoint64bit-notables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_toExtended (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold sub_assign
  exact «CoreOpsArithSubAssignSharedAEdwardsPoint64bit-notables».sub_assign_spec self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignEdwardsPoint64bit-notables»
end edwards.EdwardsPoint.«64bit-notables».Insts

namespace edwards.EdwardsPoint.«32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
  (sub_spec)

namespace «CoreOpsArithSubAssignSharedAEdwardsPoint32bit-notables»

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_toExtended (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  exact sub_spec self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignSharedAEdwardsPoint32bit-notables»

namespace «CoreOpsArithSubAssignEdwardsPoint32bit-notables»

/-- `SubAssign<EdwardsPoint> for EdwardsPoint`: as `Sub`. -/
@[step]
theorem sub_assign_toExtended (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  step*

/-- `SubAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_assign_spec (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub_assign self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold sub_assign
  exact «CoreOpsArithSubAssignSharedAEdwardsPoint32bit-notables».sub_assign_spec self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithSubAssignEdwardsPoint32bit-notables»
end edwards.EdwardsPoint.«32bit-notables».Insts

end Curve25519Dalek
