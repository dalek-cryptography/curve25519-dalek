/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.Add
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
  (add_spec)

namespace edwards.EdwardsPoint.«64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddAssignSharedAEdwardsPoint64bit-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_toExtended (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  exact add_spec self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignSharedAEdwardsPoint64bit-tables»

namespace «CoreOpsArithAddAssignEdwardsPoint64bit-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_toExtended (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  exact «CoreOpsArithAddAssignSharedAEdwardsPoint64bit-tables».add_assign_spec self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignEdwardsPoint64bit-tables»
end edwards.EdwardsPoint.«64bit-tables».Insts

namespace edwards.EdwardsPoint.«32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
  (add_spec)

namespace «CoreOpsArithAddAssignSharedAEdwardsPoint32bit-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_toExtended (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  exact add_spec self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignSharedAEdwardsPoint32bit-tables»

namespace «CoreOpsArithAddAssignEdwardsPoint32bit-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_toExtended (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  exact «CoreOpsArithAddAssignSharedAEdwardsPoint32bit-tables».add_assign_spec self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignEdwardsPoint32bit-tables»
end edwards.EdwardsPoint.«32bit-tables».Insts

open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
  (add_spec)

namespace edwards.EdwardsPoint.«64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddAssignSharedAEdwardsPoint64bit-notables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_toExtended (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  exact add_spec self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignSharedAEdwardsPoint64bit-notables»

namespace «CoreOpsArithAddAssignEdwardsPoint64bit-notables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_toExtended (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  exact «CoreOpsArithAddAssignSharedAEdwardsPoint64bit-notables».add_assign_spec self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignEdwardsPoint64bit-notables»
end edwards.EdwardsPoint.«64bit-notables».Insts

namespace edwards.EdwardsPoint.«32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
  (add_spec)

namespace «CoreOpsArithAddAssignSharedAEdwardsPoint32bit-notables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_toExtended (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  exact add_spec self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignSharedAEdwardsPoint32bit-notables»

namespace «CoreOpsArithAddAssignEdwardsPoint32bit-notables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_toExtended (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  exact «CoreOpsArithAddAssignSharedAEdwardsPoint32bit-notables».add_assign_spec self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignEdwardsPoint32bit-notables»
end edwards.EdwardsPoint.«32bit-notables».Insts

end Curve25519Dalek
