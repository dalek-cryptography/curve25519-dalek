/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.Add
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
  (add_spec_point)

namespace edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  exact add_spec_point self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-tables»

namespace «CoreOpsArithAddAssignEdwardsPointx86_64-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  exact «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-tables».add_assign_spec_point self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignEdwardsPointx86_64-tables»
end edwards.EdwardsPoint.«x86_64-tables».Insts

namespace edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»
  (add_spec_point)

namespace «CoreOpsArithAddAssignSharedAEdwardsPointi686-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec_point (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  exact add_spec_point self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignSharedAEdwardsPointi686-tables»

namespace «CoreOpsArithAddAssignEdwardsPointi686-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec_point (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  exact «CoreOpsArithAddAssignSharedAEdwardsPointi686-tables».add_assign_spec_point self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignEdwardsPointi686-tables»
end edwards.EdwardsPoint.«i686-tables».Insts

open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithAddSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
  (add_spec_point)

namespace edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-no-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  exact add_spec_point self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ := by
  unfold add_assign
  exact «CoreOpsArithAddAssignSharedAEdwardsPointx86_64-no-tables».add_assign_spec_point self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignEdwardsPointx86_64-no-tables»
end edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
  (add_spec_point)

namespace «CoreOpsArithAddAssignSharedAEdwardsPointi686-no-tables»

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec_point (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  exact add_spec_point self rhs hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignSharedAEdwardsPointi686-no-tables»

namespace «CoreOpsArithAddAssignEdwardsPointi686-no-tables»

/-- `AddAssign<EdwardsPoint> for EdwardsPoint`: as `Add`. -/
@[step]
theorem add_assign_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add_assign
  step*

/-- `AddAssign<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_assign_spec_point (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add_assign self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ := by
  unfold add_assign
  exact «CoreOpsArithAddAssignSharedAEdwardsPointi686-no-tables».add_assign_spec_point self rhs
    hself hrhs hself_on hrhs_on

end «CoreOpsArithAddAssignEdwardsPointi686-no-tables»
end edwards.EdwardsPoint.«i686-no-tables».Insts

end Curve25519Dalek
