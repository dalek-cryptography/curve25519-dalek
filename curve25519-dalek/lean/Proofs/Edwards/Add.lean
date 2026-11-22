/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Edwards.AsProjectiveNiels
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek

namespace «Shared0EdwardsPoint64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `addProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^52`. -/
@[step]
theorem add_toExtended (self other : edwards.EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    add self other ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `add_toExtended`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«64bit-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.addProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 52) :
    r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 52 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.addProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«64bit-tables».onCurve_iff,
    edwards.EdwardsPoint.«64bit-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«64bit-tables».toPoint_def,
    edwards.EdwardsPoint.«64bit-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_addProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem add_spec (self other : edwards.EdwardsPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (add_toExtended self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithAddSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
end «Shared0EdwardsPoint64bit-tables».Insts

namespace «Shared0EdwardsPoint32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `addProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^26`. -/
@[step]
theorem add_toExtended (self other : edwards.EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    add self other ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `add_toExtended`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«32bit-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.addProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 26) :
    r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 26 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.addProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«32bit-tables».onCurve_iff,
    edwards.EdwardsPoint.«32bit-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«32bit-tables».toPoint_def,
    edwards.EdwardsPoint.«32bit-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_addProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem add_spec (self other : edwards.EdwardsPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (add_toExtended self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithAddSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end «Shared0EdwardsPoint32bit-tables».Insts

open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
  (point_of_post)

namespace edwards.EdwardsPoint.«64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Add<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add
  step*

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

namespace «CoreOpsArithAddSharedBEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Add<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add
  step*

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddSharedBEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
end edwards.EdwardsPoint.«64bit-tables».Insts

namespace edwards.EdwardsPoint.«32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
  (point_of_post)

namespace «CoreOpsArithAddEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Add<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add
  step*

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

namespace «CoreOpsArithAddSharedBEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Add<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add
  step*

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddSharedBEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end edwards.EdwardsPoint.«32bit-tables».Insts

namespace «SharedAEdwardsPoint64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Add<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : edwards.EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add
  step*

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : edwards.EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
end «SharedAEdwardsPoint64bit-tables».Insts

namespace «SharedAEdwardsPoint32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
  (point_of_post)

namespace «CoreOpsArithAddEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Add<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : edwards.EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add
  step*

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : edwards.EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end «SharedAEdwardsPoint32bit-tables».Insts

namespace «Shared0EdwardsPoint64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `addProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^52`. -/
@[step]
theorem add_toExtended (self other : edwards.EdwardsPoint.«64bit-notables») (hself : self.LimbsLt
    52)
    (hother : other.LimbsLt 52) :
    add self other ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `add_toExtended`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«64bit-notables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.addProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 52) :
    r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 52 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.addProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«64bit-notables».onCurve_iff,
    edwards.EdwardsPoint.«64bit-notables».toPoint_def, hr,
    edwards.EdwardsPoint.«64bit-notables».toPoint_def,
    edwards.EdwardsPoint.«64bit-notables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_addProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem add_spec (self other : edwards.EdwardsPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (add_toExtended self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithAddSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
end «Shared0EdwardsPoint64bit-notables».Insts

namespace «Shared0EdwardsPoint32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithAddSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Add<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `addProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^26`. -/
@[step]
theorem add_toExtended (self other : edwards.EdwardsPoint.«32bit-notables») (hself : self.LimbsLt
    26)
    (hother : other.LimbsLt 26) :
    add self other ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `add_toExtended`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«32bit-notables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.addProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 26) :
    r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 26 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.addProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«32bit-notables».onCurve_iff,
    edwards.EdwardsPoint.«32bit-notables».toPoint_def, hr,
    edwards.EdwardsPoint.«32bit-notables».toPoint_def,
    edwards.EdwardsPoint.«32bit-notables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_addProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Add<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem add_spec (self other : edwards.EdwardsPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    add self other ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + other.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (add_toExtended self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithAddSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end «Shared0EdwardsPoint32bit-notables».Insts

open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
  (point_of_post)

namespace edwards.EdwardsPoint.«64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Add<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add
  step*

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

namespace «CoreOpsArithAddSharedBEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Add<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    add self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add
  step*

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddSharedBEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
end edwards.EdwardsPoint.«64bit-notables».Insts

namespace edwards.EdwardsPoint.«32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
  (point_of_post)

namespace «CoreOpsArithAddEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Add<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add
  step*

/-- `Add<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

namespace «CoreOpsArithAddSharedBEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Add<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add
  step*

/-- `Add<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddSharedBEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end edwards.EdwardsPoint.«32bit-notables».Insts

namespace «SharedAEdwardsPoint64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithAddEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Add<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : edwards.EdwardsPoint.«64bit-notables») (hself : self.LimbsLt
    52)
    (hrhs : rhs.LimbsLt 52) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold add
  step*

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : edwards.EdwardsPoint.«64bit-notables»)
    (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
end «SharedAEdwardsPoint64bit-notables».Insts

namespace «SharedAEdwardsPoint32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
  (point_of_post)

namespace «CoreOpsArithAddEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Add<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem add_toExtended (self rhs : edwards.EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.addProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold add
  step*

/-- `Add<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem add_spec (self rhs : edwards.EdwardsPoint.«32bit-notables»)
    (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    add self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint + rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (add_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithAddEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end «SharedAEdwardsPoint32bit-notables».Insts

end Curve25519Dalek
