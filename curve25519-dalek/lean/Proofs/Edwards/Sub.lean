module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
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

namespace «CoreOpsArithSubSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^52`. -/
@[step]
theorem sub_toExtended (self other : edwards.EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_toExtended`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«64bit-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 52) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«64bit-tables».onCurve_iff,
    edwards.EdwardsPoint.«64bit-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«64bit-tables».toPoint_def,
    edwards.EdwardsPoint.«64bit-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec (self other : edwards.EdwardsPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_toExtended self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
end «Shared0EdwardsPoint64bit-tables».Insts

namespace «Shared0EdwardsPoint32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^26`. -/
@[step]
theorem sub_toExtended (self other : edwards.EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_toExtended`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«32bit-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 26) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«32bit-tables».onCurve_iff,
    edwards.EdwardsPoint.«32bit-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«32bit-tables».toPoint_def,
    edwards.EdwardsPoint.«32bit-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec (self other : edwards.EdwardsPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_toExtended self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end «Shared0EdwardsPoint32bit-tables».Insts

open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
  (point_of_post)

namespace edwards.EdwardsPoint.«64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

namespace «CoreOpsArithSubSharedBEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
end edwards.EdwardsPoint.«64bit-tables».Insts

namespace edwards.EdwardsPoint.«32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
  (point_of_post)

namespace «CoreOpsArithSubEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

namespace «CoreOpsArithSubSharedBEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end edwards.EdwardsPoint.«32bit-tables».Insts

namespace «SharedAEdwardsPoint64bit-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : edwards.EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : edwards.EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
end «SharedAEdwardsPoint64bit-tables».Insts

namespace «SharedAEdwardsPoint32bit-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
  (point_of_post)

namespace «CoreOpsArithSubEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : edwards.EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : edwards.EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
end «SharedAEdwardsPoint32bit-tables».Insts

namespace «Shared0EdwardsPoint64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^52`. -/
@[step]
theorem sub_toExtended (self other : edwards.EdwardsPoint.«64bit-notables») (hself : self.LimbsLt
    52)
    (hother : other.LimbsLt 52) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_toExtended`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«64bit-notables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 52) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«64bit-notables».onCurve_iff,
    edwards.EdwardsPoint.«64bit-notables».toPoint_def, hr,
    edwards.EdwardsPoint.«64bit-notables».toPoint_def,
    edwards.EdwardsPoint.«64bit-notables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec (self other : edwards.EdwardsPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_toExtended self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
end «Shared0EdwardsPoint64bit-notables».Insts

namespace «Shared0EdwardsPoint32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^26`. -/
@[step]
theorem sub_toExtended (self other : edwards.EdwardsPoint.«32bit-notables») (hself : self.LimbsLt
    26)
    (hother : other.LimbsLt 26) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_toExtended`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«32bit-notables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 26) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«32bit-notables».onCurve_iff,
    edwards.EdwardsPoint.«32bit-notables».toPoint_def, hr,
    edwards.EdwardsPoint.«32bit-notables».toPoint_def,
    edwards.EdwardsPoint.«32bit-notables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec (self other : edwards.EdwardsPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_toExtended self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end «Shared0EdwardsPoint32bit-notables».Insts

open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
  (point_of_post)

namespace edwards.EdwardsPoint.«64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

namespace «CoreOpsArithSubSharedBEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
end edwards.EdwardsPoint.«64bit-notables».Insts

namespace edwards.EdwardsPoint.«32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
  (point_of_post)

namespace «CoreOpsArithSubEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

namespace «CoreOpsArithSubSharedBEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end edwards.EdwardsPoint.«32bit-notables».Insts

namespace «SharedAEdwardsPoint64bit-notables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : edwards.EdwardsPoint.«64bit-notables») (hself : self.LimbsLt
    52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : edwards.EdwardsPoint.«64bit-notables»)
    (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
end «SharedAEdwardsPoint64bit-notables».Insts

namespace «SharedAEdwardsPoint32bit-notables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithSubSharedAEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
  (point_of_post)

namespace «CoreOpsArithSubEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_toExtended (self rhs : edwards.EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec (self rhs : edwards.EdwardsPoint.«32bit-notables»)
    (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_toExtended self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
end «SharedAEdwardsPoint32bit-notables».Insts

end Curve25519Dalek
