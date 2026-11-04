/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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

namespace «Shared0EdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^52`. -/
@[step]
theorem sub_spec (self other : edwards.EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_spec`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«x86_64-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 52) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«x86_64-tables».toPoint_def,
    edwards.EdwardsPoint.«x86_64-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self other : edwards.EdwardsPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_spec self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end «Shared0EdwardsPointx86_64-tables».Insts

namespace «Shared0EdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^26`. -/
@[step]
theorem sub_spec (self other : edwards.EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_spec`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«i686-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 26) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
    edwards.EdwardsPoint.«i686-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«i686-tables».toPoint_def,
    edwards.EdwardsPoint.«i686-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self other : edwards.EdwardsPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_spec self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»
end «Shared0EdwardsPointi686-tables».Insts

open «Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
  (point_of_post)

namespace edwards.EdwardsPoint.«x86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

namespace «CoreOpsArithSubSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end edwards.EdwardsPoint.«x86_64-tables».Insts

namespace edwards.EdwardsPoint.«i686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»
  (point_of_post)

namespace «CoreOpsArithSubEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointi686-tablesEdwardsPointi686-tables»

namespace «CoreOpsArithSubSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPointi686-tablesEdwardsPointi686-tables»
end edwards.EdwardsPoint.«i686-tables».Insts

namespace «SharedAEdwardsPointx86_64-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : edwards.EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : edwards.EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointx86_64-tablesEdwardsPointx86_64-tables»
end «SharedAEdwardsPointx86_64-tables».Insts

namespace «SharedAEdwardsPointi686-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointi686-tablesEdwardsPointi686-tables»
  (point_of_post)

namespace «CoreOpsArithSubEdwardsPointi686-tablesEdwardsPointi686-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : edwards.EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : edwards.EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointi686-tablesEdwardsPointi686-tables»
end «SharedAEdwardsPointi686-tables».Insts

namespace «Shared0EdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^52`. -/
@[step]
theorem sub_spec (self other : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hother : other.LimbsLt 52) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_spec`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«x86_64-no-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 52) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def,
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self other : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hother : other.LimbsLt 52) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_spec self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end «Shared0EdwardsPointx86_64-no-tables».Insts

namespace «Shared0EdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace «CoreOpsArithSubSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Sub<&EdwardsPoint> for &EdwardsPoint`: the mixed formula `subProjectiveNiels` on the projective
Niels form of `other`, back in extended coordinates; limbs `< 2^26`. -/
@[step]
theorem sub_spec (self other : edwards.EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hother : other.LimbsLt 26) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step as ⟨pnp, hpnp, hpnpb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpnp], hrb⟩

/-- The point-level reading of the postcondition of `sub_spec`. -/
private theorem point_of_post {self other r : edwards.EdwardsPoint.«i686-no-tables»}
    (hself_on : self.OnCurve) (hother_on : other.OnCurve)
    (h : r.toExtended =
        (self.toExtended.subProjectiveNiels other.toExtended.toProjectiveNiels).toExtended ∧
      r.LimbsLt 26) :
    r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 := by
  obtain ⟨hr, hb⟩ := h
  have hon' := Extended.subProjectiveNiels_onCurve edwards_a_eq_neg_one hself_on
    (Extended.onCurve_toProjectiveNiels hother_on)
  rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«i686-no-tables».toPoint_def, hr,
    edwards.EdwardsPoint.«i686-no-tables».toPoint_def,
    edwards.EdwardsPoint.«i686-no-tables».toPoint_def, Completed.toPoint_toExtended hon',
    Extended.toPoint_subProjectiveNiels edwards_a_eq_neg_one hself_on
      (Extended.onCurve_toProjectiveNiels hother_on),
    Extended.toPoint_toProjectiveNiels hother_on]
  exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

/-- `Sub<&EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self other : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hother : other.LimbsLt 26) (hself_on : self.OnCurve)
    (hother_on : other.OnCurve) :
    sub self other ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - other.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_spec self other hself hother) fun _ => point_of_post hself_on hother_on

end «CoreOpsArithSubSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end «Shared0EdwardsPointi686-no-tables».Insts

open «Shared0EdwardsPointx86_64-no-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
  (point_of_post)

namespace edwards.EdwardsPoint.«x86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

namespace «CoreOpsArithSubSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end edwards.EdwardsPoint.«x86_64-no-tables».Insts

namespace edwards.EdwardsPoint.«i686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
  (point_of_post)

namespace «CoreOpsArithSubEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Sub<EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

namespace «CoreOpsArithSubSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Sub<&EdwardsPoint> for EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<&EdwardsPoint> for EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubSharedBEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end edwards.EdwardsPoint.«i686-no-tables».Insts

namespace «SharedAEdwardsPointx86_64-no-tables».Insts

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : edwards.EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 52 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : edwards.EdwardsPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52)
    (hrhs : rhs.LimbsLt 52) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointx86_64-no-tablesEdwardsPointx86_64-no-tables»
end «SharedAEdwardsPointx86_64-no-tables».Insts

namespace «SharedAEdwardsPointi686-no-tables».Insts

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithSubSharedAEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
  (point_of_post)

namespace «CoreOpsArithSubEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»

/-- `Sub<EdwardsPoint> for &EdwardsPoint`: as the borrowed form. -/
@[step]
theorem sub_spec (self rhs : edwards.EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.toExtended =
        (self.toExtended.subProjectiveNiels rhs.toExtended.toProjectiveNiels).toExtended ∧
        r.LimbsLt 26 ⦄ := by
  unfold sub
  step*

/-- `Sub<EdwardsPoint> for &EdwardsPoint` on the represented points. -/
theorem sub_spec_point (self rhs : edwards.EdwardsPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26)
    (hrhs : rhs.LimbsLt 26) (hself_on : self.OnCurve) (hrhs_on : rhs.OnCurve) :
    sub self rhs ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint - rhs.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (sub_spec self rhs hself hrhs) fun _ => point_of_post hself_on hrhs_on

end «CoreOpsArithSubEdwardsPointi686-no-tablesEdwardsPointi686-no-tables»
end «SharedAEdwardsPointi686-no-tables».Insts

end Curve25519Dalek
