/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Edwards.AsProjective
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::double`: the projective doubling formula, back in extended coordinates;
limbs `< 2^52`. -/
@[step]
theorem double_toExtended (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52) :
    double self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended = self.toExtended.toProjective.double.toExtended ∧ r.LimbsLt 52 ⦄ := by
  unfold double
  step as ⟨pp, hpp, hppb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpp], hrb⟩

/-- `EdwardsPoint::double` doubles the represented point. -/
theorem double_spec (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    double self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (double_toExtended self hself) fun r ⟨hr, hb⟩ => by
    have hon' := Projective.double_onCurve (Extended.onCurve_toProjective hon)
    rw [EdwardsPoint.«64bit-tables».onCurve_iff,
      EdwardsPoint.«64bit-tables».toPoint_def,
      hr,
      EdwardsPoint.«64bit-tables».toPoint_def, Completed.toPoint_toExtended hon',
      Projective.toPoint_double (Extended.onCurve_toProjective hon),
      Extended.toPoint_toProjective hon]
    exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::double`: the projective doubling formula, back in extended coordinates;
limbs `< 2^26`. -/
@[step]
theorem double_toExtended (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26) :
    double self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended = self.toExtended.toProjective.double.toExtended ∧ r.LimbsLt 26 ⦄ := by
  unfold double
  step as ⟨pp, hpp, hppb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpp], hrb⟩

/-- `EdwardsPoint::double` doubles the represented point. -/
theorem double_spec (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    double self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (double_toExtended self hself) fun r ⟨hr, hb⟩ => by
    have hon' := Projective.double_onCurve (Extended.onCurve_toProjective hon)
    rw [EdwardsPoint.«32bit-tables».onCurve_iff,
      EdwardsPoint.«32bit-tables».toPoint_def,
      hr,
      EdwardsPoint.«32bit-tables».toPoint_def, Completed.toPoint_toExtended hon',
      Projective.toPoint_double (Extended.onCurve_toProjective hon),
      Extended.toPoint_toProjective hon]
    exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::double`: the projective doubling formula, back in extended coordinates;
limbs `< 2^52`. -/
@[step]
theorem double_toExtended (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52) :
    double self ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended = self.toExtended.toProjective.double.toExtended ∧ r.LimbsLt 52 ⦄ := by
  unfold double
  step as ⟨pp, hpp, hppb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpp], hrb⟩

/-- `EdwardsPoint::double` doubles the represented point. -/
theorem double_spec (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    double self ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (double_toExtended self hself) fun r ⟨hr, hb⟩ => by
    have hon' := Projective.double_onCurve (Extended.onCurve_toProjective hon)
    rw [EdwardsPoint.«64bit-notables».onCurve_iff,
      EdwardsPoint.«64bit-notables».toPoint_def,
      hr,
      EdwardsPoint.«64bit-notables».toPoint_def, Completed.toPoint_toExtended hon',
      Projective.toPoint_double (Extended.onCurve_toProjective hon),
      Extended.toPoint_toProjective hon]
    exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::double`: the projective doubling formula, back in extended coordinates;
limbs `< 2^26`. -/
@[step]
theorem double_toExtended (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26) :
    double self ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended = self.toExtended.toProjective.double.toExtended ∧ r.LimbsLt 26 ⦄ := by
  unfold double
  step as ⟨pp, hpp, hppb⟩
  step as ⟨cp, hcp, hcpb⟩
  step as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, hcp, hpp], hrb⟩

/-- `EdwardsPoint::double` doubles the represented point. -/
theorem double_spec (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    double self ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 2 • self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (double_toExtended self hself) fun r ⟨hr, hb⟩ => by
    have hon' := Projective.double_onCurve (Extended.onCurve_toProjective hon)
    rw [EdwardsPoint.«32bit-notables».onCurve_iff,
      EdwardsPoint.«32bit-notables».toPoint_def,
      hr,
      EdwardsPoint.«32bit-notables».toPoint_def, Completed.toPoint_toExtended hon',
      Projective.toPoint_double (Extended.onCurve_toProjective hon),
      Extended.toPoint_toProjective hon]
    exact ⟨Completed.onCurve_toExtended hon', rfl, hb⟩

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
