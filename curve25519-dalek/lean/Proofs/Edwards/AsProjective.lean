module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_projective`: forget `T`, limbs `< 2^52`. -/
@[step]
theorem as_projective_toProjective (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52) :
    as_projective self ⦃ (r : ProjectivePoint.«64bit-tables») =>
      r.toProjective = self.toExtended.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step*
  exact ⟨by simp only [ProjectivePoint.«64bit-tables».toProjective_def,
    EdwardsPoint.«64bit-tables».toExtended_def, Extended.toProjective], hX, hY, hZ⟩

/-- `EdwardsPoint::as_projective` represents the same point. -/
theorem as_projective_spec (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_toProjective self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«64bit-tables».onCurve_iff,
      ProjectivePoint.«64bit-tables».toPoint_def, hr,
      EdwardsPoint.«64bit-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjective hon, Extended.toPoint_toProjective hon, hb⟩

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_projective`: forget `T`, limbs `< 2^26`. -/
@[step]
theorem as_projective_toProjective (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26) :
    as_projective self ⦃ (r : ProjectivePoint.«32bit-tables») =>
      r.toProjective = self.toExtended.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step*
  exact ⟨by simp only [ProjectivePoint.«32bit-tables».toProjective_def,
    EdwardsPoint.«32bit-tables».toExtended_def, Extended.toProjective], hX, hY, hZ⟩

/-- `EdwardsPoint::as_projective` represents the same point. -/
theorem as_projective_spec (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_toProjective self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«32bit-tables».onCurve_iff,
      ProjectivePoint.«32bit-tables».toPoint_def, hr,
      EdwardsPoint.«32bit-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjective hon, Extended.toPoint_toProjective hon, hb⟩

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_projective`: forget `T`, limbs `< 2^52`. -/
@[step]
theorem as_projective_toProjective (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt
    52) :
    as_projective self ⦃ (r : ProjectivePoint.«64bit-notables») =>
      r.toProjective = self.toExtended.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step*
  exact ⟨by simp only [ProjectivePoint.«64bit-notables».toProjective_def,
    EdwardsPoint.«64bit-notables».toExtended_def, Extended.toProjective], hX, hY, hZ⟩

/-- `EdwardsPoint::as_projective` represents the same point. -/
theorem as_projective_spec (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_toProjective self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«64bit-notables».onCurve_iff,
      ProjectivePoint.«64bit-notables».toPoint_def, hr,
      EdwardsPoint.«64bit-notables».toPoint_def]
    exact ⟨Extended.onCurve_toProjective hon, Extended.toPoint_toProjective hon, hb⟩

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_projective`: forget `T`, limbs `< 2^26`. -/
@[step]
theorem as_projective_toProjective (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    :
    as_projective self ⦃ (r : ProjectivePoint.«32bit-notables») =>
      r.toProjective = self.toExtended.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step*
  exact ⟨by simp only [ProjectivePoint.«32bit-notables».toProjective_def,
    EdwardsPoint.«32bit-notables».toExtended_def, Extended.toProjective], hX, hY, hZ⟩

/-- `EdwardsPoint::as_projective` represents the same point. -/
theorem as_projective_spec (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_toProjective self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«32bit-notables».onCurve_iff,
      ProjectivePoint.«32bit-notables».toPoint_def, hr,
      EdwardsPoint.«32bit-notables».toPoint_def]
    exact ⟨Extended.onCurve_toProjective hon, Extended.toPoint_toProjective hon, hb⟩

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
