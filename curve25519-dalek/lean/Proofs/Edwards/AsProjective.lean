/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_projective`: forget `T`, limbs `< 2^52`. -/
@[step]
theorem as_projective_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-tables») =>
      r.toProjective = self.toExtended.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step*
  exact ⟨by simp only [ProjectivePoint.«x86_64-tables».toProjective_def,
    EdwardsPoint.«x86_64-tables».toExtended_def, Extended.toProjective], hX, hY, hZ⟩

/-- `EdwardsPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«x86_64-tables».onCurve_iff,
      ProjectivePoint.«x86_64-tables».toPoint_def, hr,
      EdwardsPoint.«x86_64-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjective hon, Extended.toPoint_toProjective hon, hb⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_projective`: forget `T`, limbs `< 2^26`. -/
@[step]
theorem as_projective_spec (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-tables») =>
      r.toProjective = self.toExtended.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step*
  exact ⟨by simp only [ProjectivePoint.«i686-tables».toProjective_def,
    EdwardsPoint.«i686-tables».toExtended_def, Extended.toProjective], hX, hY, hZ⟩

/-- `EdwardsPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«i686-tables».onCurve_iff,
      ProjectivePoint.«i686-tables».toPoint_def, hr,
      EdwardsPoint.«i686-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjective hon, Extended.toPoint_toProjective hon, hb⟩

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_projective`: forget `T`, limbs `< 2^52`. -/
@[step]
theorem as_projective_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-no-tables») =>
      r.toProjective = self.toExtended.toProjective ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step*
  exact ⟨by simp only [ProjectivePoint.«x86_64-no-tables».toProjective_def,
    EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.toProjective], hX, hY, hZ⟩

/-- `EdwardsPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«x86_64-no-tables».onCurve_iff,
      ProjectivePoint.«x86_64-no-tables».toPoint_def, hr,
      EdwardsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjective hon, Extended.toPoint_toProjective hon, hb⟩

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_projective`: forget `T`, limbs `< 2^26`. -/
@[step]
theorem as_projective_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-no-tables») =>
      r.toProjective = self.toExtended.toProjective ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective
  step*
  exact ⟨by simp only [ProjectivePoint.«i686-no-tables».toProjective_def,
    EdwardsPoint.«i686-no-tables».toExtended_def, Extended.toProjective], hX, hY, hZ⟩

/-- `EdwardsPoint::as_projective` represents the same point. -/
theorem as_projective_spec_point (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    as_projective self ⦃ (r : ProjectivePoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (as_projective_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«i686-no-tables».onCurve_iff,
      ProjectivePoint.«i686-no-tables».toPoint_def, hr,
      EdwardsPoint.«i686-no-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjective hon, Extended.toPoint_toProjective hon, hb⟩

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
