/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Constants.EdwardsD2
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Constants.EdwardsD2
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_projective_niels`: `(Y + X : Y - X : Z : T (2 d))`; limbs `< 2^52` in,
`< 2^54` out. -/
@[step]
theorem as_projective_niels_toProjectiveNiels (self : EdwardsPoint.«x86_64-tables») (hself :
    self.LimbsLt 52) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.toProjectiveNiels = self.toExtended.toProjectiveNiels ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective_niels
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨T2d, hT2d, hT2d_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«x86_64-tables».toProjectiveNiels_def,
      EdwardsPoint.«x86_64-tables».toExtended_def, Extended.toProjectiveNiels,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X, toField_mul_of_mod hT2d,
      toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hY_plus_X hY hX),
      limbs_lt_of_le (by decide) hY_minus_X_lt, limbs_lt_of_le (by decide) hZ,
      limbs_lt_of_le (by decide) hT2d_lt⟩

/-- `EdwardsPoint::as_projective_niels` represents the same point. -/
theorem as_projective_niels_spec (self : EdwardsPoint.«x86_64-tables»)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (as_projective_niels_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-tables».toPoint_def, hr,
      EdwardsPoint.«x86_64-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjectiveNiels hon,
      Extended.toPoint_toProjectiveNiels hon, hb⟩

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_projective_niels`: `(Y + X : Y - X : Z : T (2 d))`; limbs `< 2^26` in,
`< 2^27` out. -/
@[step]
theorem as_projective_niels_toProjectiveNiels (self : EdwardsPoint.«i686-tables») (hself :
    self.LimbsLt 26) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«i686-tables») =>
      r.toProjectiveNiels = self.toExtended.toProjectiveNiels ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective_niels
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨T2d, hT2d, hT2d_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«i686-tables».toProjectiveNiels_def,
      EdwardsPoint.«i686-tables».toExtended_def, Extended.toProjectiveNiels,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X, toField_mul_of_mod hT2d,
      toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hY_plus_X hY hX),
      limbs_lt_of_le (by decide) hY_minus_X_lt, limbs_lt_of_le (by decide) hZ,
      limbs_lt_of_le (by decide) hT2d_lt⟩

/-- `EdwardsPoint::as_projective_niels` represents the same point. -/
theorem as_projective_niels_spec (self : EdwardsPoint.«i686-tables»)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (as_projective_niels_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«i686-tables».onCurve_iff,
      ProjectiveNielsPoint.«i686-tables».toPoint_def, hr,
      EdwardsPoint.«i686-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjectiveNiels hon,
      Extended.toPoint_toProjectiveNiels hon, hb⟩

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_projective_niels`: `(Y + X : Y - X : Z : T (2 d))`; limbs `< 2^52` in,
`< 2^54` out. -/
@[step]
theorem as_projective_niels_toProjectiveNiels (self : EdwardsPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.toProjectiveNiels = self.toExtended.toProjectiveNiels ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective_niels
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨T2d, hT2d, hT2d_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«x86_64-no-tables».toProjectiveNiels_def,
      EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.toProjectiveNiels,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X, toField_mul_of_mod hT2d,
      toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hY_plus_X hY hX),
      limbs_lt_of_le (by decide) hY_minus_X_lt, limbs_lt_of_le (by decide) hZ,
      limbs_lt_of_le (by decide) hT2d_lt⟩

/-- `EdwardsPoint::as_projective_niels` represents the same point. -/
theorem as_projective_niels_spec (self : EdwardsPoint.«x86_64-no-tables»)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (as_projective_niels_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«x86_64-no-tables».onCurve_iff,
      ProjectiveNielsPoint.«x86_64-no-tables».toPoint_def, hr,
      EdwardsPoint.«x86_64-no-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjectiveNiels hon,
      Extended.toPoint_toProjectiveNiels hon, hb⟩

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_projective_niels`: `(Y + X : Y - X : Z : T (2 d))`; limbs `< 2^26` in,
`< 2^27` out. -/
@[step]
theorem as_projective_niels_toProjectiveNiels (self : EdwardsPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«i686-no-tables») =>
      r.toProjectiveNiels = self.toExtended.toProjectiveNiels ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective_niels
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨T2d, hT2d, hT2d_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«i686-no-tables».toProjectiveNiels_def,
      EdwardsPoint.«i686-no-tables».toExtended_def, Extended.toProjectiveNiels,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X, toField_mul_of_mod hT2d,
      toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hY_plus_X hY hX),
      limbs_lt_of_le (by decide) hY_minus_X_lt, limbs_lt_of_le (by decide) hZ,
      limbs_lt_of_le (by decide) hT2d_lt⟩

/-- `EdwardsPoint::as_projective_niels` represents the same point. -/
theorem as_projective_niels_spec (self : EdwardsPoint.«i686-no-tables»)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (as_projective_niels_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«i686-no-tables».onCurve_iff,
      ProjectiveNielsPoint.«i686-no-tables».toPoint_def, hr,
      EdwardsPoint.«i686-no-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjectiveNiels hon,
      Extended.toPoint_toProjectiveNiels hon, hb⟩

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
