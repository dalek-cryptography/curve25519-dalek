module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
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

namespace «EdwardsPoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_projective_niels`: `(Y + X : Y - X : Z : T (2 d))`; limbs `< 2^52` in,
`< 2^54` out. -/
@[step]
theorem as_projective_niels_toProjectiveNiels (self : EdwardsPoint.«64bit-tables») (hself :
    self.LimbsLt 52) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
      r.toProjectiveNiels = self.toExtended.toProjectiveNiels ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective_niels
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨T2d, hT2d, hT2d_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«64bit-tables».toProjectiveNiels_def,
      EdwardsPoint.«64bit-tables».toExtended_def, Extended.toProjectiveNiels,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X, toField_mul_of_mod hT2d,
      toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hY_plus_X hY hX),
      limbs_lt_of_le (by decide) hY_minus_X_lt, limbs_lt_of_le (by decide) hZ,
      limbs_lt_of_le (by decide) hT2d_lt⟩

/-- `EdwardsPoint::as_projective_niels` represents the same point. -/
theorem as_projective_niels_spec (self : EdwardsPoint.«64bit-tables»)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (as_projective_niels_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«64bit-tables».onCurve_iff,
      ProjectiveNielsPoint.«64bit-tables».toPoint_def, hr,
      EdwardsPoint.«64bit-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjectiveNiels hon,
      Extended.toPoint_toProjectiveNiels hon, hb⟩

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_projective_niels`: `(Y + X : Y - X : Z : T (2 d))`; limbs `< 2^26` in,
`< 2^27` out. -/
@[step]
theorem as_projective_niels_toProjectiveNiels (self : EdwardsPoint.«32bit-tables») (hself :
    self.LimbsLt 26) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
      r.toProjectiveNiels = self.toExtended.toProjectiveNiels ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective_niels
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨T2d, hT2d, hT2d_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«32bit-tables».toProjectiveNiels_def,
      EdwardsPoint.«32bit-tables».toExtended_def, Extended.toProjectiveNiels,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X, toField_mul_of_mod hT2d,
      toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hY_plus_X hY hX),
      limbs_lt_of_le (by decide) hY_minus_X_lt, limbs_lt_of_le (by decide) hZ,
      limbs_lt_of_le (by decide) hT2d_lt⟩

/-- `EdwardsPoint::as_projective_niels` represents the same point. -/
theorem as_projective_niels_spec (self : EdwardsPoint.«32bit-tables»)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (as_projective_niels_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«32bit-tables».onCurve_iff,
      ProjectiveNielsPoint.«32bit-tables».toPoint_def, hr,
      EdwardsPoint.«32bit-tables».toPoint_def]
    exact ⟨Extended.onCurve_toProjectiveNiels hon,
      Extended.toPoint_toProjectiveNiels hon, hb⟩

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::as_projective_niels`: `(Y + X : Y - X : Z : T (2 d))`; limbs `< 2^52` in,
`< 2^54` out. -/
@[step]
theorem as_projective_niels_toProjectiveNiels (self : EdwardsPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
      r.toProjectiveNiels = self.toExtended.toProjectiveNiels ∧ r.LimbsLt 54 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective_niels
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨T2d, hT2d, hT2d_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«64bit-notables».toProjectiveNiels_def,
      EdwardsPoint.«64bit-notables».toExtended_def, Extended.toProjectiveNiels,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X, toField_mul_of_mod hT2d,
      toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hY_plus_X hY hX),
      limbs_lt_of_le (by decide) hY_minus_X_lt, limbs_lt_of_le (by decide) hZ,
      limbs_lt_of_le (by decide) hT2d_lt⟩

/-- `EdwardsPoint::as_projective_niels` represents the same point. -/
theorem as_projective_niels_spec (self : EdwardsPoint.«64bit-notables»)
    (hself : self.LimbsLt 52) (hon : self.OnCurve) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (as_projective_niels_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«64bit-notables».onCurve_iff,
      ProjectiveNielsPoint.«64bit-notables».toPoint_def, hr,
      EdwardsPoint.«64bit-notables».toPoint_def]
    exact ⟨Extended.onCurve_toProjectiveNiels hon,
      Extended.toPoint_toProjectiveNiels hon, hb⟩

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::as_projective_niels`: `(Y + X : Y - X : Z : T (2 d))`; limbs `< 2^26` in,
`< 2^27` out. -/
@[step]
theorem as_projective_niels_toProjectiveNiels (self : EdwardsPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
      r.toProjectiveNiels = self.toExtended.toProjectiveNiels ∧ r.LimbsLt 27 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold as_projective_niels
  step as ⟨Y_plus_X, hY_plus_X⟩
  step as ⟨Y_minus_X, hY_minus_X, hY_minus_X_lt⟩
  step as ⟨D2, hD2, hD2_lt⟩
  step as ⟨T2d, hT2d, hT2d_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«32bit-notables».toProjectiveNiels_def,
      EdwardsPoint.«32bit-notables».toExtended_def, Extended.toProjectiveNiels,
      toField_add_of_limbs hY_plus_X, toField_sub_of_mod hY_minus_X, toField_mul_of_mod hT2d,
      toField_eq_two_mul_d_of_asNat hD2, edwards_d]
  · exact ⟨limbs_lt_of_le (by decide) (limbs_add_lt hY_plus_X hY hX),
      limbs_lt_of_le (by decide) hY_minus_X_lt, limbs_lt_of_le (by decide) hZ,
      limbs_lt_of_le (by decide) hT2d_lt⟩

/-- `EdwardsPoint::as_projective_niels` represents the same point. -/
theorem as_projective_niels_spec (self : EdwardsPoint.«32bit-notables»)
    (hself : self.LimbsLt 26) (hon : self.OnCurve) :
    as_projective_niels self ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (as_projective_niels_toProjectiveNiels self hself) fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«32bit-notables».onCurve_iff,
      ProjectiveNielsPoint.«32bit-notables».toPoint_def, hr,
      EdwardsPoint.«32bit-notables».toPoint_def]
    exact ⟨Extended.onCurve_toProjectiveNiels hon,
      Extended.toPoint_toProjectiveNiels hon, hb⟩

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
