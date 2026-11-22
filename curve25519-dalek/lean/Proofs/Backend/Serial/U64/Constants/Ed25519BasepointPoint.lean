/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.U64.Field.FromLimbs
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
public import Proofs.Helpers.ByteValues
public section

/-! # `ED25519_BASEPOINT_POINT`

The limbs are the RFC 8032 basepoint `curve25519.basepoint` in the extended coordinates
`(x : y : 1 : x y)`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51

namespace Curve25519Dalek.backend.serial.u64.constants

namespace «64bit-tables»

/-- `ED25519_BASEPOINT_POINT`: the extended coordinates `(x : y : 1 : x y)` of the basepoint;
limbs `< 2^51`. -/
@[step]
theorem ED25519_BASEPOINT_POINT_toExtended :
    ED25519_BASEPOINT_POINT.«64bit-tables» ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.toExtended = basepoint.toExtended ∧ r.LimbsLt 52 ⦄ := by
  unfold ED25519_BASEPOINT_POINT.«64bit-tables»
  step as ⟨X, hX⟩
  step as ⟨Y, hY⟩
  step as ⟨Z, hZ⟩
  step as ⟨T, hT⟩
  have hXn : X.asNat =
      15112221349535400772501151409588531511454012693041857206046113283949847762202 := by
    rw [hX, asNat_def, Array.asNat_def, Array.make_val]; decide
  have hYn : Y.asNat =
      46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
    rw [hY, asNat_def, Array.asNat_def, Array.make_val]; decide
  have hZn : Z.asNat = 1 := by rw [hZ, asNat_def, Array.asNat_def, Array.make_val]; decide
  have hTn : T.asNat % p = X.asNat * Y.asNat % p := by
    rw [hXn, hYn, hT, asNat_def, Array.asNat_def, Array.make_val, p_eq_numeral]; decide
  refine ⟨?_, ?_⟩
  · rw [edwards.EdwardsPoint.«64bit-tables».toExtended_def, Point.toExtended,
      toField_mul_of_mod hTn, toField_eq_ofNat_of_asNat hXn, toField_eq_ofNat_of_asNat hYn,
      toField_eq_one_of_asNat hZn, basepoint_x_eq, basepoint_y_eq]
  · unfold edwards.EdwardsPoint.«64bit-tables».LimbsLt
    subst hX hY hZ hT
    decide

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
theorem ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT.«64bit-tables» ⦃ (r : edwards.EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono ED25519_BASEPOINT_POINT_toExtended fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«64bit-tables».onCurve_iff,
      edwards.EdwardsPoint.«64bit-tables».toPoint_def, hr]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «64bit-tables»

namespace «64bit-notables»

/-- `ED25519_BASEPOINT_POINT`: the extended coordinates `(x : y : 1 : x y)` of the basepoint;
limbs `< 2^51`. -/
@[step]
theorem ED25519_BASEPOINT_POINT_toExtended :
    ED25519_BASEPOINT_POINT.«64bit-notables» ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.toExtended = basepoint.toExtended ∧ r.LimbsLt 52 ⦄ := by
  unfold ED25519_BASEPOINT_POINT.«64bit-notables»
  step as ⟨X, hX⟩
  step as ⟨Y, hY⟩
  step as ⟨Z, hZ⟩
  step as ⟨T, hT⟩
  have hXn : X.asNat =
      15112221349535400772501151409588531511454012693041857206046113283949847762202 := by
    rw [hX, asNat_def, Array.asNat_def, Array.make_val]; decide
  have hYn : Y.asNat =
      46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
    rw [hY, asNat_def, Array.asNat_def, Array.make_val]; decide
  have hZn : Z.asNat = 1 := by rw [hZ, asNat_def, Array.asNat_def, Array.make_val]; decide
  have hTn : T.asNat % p = X.asNat * Y.asNat % p := by
    rw [hXn, hYn, hT, asNat_def, Array.asNat_def, Array.make_val, p_eq_numeral]; decide
  refine ⟨?_, ?_⟩
  · rw [edwards.EdwardsPoint.«64bit-notables».toExtended_def, Point.toExtended,
      toField_mul_of_mod hTn, toField_eq_ofNat_of_asNat hXn, toField_eq_ofNat_of_asNat hYn,
      toField_eq_one_of_asNat hZn, basepoint_x_eq, basepoint_y_eq]
  · unfold edwards.EdwardsPoint.«64bit-notables».LimbsLt
    subst hX hY hZ hT
    decide

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
theorem ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT.«64bit-notables» ⦃ (r : edwards.EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono ED25519_BASEPOINT_POINT_toExtended fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«64bit-notables».onCurve_iff,
      edwards.EdwardsPoint.«64bit-notables».toPoint_def, hr]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «64bit-notables»

end Curve25519Dalek.backend.serial.u64.constants
