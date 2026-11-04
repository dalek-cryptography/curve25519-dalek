/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U32.Field.FromLimbs
import Proofs.Helpers.Coords
import Proofs.Helpers.FieldElement2625
import Proofs.Helpers.ToField2625
public section

/-! # `ED25519_BASEPOINT_POINT`

The limbs are the RFC 8032 basepoint `curve25519.basepoint` in the extended coordinates
`(x : y : 1 : x y)`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Curve25519Dalek.backend.serial.u32.constants

namespace «i686-tables»

/-- `ED25519_BASEPOINT_POINT`: the extended coordinates `(x : y : 1 : x y)` of the basepoint;
limbs `< 2^26`. -/
@[step]
theorem ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT.«i686-tables» ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.toExtended = basepoint.toExtended ∧ r.LimbsLt 26 ⦄ := by
  unfold ED25519_BASEPOINT_POINT.«i686-tables»
  step as ⟨X, hX⟩
  step as ⟨Y, hY⟩
  step as ⟨Z, hZ⟩
  step as ⟨T, hT⟩
  have hXn : X.asNat =
      15112221349535400772501151409588531511454012693041857206046113283949847762202 := by
    rw [hX, asNat_def, Array.asNat2625_make]; decide
  have hYn : Y.asNat =
      46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
    rw [hY, asNat_def, Array.asNat2625_make]; decide
  have hZn : Z.asNat = 1 := by rw [hZ, asNat_def, Array.asNat2625_make]; decide
  have hTn : T.asNat % p = X.asNat * Y.asNat % p := by
    rw [hXn, hYn, hT, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  refine ⟨?_, ?_⟩
  · rw [edwards.EdwardsPoint.«i686-tables».toExtended_def, Point.toExtended,
      toField_mul_of_mod hTn, toField_eq_ofNat_of_asNat hXn, toField_eq_ofNat_of_asNat hYn,
      toField_eq_one_of_asNat hZn, basepoint_x_eq, basepoint_y_eq]
  · unfold edwards.EdwardsPoint.«i686-tables».LimbsLt
    subst hX hY hZ hT
    decide

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
theorem ED25519_BASEPOINT_POINT_spec_point :
    ED25519_BASEPOINT_POINT.«i686-tables» ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono ED25519_BASEPOINT_POINT_spec fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-tables».toPoint_def, hr]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «i686-tables»

namespace «i686-no-tables»

/-- `ED25519_BASEPOINT_POINT`: the extended coordinates `(x : y : 1 : x y)` of the basepoint;
limbs `< 2^26`. -/
@[step]
theorem ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT.«i686-no-tables» ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.toExtended = basepoint.toExtended ∧ r.LimbsLt 26 ⦄ := by
  unfold ED25519_BASEPOINT_POINT.«i686-no-tables»
  step as ⟨X, hX⟩
  step as ⟨Y, hY⟩
  step as ⟨Z, hZ⟩
  step as ⟨T, hT⟩
  have hXn : X.asNat =
      15112221349535400772501151409588531511454012693041857206046113283949847762202 := by
    rw [hX, asNat_def, Array.asNat2625_make]; decide
  have hYn : Y.asNat =
      46316835694926478169428394003475163141307993866256225615783033603165251855960 := by
    rw [hY, asNat_def, Array.asNat2625_make]; decide
  have hZn : Z.asNat = 1 := by rw [hZ, asNat_def, Array.asNat2625_make]; decide
  have hTn : T.asNat % p = X.asNat * Y.asNat % p := by
    rw [hXn, hYn, hT, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  refine ⟨?_, ?_⟩
  · rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Point.toExtended,
      toField_mul_of_mod hTn, toField_eq_ofNat_of_asNat hXn, toField_eq_ofNat_of_asNat hYn,
      toField_eq_one_of_asNat hZn, basepoint_x_eq, basepoint_y_eq]
  · unfold edwards.EdwardsPoint.«i686-no-tables».LimbsLt
    subst hX hY hZ hT
    decide

/-- `ED25519_BASEPOINT_POINT` represents the basepoint. -/
theorem ED25519_BASEPOINT_POINT_spec_point :
    ED25519_BASEPOINT_POINT.«i686-no-tables» ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono ED25519_BASEPOINT_POINT_spec fun r ⟨hr, hb⟩ => by
    rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-no-tables».toPoint_def, hr]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «i686-no-tables»

end Curve25519Dalek.backend.serial.u32.constants
