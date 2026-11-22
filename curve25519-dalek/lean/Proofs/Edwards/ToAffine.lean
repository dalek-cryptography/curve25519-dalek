/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Field.Invert
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_affine`: `(X / Z, Y / Z)` (`0⁻¹ = 0`), limbs `< 2^52`. -/
@[step]
theorem to_affine_coords (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52) :
    to_affine self ⦃ (r : affine.AffinePoint.«64bit-tables») =>
      r.x.toField = self.X.toField / self.Z.toField ∧
        r.y.toField = self.Y.toField / self.Z.toField ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold to_affine
  step as ⟨recip, hrecip1, hrecip0, hrecip_lt⟩
  step as ⟨x, hx, hx_lt⟩
  step as ⟨y, hy, hy_lt⟩
  rw [toField_mul_of_mod hx, toField_mul_of_mod hy, toField_inv_of_mod hrecip1 hrecip0,
    div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨rfl, rfl, hx_lt, hy_lt⟩

/-- `EdwardsPoint::to_affine` represents the same point. -/
theorem to_affine_spec (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_affine self ⦃ (r : affine.AffinePoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (to_affine_coords self hself) fun r ⟨hx, hy, hb⟩ => by
    obtain ⟨-, -, heq⟩ := (EdwardsPoint.«64bit-tables».onCurve_iff_equation self).mp hon
    have hr : r.OnCurve := by
      rw [affine.AffinePoint.«64bit-tables».onCurve_iff, hx, hy]
      exact heq
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [affine.AffinePoint.«64bit-tables».toPoint_x hr,
        EdwardsPoint.«64bit-tables».toPoint_x hon, hx]
    · rw [affine.AffinePoint.«64bit-tables».toPoint_y hr,
        EdwardsPoint.«64bit-tables».toPoint_y hon, hy]

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_affine`: `(X / Z, Y / Z)` (`0⁻¹ = 0`), limbs `< 2^26`. -/
@[step]
theorem to_affine_coords (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26) :
    to_affine self ⦃ (r : affine.AffinePoint.«32bit-tables») =>
      r.x.toField = self.X.toField / self.Z.toField ∧
        r.y.toField = self.Y.toField / self.Z.toField ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold to_affine
  step as ⟨recip, hrecip1, hrecip0, hrecip_lt⟩
  step as ⟨x, hx, hx_lt⟩
  step as ⟨y, hy, hy_lt⟩
  rw [toField_mul_of_mod hx, toField_mul_of_mod hy, toField_inv_of_mod hrecip1 hrecip0,
    div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨rfl, rfl, hx_lt, hy_lt⟩

/-- `EdwardsPoint::to_affine` represents the same point. -/
theorem to_affine_spec (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_affine self ⦃ (r : affine.AffinePoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (to_affine_coords self hself) fun r ⟨hx, hy, hb⟩ => by
    obtain ⟨-, -, heq⟩ := (EdwardsPoint.«32bit-tables».onCurve_iff_equation self).mp hon
    have hr : r.OnCurve := by
      rw [affine.AffinePoint.«32bit-tables».onCurve_iff, hx, hy]
      exact heq
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [affine.AffinePoint.«32bit-tables».toPoint_x hr,
        EdwardsPoint.«32bit-tables».toPoint_x hon, hx]
    · rw [affine.AffinePoint.«32bit-tables».toPoint_y hr,
        EdwardsPoint.«32bit-tables».toPoint_y hon, hy]

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_affine`: `(X / Z, Y / Z)` (`0⁻¹ = 0`), limbs `< 2^52`. -/
@[step]
theorem to_affine_coords (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52) :
    to_affine self ⦃ (r : affine.AffinePoint.«64bit-notables») =>
      r.x.toField = self.X.toField / self.Z.toField ∧
        r.y.toField = self.Y.toField / self.Z.toField ∧ r.LimbsLt 52 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold to_affine
  step as ⟨recip, hrecip1, hrecip0, hrecip_lt⟩
  step as ⟨x, hx, hx_lt⟩
  step as ⟨y, hy, hy_lt⟩
  rw [toField_mul_of_mod hx, toField_mul_of_mod hy, toField_inv_of_mod hrecip1 hrecip0,
    div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨rfl, rfl, hx_lt, hy_lt⟩

/-- `EdwardsPoint::to_affine` represents the same point. -/
theorem to_affine_spec (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_affine self ⦃ (r : affine.AffinePoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (to_affine_coords self hself) fun r ⟨hx, hy, hb⟩ => by
    obtain ⟨-, -, heq⟩ := (EdwardsPoint.«64bit-notables».onCurve_iff_equation self).mp hon
    have hr : r.OnCurve := by
      rw [affine.AffinePoint.«64bit-notables».onCurve_iff, hx, hy]
      exact heq
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [affine.AffinePoint.«64bit-notables».toPoint_x hr,
        EdwardsPoint.«64bit-notables».toPoint_x hon, hx]
    · rw [affine.AffinePoint.«64bit-notables».toPoint_y hr,
        EdwardsPoint.«64bit-notables».toPoint_y hon, hy]

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_affine`: `(X / Z, Y / Z)` (`0⁻¹ = 0`), limbs `< 2^26`. -/
@[step]
theorem to_affine_coords (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26) :
    to_affine self ⦃ (r : affine.AffinePoint.«32bit-notables») =>
      r.x.toField = self.X.toField / self.Z.toField ∧
        r.y.toField = self.Y.toField / self.Z.toField ∧ r.LimbsLt 26 ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold to_affine
  step as ⟨recip, hrecip1, hrecip0, hrecip_lt⟩
  step as ⟨x, hx, hx_lt⟩
  step as ⟨y, hy, hy_lt⟩
  rw [toField_mul_of_mod hx, toField_mul_of_mod hy, toField_inv_of_mod hrecip1 hrecip0,
    div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨rfl, rfl, hx_lt, hy_lt⟩

/-- `EdwardsPoint::to_affine` represents the same point. -/
theorem to_affine_spec (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_affine self ⦃ (r : affine.AffinePoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (to_affine_coords self hself) fun r ⟨hx, hy, hb⟩ => by
    obtain ⟨-, -, heq⟩ := (EdwardsPoint.«32bit-notables».onCurve_iff_equation self).mp hon
    have hr : r.OnCurve := by
      rw [affine.AffinePoint.«32bit-notables».onCurve_iff, hx, hy]
      exact heq
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [affine.AffinePoint.«32bit-notables».toPoint_x hr,
        EdwardsPoint.«32bit-notables».toPoint_x hon, hx]
    · rw [affine.AffinePoint.«32bit-notables».toPoint_y hr,
        EdwardsPoint.«32bit-notables».toPoint_y hon, hy]

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
