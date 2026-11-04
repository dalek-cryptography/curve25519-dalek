/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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

namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_affine`: `(X / Z, Y / Z)` (`0⁻¹ = 0`), limbs `< 2^52`. -/
@[step]
theorem to_affine_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    to_affine self ⦃ (r : affine.AffinePoint.«x86_64-tables») =>
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
theorem to_affine_spec_point (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_affine self ⦃ (r : affine.AffinePoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (to_affine_spec self hself) fun r ⟨hx, hy, hb⟩ => by
    obtain ⟨-, -, heq⟩ := (EdwardsPoint.«x86_64-tables».onCurve_iff_equation self).mp hon
    have hr : r.OnCurve := by
      rw [affine.AffinePoint.«x86_64-tables».onCurve_iff, hx, hy]
      exact heq
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [affine.AffinePoint.«x86_64-tables».toPoint_x hr,
        EdwardsPoint.«x86_64-tables».toPoint_x hon, hx]
    · rw [affine.AffinePoint.«x86_64-tables».toPoint_y hr,
        EdwardsPoint.«x86_64-tables».toPoint_y hon, hy]

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_affine`: `(X / Z, Y / Z)` (`0⁻¹ = 0`), limbs `< 2^26`. -/
@[step]
theorem to_affine_spec (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26) :
    to_affine self ⦃ (r : affine.AffinePoint.«i686-tables») =>
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
theorem to_affine_spec_point (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_affine self ⦃ (r : affine.AffinePoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (to_affine_spec self hself) fun r ⟨hx, hy, hb⟩ => by
    obtain ⟨-, -, heq⟩ := (EdwardsPoint.«i686-tables».onCurve_iff_equation self).mp hon
    have hr : r.OnCurve := by
      rw [affine.AffinePoint.«i686-tables».onCurve_iff, hx, hy]
      exact heq
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [affine.AffinePoint.«i686-tables».toPoint_x hr,
        EdwardsPoint.«i686-tables».toPoint_x hon, hx]
    · rw [affine.AffinePoint.«i686-tables».toPoint_y hr,
        EdwardsPoint.«i686-tables».toPoint_y hon, hy]

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_affine`: `(X / Z, Y / Z)` (`0⁻¹ = 0`), limbs `< 2^52`. -/
@[step]
theorem to_affine_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    to_affine self ⦃ (r : affine.AffinePoint.«x86_64-no-tables») =>
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
theorem to_affine_spec_point (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_affine self ⦃ (r : affine.AffinePoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (to_affine_spec self hself) fun r ⟨hx, hy, hb⟩ => by
    obtain ⟨-, -, heq⟩ := (EdwardsPoint.«x86_64-no-tables».onCurve_iff_equation self).mp hon
    have hr : r.OnCurve := by
      rw [affine.AffinePoint.«x86_64-no-tables».onCurve_iff, hx, hy]
      exact heq
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [affine.AffinePoint.«x86_64-no-tables».toPoint_x hr,
        EdwardsPoint.«x86_64-no-tables».toPoint_x hon, hx]
    · rw [affine.AffinePoint.«x86_64-no-tables».toPoint_y hr,
        EdwardsPoint.«x86_64-no-tables».toPoint_y hon, hy]

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_affine`: `(X / Z, Y / Z)` (`0⁻¹ = 0`), limbs `< 2^26`. -/
@[step]
theorem to_affine_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    to_affine self ⦃ (r : affine.AffinePoint.«i686-no-tables») =>
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
theorem to_affine_spec_point (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_affine self ⦃ (r : affine.AffinePoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (to_affine_spec self hself) fun r ⟨hx, hy, hb⟩ => by
    obtain ⟨-, -, heq⟩ := (EdwardsPoint.«i686-no-tables».onCurve_iff_equation self).mp hon
    have hr : r.OnCurve := by
      rw [affine.AffinePoint.«i686-no-tables».onCurve_iff, hx, hy]
      exact heq
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [affine.AffinePoint.«i686-no-tables».toPoint_x hr,
        EdwardsPoint.«i686-no-tables».toPoint_x hon, hx]
    · rw [affine.AffinePoint.«i686-no-tables».toPoint_y hr,
        EdwardsPoint.«i686-no-tables».toPoint_y hon, hy]

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
