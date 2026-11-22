/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.edwards.affine

namespace «AffinePoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^52`. -/
@[step]
theorem to_edwards_toExtended (self : AffinePoint.«64bit-tables») (hself : self.LimbsLt 52) :
    to_edwards self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.LimbsLt 52 ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«64bit-tables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec (self : AffinePoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (to_edwards_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«64bit-tables».onCurve_iff,
      EdwardsPoint.«64bit-tables».toPoint_def,
      hr,
      ← AffinePoint.«64bit-tables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePoint64bit-tables»

namespace «AffinePoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^26`. -/
@[step]
theorem to_edwards_toExtended (self : AffinePoint.«32bit-tables») (hself : self.LimbsLt 26) :
    to_edwards self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.LimbsLt 26 ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«32bit-tables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec (self : AffinePoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (to_edwards_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«32bit-tables».onCurve_iff,
      EdwardsPoint.«32bit-tables».toPoint_def,
      hr,
      ← AffinePoint.«32bit-tables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePoint32bit-tables»

namespace «AffinePoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^52`. -/
@[step]
theorem to_edwards_toExtended (self : AffinePoint.«64bit-notables») (hself : self.LimbsLt 52) :
    to_edwards self ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.LimbsLt 52 ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«64bit-notables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec (self : AffinePoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (to_edwards_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«64bit-notables».onCurve_iff,
      EdwardsPoint.«64bit-notables».toPoint_def,
      hr,
      ← AffinePoint.«64bit-notables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePoint64bit-notables»

namespace «AffinePoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^26`. -/
@[step]
theorem to_edwards_toExtended (self : AffinePoint.«32bit-notables») (hself : self.LimbsLt 26) :
    to_edwards self ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.LimbsLt 26 ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«32bit-notables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec (self : AffinePoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (to_edwards_toExtended self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«32bit-notables».onCurve_iff,
      EdwardsPoint.«32bit-notables».toPoint_def,
      hr,
      ← AffinePoint.«32bit-notables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePoint32bit-notables»

end Curve25519Dalek.edwards.affine
