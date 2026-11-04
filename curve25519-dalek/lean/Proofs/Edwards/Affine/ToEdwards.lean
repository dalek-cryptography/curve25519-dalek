/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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

namespace «AffinePointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^52`. -/
@[step]
theorem to_edwards_spec (self : AffinePoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    to_edwards self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.LimbsLt 52 ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«x86_64-tables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec_point (self : AffinePoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (to_edwards_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«x86_64-tables».onCurve_iff,
      EdwardsPoint.«x86_64-tables».toPoint_def,
      hr,
      ← AffinePoint.«x86_64-tables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePointx86_64-tables»

namespace «AffinePointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^26`. -/
@[step]
theorem to_edwards_spec (self : AffinePoint.«i686-tables») (hself : self.LimbsLt 26) :
    to_edwards self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.LimbsLt 26 ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«i686-tables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec_point (self : AffinePoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (to_edwards_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«i686-tables».onCurve_iff,
      EdwardsPoint.«i686-tables».toPoint_def,
      hr,
      ← AffinePoint.«i686-tables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePointi686-tables»

namespace «AffinePointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^52`. -/
@[step]
theorem to_edwards_spec (self : AffinePoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    to_edwards self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.LimbsLt 52 ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec_point (self : AffinePoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (to_edwards_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«x86_64-no-tables».onCurve_iff,
      EdwardsPoint.«x86_64-no-tables».toPoint_def,
      hr,
      ← AffinePoint.«x86_64-no-tables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePointx86_64-no-tables»

namespace «AffinePointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `AffinePoint::to_edwards`: `(x : y : 1 : x y)`, limbs `< 2^26`. -/
@[step]
theorem to_edwards_spec (self : AffinePoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    to_edwards self ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.toExtended = ⟨self.x.toField, self.y.toField, 1, self.x.toField * self.y.toField⟩ ∧
        r.LimbsLt 26 ⦄ := by
  obtain ⟨hx, hy⟩ := hself
  unfold to_edwards
  step as ⟨xy, hxy, hxy_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«i686-no-tables».toExtended_def, toField_mul_of_mod hxy,
      toField_eq_one_of_asNat hone]
  · exact ⟨hx, hy, limbs_lt_of_le (by decide) hone_lt, hxy_lt⟩

/-- `AffinePoint::to_edwards` represents the same point. -/
theorem to_edwards_spec_point (self : AffinePoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_edwards self ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = self.toPoint ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (to_edwards_spec self hself) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«i686-no-tables».onCurve_iff,
      EdwardsPoint.«i686-no-tables».toPoint_def,
      hr,
      ← AffinePoint.«i686-no-tables».toExtended_toPoint hon]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «AffinePointi686-no-tables»

end Curve25519Dalek.edwards.affine
